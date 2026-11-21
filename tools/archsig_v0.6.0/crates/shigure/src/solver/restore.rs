//! 具体解・自由パラメータからの操作式・状態 Law・状態比較 h・語翻訳 τ の復元と
//! 独立した数学モデル再評価検算（G-140 E2・P1.2・P4・P6 / R3.2–R3.3）。

use crate::algebra::{
    AffineSolutionQ, ExprBindings, FpElem, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder,
    rabinowitsch_solve, solve_affine_q,
};
use crate::ir::change::EvalCondition;
use crate::ir::presentation::ComparisonPair;
use crate::ir::result::{ReevalCheck, RestoredArtifact, SilenceReason};
use crate::ir::term::{PolyExpr, ScalarLit};
use crate::solver::preservation::{
    build_preservation_obligations, compute_preservation_locus_q, extract_closed_residuals_fp,
    extract_closed_residuals_z, is_stratum_covered_by_union, map_algebra_silence,
    substitute_poly_expr,
};
use crate::solver::restore_format::{
    format_restored_pair_fp, format_restored_pair_q, format_restored_pair_z,
    substitute_comparison_pair,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// 復元時に抽出されたパラメータ代入（pivot 変数 -> 自由変数式、および自由変数一覧）。
#[derive(Clone, Debug)]
pub struct ExtractedSubstitutionQ {
    pub param_subst: BTreeMap<String, PolyExpr>,
    pub display_assignments: BTreeMap<String, String>,
    pub free_parameters: Vec<String>,
    pub remaining_nonlinear: Vec<Poly<Rat>>,
}

/// Q 上のパラメータ方程式列からアフィン部分を抽出し、RREF により pivot 変数を
/// 自由パラメータの一次式として解く。
///
/// 返り値が `Ok(None)` のときはアフィン部分自体が矛盾（空集合）。
pub fn extract_affine_substitution_q(
    equations: &[Poly<Rat>],
    param_vars: &VarOrder,
    prefer_z_literals: bool,
) -> Result<Option<ExtractedSubstitutionQ>, SilenceReason> {
    let n = param_vars.len();
    let mut affine_polys = Vec::new();
    let mut nonlinear_polys = Vec::new();
    for eq in equations {
        if eq.is_zero() {
            continue;
        }
        if eq.is_affine() {
            affine_polys.push(eq.clone());
        } else {
            nonlinear_polys.push(eq.clone());
        }
    }

    if affine_polys.is_empty() {
        return Ok(Some(ExtractedSubstitutionQ {
            param_subst: BTreeMap::new(),
            display_assignments: BTreeMap::new(),
            free_parameters: param_vars.vars().to_vec(),
            remaining_nonlinear: nonlinear_polys,
        }));
    }

    let (matrix, rhs) = polys_to_affine_system_q(&affine_polys, n);
    match solve_affine_q(&matrix, &rhs, n).map_err(map_algebra_silence)? {
        AffineSolutionQ::Inconsistent { .. } => return Ok(None),
        AffineSolutionQ::Consistent { .. } => {}
    }

    // RREF を直接計算し、各 pivot 変数 x_p = b[r] - sum_{free} a[r][free] * x_free を構築する。
    let (rref_a, rref_b, pivot_cols) = rref_q(&matrix, &rhs, n);
    let pivot_set: BTreeSet<usize> = pivot_cols.iter().map(|&(_, c)| c).collect();
    let free_indices: Vec<usize> = (0..n).filter(|c| !pivot_set.contains(c)).collect();
    let free_parameters: Vec<String> = free_indices
        .iter()
        .map(|&c| param_vars.vars()[c].clone())
        .collect();
    let free_order = VarOrder::new(free_parameters.clone()).map_err(map_algebra_silence)?;
    let free_bind = ExprBindings::params_only(&free_order);

    let mut param_subst = BTreeMap::new();
    let mut display_assignments = BTreeMap::new();
    for &(row, pcol) in &pivot_cols {
        let mut terms: Vec<(String, Rat)> = Vec::new();
        for &fcol in &free_indices {
            if !rref_a[row][fcol].is_zero() {
                terms.push((param_vars.vars()[fcol].clone(), -&rref_a[row][fcol]));
            }
        }
        let expr = affine_expr_q(&rref_b[row], &terms, prefer_z_literals);
        let poly_disp = Poly::from_expr_q(&expr, &free_bind)
            .map_err(map_algebra_silence)?
            .display(&free_order, MonomialOrder::Grevlex);
        let pname = param_vars.vars()[pcol].clone();
        param_subst.insert(pname.clone(), expr);
        display_assignments.insert(pname, poly_disp);
    }

    // 残余の非線形多項式にも抽出したアフィン代入を適用し、自由変数環へ縮約する。
    let mut remaining_nonlinear = Vec::new();
    if !nonlinear_polys.is_empty() {
        let subst_polys: Vec<Poly<Rat>> = (0..n)
            .map(|idx| {
                let name = &param_vars.vars()[idx];
                if let Some(expr) = param_subst.get(name) {
                    Poly::from_expr_q(expr, &free_bind).map_err(map_algebra_silence)
                } else {
                    let fidx = free_order
                        .index_of(name)
                        .expect("non-pivot parameter must be in free_order");
                    Ok(Poly::var(free_order.len(), fidx, Rat::zero()))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        for nl in &nonlinear_polys {
            let reduced = eval_poly_with_polys_q(nl, &subst_polys, free_order.len())?;
            if !reduced.is_zero() {
                remaining_nonlinear.push(reduced);
            }
        }
    }

    Ok(Some(ExtractedSubstitutionQ {
        param_subst,
        display_assignments,
        free_parameters,
        remaining_nonlinear,
    }))
}

/// Q アフィン解空間 `particular + span(kernel_basis)` 上で、`invertibles` がすべて非零となる
/// 具体的な有理点（整数パラメータ選択による）を決定的に探索し検算する。
pub fn find_witness_point_q(
    particular: &[Rat],
    kernel_basis: &[Vec<Rat>],
    equations: &[Poly<Rat>],
    invertibles: &[Poly<Rat>],
) -> Result<Option<Vec<Rat>>, SilenceReason> {
    let check_point = |pt: &[Rat]| -> Result<bool, SilenceReason> {
        for eq in equations {
            if !eq.eval_at(pt).map_err(map_algebra_silence)?.is_zero() {
                return Ok(false);
            }
        }
        for inv in invertibles {
            if inv.eval_at(pt).map_err(map_algebra_silence)?.is_zero() {
                return Ok(false);
            }
        }
        Ok(true)
    };

    if kernel_basis.is_empty() {
        return Ok(check_point(particular)?.then(|| particular.to_vec()));
    }

    // 各自由座標に小さな整数列を当て、開条件をすべて満たす具体点を探索する。
    let k = kernel_basis.len();
    let max_samples = 256usize;
    let mut tested = 0usize;

    // 1. まず全自由変数が同一値 c ∈ {0, 1, -1, 2, -2, ..., 16, -16} の対角線候補を試す。
    let mut diag_vals = vec![0i64];
    for v in 1..=16i64 {
        diag_vals.push(v);
        diag_vals.push(-v);
    }
    for c in diag_vals {
        let pt = combine_affine_q(particular, kernel_basis, &vec![c; k]);
        tested += 1;
        if check_point(&pt)? {
            return Ok(Some(pt));
        }
    }

    // 2. 次に決定的な線形合同・進数格子で異成分の整数ベクトルを試す（最大 max_samples 点）。
    let digits = [1i64, -1, 2, -2, 3, -3, 5];
    let base = digits.len();
    for idx in 0..max_samples.saturating_sub(tested) {
        let mut x = idx + 1;
        let mut coeffs = Vec::with_capacity(k);
        for d in 0..k {
            let slot = (x + d * 3) % base;
            coeffs.push(digits[slot]);
            x /= base;
        }
        let pt = combine_affine_q(particular, kernel_basis, &coeffs);
        if check_point(&pt)? {
            return Ok(Some(pt));
        }
    }

    Ok(None)
}

/// Z アフィン解空間 `particular + span(kernel_basis)` 上で、`invertibles` がすべて非零となる
/// 具体的な整数点を決定的に探索し検算する。
pub fn find_witness_point_z(
    particular: &[BigInt],
    kernel_basis: &[Vec<BigInt>],
    equations: &[Poly<BigInt>],
    invertibles: &[Poly<BigInt>],
) -> Result<Option<Vec<BigInt>>, SilenceReason> {
    let check_point = |pt: &[BigInt]| -> Result<bool, SilenceReason> {
        for eq in equations {
            if !eq.eval_at(pt).map_err(map_algebra_silence)?.is_zero() {
                return Ok(false);
            }
        }
        for inv in invertibles {
            if inv.eval_at(pt).map_err(map_algebra_silence)?.is_zero() {
                return Ok(false);
            }
        }
        Ok(true)
    };

    if kernel_basis.is_empty() {
        return Ok(check_point(particular)?.then(|| particular.to_vec()));
    }

    let k = kernel_basis.len();
    let mut diag_vals = vec![0i64];
    for v in 1..=16i64 {
        diag_vals.push(v);
        diag_vals.push(-v);
    }
    for c in diag_vals {
        let pt = combine_affine_z(particular, kernel_basis, &vec![c; k]);
        if check_point(&pt)? {
            return Ok(Some(pt));
        }
    }

    let digits = [1i64, -1, 2, -2, 3, -3, 5];
    let base = digits.len();
    for idx in 0..220usize {
        let mut x = idx + 1;
        let mut coeffs = Vec::with_capacity(k);
        for d in 0..k {
            let slot = (x + d * 3) % base;
            coeffs.push(digits[slot]);
            x /= base;
        }
        let pt = combine_affine_z(particular, kernel_basis, &coeffs);
        if check_point(&pt)? {
            return Ok(Some(pt));
        }
    }

    Ok(None)
}

/// Q（または代数閉包）上の抽出代入から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_q(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    extra_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    extracted: &ExtractedSubstitutionQ,
) -> Result<RestoredArtifact, SilenceReason> {
    let restored_pair = substitute_comparison_pair(pair, &extracted.param_subst);
    let free_order =
        VarOrder::new(extracted.free_parameters.clone()).map_err(map_algebra_silence)?;
    let free_bind = ExprBindings::params_only(&free_order);

    let (operations, state_laws, state_comparisons, word_translation) =
        format_restored_pair_q(&restored_pair, &extracted.free_parameters)?;

    // extra_invs を自由変数空間へ縮約する（非閉な商環層の開条件を検算にも引き継ぐ）。
    let subst_polys: Vec<Poly<Rat>> = (0..param_vars.len())
        .map(|idx| {
            let name = &param_vars.vars()[idx];
            if let Some(expr) = extracted.param_subst.get(name) {
                Poly::from_expr_q(expr, &free_bind).map_err(map_algebra_silence)
            } else {
                let fidx = free_order
                    .index_of(name)
                    .expect("non-pivot parameter must be in free_order");
                Ok(Poly::var(free_order.len(), fidx, Rat::zero()))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut reduced_extra_invs = Vec::with_capacity(extra_invs.len());
    for inv in extra_invs {
        reduced_extra_invs.push(eval_poly_with_polys_q(inv, &subst_polys, free_order.len())?);
    }

    // 独立再評価検算: 復元後の ComparisonPair から保存義務を再構成して成立を確認する。
    let reeval = reeval_restored_pair_q(
        &restored_pair,
        eval_cond,
        &extracted.param_subst,
        &extracted.remaining_nonlinear,
        &reduced_extra_invs,
        &free_order,
        &free_bind,
    )?;

    Ok(RestoredArtifact {
        parameter_assignments: extracted.display_assignments.clone(),
        free_parameters: extracted.free_parameters.clone(),
        operations,
        state_laws,
        state_comparisons,
        word_translation,
        reeval,
    })
}

/// Z 上の具体的整数点から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_z(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    point: &[BigInt],
) -> Result<RestoredArtifact, SilenceReason> {
    let mut param_subst = BTreeMap::new();
    let mut display_assignments = BTreeMap::new();
    for (name, val) in param_vars.vars().iter().zip(point) {
        param_subst.insert(name.clone(), PolyExpr::Const(ScalarLit::Z(val.clone())));
        display_assignments.insert(name.clone(), val.to_string());
    }
    let restored_pair = substitute_comparison_pair(pair, &param_subst);
    let (operations, state_laws, state_comparisons, word_translation) =
        format_restored_pair_z(&restored_pair)?;

    // 独立再評価検算: 復元後の ComparisonPair から直接 Z 残差を再構成し全零・評価条件一致を検証。
    let obligations = build_preservation_obligations(&restored_pair)?;
    let empty_bind =
        ExprBindings::params_only(&VarOrder::new(vec![]).map_err(map_algebra_silence)?);
    let mut matched = true;
    let mut fail_detail = String::new();

    if let Some(residuals) = extract_closed_residuals_z(&obligations, &[])? {
        if residuals.iter().any(|r| !r.is_zero()) {
            matched = false;
            fail_detail = "restored Z presentation has nonzero preservation residual".to_owned();
        }
    } else {
        // 状態 Law を持つ場合は Q 商環検算へフォールバック。
        let zero_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
        let locus = compute_preservation_locus_q(&obligations, &zero_order)?;
        if locus.strata.is_empty() {
            matched = false;
            fail_detail = "restored presentation violates quotient state-law closure".to_owned();
        }
    }

    if matched && let Some(cond) = eval_cond {
        let empty = BTreeMap::new();
        for eq in &cond.equations {
            let sub = substitute_poly_expr(&eq.expr, &empty, &empty, &param_subst);
            let p = Poly::from_expr_z(&sub, &empty_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                matched = false;
                fail_detail = format!(
                    "eval equation `{}` did not vanish after restoration",
                    eq.name
                );
                break;
            }
        }
        if matched {
            for inv in &cond.invertibles {
                let sub = substitute_poly_expr(&inv.expr, &empty, &empty, &param_subst);
                let p = Poly::from_expr_z(&sub, &empty_bind).map_err(map_algebra_silence)?;
                if p.is_zero() {
                    matched = false;
                    fail_detail =
                        format!("eval invertible `{}` vanished after restoration", inv.name);
                    break;
                }
            }
        }
    }

    let detail = if matched {
        format!(
            "verified all {} preservation obligations and evaluation conditions on restored Z model",
            obligations.len()
        )
    } else {
        fail_detail
    };

    Ok(RestoredArtifact {
        parameter_assignments: display_assignments,
        free_parameters: vec![],
        operations,
        state_laws,
        state_comparisons,
        word_translation,
        reeval: ReevalCheck {
            checked: true,
            matched,
            detail,
        },
    })
}

/// F_p 上の具体点から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_fp(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    point: &[FpElem],
    modulus: &BigUint,
) -> Result<RestoredArtifact, SilenceReason> {
    let mut param_subst = BTreeMap::new();
    let mut display_assignments = BTreeMap::new();
    for (name, val) in param_vars.vars().iter().zip(point) {
        param_subst.insert(
            name.clone(),
            PolyExpr::Const(ScalarLit::Fp {
                value: val.value().clone(),
                modulus: modulus.clone(),
            }),
        );
        display_assignments.insert(name.clone(), val.to_string());
    }
    let restored_pair = substitute_comparison_pair(pair, &param_subst);
    let (operations, state_laws, state_comparisons, word_translation) =
        format_restored_pair_fp(&restored_pair, modulus)?;

    let obligations = build_preservation_obligations(&restored_pair)?;
    let empty_bind =
        ExprBindings::params_only(&VarOrder::new(vec![]).map_err(map_algebra_silence)?);
    let mut matched = true;
    let mut fail_detail = String::new();

    if let Some(residuals) = extract_closed_residuals_fp(&obligations, &[], modulus)? {
        if residuals.iter().any(|r| !r.is_zero()) {
            matched = false;
            fail_detail = "restored Fp presentation has nonzero preservation residual".to_owned();
        }
    } else {
        matched = false;
        fail_detail = "quotient state-law re-evaluation over Fp is out of scope".to_owned();
    }

    if matched && let Some(cond) = eval_cond {
        let empty = BTreeMap::new();
        for eq in &cond.equations {
            let sub = substitute_poly_expr(&eq.expr, &empty, &empty, &param_subst);
            let p = Poly::from_expr_fp(&sub, &empty_bind, modulus).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                matched = false;
                fail_detail = format!("eval equation `{}` did not vanish over Fp", eq.name);
                break;
            }
        }
        if matched {
            for inv in &cond.invertibles {
                let sub = substitute_poly_expr(&inv.expr, &empty, &empty, &param_subst);
                let p =
                    Poly::from_expr_fp(&sub, &empty_bind, modulus).map_err(map_algebra_silence)?;
                if p.is_zero() {
                    matched = false;
                    fail_detail = format!("eval invertible `{}` vanished over Fp", inv.name);
                    break;
                }
            }
        }
    }

    let detail = if matched {
        format!(
            "verified all {} preservation obligations and evaluation conditions on restored Fp({modulus}) model",
            obligations.len()
        )
    } else {
        fail_detail
    };

    Ok(RestoredArtifact {
        parameter_assignments: display_assignments,
        free_parameters: vec![],
        operations,
        state_laws,
        state_comparisons,
        word_translation,
        reeval: ReevalCheck {
            checked: true,
            matched,
            detail,
        },
    })
}

fn reeval_restored_pair_q(
    restored_pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_subst: &BTreeMap<String, PolyExpr>,
    remaining_nonlinear: &[Poly<Rat>],
    extra_invs: &[Poly<Rat>],
    free_order: &VarOrder,
    free_bind: &ExprBindings,
) -> Result<ReevalCheck, SilenceReason> {
    let obligations = build_preservation_obligations(restored_pair)?;
    let locus = compute_preservation_locus_q(&obligations, free_order)?;

    let empty = BTreeMap::new();
    let mut eval_eqs = remaining_nonlinear.to_vec();
    let mut eval_invs = extra_invs.to_vec();
    if let Some(cond) = eval_cond {
        for eq in &cond.equations {
            let sub = substitute_poly_expr(&eq.expr, &empty, &empty, param_subst);
            let p = Poly::from_expr_q(&sub, free_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                eval_eqs.push(p);
            }
        }
        for inv in &cond.invertibles {
            let sub = substitute_poly_expr(&inv.expr, &empty, &empty, param_subst);
            let p = Poly::from_expr_q(&sub, free_bind).map_err(map_algebra_silence)?;
            if !eval_invs.contains(&p) {
                eval_invs.push(p);
            }
        }
    }

    // 復元後の評価条件ローカスが非空かつ、その全点が復元後の保存ローカスに含まれることを厳密検算する。
    let target_rab =
        rabinowitsch_solve(&eval_eqs, &eval_invs, free_order).map_err(map_algebra_silence)?;
    if target_rab.is_empty_over_closure || locus.strata.is_empty() {
        return Ok(ReevalCheck {
            checked: true,
            matched: false,
            detail: "restored model violates preservation or evaluation conditions".to_owned(),
        });
    }

    let sat_gb = GroebnerBasis::compute(
        &target_rab.parameter_equations,
        free_order.clone(),
        MonomialOrder::Grevlex,
    )
    .map_err(map_algebra_silence)?;

    for res_poly in &locus.closure_ideal {
        let nf = sat_gb.normal_form(res_poly).map_err(map_algebra_silence)?;
        if !nf.is_zero() {
            return Ok(ReevalCheck {
                checked: true,
                matched: false,
                detail: format!(
                    "restored preservation residual `{}` did not vanish modulo remaining constraints",
                    res_poly.display(free_order, MonomialOrder::Grevlex)
                ),
            });
        }
    }

    if !locus.is_zariski_closed
        && !is_stratum_covered_by_union(
            &target_rab.parameter_equations,
            &eval_invs,
            &locus.strata,
            free_order,
        )?
    {
        return Ok(ReevalCheck {
            checked: true,
            matched: false,
            detail: "restored locus is not contained in non-closed quotient preservation strata"
                .to_owned(),
        });
    }

    Ok(ReevalCheck {
        checked: true,
        matched: true,
        detail: format!(
            "verified all {} preservation obligations and evaluation conditions on restored Q model",
            obligations.len()
        ),
    })
}

pub fn polys_to_affine_system_q(polys: &[Poly<Rat>], num_vars: usize) -> (Vec<Vec<Rat>>, Vec<Rat>) {
    let mut matrix = Vec::with_capacity(polys.len());
    let mut rhs = Vec::with_capacity(polys.len());
    for p in polys {
        assert!(
            p.is_affine(),
            "polys_to_affine_system_q requires affine polynomials"
        );
        let mut row = vec![Rat::zero(); num_vars];
        let mut c0 = Rat::zero();
        for (mono, coeff) in p.terms() {
            if mono.is_one() {
                c0 = coeff.clone();
            } else if let Some(idx) = mono.exps().iter().position(|&e| e == 1) {
                row[idx] = coeff.clone();
            }
        }
        matrix.push(row);
        rhs.push(-&c0);
    }
    (matrix, rhs)
}

pub fn polys_to_affine_system_z(
    polys: &[Poly<BigInt>],
    num_vars: usize,
) -> (Vec<Vec<BigInt>>, Vec<BigInt>) {
    let mut matrix = Vec::with_capacity(polys.len());
    let mut rhs = Vec::with_capacity(polys.len());
    for p in polys {
        assert!(
            p.is_affine(),
            "polys_to_affine_system_z requires affine polynomials"
        );
        let mut row = vec![BigInt::zero(); num_vars];
        let mut c0 = BigInt::zero();
        for (mono, coeff) in p.terms() {
            if mono.is_one() {
                c0 = coeff.clone();
            } else if let Some(idx) = mono.exps().iter().position(|&e| e == 1) {
                row[idx] = coeff.clone();
            }
        }
        matrix.push(row);
        rhs.push(-c0);
    }
    (matrix, rhs)
}

type RrefResultQ = (Vec<Vec<Rat>>, Vec<Rat>, Vec<(usize, usize)>);

fn rref_q(matrix: &[Vec<Rat>], rhs: &[Rat], num_vars: usize) -> RrefResultQ {
    let m = matrix.len();
    let mut a = matrix.to_vec();
    let mut b = rhs.to_vec();
    let mut pivots = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..num_vars {
        if pivot_row >= m {
            break;
        }
        let Some(found) = (pivot_row..m).find(|&r| !a[r][col].is_zero()) else {
            continue;
        };
        a.swap(pivot_row, found);
        b.swap(pivot_row, found);
        let inv = a[pivot_row][col].inv().expect("nonzero pivot");
        for val in &mut a[pivot_row] {
            *val = &*val * &inv;
        }
        b[pivot_row] = &b[pivot_row] * &inv;
        for r in 0..m {
            if r == pivot_row || a[r][col].is_zero() {
                continue;
            }
            let factor = a[r][col].clone();
            let piv = a[pivot_row][col..num_vars].to_vec();
            for (dst, pv) in a[r][col..num_vars].iter_mut().zip(&piv) {
                *dst = &*dst - &(&factor * pv);
            }
            b[r] = &b[r] - &(&factor * &b[pivot_row]);
        }
        pivots.push((pivot_row, col));
        pivot_row += 1;
    }
    (a, b, pivots)
}

fn rat_to_expr(r: &Rat, prefer_z: bool) -> PolyExpr {
    if prefer_z && r.den().is_one() {
        PolyExpr::Const(ScalarLit::Z(r.num().clone()))
    } else {
        PolyExpr::Const(ScalarLit::Q {
            num: r.num().clone(),
            den: r.den().clone(),
        })
    }
}

fn affine_expr_q(constant: &Rat, terms: &[(String, Rat)], prefer_z: bool) -> PolyExpr {
    let mut acc: Option<PolyExpr> = if !constant.is_zero() {
        Some(rat_to_expr(constant, prefer_z))
    } else {
        None
    };
    for (name, coeff) in terms {
        if coeff.is_zero() {
            continue;
        }
        let var = PolyExpr::ParamVar(name.clone());
        let term = if coeff.is_one() {
            var
        } else if *coeff == -&Rat::one() {
            PolyExpr::negate(var)
        } else {
            PolyExpr::prod(rat_to_expr(coeff, prefer_z), var)
        };
        acc = Some(match acc {
            Some(prev) => PolyExpr::sum(prev, term),
            None => term,
        });
    }
    acc.unwrap_or_else(|| rat_to_expr(&Rat::zero(), prefer_z))
}

fn eval_poly_with_polys_q(
    poly: &Poly<Rat>,
    subst: &[Poly<Rat>],
    out_vars: usize,
) -> Result<Poly<Rat>, SilenceReason> {
    let mut acc = Poly::zero(out_vars, Rat::zero());
    for (mono, coeff) in poly.terms() {
        let mut term = Poly::constant(out_vars, coeff.clone());
        for (idx, &e) in mono.exps().iter().enumerate() {
            if e > 0 {
                let p = subst[idx].checked_pow(e).map_err(map_algebra_silence)?;
                term = term.checked_mul(&p).map_err(map_algebra_silence)?;
            }
        }
        acc = acc.add(&term);
    }
    Ok(acc)
}

fn combine_affine_q(particular: &[Rat], kernel: &[Vec<Rat>], coeffs: &[i64]) -> Vec<Rat> {
    let mut pt = particular.to_vec();
    for (vec, &c) in kernel.iter().zip(coeffs) {
        if c == 0 {
            continue;
        }
        let rc = Rat::from_int(BigInt::from(c));
        for (dst, v) in pt.iter_mut().zip(vec) {
            *dst = &*dst + &(&rc * v);
        }
    }
    pt
}

fn combine_affine_z(particular: &[BigInt], kernel: &[Vec<BigInt>], coeffs: &[i64]) -> Vec<BigInt> {
    let mut pt = particular.to_vec();
    for (vec, &c) in kernel.iter().zip(coeffs) {
        if c == 0 {
            continue;
        }
        let bc = BigInt::from(c);
        for (dst, v) in pt.iter_mut().zip(vec) {
            *dst += &bc * v;
        }
    }
    pt
}

/// 座標固定方程式 `a * param + b = 0`（単変数 1 次、`a != 0`）を抽出し、
/// `(param_name, -b/a)` を返す。非座標固定の式なら `None`。
pub fn extract_coordinate_fix_q(poly: &Poly<Rat>, vars: &VarOrder) -> Option<(String, Rat)> {
    if poly.total_degree() != 1 {
        return None;
    }
    let mut var_idx: Option<usize> = None;
    let mut var_coeff = Rat::zero();
    let mut const_coeff = Rat::zero();
    for (mono, coeff) in poly.terms() {
        if mono.is_one() {
            const_coeff = coeff.clone();
        } else {
            let idx = mono.exps().iter().position(|&e| e == 1)?;
            if var_idx.is_some() {
                // 2 変数以上の一次結合（例: x - y = 0）は座標面固定ではない。
                return None;
            }
            var_idx = Some(idx);
            var_coeff = coeff.clone();
        }
    }
    let idx = var_idx?;
    let val = (&(-&const_coeff) / &var_coeff)?;
    Some((vars.vars()[idx].clone(), val))
}

/// F_p 上の座標固定方程式 `a * param + b = 0`（単変数 1 次、`a != 0`）を抽出する。
pub fn extract_coordinate_fix_fp(poly: &Poly<FpElem>, vars: &VarOrder) -> Option<(String, FpElem)> {
    if poly.total_degree() != 1 {
        return None;
    }
    let mut var_idx: Option<usize> = None;
    let mut var_coeff = poly.zero_coeff().clone();
    let mut const_coeff = poly.zero_coeff().clone();
    for (mono, coeff) in poly.terms() {
        if mono.is_one() {
            const_coeff = coeff.clone();
        } else {
            let idx = mono.exps().iter().position(|&e| e == 1)?;
            if var_idx.is_some() {
                return None;
            }
            var_idx = Some(idx);
            var_coeff = coeff.clone();
        }
    }
    let idx = var_idx?;
    let inv = var_coeff.inv()?;
    let val = const_coeff.neg_elem().mul_checked(&inv)?;
    Some((vars.vars()[idx].clone(), val))
}
