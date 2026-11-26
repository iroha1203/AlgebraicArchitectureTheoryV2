//! 具体解・自由パラメータからの操作式・状態 Law・状態比較 h・語翻訳 τ の復元と
//! 独立した数学モデル再評価検算（G-140 E2・P1.2・P4・P6 / R3.2–R3.3）。

use crate::algebra::{
    AlgebraError, ExprBindings, FpElem, GroebnerBasis, MonomialOrder, Poly, Rat, RingCoeff,
    VarOrder, rabinowitsch_solve,
};
use crate::ir::change::EvalCondition;
use crate::ir::presentation::ComparisonPair;
use crate::ir::result::{ReevalCheck, RestoredArtifact, SilenceReason};
use crate::ir::term::{PolyExpr, ScalarLit};
use crate::solver::preservation::{
    PreservationObligation, build_preservation_obligations, compute_preservation_locus_q,
    extract_closed_residuals_fp, extract_closed_residuals_z, is_stratum_covered_by_union,
    map_algebra_silence, substitute_poly_expr,
};
use crate::solver::restore_format::{
    FormattedRestoredMaps, format_restored_pair_fp, format_restored_pair_q, format_restored_pair_z,
    substitute_comparison_pair,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// 復元時に抽出されたパラメータ代入（pivot 変数 -> 未代入変数式、および自由変数一覧）。
#[derive(Clone, Debug)]
pub struct ExtractedSubstitutionQ {
    pub param_subst: BTreeMap<String, PolyExpr>,
    pub display_assignments: BTreeMap<String, String>,
    /// 式展開に残る未代入パラメータ全体（非線形制約を受ける変数を含む）。
    pub unassigned_parameters: Vec<String>,
    /// 非線形制約にも現れない真の自由パラメータのみ（`RestoredArtifact.free_parameters` 用、F6）。
    pub free_parameters: Vec<String>,
    pub remaining_nonlinear: Vec<Poly<Rat>>,
}

fn filter_truly_free_parameters(
    unassigned: &[String],
    remaining_nonlinear: &[Poly<Rat>],
) -> Vec<String> {
    let mut constrained_indices = BTreeSet::new();
    for nl in remaining_nonlinear {
        for mono in nl.terms().keys() {
            for (idx, &e) in mono.exps().iter().enumerate() {
                if e > 0 {
                    constrained_indices.insert(idx);
                }
            }
        }
    }
    unassigned
        .iter()
        .enumerate()
        .filter(|(idx, _)| !constrained_indices.contains(idx))
        .map(|(_, name)| name.clone())
        .collect()
}

/// Q 上のパラメータ方程式列からアフィン部分を抽出し、RREF により pivot 変数を
/// 未代入パラメータの一次式として解く。
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
        let unassigned = param_vars.vars().to_vec();
        let free_parameters = filter_truly_free_parameters(&unassigned, &nonlinear_polys);
        return Ok(Some(ExtractedSubstitutionQ {
            param_subst: BTreeMap::new(),
            display_assignments: BTreeMap::new(),
            unassigned_parameters: unassigned,
            free_parameters,
            remaining_nonlinear: nonlinear_polys,
        }));
    }

    let (matrix, rhs) = polys_to_affine_system_q(&affine_polys, n)?;
    // 単一の RREF で整合性判定と pivot 表現 x_p = b[r] - sum_{free} a[r][free] * x_free を同時に得る。
    let (rref_a, rref_b, pivot_cols) = rref_q(&matrix, &rhs, n);
    if (pivot_cols.len()..rref_b.len()).any(|r| !rref_b[r].is_zero()) {
        return Ok(None);
    }
    let pivot_set: BTreeSet<usize> = pivot_cols.iter().map(|&(_, c)| c).collect();
    let free_indices: Vec<usize> = (0..n).filter(|c| !pivot_set.contains(c)).collect();
    let unassigned_parameters: Vec<String> = free_indices
        .iter()
        .map(|&c| param_vars.vars()[c].clone())
        .collect();
    let free_order = VarOrder::new(unassigned_parameters.clone()).map_err(map_algebra_silence)?;
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

    // 残余の非線形多項式にも抽出したアフィン代入を適用し、未代入変数環へ縮約する。
    let mut remaining_nonlinear = Vec::new();
    if !nonlinear_polys.is_empty() {
        let subst_polys =
            build_param_subst_polys_q(param_vars, &param_subst, &free_order, &free_bind)?;
        for nl in &nonlinear_polys {
            let reduced = eval_poly_with_polys_q(nl, &subst_polys, free_order.len())?;
            if !reduced.is_zero() {
                remaining_nonlinear.push(reduced);
            }
        }
    }

    let free_parameters =
        filter_truly_free_parameters(&unassigned_parameters, &remaining_nonlinear);

    Ok(Some(ExtractedSubstitutionQ {
        param_subst,
        display_assignments,
        unassigned_parameters,
        free_parameters,
        remaining_nonlinear,
    }))
}

/// 決定論的かつ重複のない小さな整数係数サンプル列を生成する。
fn witness_sample_vectors(k: usize) -> Vec<Vec<i64>> {
    let mut seen: BTreeSet<Vec<i64>> = BTreeSet::new();
    let mut out = Vec::new();
    let mut push_unique = |v: Vec<i64>| {
        if seen.insert(v.clone()) {
            out.push(v);
        }
    };

    if k == 1 {
        push_unique(vec![0]);
        for v in 1..=64i64 {
            push_unique(vec![v]);
            push_unique(vec![-v]);
        }
        return out;
    }

    // 1. 対角線候補 c ∈ {0, 1, -1, 2, -2, ..., 16, -16}。
    push_unique(vec![0; k]);
    for v in 1..=16i64 {
        push_unique(vec![v; k]);
        push_unique(vec![-v; k]);
    }
    // 2. 座標軸方向と異成分の格子点（重複を除外し最大 256 点まで）。
    let digits = [0i64, 1, -1, 2, -2, 3, -3, 5];
    let base = digits.len();
    for idx in 1..=512usize {
        let mut x = idx;
        let mut coeffs = Vec::with_capacity(k);
        for d in 0..k {
            coeffs.push(digits[(x + d * 3) % base]);
            x /= base;
        }
        if seen.insert(coeffs.clone()) {
            out.push(coeffs);
            if out.len() >= 256 {
                break;
            }
        }
    }
    out
}

/// Q アフィン解空間 `particular + span(kernel_basis)` 上で、`invertibles` がすべて非零となる
/// 具体的な有理点（整数パラメータ選択による）を決定的に探索し検算する。
pub fn find_witness_point_q(
    particular: &[Rat],
    kernel_basis: &[Vec<Rat>],
    equations: &[Poly<Rat>],
    invertibles: &[Poly<Rat>],
) -> Result<Option<Vec<Rat>>, SilenceReason> {
    find_witness_point_with(
        particular,
        kernel_basis,
        equations,
        invertibles,
        |v| !v.is_zero(),
        |c| Rat::from_int(BigInt::from(c)),
    )
}

/// Z アフィン解空間 `particular + span(kernel_basis)` 上で、`invertibles` がすべて
/// Z の単元（`|g(pt)| == 1`, すなわち `∃ u ∈ Z, u*g - 1 = 0`）となる具体的整数点を探索する（G-141 D5）。
pub fn find_witness_point_z(
    particular: &[BigInt],
    kernel_basis: &[Vec<BigInt>],
    equations: &[Poly<BigInt>],
    invertibles: &[Poly<BigInt>],
) -> Result<Option<Vec<BigInt>>, SilenceReason> {
    find_witness_point_with(
        particular,
        kernel_basis,
        equations,
        invertibles,
        |v| v.abs().is_one(),
        BigInt::from,
    )
}

fn find_witness_point_with<C: RingCoeff>(
    particular: &[C],
    kernel_basis: &[Vec<C>],
    equations: &[Poly<C>],
    invertibles: &[Poly<C>],
    is_inv_unit: impl Fn(&C) -> bool,
    from_i64: impl Fn(i64) -> C,
) -> Result<Option<Vec<C>>, SilenceReason> {
    let check_point = |pt: &[C]| -> Result<bool, SilenceReason> {
        for eq in equations {
            if !eq.eval_at(pt).map_err(map_algebra_silence)?.coeff_is_zero() {
                return Ok(false);
            }
        }
        for inv in invertibles {
            let val = inv.eval_at(pt).map_err(map_algebra_silence)?;
            if !is_inv_unit(&val) {
                return Ok(false);
            }
        }
        Ok(true)
    };

    if kernel_basis.is_empty() {
        return Ok(check_point(particular)?.then(|| particular.to_vec()));
    }

    for coeffs in witness_sample_vectors(kernel_basis.len()) {
        let pt = combine_affine_with(particular, kernel_basis, &coeffs, &from_i64);
        if check_point(&pt)? {
            return Ok(Some(pt));
        }
    }

    Ok(None)
}

fn build_param_subst_polys_q(
    param_vars: &VarOrder,
    param_subst: &BTreeMap<String, PolyExpr>,
    free_order: &VarOrder,
    free_bind: &ExprBindings,
) -> Result<Vec<Poly<Rat>>, SilenceReason> {
    (0..param_vars.len())
        .map(|idx| {
            let name = &param_vars.vars()[idx];
            if let Some(expr) = param_subst.get(name) {
                Poly::from_expr_q(expr, free_bind).map_err(map_algebra_silence)
            } else {
                let fidx = free_order.index_of(name).ok_or_else(|| {
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "parameter_binding_consistent".to_owned(),
                        detail: format!("non-pivot parameter `{name}` missing from free order"),
                    }
                })?;
                Ok(Poly::var(free_order.len(), fidx, Rat::zero()))
            }
        })
        .collect()
}

/// Q（または代数閉包）上の抽出代入から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_q(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    extra_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    extracted: &ExtractedSubstitutionQ,
    require_strict_ideal: bool,
) -> Result<RestoredArtifact, SilenceReason> {
    let restored_pair = substitute_comparison_pair(pair, &extracted.param_subst);
    let free_order =
        VarOrder::new(extracted.unassigned_parameters.clone()).map_err(map_algebra_silence)?;
    let free_bind = ExprBindings::params_only(&free_order);

    let (operations, state_laws, state_comparisons, word_translation) =
        format_restored_pair_q(&restored_pair, &extracted.unassigned_parameters)?;

    // extra_invs を未代入変数空間へ縮約する（非閉な商環層の開条件を検算にも引き継ぐ）。
    let subst_polys =
        build_param_subst_polys_q(param_vars, &extracted.param_subst, &free_order, &free_bind)?;
    let mut reduced_extra_invs = Vec::with_capacity(extra_invs.len());
    for inv in extra_invs {
        reduced_extra_invs.push(eval_poly_with_polys_q(inv, &subst_polys, free_order.len())?);
    }

    // 独立再評価検算: 復元後の ComparisonPair から保存義務を再構成して成立を確認する。
    let reeval = reeval_restored_pair_q(
        &restored_pair,
        eval_cond,
        extracted,
        &reduced_extra_invs,
        &free_order,
        &free_bind,
        require_strict_ideal,
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

fn check_point_arity(param_vars: &VarOrder, got: usize) -> Result<(), SilenceReason> {
    if got != param_vars.len() {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "parameter_point_arity_match".to_owned(),
            detail: format!("expected {} parameter values, got {got}", param_vars.len()),
        });
    }
    Ok(())
}

type ConcretePointMaps = (BTreeMap<String, PolyExpr>, BTreeMap<String, String>);

fn build_concrete_point_assignments<T: std::fmt::Display>(
    param_vars: &VarOrder,
    point: &[T],
    mut to_lit: impl FnMut(&T) -> PolyExpr,
) -> Result<ConcretePointMaps, SilenceReason> {
    check_point_arity(param_vars, point.len())?;
    let mut param_subst = BTreeMap::new();
    let mut display_assignments = BTreeMap::new();
    for (name, val) in param_vars.vars().iter().zip(point) {
        param_subst.insert(name.clone(), to_lit(val));
        display_assignments.insert(name.clone(), val.to_string());
    }
    Ok((param_subst, display_assignments))
}

/// Q 上の具体的有理点から `RestoredArtifact` を復元し、暗黙の開条件なしで独立再評価検算を行う（F2 対策）。
pub fn restore_and_reeval_q_point(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    point: &[Rat],
) -> Result<RestoredArtifact, SilenceReason> {
    let (param_subst, display_assignments) =
        build_concrete_point_assignments(param_vars, point, |val| rat_to_expr(val, false))?;
    let extracted = ExtractedSubstitutionQ {
        param_subst,
        display_assignments,
        unassigned_parameters: vec![],
        free_parameters: vec![],
        remaining_nonlinear: vec![],
    };
    restore_and_reeval_q(pair, eval_cond, &[], param_vars, &extracted, false)
}

type PairFormatter<'a> =
    &'a dyn Fn(&ComparisonPair) -> Result<FormattedRestoredMaps, SilenceReason>;
type ResidualExtractor<'a, C> =
    &'a dyn Fn(&[PreservationObligation]) -> Result<Option<Vec<Poly<C>>>, SilenceReason>;
type ExprParser<'a, C> = &'a dyn Fn(&PolyExpr, &ExprBindings) -> Result<Poly<C>, AlgebraError>;

struct ConcreteRestoreOps<'a, C: RingCoeff> {
    format_pair: PairFormatter<'a>,
    extract_residuals: ResidualExtractor<'a, C>,
    parse_expr: ExprParser<'a, C>,
    is_inv_unit: fn(&Poly<C>) -> bool,
    nonzero_residual_msg: &'a str,
    quotient_out_of_scope_msg: &'a str,
    eval_eq_suffix: &'a str,
    eval_inv_suffix: &'a str,
    model_label: String,
}

fn restore_and_reeval_concrete_point<C: RingCoeff>(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    assignments: ConcretePointMaps,
    ops: &ConcreteRestoreOps<'_, C>,
) -> Result<RestoredArtifact, SilenceReason> {
    let (param_subst, display_assignments) = assignments;
    let restored_pair = substitute_comparison_pair(pair, &param_subst);
    let (operations, state_laws, state_comparisons, word_translation) =
        (ops.format_pair)(&restored_pair)?;

    // 独立再評価検算: 復元後の ComparisonPair から残差を再構成し全零・評価条件一致を検証。
    let obligations = build_preservation_obligations(&restored_pair)?;
    let empty_bind =
        ExprBindings::params_only(&VarOrder::new(vec![]).map_err(map_algebra_silence)?);
    let mut matched = true;
    let mut fail_detail = String::new();

    if let Some(residuals) = (ops.extract_residuals)(&obligations)? {
        if residuals.iter().any(|r| !r.is_zero()) {
            matched = false;
            fail_detail = ops.nonzero_residual_msg.to_owned();
        }
    } else {
        matched = false;
        fail_detail = ops.quotient_out_of_scope_msg.to_owned();
    }

    if matched && let Some(cond) = eval_cond {
        let empty = BTreeMap::new();
        for eq in &cond.equations {
            let sub = substitute_poly_expr(&eq.expr, &empty, &empty, &param_subst);
            let p = (ops.parse_expr)(&sub, &empty_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                matched = false;
                fail_detail = format!("eval equation `{}` {}", eq.name, ops.eval_eq_suffix);
                break;
            }
        }
        if matched {
            for inv in &cond.invertibles {
                let sub = substitute_poly_expr(&inv.expr, &empty, &empty, &param_subst);
                let p = (ops.parse_expr)(&sub, &empty_bind).map_err(map_algebra_silence)?;
                if !(ops.is_inv_unit)(&p) {
                    matched = false;
                    fail_detail = format!("eval invertible `{}` {}", inv.name, ops.eval_inv_suffix);
                    break;
                }
            }
        }
    }

    let detail = if matched {
        format!(
            "verified all {} preservation obligations and evaluation conditions on restored {} model",
            obligations.len(),
            ops.model_label
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

/// Z 上の具体的整数点から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_z(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    point: &[BigInt],
) -> Result<RestoredArtifact, SilenceReason> {
    let assignments = build_concrete_point_assignments(param_vars, point, |val| {
        PolyExpr::Const(ScalarLit::Z(val.clone()))
    })?;
    let ops = ConcreteRestoreOps {
        format_pair: &format_restored_pair_z,
        extract_residuals: &|obs| extract_closed_residuals_z(obs, &[]),
        parse_expr: &Poly::from_expr_z,
        is_inv_unit: |p| p.constant_value().abs().is_one(),
        nonzero_residual_msg: "restored Z presentation has nonzero preservation residual",
        quotient_out_of_scope_msg: "quotient state-law re-evaluation over Z is out of scope",
        eval_eq_suffix: "did not vanish after restoration",
        eval_inv_suffix: "is not a unit in Z (|g| != 1) after restoration",
        model_label: "Z".to_owned(),
    };
    restore_and_reeval_concrete_point(pair, eval_cond, assignments, &ops)
}

/// F_p 上の具体点から `RestoredArtifact` を復元し、独立再評価検算を行う。
pub fn restore_and_reeval_fp(
    pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    point: &[FpElem],
    modulus: &BigUint,
) -> Result<RestoredArtifact, SilenceReason> {
    let assignments = build_concrete_point_assignments(param_vars, point, |val| {
        PolyExpr::Const(ScalarLit::Fp {
            value: val.value().clone(),
            modulus: modulus.clone(),
        })
    })?;
    let format_fp = |rp: &ComparisonPair| format_restored_pair_fp(rp, modulus);
    let extract_fp =
        |obs: &[PreservationObligation]| extract_closed_residuals_fp(obs, &[], modulus);
    let parse_fp = |expr: &PolyExpr, bind: &ExprBindings| Poly::from_expr_fp(expr, bind, modulus);
    let ops = ConcreteRestoreOps {
        format_pair: &format_fp,
        extract_residuals: &extract_fp,
        parse_expr: &parse_fp,
        is_inv_unit: |p| !p.is_zero(),
        nonzero_residual_msg: "restored Fp presentation has nonzero preservation residual",
        quotient_out_of_scope_msg: "quotient state-law re-evaluation over Fp is out of scope",
        eval_eq_suffix: "did not vanish over Fp",
        eval_inv_suffix: "vanished over Fp",
        model_label: format!("Fp({modulus})"),
    };
    restore_and_reeval_concrete_point(pair, eval_cond, assignments, &ops)
}

fn reeval_restored_pair_q(
    restored_pair: &ComparisonPair,
    eval_cond: Option<&EvalCondition>,
    extracted: &ExtractedSubstitutionQ,
    extra_invs: &[Poly<Rat>],
    free_order: &VarOrder,
    free_bind: &ExprBindings,
    require_strict_ideal: bool,
) -> Result<ReevalCheck, SilenceReason> {
    let param_subst = &extracted.param_subst;
    let remaining_nonlinear = &extracted.remaining_nonlinear;
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

    if require_strict_ideal {
        if !locus.is_zariski_closed {
            return Ok(ReevalCheck {
                checked: true,
                matched: false,
                detail: "restored preservation locus is not Zariski-closed for UniversalRing"
                    .to_owned(),
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
    } else if !is_stratum_covered_by_union(
        &target_rab.parameter_equations,
        &eval_invs,
        &locus.strata,
        free_order,
    )? {
        return Ok(ReevalCheck {
            checked: true,
            matched: false,
            detail: "restored locus is not contained in preservation strata over algebraic closure"
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

type AffineSystemQ = (Vec<Vec<Rat>>, Vec<Rat>);
type AffineSystemZ = (Vec<Vec<BigInt>>, Vec<BigInt>);

fn polys_to_affine_system_with<C: RingCoeff>(
    polys: &[Poly<C>],
    num_vars: usize,
    zero: C,
) -> Result<(Vec<Vec<C>>, Vec<C>), SilenceReason> {
    let mut matrix = Vec::with_capacity(polys.len());
    let mut rhs = Vec::with_capacity(polys.len());
    for p in polys {
        if p.num_vars() != num_vars || !p.is_affine() {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "affine_system_expected".to_owned(),
                detail: "polynomial arity or degree exceeds affine system bounds".to_owned(),
            });
        }
        let mut row = vec![zero.clone(); num_vars];
        let mut c0 = zero.clone();
        for (mono, coeff) in p.terms() {
            if mono.is_one() {
                c0 = coeff.clone();
            } else if let Some(idx) = mono.exps().iter().position(|&e| e == 1) {
                row[idx] = coeff.clone();
            }
        }
        matrix.push(row);
        rhs.push(c0.neg_ref());
    }
    Ok((matrix, rhs))
}

pub fn polys_to_affine_system_q(
    polys: &[Poly<Rat>],
    num_vars: usize,
) -> Result<AffineSystemQ, SilenceReason> {
    polys_to_affine_system_with(polys, num_vars, Rat::zero())
}

pub fn polys_to_affine_system_z(
    polys: &[Poly<BigInt>],
    num_vars: usize,
) -> Result<AffineSystemZ, SilenceReason> {
    polys_to_affine_system_with(polys, num_vars, BigInt::zero())
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

fn combine_affine_with<C: RingCoeff>(
    particular: &[C],
    kernel: &[Vec<C>],
    coeffs: &[i64],
    from_i64: impl Fn(i64) -> C,
) -> Vec<C> {
    let mut pt = particular.to_vec();
    for (vec, &c) in kernel.iter().zip(coeffs) {
        if c == 0 {
            continue;
        }
        let sc = from_i64(c);
        for (dst, v) in pt.iter_mut().zip(vec) {
            *dst = dst.add_ref(&sc.mul_ref(v));
        }
    }
    pt
}

/// 単変数 1 次式 `a * x_idx + b` から `(idx, a, b)` を抽出する共通ヘルパ（F7）。
fn extract_univariate_linear<C: RingCoeff>(poly: &Poly<C>) -> Option<(usize, C, C)> {
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
    if var_coeff.coeff_is_zero() {
        return None;
    }
    Some((idx, var_coeff, const_coeff))
}

/// 座標固定方程式 `a * param + b = 0`（単変数 1 次、`a != 0`）を抽出し、
/// `(param_name, -b/a)` を返す。非座標固定の式なら `None`。
pub fn extract_coordinate_fix_q(poly: &Poly<Rat>, vars: &VarOrder) -> Option<(String, Rat)> {
    let (idx, a, b) = extract_univariate_linear(poly)?;
    let val = (&(-&b) / &a)?;
    Some((vars.vars()[idx].clone(), val))
}

/// F_p 上の座標固定方程式 `a * param + b = 0`（単変数 1 次、`a != 0`）を抽出する。
pub fn extract_coordinate_fix_fp(poly: &Poly<FpElem>, vars: &VarOrder) -> Option<(String, FpElem)> {
    let (idx, a, b) = extract_univariate_linear(poly)?;
    let inv = a.inv()?;
    let val = b.neg_elem().mul_checked(&inv)?;
    Some((vars.vars()[idx].clone(), val))
}

/// Z 上の座標固定方程式 `a * param + b = 0`（単変数 1 次、`a != 0`）を抽出する。
/// `UniversalRing`（全可換環 R）上で座標超平面 `param = -b/a` を定めるには係数が単元 `a ∈ Z^× = {±1}`
/// である必要があるため、非単元係数の場合は `Some((name, None))` として呼び出し側へ沈黙を伝える。
pub fn extract_coordinate_fix_z(
    poly: &Poly<BigInt>,
    vars: &VarOrder,
) -> Option<(String, Option<BigInt>)> {
    let (idx, a, b) = extract_univariate_linear(poly)?;
    let neg_b = -b;
    let exact = a.abs().is_one().then(|| neg_b / a);
    Some((vars.vars()[idx].clone(), exact))
}
