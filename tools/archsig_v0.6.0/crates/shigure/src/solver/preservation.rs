//! 一般原始表示からの意味保存方程式・商環状態 Law 閉性の導出（G-140 A2, P0.1, P1, P3–P5 / G-141 D5）。
//!
//! 特定の題材に依存せず、任意の検証済み `ComparisonPair` に対して次の 4 義務を生成する:
//! 1. 状態比較射 `h` の合法性（`h^*(before_law) in (after_laws)`）
//! 2. 観測写像の保存（`obs_after - obs_before(h) in (after_laws)`）
//! 3. 生成操作の状態 Law 閉性（`op_after^*(dst_law) in (src_laws)`）
//! 4. 生成操作と語翻訳 `tau` の可換性（`h_dst(op_after) - eval_before(tau(op_after), h_src) in (src_laws)`）

use crate::algebra::{
    AlgebraError, ExprBindings, FpElem, GroebnerBasis, Monomial, MonomialOrder, Poly,
    QuotientStratum, Rat, RingCoeff, VarOrder, quotient_membership_locus, rabinowitsch_solve,
};
use crate::ir::presentation::{ComparisonPair, CoordValue, OperationDecl, PhaseDecl, Presentation};
use crate::ir::result::{EmptyWitness, SilenceReason};
use crate::ir::term::PolyExpr;
use num_bigint::{BigInt, BigUint};
use std::collections::{BTreeMap, BTreeSet};

/// 複数義務の層別積・閉包検査で許容する最大層数（組合せ爆発時に fail-closed する）。
pub const MAX_COMBINED_STRATA: usize = 128;

/// 単一の保存義務 `target(state, arg, param) in (source_laws(state, param))`。
#[derive(Clone, Debug)]
pub struct PreservationObligation {
    pub state_vars: Vec<String>,
    pub arg_vars: Vec<String>,
    pub source_laws: Vec<PolyExpr>,
    pub target: PolyExpr,
}

/// Q（および代数閉包）上での意味保存ローカス `⋃_j (V(E_j) ∩ D(U_j))` とその Zariski 閉包。
#[derive(Clone, Debug)]
pub struct PreservationLocusQ {
    /// 非空な局所閉層の和集合。空のときは保存ローカス自体が空。
    pub strata: Vec<QuotientStratum>,
    /// 層の和集合の Zariski 閉包を定める簡約 Gröbner 基底（`V(closure_ideal)`）。
    pub closure_ideal: Vec<Poly<Rat>>,
    /// `⋃_j (V(E_j) ∩ D(U_j)) == V(closure_ideal)` が真に成り立つ（開条件の欠損がない）とき `true`。
    pub is_zariski_closed: bool,
    /// 実残差生成元からの空性証明 witness（`base_gb` で `1 in I` が直接示された場合のみ保持）。
    pub empty_witness: Option<EmptyWitness>,
}

/// `PolyExpr` の状態変数・引数変数・パラメータ変数を指定写像で同時置換する。
pub fn substitute_poly_expr(
    expr: &PolyExpr,
    state_map: &BTreeMap<String, PolyExpr>,
    arg_map: &BTreeMap<String, PolyExpr>,
    param_map: &BTreeMap<String, PolyExpr>,
) -> PolyExpr {
    crate::ir::morphism::substitute_poly_expr_iter(expr, state_map, arg_map, param_map)
}

/// phase の状態座標から、自由記号変数リストと `Observed` 座標の定数置換写像を抽出する。
fn phase_state_env(phase: &PhaseDecl) -> (Vec<String>, BTreeMap<String, PolyExpr>) {
    let mut symbolic = Vec::new();
    let mut observed_map = BTreeMap::new();
    for coord in &phase.coords {
        match &coord.value {
            CoordValue::Symbolic => symbolic.push(coord.name.clone()),
            CoordValue::Observed(lit) => {
                observed_map.insert(coord.name.clone(), PolyExpr::Const(lit.clone()));
            }
            CoordValue::Missing => {
                // 未観測は前段の適用条件検査で沈黙へ落とされるが、万一到達しても零化しない。
                observed_map.insert(
                    coord.name.clone(),
                    PolyExpr::Unobserved {
                        slot: format!("{}.{}", phase.name, coord.name),
                        origin: coord.provenance.clone(),
                    },
                );
            }
        }
    }
    (symbolic, observed_map)
}

/// `ComparisonPair` から 4 族すべての意味保存・状態 Law 閉性義務を一般構成する。
pub fn build_preservation_obligations(
    pair: &ComparisonPair,
) -> Result<Vec<PreservationObligation>, SilenceReason> {
    let empty = BTreeMap::new();
    let comp_by_after: BTreeMap<&str, _> = pair
        .state_comparisons
        .iter()
        .map(|sc| (sc.after_phase.as_str(), sc))
        .collect();
    let before_phases: BTreeMap<&str, &PhaseDecl> = pair
        .before
        .phases
        .iter()
        .map(|p| (p.name.as_str(), p))
        .collect();
    let after_phases: BTreeMap<&str, &PhaseDecl> = pair
        .after
        .phases
        .iter()
        .map(|p| (p.name.as_str(), p))
        .collect();
    let before_ops: BTreeMap<&str, &OperationDecl> = pair
        .before
        .operations
        .iter()
        .map(|op| (op.name.as_str(), op))
        .collect();

    let mut obligations = Vec::new();

    // 1 & 2. 各 after phase について、比較射 h の合法性と観測写像の保存を生成する。
    for after_phase in &pair.after.phases {
        let sc = comp_by_after
            .get(after_phase.name.as_str())
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "state_comparison_present".to_owned(),
                detail: format!("missing state comparison for phase `{}`", after_phase.name),
            })?;
        let before_phase = before_phases.get(sc.before_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "before_phase_present".to_owned(),
                detail: format!("missing before phase `{}`", sc.before_phase),
            }
        })?;

        let (state_vars, obs_coord_map) = phase_state_env(after_phase);
        let src_laws: Vec<PolyExpr> = after_phase
            .state_laws
            .iter()
            .map(|l| substitute_poly_expr(&l.polynomial, &obs_coord_map, &empty, &empty))
            .collect();
        let h_map: BTreeMap<String, PolyExpr> = sc
            .map
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    substitute_poly_expr(v, &obs_coord_map, &empty, &empty),
                )
            })
            .collect();

        // 1a. before 側に固定観測値を持つ座標があれば h の像も一致する義務。
        for b_coord in &before_phase.coords {
            if let CoordValue::Observed(lit) = &b_coord.value
                && let Some(h_expr) = h_map.get(&b_coord.name)
            {
                obligations.push(PreservationObligation {
                    state_vars: state_vars.clone(),
                    arg_vars: vec![],
                    source_laws: src_laws.clone(),
                    target: PolyExpr::diff(h_expr.clone(), PolyExpr::Const(lit.clone())),
                });
            }
        }

        // 1b. before 側の全状態 Law が h を通して after 側の状態 Law ideal に属する義務。
        for b_law in &before_phase.state_laws {
            let pulled = substitute_poly_expr(&b_law.polynomial, &h_map, &empty, &empty);
            obligations.push(PreservationObligation {
                state_vars: state_vars.clone(),
                arg_vars: vec![],
                source_laws: src_laws.clone(),
                target: pulled,
            });
        }

        // 2. 観測写像の保存: obs_after(s) - obs_before(h(s)) in (src_laws)。
        let after_obs_map: BTreeMap<&str, _> = pair
            .after
            .observations
            .iter()
            .filter(|o| o.phase == after_phase.name)
            .map(|o| (o.name.as_str(), o))
            .collect();
        for b_obs in pair
            .before
            .observations
            .iter()
            .filter(|o| o.phase == before_phase.name)
        {
            let a_obs = after_obs_map.get(b_obs.name.as_str()).ok_or_else(|| {
                SilenceReason::ApplicabilityConditionNotMet {
                    condition: "observation_correspondence".to_owned(),
                    detail: format!(
                        "missing after observation `{}` on phase `{}`",
                        b_obs.name, after_phase.name
                    ),
                }
            })?;
            for (a_comp, b_comp) in a_obs.components.iter().zip(&b_obs.components) {
                let a_eval = substitute_poly_expr(a_comp, &obs_coord_map, &empty, &empty);
                let b_eval = substitute_poly_expr(b_comp, &h_map, &empty, &empty);
                obligations.push(PreservationObligation {
                    state_vars: state_vars.clone(),
                    arg_vars: vec![],
                    source_laws: src_laws.clone(),
                    target: PolyExpr::diff(a_eval, b_eval),
                });
            }
        }
    }

    // 3 & 4. 各 after 操作について、遷移先状態 Law 閉性と語翻訳 τ に対する可換性を生成する。
    for after_op in &pair.after.operations {
        let src_phase = after_phases
            .get(after_op.source_phase.as_str())
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_source_phase_present".to_owned(),
                detail: format!("missing after phase `{}`", after_op.source_phase),
            })?;
        let dst_phase = after_phases
            .get(after_op.target_phase.as_str())
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "after_target_phase_present".to_owned(),
                detail: format!("missing after phase `{}`", after_op.target_phase),
            })?;
        let sc_src = comp_by_after.get(src_phase.name.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "state_comparison_present".to_owned(),
                detail: format!("missing state comparison for phase `{}`", src_phase.name),
            }
        })?;
        let sc_dst = comp_by_after.get(dst_phase.name.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "state_comparison_present".to_owned(),
                detail: format!("missing state comparison for phase `{}`", dst_phase.name),
            }
        })?;
        let tw = pair
            .word_translation
            .for_operation(&after_op.name)
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "word_translation_present".to_owned(),
                detail: format!("missing word translation for operation `{}`", after_op.name),
            })?;

        let (state_vars, src_obs_map) = phase_state_env(src_phase);
        let arg_vars: Vec<String> = after_op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut src_laws: Vec<PolyExpr> = src_phase
            .state_laws
            .iter()
            .map(|l| substitute_poly_expr(&l.polynomial, &src_obs_map, &empty, &empty))
            .collect();
        for dlaw in &after_op.domain_laws {
            src_laws.push(substitute_poly_expr(
                &dlaw.polynomial,
                &src_obs_map,
                &empty,
                &empty,
            ));
        }
        let after_updates: BTreeMap<String, PolyExpr> = after_op
            .updates
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    substitute_poly_expr(v, &src_obs_map, &empty, &empty),
                )
            })
            .collect();

        // 3a & 3b. dst_phase の固定観測値一致と状態 Law 閉性
        collect_op_closure_obligations(
            after_op,
            dst_phase,
            &state_vars,
            &arg_vars,
            &src_laws,
            &after_updates,
            &mut obligations,
        );

        // 4. 操作可換性および翻訳先操作の事前定義域（domain_laws）引き戻し義務:
        let mut before_state: BTreeMap<String, PolyExpr> = sc_src
            .map
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    substitute_poly_expr(v, &src_obs_map, &empty, &empty),
                )
            })
            .collect();
        for step in &tw.steps {
            let b_op = before_ops
                .get(step.before_operation.as_str())
                .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "before_operation_present".to_owned(),
                    detail: format!("missing before operation `{}`", step.before_operation),
                })?;
            let mut step_args = BTreeMap::new();
            for ((arg_name, _), expr) in b_op.args.iter().zip(&step.arg_exprs) {
                step_args.insert(
                    arg_name.clone(),
                    substitute_poly_expr(expr, &src_obs_map, &empty, &empty),
                );
            }
            for b_dlaw in &b_op.domain_laws {
                let pulled =
                    substitute_poly_expr(&b_dlaw.polynomial, &before_state, &step_args, &empty);
                obligations.push(PreservationObligation {
                    state_vars: state_vars.clone(),
                    arg_vars: arg_vars.clone(),
                    source_laws: src_laws.clone(),
                    target: pulled,
                });
            }
            let mut next_before = BTreeMap::new();
            for (coord, upd) in &b_op.updates {
                next_before.insert(
                    coord.clone(),
                    substitute_poly_expr(upd, &before_state, &step_args, &empty),
                );
            }
            before_state = next_before;
        }

        for (coord, h_dst_expr) in &sc_dst.map {
            let lhs = substitute_poly_expr(h_dst_expr, &after_updates, &empty, &empty);
            let rhs = before_state.get(coord).ok_or_else(|| {
                SilenceReason::ApplicabilityConditionNotMet {
                    condition: "before_state_coord_present".to_owned(),
                    detail: format!("missing before coord `{coord}` after word translation"),
                }
            })?;
            obligations.push(PreservationObligation {
                state_vars: state_vars.clone(),
                arg_vars: arg_vars.clone(),
                source_laws: src_laws.clone(),
                target: PolyExpr::diff(lhs, rhs.clone()),
            });
        }
    }

    Ok(obligations)
}

fn collect_op_closure_obligations(
    op: &OperationDecl,
    dst_phase: &PhaseDecl,
    state_vars: &[String],
    arg_vars: &[String],
    src_laws: &[PolyExpr],
    op_updates: &BTreeMap<String, PolyExpr>,
    obligations: &mut Vec<PreservationObligation>,
) {
    let empty = BTreeMap::new();
    let _ = op;
    for d_coord in &dst_phase.coords {
        if let CoordValue::Observed(lit) = &d_coord.value
            && let Some(upd) = op_updates.get(&d_coord.name)
        {
            obligations.push(PreservationObligation {
                state_vars: state_vars.to_vec(),
                arg_vars: arg_vars.to_vec(),
                source_laws: src_laws.to_vec(),
                target: PolyExpr::diff(upd.clone(), PolyExpr::Const(lit.clone())),
            });
        }
    }
    for dst_law in &dst_phase.state_laws {
        let pulled = substitute_poly_expr(&dst_law.polynomial, op_updates, &empty, &empty);
        obligations.push(PreservationObligation {
            state_vars: state_vars.to_vec(),
            arg_vars: arg_vars.to_vec(),
            source_laws: src_laws.to_vec(),
            target: pulled,
        });
    }
}

/// 単一 `Presentation` 上の全操作について遷移先状態 Law 閉性・観測座標一致義務を生成する。
pub(crate) fn build_presentation_closure_obligations(
    pres: &Presentation,
) -> Result<Vec<PreservationObligation>, SilenceReason> {
    let empty = BTreeMap::new();
    let phases: BTreeMap<&str, &PhaseDecl> =
        pres.phases.iter().map(|p| (p.name.as_str(), p)).collect();
    let mut obligations = Vec::new();
    for op in &pres.operations {
        let src_phase = phases.get(op.source_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "presentation_source_phase_present".to_owned(),
                detail: format!("missing phase `{}` in `{}`", op.source_phase, pres.name),
            }
        })?;
        let dst_phase = phases.get(op.target_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "presentation_target_phase_present".to_owned(),
                detail: format!("missing phase `{}` in `{}`", op.target_phase, pres.name),
            }
        })?;
        let (state_vars, src_obs_map) = phase_state_env(src_phase);
        let arg_vars: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut src_laws: Vec<PolyExpr> = src_phase
            .state_laws
            .iter()
            .map(|l| substitute_poly_expr(&l.polynomial, &src_obs_map, &empty, &empty))
            .collect();
        for dlaw in &op.domain_laws {
            src_laws.push(substitute_poly_expr(
                &dlaw.polynomial,
                &src_obs_map,
                &empty,
                &empty,
            ));
        }
        let op_updates: BTreeMap<String, PolyExpr> = op
            .updates
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    substitute_poly_expr(v, &src_obs_map, &empty, &empty),
                )
            })
            .collect();
        collect_op_closure_obligations(
            op,
            dst_phase,
            &state_vars,
            &arg_vars,
            &src_laws,
            &op_updates,
            &mut obligations,
        );
    }
    Ok(obligations)
}

/// 状態 Law が空の義務に対し、`k[param][state, arg]` の全 `(state, arg)` 単項式係数を
/// パラメータ多項式として厳密抽出する（Z / Q / F_p 共通）。
pub fn extract_ambient_param_coeffs<C: RingCoeff>(
    poly: &Poly<C>,
    state_arg_count: usize,
    param_count: usize,
) -> Vec<Poly<C>> {
    let mut by_state_mono: BTreeMap<Monomial, Poly<C>> = BTreeMap::new();
    for (mono, coeff) in poly.terms() {
        let y_mono = Monomial::from_exps(mono.exps()[..state_arg_count].to_vec());
        let c_mono = Monomial::from_exps(mono.exps()[state_arg_count..].to_vec());
        let entry = by_state_mono
            .entry(y_mono)
            .or_insert_with(|| Poly::zero(param_count, poly.zero_coeff().clone()));
        entry.add_term(c_mono, coeff.clone());
    }
    by_state_mono
        .into_values()
        .filter(|p| !p.is_zero())
        .collect()
}

/// 状態 Law が空のときに、任意の係数環（Z または F_p）上で直接パラメータ残差多項式列を抽出する。
pub fn extract_closed_residuals_z(
    obligations: &[PreservationObligation],
    param_names: &[String],
) -> Result<Option<Vec<Poly<BigInt>>>, SilenceReason> {
    if obligations.iter().any(|o| !o.source_laws.is_empty()) {
        return Ok(None);
    }
    let mut out = Vec::new();
    for ob in obligations {
        let (_, bindings) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, param_names)
            .map_err(map_algebra_silence)?;
        let poly = Poly::from_expr_z(&ob.target, &bindings).map_err(map_algebra_silence)?;
        let sa = ob.state_vars.len() + ob.arg_vars.len();
        out.extend(extract_ambient_param_coeffs(&poly, sa, param_names.len()));
    }
    Ok(Some(out))
}

/// 状態 Law が空のときに、`Fp(modulus)` 上で直接パラメータ残差多項式列を抽出する。
pub fn extract_closed_residuals_fp(
    obligations: &[PreservationObligation],
    param_names: &[String],
    modulus: &BigUint,
) -> Result<Option<Vec<Poly<FpElem>>>, SilenceReason> {
    if obligations.iter().any(|o| !o.source_laws.is_empty()) {
        return Ok(None);
    }
    let mut out = Vec::new();
    for ob in obligations {
        let (_, bindings) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, param_names)
            .map_err(map_algebra_silence)?;
        let poly =
            Poly::from_expr_fp(&ob.target, &bindings, modulus).map_err(map_algebra_silence)?;
        let sa = ob.state_vars.len() + ob.arg_vars.len();
        out.extend(extract_ambient_param_coeffs(&poly, sa, param_names.len()));
    }
    Ok(Some(out))
}

/// Q 上で全意味保存義務を解き、局所閉層の和集合・Zariski 閉包 ideal・閉性判定を計算する。
pub fn compute_preservation_locus_q(
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
) -> Result<PreservationLocusQ, SilenceReason> {
    let param_names = param_vars.vars();
    let mut ambient_eqs: Vec<Poly<Rat>> = Vec::new();
    let mut quotient_groups: Vec<Vec<QuotientStratum>> = Vec::new();

    for ob in obligations {
        let (_, bindings) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, param_names)
            .map_err(map_algebra_silence)?;
        let target_poly = Poly::from_expr_q(&ob.target, &bindings).map_err(map_algebra_silence)?;
        let state_arg_count = ob.state_vars.len() + ob.arg_vars.len();

        let mut source_polys = Vec::new();
        for law in &ob.source_laws {
            let p = Poly::from_expr_q(law, &bindings).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                source_polys.push(p);
            }
        }

        if target_poly.is_zero() {
            continue;
        }
        if source_polys.is_empty() {
            ambient_eqs.extend(extract_ambient_param_coeffs(
                &target_poly,
                state_arg_count,
                param_vars.len(),
            ));
        } else {
            let strata = quotient_membership_locus(
                &target_poly,
                &source_polys,
                state_arg_count,
                param_vars,
            )?;
            quotient_groups.push(strata);
        }
    }

    // 初期層: ambient 等式のみ。
    let base_gb = GroebnerBasis::compute(&ambient_eqs, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    if base_gb.contains_one() {
        let empty_witness = base_gb.empty_witness().ok().flatten();
        return Ok(PreservationLocusQ {
            strata: vec![],
            closure_ideal: vec![Poly::one(param_vars.len(), Rat::zero())],
            is_zariski_closed: true,
            empty_witness,
        });
    }
    let clean_ambient: Vec<Poly<Rat>> = base_gb.basis_polys().into_iter().cloned().collect();
    let mut combined = vec![QuotientStratum {
        equations: clean_ambient,
        invertibles: vec![],
    }];

    for group in quotient_groups {
        combined = intersect_strata_lists(&combined, &group, param_vars)?;
        if combined.is_empty() {
            return Ok(PreservationLocusQ {
                strata: vec![],
                closure_ideal: vec![Poly::one(param_vars.len(), Rat::zero())],
                is_zariski_closed: true,
                empty_witness: None,
            });
        }
    }

    let closure_ideal = compute_strata_closure_ideal(&combined, param_vars)?;
    let is_zariski_closed = is_union_equal_to_closure(&closure_ideal, &combined, param_vars)?;

    Ok(PreservationLocusQ {
        strata: combined,
        closure_ideal,
        is_zariski_closed,
        empty_witness: None,
    })
}

/// 全保存義務がスキーム論的（冪零元を含む全可換 Q-代数上）に
/// `ob.target ∈ (ob.source_laws) + (closure_ideal)` を満たすことを `Q[y, u, c]` 上の
/// Gröbner 基底所属判定で直接検算する（G-141 F11 健全性、F1 対策）。
pub(crate) fn verify_scheme_membership_q(
    obligations: &[PreservationObligation],
    closure_ideal: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Result<bool, SilenceReason> {
    let param_names = param_vars.vars();
    for ob in obligations {
        if ob.source_laws.is_empty() {
            continue;
        }
        let (order, bindings) =
            ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, param_names)
                .map_err(map_algebra_silence)?;
        let target_poly = Poly::from_expr_q(&ob.target, &bindings).map_err(map_algebra_silence)?;
        if target_poly.is_zero() {
            continue;
        }
        let state_arg_count = ob.state_vars.len() + ob.arg_vars.len();
        let mut gens: Vec<Poly<Rat>> =
            Vec::with_capacity(ob.source_laws.len() + closure_ideal.len());
        for law in &ob.source_laws {
            let p = Poly::from_expr_q(law, &bindings).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                gens.push(p);
            }
        }
        for c_poly in closure_ideal {
            if !c_poly.is_zero() {
                gens.push(c_poly.lift_vars(state_arg_count));
            }
        }
        let gb = GroebnerBasis::compute(&gens, order, MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        let mem = gb.membership(&target_poly).map_err(map_algebra_silence)?;
        if !mem.is_member || !mem.verified {
            return Ok(false);
        }
    }
    Ok(true)
}

/// 2 つの層族の直積交わりを計算し、空な層を Rabinowitsch で即時剪定する。
pub fn intersect_strata_lists(
    lhs: &[QuotientStratum],
    rhs: &[QuotientStratum],
    param_vars: &VarOrder,
) -> Result<Vec<QuotientStratum>, SilenceReason> {
    let mut next = Vec::new();
    for a in lhs {
        for b in rhs {
            let mut eqs = a.equations.clone();
            eqs.extend(b.equations.iter().cloned());
            let mut invs = a.invertibles.clone();
            for inv in &b.invertibles {
                if !invs.contains(inv) {
                    invs.push(inv.clone());
                }
            }
            let rab = rabinowitsch_solve(&eqs, &invs, param_vars).map_err(map_algebra_silence)?;
            if !rab.is_empty_over_closure {
                let candidate = QuotientStratum {
                    equations: rab.parameter_equations,
                    invertibles: invs,
                };
                if !next.contains(&candidate) {
                    next.push(candidate);
                    if next.len() > MAX_COMBINED_STRATA {
                        return Err(SilenceReason::QuotientIdealOutOfScope {
                            detail: format!(
                                "combined quotient strata exceeded limit ({MAX_COMBINED_STRATA})"
                            ),
                        });
                    }
                }
            }
        }
    }
    Ok(next)
}

/// 局所閉層の和集合 `⋃_j (V(E_j) ∩ D(U_j))` の Zariski 閉包 ideal `⋂_j sat(E_j, U_j)` を計算する。
pub(crate) fn compute_strata_closure_ideal(
    strata: &[QuotientStratum],
    param_vars: &VarOrder,
) -> Result<Vec<Poly<Rat>>, SilenceReason> {
    if strata.is_empty() {
        return Ok(vec![Poly::one(param_vars.len(), Rat::zero())]);
    }
    let saturate_stratum = |s: &QuotientStratum| -> Result<Vec<Poly<Rat>>, SilenceReason> {
        if s.invertibles.is_empty() {
            Ok(s.equations.clone())
        } else {
            let rab = rabinowitsch_solve(&s.equations, &s.invertibles, param_vars)
                .map_err(map_algebra_silence)?;
            Ok(rab.parameter_equations)
        }
    };
    let mut iter = strata.iter();
    let first = iter.next().expect("non-empty strata");
    let mut acc = saturate_stratum(first)?;
    for s in iter {
        let sat = saturate_stratum(s)?;
        acc = intersect_ideals_q(&acc, &sat, param_vars)?;
    }
    let gb = GroebnerBasis::compute(&acc, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    Ok(gb.basis_polys().into_iter().cloned().collect())
}

/// 2 つの ideal `I_1, I_2 ⊆ Q[params]` の交わり `I_1 ∩ I_2 = (t * I_1 + (1 - t) * I_2) ∩ Q[params]`。
pub fn intersect_ideals_q(
    i1: &[Poly<Rat>],
    i2: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Result<Vec<Poly<Rat>>, SilenceReason> {
    if i1.is_empty() || i1.iter().all(Poly::is_zero) {
        return Ok(vec![]);
    }
    if i2.is_empty() || i2.iter().all(Poly::is_zero) {
        return Ok(vec![]);
    }
    let gb1 = GroebnerBasis::compute(i1, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    if gb1.contains_one() {
        let gb2 = GroebnerBasis::compute(i2, param_vars.clone(), MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        return Ok(gb2.basis_polys().into_iter().cloned().collect());
    }
    let gb2 = GroebnerBasis::compute(i2, param_vars.clone(), MonomialOrder::Grevlex)
        .map_err(map_algebra_silence)?;
    if gb2.contains_one() {
        return Ok(gb1.basis_polys().into_iter().cloned().collect());
    }

    let mut t_name = "__t_cap".to_owned();
    while param_vars.index_of(&t_name).is_some() {
        t_name.push('_');
    }
    let ext_vars = param_vars
        .prepend_vars(vec![t_name])
        .map_err(map_algebra_silence)?;
    let ext_n = ext_vars.len();
    let t_poly = Poly::var(ext_n, 0, Rat::zero());
    let one_minus_t = Poly::one(ext_n, Rat::zero()).sub(&t_poly);

    let mut gens = Vec::new();
    for f in gb1.basis_polys() {
        gens.push(
            t_poly
                .checked_mul(&f.lift_vars(1))
                .map_err(map_algebra_silence)?,
        );
    }
    for g in gb2.basis_polys() {
        gens.push(
            one_minus_t
                .checked_mul(&g.lift_vars(1))
                .map_err(map_algebra_silence)?,
        );
    }
    let elim =
        GroebnerBasis::compute(&gens, ext_vars, MonomialOrder::Lex).map_err(map_algebra_silence)?;
    let mut inter = Vec::new();
    for p in elim.basis_polys() {
        if let Some(proj) = p.drop_prefix_vars(1)
            && !proj.is_zero()
        {
            inter.push(proj);
        }
    }
    Ok(inter)
}

/// 局所閉集合 `V(target_eqs) ∩ D(target_invs)` が層族 `⋃_j (V(E_j) ∩ D(U_j))` に
/// 代数閉包上の点として完全に含まれるか（差集合が空か）を Nullstellensatz で厳密判定する。
pub fn is_stratum_covered_by_union(
    target_eqs: &[Poly<Rat>],
    target_invs: &[Poly<Rat>],
    strata: &[QuotientStratum],
    param_vars: &VarOrder,
) -> Result<bool, SilenceReason> {
    let init_rab =
        rabinowitsch_solve(target_eqs, target_invs, param_vars).map_err(map_algebra_silence)?;
    if init_rab.is_empty_over_closure {
        return Ok(true);
    }
    let mut remaining = vec![QuotientStratum {
        equations: init_rab.parameter_equations,
        invertibles: target_invs.to_vec(),
    }];

    for stratum in strata {
        let mut next_rem = Vec::new();
        for piece in &remaining {
            // piece \ (V(E) ∩ D(U)) = (⋃_{e in E} piece ∩ D(e)) ∪ (⋃_{u in U} piece ∩ V(u))
            for e in &stratum.equations {
                let mut invs = piece.invertibles.clone();
                if !invs.contains(e) {
                    invs.push(e.clone());
                }
                let rab = rabinowitsch_solve(&piece.equations, &invs, param_vars)
                    .map_err(map_algebra_silence)?;
                if !rab.is_empty_over_closure {
                    next_rem.push(QuotientStratum {
                        equations: rab.parameter_equations,
                        invertibles: invs,
                    });
                }
            }
            for u in &stratum.invertibles {
                let mut eqs = piece.equations.clone();
                eqs.push(u.clone());
                let rab = rabinowitsch_solve(&eqs, &piece.invertibles, param_vars)
                    .map_err(map_algebra_silence)?;
                if !rab.is_empty_over_closure {
                    next_rem.push(QuotientStratum {
                        equations: rab.parameter_equations,
                        invertibles: piece.invertibles.clone(),
                    });
                }
            }
            if next_rem.len() > MAX_COMBINED_STRATA {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail: format!(
                        "Zariski containment verification exceeded piece limit ({MAX_COMBINED_STRATA})"
                    ),
                });
            }
        }
        remaining = next_rem;
        if remaining.is_empty() {
            return Ok(true);
        }
    }
    Ok(remaining.is_empty())
}

/// 閉包 `V(closure_ideal)` から各層 `V(E_j) ∩ D(U_j)` を順に差し引き、
/// 残差が空（真の Zariski 閉集合）かどうかを Nullstellensatz で厳密判定する。
fn is_union_equal_to_closure(
    closure_ideal: &[Poly<Rat>],
    strata: &[QuotientStratum],
    param_vars: &VarOrder,
) -> Result<bool, SilenceReason> {
    is_stratum_covered_by_union(closure_ideal, &[], strata, param_vars)
}

/// `AlgebraError` を対応する `SilenceReason` へ fail-closed 変換する。
pub fn map_algebra_silence(err: AlgebraError) -> SilenceReason {
    match err {
        AlgebraError::UnobservedDependency { slots } => {
            SilenceReason::UnobservedDependency { slots }
        }
        AlgebraError::InvalidPrimeModulus { modulus } => SilenceReason::UnsupportedCoeffRing {
            domain: crate::ir::term::CoeffDomain::Fp(modulus),
            detail: "modulus is not prime".to_owned(),
        },
        other => SilenceReason::ApplicabilityConditionNotMet {
            condition: "algebraic_computation_in_scope".to_owned(),
            detail: other.to_string(),
        },
    }
}

/// `ComparisonPair` の全観測・操作・比較射・語翻訳に含まれる非自明な `SourceRef` 群を収集する（重複除去・決定順）。
pub fn collect_all_provenance_origins(
    pair: &ComparisonPair,
    change_origins: &[crate::ir::provenance::SourceRef],
    eval_origins: &[crate::ir::provenance::SourceRef],
) -> Vec<crate::ir::provenance::SourceRef> {
    let mut set = BTreeSet::new();
    for pres in [&pair.before, &pair.after] {
        for o in &pres.provenance.origins {
            set.insert(o.clone());
        }
        for s in &pres.sorts {
            if let Some(o) = &s.provenance {
                set.insert(o.clone());
            }
        }
        for p in &pres.phases {
            if let Some(o) = &p.provenance {
                set.insert(o.clone());
            }
            for c in &p.coords {
                if let Some(o) = &c.provenance {
                    set.insert(o.clone());
                }
            }
            for l in &p.state_laws {
                if let Some(o) = &l.provenance {
                    set.insert(o.clone());
                }
            }
        }
        for op in &pres.operations {
            if let Some(o) = &op.provenance {
                set.insert(o.clone());
            }
        }
        for obs in &pres.observations {
            if let Some(o) = &obs.provenance {
                set.insert(o.clone());
            }
        }
    }
    for sc in &pair.state_comparisons {
        if let Some(o) = &sc.provenance {
            set.insert(o.clone());
        }
    }
    for tw in &pair.word_translation.entries {
        if let Some(o) = &tw.provenance {
            set.insert(o.clone());
        }
    }
    for o in change_origins.iter().chain(eval_origins) {
        set.insert(o.clone());
    }
    set.into_iter().collect()
}
