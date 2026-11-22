//! 射の合成列・状態比較・操作語翻訳の一致比較（図式補完・経路細分化で共有）。

use crate::algebra::{ExprBindings, VarOrder};
use crate::ir::morphism::{
    MorphismDirection, StateMorphism, TimeStepMorphism, compose_state_order, compose_time_order,
};
use crate::ir::presentation::Presentation;
use crate::ir::result::SilenceReason;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::common_format::{fmt_poly_expr, symbolic_and_observed};
use crate::solver::preservation::{
    PreservationObligation, map_algebra_silence, substitute_poly_expr,
};
use std::collections::BTreeMap;

/// 生成辺列 `(source, target, morphism)` を図式・経路の向きに従って合成し、
/// `(合成射, 合成射の始点 Presentation)` を返す。
pub(crate) fn compose_morphism_chain<'a>(
    edges: &[(&str, &str, &StateMorphism)],
    vertices: &BTreeMap<&str, &'a Presentation>,
    direction: MorphismDirection,
) -> Result<(StateMorphism, &'a Presentation), SilenceReason> {
    let first = edges
        .first()
        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
            condition: "non_empty_morphism_chain".to_owned(),
            detail: "cannot compose empty edge chain".to_owned(),
        })?;
    let mut node_pres = Vec::with_capacity(edges.len() + 1);
    let mut morphs = Vec::with_capacity(edges.len());
    let first_pres =
        *vertices
            .get(first.0)
            .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                condition: "chain_vertex_present".to_owned(),
                detail: format!("missing vertex `{}`", first.0),
            })?;
    node_pres.push(first_pres);
    for (_, tgt, m) in edges {
        let tgt_pres =
            *vertices
                .get(tgt)
                .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "chain_vertex_present".to_owned(),
                    detail: format!("missing vertex `{tgt}`"),
                })?;
        node_pres.push(tgt_pres);
        morphs.push(*m);
    }
    compose_morphism_step_chain(&morphs, &node_pres, direction)
}

/// 同じ頂点名を取りうる段階列 `node_presentations`（長さ `morphs.len() + 1`）に沿って
/// 射列 `morphs` を合成し、`(合成射, 合成射の始点 Presentation)` を返す。
pub(crate) fn compose_morphism_step_chain<'a>(
    morphs: &[&StateMorphism],
    node_presentations: &[&'a Presentation],
    direction: MorphismDirection,
) -> Result<(StateMorphism, &'a Presentation), SilenceReason> {
    if morphs.is_empty() || node_presentations.len() != morphs.len() + 1 {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "non_empty_morphism_chain".to_owned(),
            detail: "morphism chain length must match node presentations".to_owned(),
        });
    }
    let first_pres = node_presentations[0];
    let second_pres = node_presentations[1];
    match direction {
        MorphismDirection::StateMap => {
            let mut acc = morphs[0].clone();
            let mut mid = second_pres;
            for (idx, edge_m) in morphs.iter().enumerate().skip(1) {
                let tgt_pres = node_presentations[idx + 1];
                if acc.target != mid.name || mid.name != edge_m.source {
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "composable_state_order_chain".to_owned(),
                        detail: format!(
                            "edge `{} -> {}` does not compose with `{}`",
                            edge_m.source, edge_m.target, acc.target
                        ),
                    });
                }
                acc = compose_state_order(edge_m, &acc, first_pres, mid).map_err(|e| {
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "morphism_composition_valid".to_owned(),
                        detail: e.to_string(),
                    }
                })?;
                mid = tgt_pres;
            }
            Ok((acc, first_pres))
        }
        MorphismDirection::TimeOrder => {
            let mut acc =
                TimeStepMorphism::new(&first_pres.name, &second_pres.name, morphs[0].clone())
                    .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                        condition: "time_step_orientation".to_owned(),
                        detail: e.to_string(),
                    })?;
            let mut mid_pres = second_pres;
            for (idx, edge_m) in morphs.iter().enumerate().skip(1) {
                let tgt_pres = node_presentations[idx + 1];
                let next = TimeStepMorphism::new(&mid_pres.name, &tgt_pres.name, (*edge_m).clone())
                    .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                        condition: "time_step_orientation".to_owned(),
                        detail: e.to_string(),
                    })?;
                acc = compose_time_order(&acc, &next, mid_pres, tgt_pres).map_err(|e| {
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "morphism_composition_valid".to_owned(),
                        detail: e.to_string(),
                    }
                })?;
                mid_pres = tgt_pres;
            }
            Ok((acc.state_map().clone(), mid_pres))
        }
    }
}

/// 射比較の結果 `(保存義務列, 非零表示残差, 構造不一致理由)`。
pub(crate) type MorphismComparison = (Vec<PreservationObligation>, Vec<String>, Option<String>);

/// 同一端点の 2 つの `StateMorphism` について、状態比較射と操作語翻訳の両方の一致義務・
/// 表示残差・構造不一致理由を生成する。
pub(crate) fn compare_morphisms(
    lhs: &StateMorphism,
    rhs: &StateMorphism,
    domain_pres: &Presentation,
    param_vars: &VarOrder,
    coeff_domain: &CoeffDomain,
) -> Result<MorphismComparison, SilenceReason> {
    if lhs.source != rhs.source || lhs.target != rhs.target {
        return Ok((
            vec![],
            vec![],
            Some(format!(
                "endpoint mismatch: `{} -> {}` vs `{} -> {}`",
                lhs.source, lhs.target, rhs.source, rhs.target
            )),
        ));
    }

    let empty = BTreeMap::new();
    if lhs.state_comparisons.len() != rhs.state_comparisons.len() {
        return Ok((
            vec![],
            vec![],
            Some(format!(
                "state comparison phase count mismatch: {} vs {}",
                lhs.state_comparisons.len(),
                rhs.state_comparisons.len()
            )),
        ));
    }
    if lhs.word_translation.entries.len() != rhs.word_translation.entries.len() {
        return Ok((
            vec![],
            vec![],
            Some(format!(
                "word translation operation count mismatch: {} vs {}",
                lhs.word_translation.entries.len(),
                rhs.word_translation.entries.len()
            )),
        ));
    }
    let phases: BTreeMap<&str, _> = domain_pres
        .phases
        .iter()
        .map(|p| (p.name.as_str(), p))
        .collect();
    let ops: BTreeMap<&str, _> = domain_pres
        .operations
        .iter()
        .map(|o| (o.name.as_str(), o))
        .collect();
    let rhs_sc_by_after: BTreeMap<&str, _> = rhs
        .state_comparisons
        .iter()
        .map(|s| (s.after_phase.as_str(), s))
        .collect();

    let mut obs = Vec::new();
    let mut residuals = Vec::new();

    for l_sc in &lhs.state_comparisons {
        let Some(r_sc) = rhs_sc_by_after.get(l_sc.after_phase.as_str()) else {
            return Ok((
                vec![],
                vec![],
                Some(format!(
                    "missing state comparison for phase `{}` on rhs",
                    l_sc.after_phase
                )),
            ));
        };
        if l_sc.before_phase != r_sc.before_phase {
            return Ok((
                vec![],
                vec![],
                Some(format!(
                    "phase target mismatch at `{}`: `{}` vs `{}`",
                    l_sc.after_phase, l_sc.before_phase, r_sc.before_phase
                )),
            ));
        }
        let ph = phases.get(l_sc.after_phase.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "domain_phase_present".to_owned(),
                detail: format!(
                    "missing phase `{}` in `{}`",
                    l_sc.after_phase, domain_pres.name
                ),
            }
        })?;
        let (sv, obs_map) = symbolic_and_observed(ph);
        let laws: Vec<PolyExpr> = ph
            .state_laws
            .iter()
            .map(|l| substitute_poly_expr(&l.polynomial, &obs_map, &empty, &empty))
            .collect();
        let (order, bind) =
            ExprBindings::from_slices(&sv, &[], param_vars.vars()).map_err(map_algebra_silence)?;
        if l_sc.map.len() != r_sc.map.len() {
            return Ok((
                vec![],
                vec![],
                Some(format!(
                    "coord count mismatch in phase `{}`: {} vs {}",
                    l_sc.after_phase,
                    l_sc.map.len(),
                    r_sc.map.len()
                )),
            ));
        }
        for (coord, l_expr) in &l_sc.map {
            let Some(r_expr) = r_sc.map.get(coord) else {
                return Ok((
                    vec![],
                    vec![],
                    Some(format!(
                        "missing coord `{coord}` in rhs phase `{}`",
                        l_sc.after_phase
                    )),
                ));
            };
            let diff = PolyExpr::diff(
                substitute_poly_expr(l_expr, &obs_map, &empty, &empty),
                substitute_poly_expr(r_expr, &obs_map, &empty, &empty),
            );
            let disp = fmt_poly_expr(&diff, &bind, &order, coeff_domain)?;
            if disp != "0" {
                residuals.push(disp);
            }
            obs.push(PreservationObligation {
                state_vars: sv.clone(),
                arg_vars: vec![],
                source_laws: laws.clone(),
                target: diff,
            });
        }
    }

    for l_tw in &lhs.word_translation.entries {
        let Some(r_tw) = rhs.word_translation.for_operation(&l_tw.after_operation) else {
            return Ok((
                vec![],
                vec![],
                Some(format!(
                    "missing word translation for operation `{}` on rhs",
                    l_tw.after_operation
                )),
            ));
        };
        if l_tw.steps.len() != r_tw.steps.len() {
            return Ok((
                vec![],
                vec![],
                Some(format!(
                    "word translation step length mismatch at `{}`: {} vs {}",
                    l_tw.after_operation,
                    l_tw.steps.len(),
                    r_tw.steps.len()
                )),
            ));
        }
        let op = ops.get(l_tw.after_operation.as_str()).ok_or_else(|| {
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "domain_op_present".to_owned(),
                detail: format!(
                    "missing operation `{}` in `{}`",
                    l_tw.after_operation, domain_pres.name
                ),
            }
        })?;
        let ph = phases[op.source_phase.as_str()];
        let (sv, obs_map) = symbolic_and_observed(ph);
        let av: Vec<String> = op.args.iter().map(|(a, _)| a.clone()).collect();
        let mut laws: Vec<PolyExpr> = ph
            .state_laws
            .iter()
            .map(|l| substitute_poly_expr(&l.polynomial, &obs_map, &empty, &empty))
            .collect();
        for dl in &op.domain_laws {
            laws.push(substitute_poly_expr(
                &dl.polynomial,
                &obs_map,
                &empty,
                &empty,
            ));
        }
        let (order, bind) =
            ExprBindings::from_slices(&sv, &av, param_vars.vars()).map_err(map_algebra_silence)?;

        for (step_idx, (ls, rs)) in l_tw.steps.iter().zip(&r_tw.steps).enumerate() {
            if ls.before_operation != rs.before_operation {
                return Ok((
                    vec![],
                    vec![],
                    Some(format!(
                        "word translation op mismatch at `{}` step {step_idx}: `{}` vs `{}`",
                        l_tw.after_operation, ls.before_operation, rs.before_operation
                    )),
                ));
            }
            if ls.arg_exprs.len() != rs.arg_exprs.len() {
                return Ok((
                    vec![],
                    vec![],
                    Some(format!(
                        "word translation arity mismatch at `{}` step {step_idx}: {} vs {}",
                        l_tw.after_operation,
                        ls.arg_exprs.len(),
                        rs.arg_exprs.len()
                    )),
                ));
            }
            for (la, ra) in ls.arg_exprs.iter().zip(&rs.arg_exprs) {
                let diff = PolyExpr::diff(
                    substitute_poly_expr(la, &obs_map, &empty, &empty),
                    substitute_poly_expr(ra, &obs_map, &empty, &empty),
                );
                let disp = fmt_poly_expr(&diff, &bind, &order, coeff_domain)?;
                if disp != "0" {
                    residuals.push(disp);
                }
                obs.push(PreservationObligation {
                    state_vars: sv.clone(),
                    arg_vars: av.clone(),
                    source_laws: laws.clone(),
                    target: diff,
                });
            }
        }
    }

    Ok((obs, residuals, None))
}
