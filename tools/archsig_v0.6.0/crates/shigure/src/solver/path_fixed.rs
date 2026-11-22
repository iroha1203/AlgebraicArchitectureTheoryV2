//! 一段変更経路探索・連結・細分化の固定図式変更経路計算（G-140 F2–F3・F3.1・P5.1）。

use crate::algebra::{ExprBindings, Poly, VarOrder, rabinowitsch_solve};
use crate::ir::change::{EvalCondition, NamedPoly, PointDomain};
use crate::ir::morphism::{MorphismDirection, StateMorphism, identity_state_morphism};
use crate::ir::path::{CheckedPathTask, OneStepRule, PathQueryMode};
use crate::ir::presentation::Presentation;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_ext::{PathOutcomeKind, RejectedPathCandidate, RestoredPath};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::common_format::{
    fmt_poly_expr, format_state_morphism, reeval_obligations_and_constraints,
    substitute_eval_condition, substitute_presentation, substitute_state_morphism,
};
use crate::solver::common_morph::{compare_morphisms, compose_morphism_step_chain};
use crate::solver::common_solve::{
    ParamWitness, SystemSolveOutcome, collect_eval_and_extra, solve_obligations_and_evals,
};
use crate::solver::path::{
    MAX_PATH_CANDIDATES, established_path, path_query_mode_wire, refuted_path, undetermined_path,
};
use crate::solver::preservation::{
    PreservationObligation, build_presentation_closure_obligations, build_preservation_obligations,
    map_algebra_silence, substitute_poly_expr,
};
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

pub(crate) fn solve_fixed_change_path(
    task: &CheckedPathTask,
    point_domain: &crate::ir::change::PointDomain,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let mode_wire = path_query_mode_wire(&spec.query_mode).to_owned();
    let start = spec.start.as_ref().expect("checked start endpoint");
    let end = spec.end.as_ref().expect("checked end endpoint");

    let mut init_state: BTreeMap<String, PolyExpr> = BTreeMap::new();
    let mut free_init_names = Vec::new();
    for p in &spec.change_spec.parameters {
        if let Some(lit) = start.param_values.get(&p.name) {
            init_state.insert(p.name.clone(), PolyExpr::Const(lit.clone()));
        } else {
            init_state.insert(p.name.clone(), PolyExpr::ParamVar(p.name.clone()));
            free_init_names.push(p.name.clone());
        }
    }
    let free_init_vars = match VarOrder::new(free_init_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                vec![],
                PathOutcomeKind::FixedProtocolChangePath,
                spec.direction,
                mode_wire,
                spec.length,
                None,
                vec![],
                vec![],
                map_algebra_silence(e),
            );
        }
    };

    let candidates: Vec<Vec<&OneStepRule>> = match &spec.query_mode {
        PathQueryMode::Find | PathQueryMode::Subdivide { .. } => {
            let n = spec.length.expect("checked length");
            match enumerate_rule_paths(&spec.rules, &start.vertex, &end.vertex, n) {
                Ok(c) => c,
                Err(reason) => {
                    return undetermined_path(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        vec![],
                        PathOutcomeKind::FixedProtocolChangePath,
                        spec.direction,
                        mode_wire,
                        spec.length,
                        None,
                        vec![],
                        vec![],
                        reason,
                    );
                }
            }
        }
        PathQueryMode::Concatenate { first, second } => {
            let rules_by_name: BTreeMap<&str, &OneStepRule> =
                spec.rules.iter().map(|r| (r.name.as_str(), r)).collect();
            let seq: Vec<&OneStepRule> = first
                .iter()
                .chain(second.iter())
                .map(|n| rules_by_name[n.as_str()])
                .collect();
            vec![seq]
        }
    };

    let mut valid_paths = Vec::new();
    let mut rejected_candidates = Vec::new();
    let mut last_residuals = Vec::new();

    for seq in &candidates {
        match evaluate_fixed_candidate(task, seq, &init_state, &free_init_vars, point_domain) {
            Ok(CandidateEval::Valid { path, residuals }) => {
                valid_paths.push(path);
                if last_residuals.is_empty() {
                    last_residuals = residuals;
                }
            }
            Ok(CandidateEval::Rejected(rej)) => {
                if !rej.residuals.is_empty() {
                    last_residuals = rej.residuals.clone();
                }
                rejected_candidates.push(rej);
            }
            Err(reason) => {
                return undetermined_path(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    vec![],
                    PathOutcomeKind::FixedProtocolChangePath,
                    spec.direction,
                    mode_wire,
                    spec.length,
                    None,
                    valid_paths,
                    rejected_candidates,
                    reason,
                );
            }
        }
    }

    if valid_paths.is_empty() {
        checks.push(ApplicabilityCheck::passed(
            "finite_path_space_refuted",
            MathClause::G140F2,
        ));
        return refuted_path(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            last_residuals,
            None,
            PathOutcomeKind::FixedProtocolChangePath,
            spec.direction,
            mode_wire,
            spec.length,
            None,
            rejected_candidates,
        );
    }

    checks.push(ApplicabilityCheck::passed(
        "finite_path_solutions_verified",
        MathClause::G140F2,
    ));
    established_path(
        coeff_domain,
        point_domain,
        checks,
        provenance,
        last_residuals,
        PathOutcomeKind::FixedProtocolChangePath,
        spec.direction,
        mode_wire,
        spec.length,
        None,
        valid_paths,
        rejected_candidates,
    )
}

enum CandidateEval {
    Valid {
        path: RestoredPath,
        residuals: Vec<String>,
    },
    Rejected(RejectedPathCandidate),
}

fn format_param_state(
    state: &BTreeMap<String, PolyExpr>,
    free_vars: &VarOrder,
    domain: &CoeffDomain,
) -> Result<BTreeMap<String, String>, SilenceReason> {
    let bind = ExprBindings::params_only(free_vars);
    let mut out = BTreeMap::new();
    for (k, expr) in state {
        out.insert(k.clone(), fmt_poly_expr(expr, &bind, free_vars, domain)?);
    }
    Ok(out)
}

fn evaluate_fixed_candidate(
    task: &CheckedPathTask,
    seq: &[&OneStepRule],
    init_state: &BTreeMap<String, PolyExpr>,
    free_init_vars: &VarOrder,
    point_domain: &crate::ir::change::PointDomain,
) -> Result<CandidateEval, SilenceReason> {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let start = spec.start.as_ref().expect("checked start");
    let end = spec.end.as_ref().expect("checked end");
    let empty = BTreeMap::new();
    let seq_names: Vec<String> = seq.iter().map(|r| r.name.clone()).collect();

    let mut state_history = vec![init_state.clone()];
    let start_pres = substitute_presentation(&spec.vertices[&start.vertex], init_state);
    let mut node_pres = vec![start_pres];
    let mut node_vertices = vec![start.vertex.clone()];
    let mut step_morphs: Vec<StateMorphism> = Vec::with_capacity(seq.len());
    let mut obligations = build_presentation_closure_obligations(&node_pres[0])?;
    let mut extra_eqs = Vec::new();
    let mut eval_conds_owned: Vec<EvalCondition> = Vec::new();
    if let Some(ec) = task.eval_condition() {
        eval_conds_owned.push(substitute_eval_condition(ec, init_state));
    }

    if seq.is_empty() {
        for (p, lit) in &end.param_values {
            let cur_expr = init_state
                .get(p)
                .cloned()
                .unwrap_or_else(|| PolyExpr::ParamVar(p.clone()));
            extra_eqs.push(PolyExpr::diff(cur_expr, PolyExpr::Const(lit.clone())));
        }
        let sub_mm = if let PathQueryMode::Subdivide { target_edge } = &spec.query_mode {
            let id_m = identity_state_morphism(&node_pres[0]);
            let tgt_sub = substitute_state_morphism(target_edge, init_state);
            let (obs, _, mm) =
                compare_morphisms(&id_m, &tgt_sub, &node_pres[0], free_init_vars, coeff_domain)?;
            obligations.extend(obs);
            mm
        } else {
            None
        };
        if let Some(mm) = sub_mm {
            return Ok(CandidateEval::Rejected(RejectedPathCandidate {
                steps: seq_names,
                failed_step: 0,
                intermediate_state: format_param_state(init_state, free_init_vars, coeff_domain)?,
                residuals: vec![mm.clone()],
                reason: format!("zero-step subdivision mismatch: {mm}"),
            }));
        }
        let eval_refs: Vec<&EvalCondition> = eval_conds_owned.iter().collect();
        let res = solve_obligations_and_evals(
            &obligations,
            &extra_eqs,
            &eval_refs,
            coeff_domain,
            point_domain,
            free_init_vars,
        );
        return finalize_fixed_path_solve(
            task,
            seq,
            &seq_names,
            &node_vertices,
            &node_pres,
            &step_morphs,
            &state_history,
            &extra_eqs,
            &eval_conds_owned,
            free_init_vars,
            point_domain,
            res,
        );
    }

    let mut last_res = None;
    for (k, rule) in seq.iter().enumerate() {
        let cur_state = state_history.last().expect("cur_state").clone();
        for g in &rule.param_guards {
            extra_eqs.push(substitute_poly_expr(&g.expr, &empty, &empty, &cur_state));
        }
        let mut next_state = cur_state.clone();
        for (p, upd) in &rule.param_updates {
            next_state.insert(
                p.clone(),
                substitute_poly_expr(upd, &empty, &empty, &cur_state),
            );
        }
        let next_pres = substitute_presentation(&spec.vertices[&rule.to_vertex], &next_state);
        let morph_subst = match spec.direction {
            MorphismDirection::StateMap => &cur_state,
            MorphismDirection::TimeOrder => &next_state,
        };
        let morph_k = substitute_state_morphism(&rule.morphism, morph_subst);
        let prev_pres = node_pres.last().expect("prev_pres");
        let pair_k = match spec.direction {
            MorphismDirection::StateMap => morph_k.to_comparison_pair(prev_pres, &next_pres),
            MorphismDirection::TimeOrder => morph_k.to_comparison_pair(&next_pres, prev_pres),
        };
        obligations.extend(build_preservation_obligations(&pair_k)?);
        obligations.extend(build_presentation_closure_obligations(&next_pres)?);
        if let Some(ec) = task.eval_condition() {
            eval_conds_owned.push(substitute_eval_condition(ec, &next_state));
        }
        if let Some(rec) = &rule.eval_condition {
            eval_conds_owned.push(substitute_eval_condition(rec, &next_state));
        }

        state_history.push(next_state.clone());
        node_pres.push(next_pres);
        node_vertices.push(rule.to_vertex.clone());
        step_morphs.push(morph_k);

        let is_last = k + 1 == seq.len();
        if is_last {
            for (p, lit) in &end.param_values {
                let end_expr = next_state
                    .get(p)
                    .cloned()
                    .unwrap_or_else(|| PolyExpr::ParamVar(p.clone()));
                extra_eqs.push(PolyExpr::diff(end_expr, PolyExpr::Const(lit.clone())));
            }
            if let PathQueryMode::Subdivide { target_edge } = &spec.query_mode {
                let morph_refs: Vec<&StateMorphism> = step_morphs.iter().collect();
                let pres_refs: Vec<&Presentation> = node_pres.iter().collect();
                let (composed_m, dom_pres) =
                    compose_morphism_step_chain(&morph_refs, &pres_refs, spec.direction)?;
                let tgt_subst = match spec.direction {
                    MorphismDirection::StateMap => &state_history[0],
                    MorphismDirection::TimeOrder => &next_state,
                };
                let tgt_sub = substitute_state_morphism(target_edge, tgt_subst);
                let (obs, _, mm) = compare_morphisms(
                    &composed_m,
                    &tgt_sub,
                    dom_pres,
                    free_init_vars,
                    coeff_domain,
                )?;
                if let Some(mm) = mm {
                    return Ok(CandidateEval::Rejected(RejectedPathCandidate {
                        steps: seq_names,
                        failed_step: k + 1,
                        intermediate_state: format_param_state(
                            &next_state,
                            free_init_vars,
                            coeff_domain,
                        )?,
                        residuals: vec![mm.clone()],
                        reason: format!("subdivision mismatch at step {}: {mm}", k + 1),
                    }));
                }
                obligations.extend(obs);
            }
        }

        let eval_refs: Vec<&EvalCondition> = eval_conds_owned.iter().collect();
        let res = solve_obligations_and_evals(
            &obligations,
            &extra_eqs,
            &eval_refs,
            coeff_domain,
            point_domain,
            free_init_vars,
        );
        match res.verdict {
            Verdict::Undetermined(reason) => return Err(reason),
            Verdict::Refuted => {
                return Ok(CandidateEval::Rejected(RejectedPathCandidate {
                    steps: seq_names,
                    failed_step: k + 1,
                    intermediate_state: format_param_state(
                        &next_state,
                        free_init_vars,
                        coeff_domain,
                    )?,
                    residuals: res.residual_display,
                    reason: format!(
                        "path candidate failed preservation/admissibility at step {}",
                        k + 1
                    ),
                }));
            }
            Verdict::Established => {
                if is_last {
                    last_res = Some(res);
                }
            }
        }
    }

    finalize_fixed_path_solve(
        task,
        seq,
        &seq_names,
        &node_vertices,
        &node_pres,
        &step_morphs,
        &state_history,
        &extra_eqs,
        &eval_conds_owned,
        free_init_vars,
        point_domain,
        last_res.expect("non-empty path solved"),
    )
}

#[allow(clippy::too_many_arguments)]
fn finalize_fixed_path_solve(
    task: &CheckedPathTask,
    seq: &[&OneStepRule],
    seq_names: &[String],
    node_vertices: &[String],
    node_pres: &[Presentation],
    step_morphs: &[StateMorphism],
    state_history: &[BTreeMap<String, PolyExpr>],
    extra_eqs: &[PolyExpr],
    eval_conds_owned: &[EvalCondition],
    free_init_vars: &VarOrder,
    point_domain: &crate::ir::change::PointDomain,
    solve_res: SystemSolveOutcome,
) -> Result<CandidateEval, SilenceReason> {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let empty = BTreeMap::new();
    match solve_res.verdict {
        Verdict::Undetermined(r) => return Err(r),
        Verdict::Refuted => {
            return Ok(CandidateEval::Rejected(RejectedPathCandidate {
                steps: seq_names.to_vec(),
                failed_step: seq.len(),
                intermediate_state: format_param_state(
                    state_history.last().expect("last state"),
                    free_init_vars,
                    coeff_domain,
                )?,
                residuals: solve_res.residual_display,
                reason: "endpoint constraint refuted".to_owned(),
            }));
        }
        Verdict::Established => {}
    }

    let witness = solve_res
        .witness
        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
            condition: "witness_present".to_owned(),
            detail: "missing witness on established path".to_owned(),
        })?;
    let param_subst = witness.to_param_subst(free_init_vars);
    let rem_free = witness.unassigned_parameters();
    let rem_vars = VarOrder::new(rem_free.clone()).map_err(map_algebra_silence)?;

    let restored_pres: Vec<Presentation> = node_pres
        .iter()
        .map(|p| substitute_presentation(p, &param_subst))
        .collect();
    let restored_morphs: Vec<StateMorphism> = step_morphs
        .iter()
        .map(|m| substitute_state_morphism(m, &param_subst))
        .collect();
    let restored_states: Vec<BTreeMap<String, PolyExpr>> = state_history
        .iter()
        .map(|st| {
            st.iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        substitute_poly_expr(v, &empty, &empty, &param_subst),
                    )
                })
                .collect()
        })
        .collect();

    let mut re_obs = build_presentation_closure_obligations(&restored_pres[0])?;
    for (k, rm) in restored_morphs.iter().enumerate() {
        let pair_k = match spec.direction {
            MorphismDirection::StateMap => {
                rm.to_comparison_pair(&restored_pres[k], &restored_pres[k + 1])
            }
            MorphismDirection::TimeOrder => {
                rm.to_comparison_pair(&restored_pres[k + 1], &restored_pres[k])
            }
        };
        re_obs.extend(build_preservation_obligations(&pair_k)?);
        re_obs.extend(build_presentation_closure_obligations(
            &restored_pres[k + 1],
        )?);
    }

    let (composed_m, dom_idx) = if restored_morphs.is_empty() {
        (identity_state_morphism(&restored_pres[0]), 0)
    } else {
        let m_refs: Vec<&StateMorphism> = restored_morphs.iter().collect();
        let p_refs: Vec<&Presentation> = restored_pres.iter().collect();
        let (cm, _) = compose_morphism_step_chain(&m_refs, &p_refs, spec.direction)?;
        let didx = match spec.direction {
            MorphismDirection::StateMap => 0,
            MorphismDirection::TimeOrder => restored_pres.len() - 1,
        };
        (cm, didx)
    };

    if let PathQueryMode::Concatenate { first, second } = &spec.query_mode
        && !first.is_empty()
        && !second.is_empty()
    {
        let split = first.len();
        let p1: Vec<&Presentation> = restored_pres[..=split].iter().collect();
        let m1: Vec<&StateMorphism> = restored_morphs[..split].iter().collect();
        let p2: Vec<&Presentation> = restored_pres[split..].iter().collect();
        let m2: Vec<&StateMorphism> = restored_morphs[split..].iter().collect();
        let (c1, _) = compose_morphism_step_chain(&m1, &p1, spec.direction)?;
        let (c2, _) = compose_morphism_step_chain(&m2, &p2, spec.direction)?;
        let p_ends = [
            &restored_pres[0],
            &restored_pres[split],
            restored_pres.last().expect("end"),
        ];
        let (assoc_m, _) = compose_morphism_step_chain(&[&c1, &c2], &p_ends, spec.direction)?;
        let (a_obs, _, a_mm) = compare_morphisms(
            &composed_m,
            &assoc_m,
            &restored_pres[dom_idx],
            &rem_vars,
            coeff_domain,
        )?;
        if a_mm.is_some() {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "concatenation_associativity".to_owned(),
                detail: "associative re-grouping of path composition differed structurally"
                    .to_owned(),
            });
        }
        re_obs.extend(a_obs);
    }

    if let PathQueryMode::Subdivide { target_edge } = &spec.query_mode {
        let tgt_subst = match spec.direction {
            MorphismDirection::StateMap => &restored_states[0],
            MorphismDirection::TimeOrder => restored_states.last().expect("end"),
        };
        let tgt_sub = substitute_state_morphism(target_edge, tgt_subst);
        let (s_obs, _, s_mm) = compare_morphisms(
            &composed_m,
            &tgt_sub,
            &restored_pres[dom_idx],
            &rem_vars,
            coeff_domain,
        )?;
        if s_mm.is_some() {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "subdivision_structure_matched".to_owned(),
                detail: "restored subdivision morphism mismatched target edge".to_owned(),
            });
        }
        re_obs.extend(s_obs);
    }

    let re_extra: Vec<PolyExpr> = extra_eqs
        .iter()
        .map(|e| substitute_poly_expr(e, &empty, &empty, &param_subst))
        .collect();
    let re_eval_owned: Vec<EvalCondition> = eval_conds_owned
        .iter()
        .map(|ec| substitute_eval_condition(ec, &param_subst))
        .collect();
    let re_eval_refs: Vec<&EvalCondition> = re_eval_owned.iter().collect();
    let reeval = reeval_obligations_and_constraints(
        &re_obs,
        &re_extra,
        &re_eval_refs,
        &witness,
        coeff_domain,
        point_domain,
        "path",
    )?;
    if !reeval.matched {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "restored_model_reevaluation_matched".to_owned(),
            detail: reeval.detail,
        });
    }

    let composite_is_one_step = if matches!(spec.query_mode, PathQueryMode::Concatenate { .. }) {
        Some(is_reproducible_in_one_step(
            spec,
            &restored_states[0],
            restored_states.last().expect("end"),
            &restored_pres[0],
            restored_pres.last().expect("end"),
            &composed_m,
            &witness,
            point_domain,
            &re_extra,
            &re_eval_refs,
        )?)
    } else {
        None
    };

    let mut formatted_states = Vec::with_capacity(restored_states.len());
    for st in &restored_states {
        formatted_states.push(format_param_state(st, &rem_vars, coeff_domain)?);
    }
    let (comp_sc, comp_wt) =
        format_state_morphism(&composed_m, &restored_pres[dom_idx], &rem_free)?;

    Ok(CandidateEval::Valid {
        path: RestoredPath {
            steps: seq_names.to_vec(),
            intermediate_vertices: node_vertices.to_vec(),
            parameter_assignments: witness.display_assignments(),
            free_parameters: witness.free_parameters(),
            step_states: formatted_states,
            composite_state_comparisons: comp_sc,
            composite_word_translation: comp_wt,
            composite_is_one_step,
            reeval,
        },
        residuals: solve_res.residual_display,
    })
}

#[allow(clippy::too_many_arguments)]
fn is_reproducible_in_one_step(
    spec: &crate::ir::path::PathSpec,
    state_0: &BTreeMap<String, PolyExpr>,
    state_end: &BTreeMap<String, PolyExpr>,
    pres_0: &Presentation,
    pres_end: &Presentation,
    composed_m: &StateMorphism,
    witness: &ParamWitness,
    point_domain: &crate::ir::change::PointDomain,
    path_extra_eqs: &[PolyExpr],
    path_eval_refs: &[&EvalCondition],
) -> Result<bool, SilenceReason> {
    let start = spec.start.as_ref().expect("start");
    let end = spec.end.as_ref().expect("end");
    let empty = BTreeMap::new();
    let free_names = witness.unassigned_parameters();
    let free_vars = VarOrder::new(free_names).map_err(map_algebra_silence)?;
    let dom_pres = match spec.direction {
        MorphismDirection::StateMap => pres_0,
        MorphismDirection::TimeOrder => pres_end,
    };

    for rule in &spec.rules {
        if rule.from_vertex != start.vertex || rule.to_vertex != end.vertex {
            continue;
        }
        let morph_subst = match spec.direction {
            MorphismDirection::StateMap => state_0,
            MorphismDirection::TimeOrder => state_end,
        };
        let rule_m = substitute_state_morphism(&rule.morphism, morph_subst);
        let (mut cmp_obs, _, mm) = compare_morphisms(
            &rule_m,
            composed_m,
            dom_pres,
            &free_vars,
            &spec.change_spec.coeff_domain,
        )?;
        if mm.is_some() {
            continue;
        }
        for g in &rule.param_guards {
            cmp_obs.push(PreservationObligation {
                state_vars: vec![],
                arg_vars: vec![],
                source_laws: vec![],
                target: substitute_poly_expr(&g.expr, &empty, &empty, state_0),
            });
        }
        for (p, end_expr) in state_end {
            let updated = rule
                .param_updates
                .get(p)
                .map(|u| substitute_poly_expr(u, &empty, &empty, state_0))
                .unwrap_or_else(|| {
                    state_0
                        .get(p)
                        .cloned()
                        .unwrap_or_else(|| PolyExpr::ParamVar(p.clone()))
                });
            cmp_obs.push(PreservationObligation {
                state_vars: vec![],
                arg_vars: vec![],
                source_laws: vec![],
                target: PolyExpr::diff(updated, end_expr.clone()),
            });
        }
        let rec_sub = rule
            .eval_condition
            .as_ref()
            .map(|rec| substitute_eval_condition(rec, state_end));
        if let Some(rc) = &rec_sub {
            for eq in &rc.equations {
                cmp_obs.push(PreservationObligation {
                    state_vars: vec![],
                    arg_vars: vec![],
                    source_laws: vec![],
                    target: eq.expr.clone(),
                });
            }
        }
        let check = reeval_obligations_and_constraints(
            &cmp_obs,
            path_extra_eqs,
            path_eval_refs,
            witness,
            &spec.change_spec.coeff_domain,
            point_domain,
            "one_step_closure",
        )?;
        if !check.matched {
            continue;
        }
        if let Some(rc) = &rec_sub
            && !rc.invertibles.is_empty()
            && !invertibles_hold_on_locus(
                &rc.invertibles,
                &free_vars,
                path_extra_eqs,
                path_eval_refs,
                witness,
                point_domain,
            )?
        {
            continue;
        }
        return Ok(true);
    }
    Ok(false)
}

fn invertibles_hold_on_locus(
    invs: &[NamedPoly],
    free_vars: &VarOrder,
    path_extra_eqs: &[PolyExpr],
    path_eval_refs: &[&EvalCondition],
    witness: &ParamWitness,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    let free_bind = ExprBindings::params_only(free_vars);
    match witness {
        ParamWitness::QPoint { .. } => {
            let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
            let empty_bind = ExprBindings::params_only(&empty_order);
            for iv in invs {
                let p = Poly::from_expr_q(&iv.expr, &empty_bind).map_err(map_algebra_silence)?;
                if p.is_zero() {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ParamWitness::ZPoint { .. } => {
            let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
            let empty_bind = ExprBindings::params_only(&empty_order);
            for iv in invs {
                let p = Poly::from_expr_z(&iv.expr, &empty_bind).map_err(map_algebra_silence)?;
                let val = p.constant_value();
                if val.is_zero() || !val.abs().is_one() {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ParamWitness::FpPoint { modulus, .. } => {
            let empty_order = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
            let empty_bind = ExprBindings::params_only(&empty_order);
            for iv in invs {
                let p = Poly::from_expr_fp(&iv.expr, &empty_bind, modulus)
                    .map_err(map_algebra_silence)?;
                if p.is_zero() {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ParamWitness::QSubst { subst } => {
            let (mut ante_eqs, ante_invs) = collect_eval_and_extra(
                path_extra_eqs,
                path_eval_refs,
                &free_bind,
                Poly::from_expr_q,
            )?;
            ante_eqs.extend(subst.remaining_nonlinear.iter().cloned());
            for iv in invs {
                let ip = Poly::from_expr_q(&iv.expr, &free_bind).map_err(map_algebra_silence)?;
                if *point_domain == PointDomain::UniversalRing {
                    if !ip.is_constant() || ip.is_zero() {
                        return Ok(false);
                    }
                } else {
                    let mut eqs_with_inv = ante_eqs.clone();
                    eqs_with_inv.push(ip);
                    let rab = rabinowitsch_solve(&eqs_with_inv, &ante_invs, free_vars)
                        .map_err(map_algebra_silence)?;
                    if !rab.is_empty_over_closure {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
    }
}

fn enumerate_rule_paths<'a>(
    rules: &'a [OneStepRule],
    start: &str,
    end: &str,
    target_len: usize,
) -> Result<Vec<Vec<&'a OneStepRule>>, SilenceReason> {
    if target_len == 0 {
        return Ok(if start == end { vec![vec![]] } else { vec![] });
    }
    let mut results = Vec::new();
    let mut stack: Vec<(String, Vec<&'a OneStepRule>)> = vec![(start.to_owned(), Vec::new())];
    while let Some((cur, seq)) = stack.pop() {
        if seq.len() == target_len {
            if cur == end {
                results.push(seq);
                if results.len() > MAX_PATH_CANDIDATES {
                    return Err(SilenceReason::UnboundedSearchOutOfScope {
                        detail: format!(
                            "fixed path enumeration exceeded finite budget of {MAX_PATH_CANDIDATES} candidates"
                        ),
                    });
                }
            }
            continue;
        }
        for r in rules.iter().rev() {
            if r.from_vertex == cur {
                let mut next = seq.clone();
                next.push(r);
                stack.push((r.to_vertex.clone(), next));
                if stack.len() + results.len() > MAX_PATH_CANDIDATES * 4 {
                    return Err(SilenceReason::UnboundedSearchOutOfScope {
                        detail: format!(
                            "fixed path search frontier exceeded finite budget ({MAX_PATH_CANDIDATES})"
                        ),
                    });
                }
            }
        }
    }
    results.sort_by(|a, b| a.iter().map(|r| &r.name).cmp(b.iter().map(|r| &r.name)));
    Ok(results)
}
