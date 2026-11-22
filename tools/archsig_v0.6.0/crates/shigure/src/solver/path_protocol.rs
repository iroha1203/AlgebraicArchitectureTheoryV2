//! 拡大 protocol 内の合法実行経路ソルバ（G-140 P5.2、`EnlargedProtocolExecutionPath`）。

use crate::algebra::{ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::morphism::StateMorphism;
use crate::ir::path::{CheckedPathTask, ProtocolExecutionSpec};
use crate::ir::presentation::{ComparisonPair, CoordValue, OperationDecl, Presentation};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_ext::{PathOutcomeKind, RejectedPathCandidate, RestoredPath};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::common_format::{
    fmt_poly_expr, format_state_morphism, poly_q_to_expr, reeval_obligations_and_constraints,
    substitute_eval_condition, substitute_presentation, substitute_state_morphism,
    symbolic_and_observed,
};
use crate::solver::common_solve::solve_obligations_and_evals;
use crate::solver::path::{
    MAX_PATH_CANDIDATES, established_path, path_query_mode_wire, refuted_path, undetermined_path,
};
use crate::solver::preservation::{
    PreservationObligation, build_preservation_obligations, map_algebra_silence,
    substitute_poly_expr,
};
use crate::solver::transfer_words::is_ideal_nonempty;
use std::collections::BTreeMap;

/// 拡大 protocol の全許可語保存と `allowed_ops` からの長さ `n` 実行経路を検証する。
pub(crate) fn solve_enlarged_protocol_path(
    task: &CheckedPathTask,
    point_domain: &PointDomain,
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let mode_wire = path_query_mode_wire(&spec.query_mode).to_owned();
    let proto = spec.protocol.as_ref().expect("checked protocol spec");
    let length = spec.length.expect("checked length");

    let param_names: Vec<String> = spec
        .change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let param_vars = match VarOrder::new(param_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                vec![],
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
                vec![],
                map_algebra_silence(e),
            );
        }
    };

    let cmp_obs = match build_preservation_obligations(&proto.comparison) {
        Ok(o) => o,
        Err(reason) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                vec![],
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
                vec![],
                reason,
            );
        }
    };

    let eval_refs: Vec<&EvalCondition> = task.eval_condition().into_iter().collect();
    let proto_solve = solve_obligations_and_evals(
        &cmp_obs,
        &[],
        &eval_refs,
        coeff_domain,
        point_domain,
        &param_vars,
    );
    checks.extend(proto_solve.checks);
    let witness = match proto_solve.verdict {
        Verdict::Undetermined(reason) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
                vec![],
                reason,
            );
        }
        Verdict::Refuted => {
            return refuted_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                proto_solve.empty_witness,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
            );
        }
        Verdict::Established => proto_solve.witness.expect("witness present"),
    };

    let param_subst = witness.to_param_subst(&param_vars);
    let restored_morph = substitute_state_morphism(
        &StateMorphism::from_comparison_pair(&proto.comparison),
        &param_subst,
    );
    let restored_after = substitute_presentation(&proto.comparison.after, &param_subst);
    let restored_cmp = ComparisonPair {
        before: proto.comparison.before.clone(),
        after: restored_after.clone(),
        state_comparisons: restored_morph.state_comparisons.clone(),
        word_translation: restored_morph.word_translation.clone(),
    };
    let re_proto_obs = match build_preservation_obligations(&restored_cmp) {
        Ok(o) => o,
        Err(reason) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
                vec![],
                reason,
            );
        }
    };
    let re_eval_owned = task
        .eval_condition()
        .map(|ec| substitute_eval_condition(ec, &param_subst));
    let re_eval_refs: Vec<&EvalCondition> = re_eval_owned.iter().collect();
    let proto_reeval = match reeval_obligations_and_constraints(
        &re_proto_obs,
        &[],
        &re_eval_refs,
        &witness,
        coeff_domain,
        point_domain,
        "enlarged_protocol",
    ) {
        Ok(r) => r,
        Err(reason) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(false),
                vec![],
                vec![],
                reason,
            );
        }
    };
    if !proto_reeval.matched {
        return undetermined_path(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            proto_solve.residual_display,
            PathOutcomeKind::EnlargedProtocolExecutionPath,
            spec.direction,
            mode_wire,
            Some(length),
            Some(false),
            vec![],
            vec![],
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "protocol_reevaluation_matched".to_owned(),
                detail: proto_reeval.detail,
            },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "enlarged_protocol_all_finite_words_preserved",
        MathClause::G140P5Dot2,
    ));

    let sequences = match enumerate_op_sequences(&restored_after, proto, length) {
        Ok(s) => s,
        Err(reason) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(true),
                vec![],
                vec![],
                reason,
            );
        }
    };

    let free_names = witness.unassigned_parameters();
    let free_vars = match VarOrder::new(free_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_path(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                proto_solve.residual_display,
                PathOutcomeKind::EnlargedProtocolExecutionPath,
                spec.direction,
                mode_wire,
                Some(length),
                Some(true),
                vec![],
                vec![],
                map_algebra_silence(e),
            );
        }
    };

    let mut valid_paths = Vec::new();
    let mut rejected = Vec::new();
    for seq in &sequences {
        match evaluate_execution_sequence(
            &restored_after,
            &restored_morph,
            proto,
            seq,
            &param_subst,
            &witness,
            &free_vars,
            re_eval_owned.as_ref(),
            point_domain,
        ) {
            Ok(Ok(rp)) => valid_paths.push(rp),
            Ok(Err(rej)) => rejected.push(rej),
            Err(reason) => {
                return undetermined_path(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    proto_solve.residual_display,
                    PathOutcomeKind::EnlargedProtocolExecutionPath,
                    spec.direction,
                    mode_wire,
                    Some(length),
                    Some(true),
                    valid_paths,
                    rejected,
                    reason,
                );
            }
        }
    }

    if valid_paths.is_empty() {
        checks.push(ApplicabilityCheck::passed(
            "enlarged_protocol_execution_paths_refuted",
            MathClause::G140P5Dot2,
        ));
        return refuted_path(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            proto_solve.residual_display,
            None,
            PathOutcomeKind::EnlargedProtocolExecutionPath,
            spec.direction,
            mode_wire,
            Some(length),
            Some(true),
            rejected,
        );
    }

    checks.push(ApplicabilityCheck::passed(
        "enlarged_protocol_execution_paths_verified",
        MathClause::G140P5Dot2,
    ));
    established_path(
        coeff_domain,
        point_domain,
        checks,
        provenance,
        proto_solve.residual_display,
        PathOutcomeKind::EnlargedProtocolExecutionPath,
        spec.direction,
        mode_wire,
        Some(length),
        Some(true),
        valid_paths,
        rejected,
    )
}

fn enumerate_op_sequences<'a>(
    after: &'a Presentation,
    proto: &ProtocolExecutionSpec,
    length: usize,
) -> Result<Vec<Vec<&'a OperationDecl>>, SilenceReason> {
    if length == 0 {
        return Ok(if proto.start_phase == proto.end_phase {
            vec![vec![]]
        } else {
            vec![]
        });
    }
    let allowed: Vec<&'a OperationDecl> = proto
        .allowed_ops
        .iter()
        .map(|name| after.operation(name).expect("checked allowed op"))
        .collect();
    let mut results = Vec::new();
    let mut stack: Vec<(&str, Vec<&'a OperationDecl>)> =
        vec![(proto.start_phase.as_str(), Vec::new())];
    while let Some((cur_ph, seq)) = stack.pop() {
        if seq.len() == length {
            if cur_ph == proto.end_phase {
                results.push(seq);
                if results.len() > MAX_PATH_CANDIDATES {
                    return Err(SilenceReason::UnboundedSearchOutOfScope {
                        detail: format!(
                            "protocol execution path enumeration exceeded {MAX_PATH_CANDIDATES} candidates"
                        ),
                    });
                }
            }
            continue;
        }
        for op in allowed.iter().rev() {
            if op.source_phase == cur_ph {
                let mut next = seq.clone();
                next.push(*op);
                stack.push((op.target_phase.as_str(), next));
                if stack.len() + results.len() > MAX_PATH_CANDIDATES * 4 {
                    return Err(SilenceReason::UnboundedSearchOutOfScope {
                        detail: format!(
                            "protocol path search frontier exceeded {MAX_PATH_CANDIDATES}"
                        ),
                    });
                }
            }
        }
    }
    results.sort_by(|a, b| a.iter().map(|o| &o.name).cmp(b.iter().map(|o| &o.name)));
    Ok(results)
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn evaluate_execution_sequence(
    after_pres: &Presentation,
    restored_morph: &StateMorphism,
    proto: &ProtocolExecutionSpec,
    seq: &[&OperationDecl],
    param_subst: &BTreeMap<String, PolyExpr>,
    witness: &crate::solver::common_solve::ParamWitness,
    free_vars: &VarOrder,
    eval_cond: Option<&EvalCondition>,
    point_domain: &PointDomain,
) -> Result<Result<RestoredPath, RejectedPathCandidate>, SilenceReason> {
    let domain = &after_pres.coeff_domain;
    let empty = BTreeMap::new();
    let seq_names: Vec<String> = seq.iter().map(|o| o.name.clone()).collect();
    let start_ph = after_pres.phase(&proto.start_phase).expect("start_phase");
    let (start_sv, start_obs) = symbolic_and_observed(start_ph);

    let mut init_laws: Vec<PolyExpr> = start_ph
        .state_laws
        .iter()
        .map(|l| substitute_poly_expr(&l.polynomial, &start_obs, &empty, &empty))
        .collect();
    for l in &proto.start_laws {
        let s1 = substitute_poly_expr(&l.polynomial, &start_obs, &empty, param_subst);
        init_laws.push(s1);
    }
    let end_laws_sub: Vec<PolyExpr> = proto
        .end_laws
        .iter()
        .map(|l| substitute_poly_expr(&l.polynomial, &empty, &empty, param_subst))
        .collect();

    let mut cur_state: BTreeMap<String, PolyExpr> = start_ph
        .coords
        .iter()
        .map(|c| match &c.value {
            CoordValue::Observed(lit) => (c.name.clone(), PolyExpr::Const(lit.clone())),
            CoordValue::Symbolic | CoordValue::Missing => {
                (c.name.clone(), PolyExpr::StateVar(c.name.clone()))
            }
        })
        .collect();
    if !is_ideal_nonempty(
        &init_laws,
        &start_sv,
        &[],
        free_vars,
        witness,
        domain,
        point_domain,
    )? {
        let disp =
            format_state_modulo_laws(&cur_state, &init_laws, &start_sv, &[], free_vars, domain)?;
        return Ok(Err(RejectedPathCandidate {
            steps: seq_names,
            failed_step: 0,
            intermediate_state: disp,
            residuals: vec!["1".to_owned()],
            reason: "protocol start domain D_0 is empty".to_owned(),
        }));
    }
    let mut state_history = vec![cur_state.clone()];
    let mut phases_visited = vec![proto.start_phase.clone()];
    let mut all_arg_vars = Vec::new();
    let mut obligations = Vec::new();
    let eval_refs: Vec<&EvalCondition> = eval_cond.into_iter().collect();
    let extra_nl: Vec<PolyExpr> = witness
        .remaining_nonlinear()
        .iter()
        .map(|p| poly_q_to_expr(p, free_vars))
        .collect();

    for (k, op) in seq.iter().enumerate() {
        let mut arg_map = BTreeMap::new();
        for (a, _) in &op.args {
            let fresh = format!("step{k}_{a}");
            all_arg_vars.push(fresh.clone());
            arg_map.insert(a.clone(), PolyExpr::ArgVar(fresh));
        }
        for dlaw in &op.domain_laws {
            obligations.push(PreservationObligation {
                state_vars: start_sv.clone(),
                arg_vars: all_arg_vars.clone(),
                source_laws: init_laws.clone(),
                target: substitute_poly_expr(&dlaw.polynomial, &cur_state, &arg_map, &empty),
            });
        }
        let mut next_state = BTreeMap::new();
        for (coord, upd) in &op.updates {
            next_state.insert(
                coord.clone(),
                substitute_poly_expr(upd, &cur_state, &arg_map, &empty),
            );
        }
        let dst_ph = after_pres.phase(&op.target_phase).expect("dst_phase");
        for dc in &dst_ph.coords {
            if let CoordValue::Observed(lit) = &dc.value
                && let Some(expr) = next_state.get(&dc.name)
            {
                obligations.push(PreservationObligation {
                    state_vars: start_sv.clone(),
                    arg_vars: all_arg_vars.clone(),
                    source_laws: init_laws.clone(),
                    target: PolyExpr::diff(expr.clone(), PolyExpr::Const(lit.clone())),
                });
            }
        }
        for sl in &dst_ph.state_laws {
            obligations.push(PreservationObligation {
                state_vars: start_sv.clone(),
                arg_vars: all_arg_vars.clone(),
                source_laws: init_laws.clone(),
                target: substitute_poly_expr(&sl.polynomial, &next_state, &empty, &empty),
            });
        }

        cur_state = next_state;
        state_history.push(cur_state.clone());
        phases_visited.push(op.target_phase.clone());
        if k + 1 == seq.len() {
            for el in &end_laws_sub {
                obligations.push(PreservationObligation {
                    state_vars: start_sv.clone(),
                    arg_vars: all_arg_vars.clone(),
                    source_laws: init_laws.clone(),
                    target: substitute_poly_expr(el, &cur_state, &empty, &empty),
                });
            }
        }

        let step_solve = solve_obligations_and_evals(
            &obligations,
            &extra_nl,
            &eval_refs,
            domain,
            point_domain,
            free_vars,
        );
        match step_solve.verdict {
            Verdict::Undetermined(r) => return Err(r),
            Verdict::Refuted => {
                let disp = format_state_modulo_laws(
                    &cur_state,
                    &init_laws,
                    &start_sv,
                    &all_arg_vars,
                    free_vars,
                    domain,
                )?;
                return Ok(Err(RejectedPathCandidate {
                    steps: seq_names,
                    failed_step: k + 1,
                    intermediate_state: disp,
                    residuals: step_solve.residual_display,
                    reason: format!("execution step `{}` violated domain or state law", op.name),
                }));
            }
            Verdict::Established => {}
        }
    }

    if seq.is_empty() {
        for el in &end_laws_sub {
            obligations.push(PreservationObligation {
                state_vars: start_sv.clone(),
                arg_vars: all_arg_vars.clone(),
                source_laws: init_laws.clone(),
                target: substitute_poly_expr(el, &cur_state, &empty, &empty),
            });
        }
        let step_solve = solve_obligations_and_evals(
            &obligations,
            &extra_nl,
            &eval_refs,
            domain,
            point_domain,
            free_vars,
        );
        match step_solve.verdict {
            Verdict::Undetermined(r) => return Err(r),
            Verdict::Refuted => {
                let disp = format_state_modulo_laws(
                    &cur_state,
                    &init_laws,
                    &start_sv,
                    &all_arg_vars,
                    free_vars,
                    domain,
                )?;
                return Ok(Err(RejectedPathCandidate {
                    steps: seq_names,
                    failed_step: 0,
                    intermediate_state: disp,
                    residuals: step_solve.residual_display,
                    reason: "zero-step execution violated start/end laws".to_owned(),
                }));
            }
            Verdict::Established => {}
        }
    }

    let reeval = reeval_obligations_and_constraints(
        &obligations,
        &[],
        &eval_refs,
        witness,
        domain,
        point_domain,
        "protocol_execution_path",
    )?;
    if !reeval.matched {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "protocol_execution_reeval".to_owned(),
            detail: reeval.detail,
        });
    }

    let mut formatted_states = Vec::with_capacity(state_history.len());
    for st in &state_history {
        formatted_states.push(format_state_modulo_laws(
            st,
            &init_laws,
            &start_sv,
            &all_arg_vars,
            free_vars,
            domain,
        )?);
    }
    let (comp_sc, mut comp_wt) =
        format_state_morphism(restored_morph, after_pres, free_vars.vars())?;
    let mut seq_translated = Vec::new();
    for name in &seq_names {
        if let Some(ws) = comp_wt.get(name) {
            seq_translated.extend(ws.iter().cloned());
        }
    }
    comp_wt.insert("sequence".to_owned(), seq_translated);

    Ok(Ok(RestoredPath {
        steps: seq_names,
        intermediate_vertices: phases_visited,
        parameter_assignments: witness.display_assignments(),
        free_parameters: witness.free_parameters(),
        step_states: formatted_states,
        composite_state_comparisons: comp_sc,
        composite_word_translation: comp_wt,
        composite_is_one_step: None,
        reeval,
    }))
}

fn format_state_modulo_laws(
    state: &BTreeMap<String, PolyExpr>,
    laws: &[PolyExpr],
    state_vars: &[String],
    arg_vars: &[String],
    free_vars: &VarOrder,
    domain: &CoeffDomain,
) -> Result<BTreeMap<String, String>, SilenceReason> {
    let (order, bind) = ExprBindings::from_slices(state_vars, arg_vars, free_vars.vars())
        .map_err(map_algebra_silence)?;
    if matches!(domain, CoeffDomain::Q | CoeffDomain::Z) && !laws.is_empty() {
        let q_laws: Result<Vec<Poly<Rat>>, _> =
            laws.iter().map(|l| Poly::from_expr_q(l, &bind)).collect();
        if let Ok(ql) = q_laws
            && let Ok(gb) = GroebnerBasis::compute(&ql, order.clone(), MonomialOrder::Grevlex)
            && !gb.contains_one()
        {
            let mut out = BTreeMap::new();
            for (k, expr) in state {
                let p = Poly::from_expr_q(expr, &bind).map_err(map_algebra_silence)?;
                let nf = gb.normal_form(&p).map_err(map_algebra_silence)?;
                out.insert(k.clone(), nf.display(&order, MonomialOrder::Grevlex));
            }
            return Ok(out);
        }
    }
    let mut out = BTreeMap::new();
    for (k, expr) in state {
        out.insert(k.clone(), fmt_poly_expr(expr, &bind, &order, domain)?);
    }
    Ok(out)
}
