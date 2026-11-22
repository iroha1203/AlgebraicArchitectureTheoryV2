//! 合法状態の移送・移送合成（fiber product）・P5.3 検算ソルバ（`CheckedTransferTask` -> `ShigureOutcome`）。

use crate::algebra::VarOrder;
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::presentation::CoordValue;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_ext::{
    DomainRelation, RestoredTransfer, TransferOutcomeDetail, TransferStepDiagnostic,
};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::transfer::{CheckedTransferTask, TransferStepSpec};
use crate::solver::common_format::{
    collect_change_and_eval_origins, collect_presentation_origins,
    reeval_obligations_and_constraints, substitute_eval_condition,
};
use crate::solver::common_solve::{resolve_consistent_point_domain, solve_obligations_and_evals};
use crate::solver::preservation::{map_algebra_silence, substitute_poly_expr};
use crate::solver::transfer_compose::{
    append_composite_transfer_obligations, collect_transfer_obligations,
    compose_and_classify_transfer, format_restored_transfer, substitute_transfer_steps,
};
use crate::solver::transfer_lift::search_old_word_lift;
use crate::solver::transfer_words::check_word_preservation;
use std::collections::{BTreeMap, BTreeSet};

/// 検証済み状態移送タスク `CheckedTransferTask` を解き、`TransferOutcomeDetail` 付き `ShigureOutcome` を返す。
pub fn solve_transfer_task(task: &CheckedTransferTask) -> ShigureOutcome {
    let spec = task.spec();
    let coeff_domain = &spec.change_spec.coeff_domain;
    let eval_refs: Vec<&EvalCondition> = task.eval_condition().into_iter().collect();
    let provenance = build_transfer_provenance(task, &eval_refs);

    let point_domain = match resolve_consistent_point_domain(coeff_domain, &eval_refs) {
        Ok(pd) => pd,
        Err(reason) => {
            return undetermined_transfer(
                coeff_domain,
                &PointDomain::AlgebraicClosure,
                vec![ApplicabilityCheck::failed(
                    "consistent_point_domain",
                    MathClause::G140G1,
                    reason.code(),
                )],
                provenance,
                vec![],
                DomainRelation::Empty,
                vec![],
                vec![],
                reason,
            );
        }
    };

    let mut checks = Vec::new();
    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return undetermined_transfer(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            DomainRelation::Empty,
            vec![],
            vec![],
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    for step in &spec.steps {
        for pres in [&step.comparison.before, &step.comparison.after] {
            for s in &pres.sorts {
                if s.rank != 1 {
                    let detail = format!(
                        "sort `{}` in `{}` has rank {}, expected 1",
                        s.name, pres.name, s.rank
                    );
                    checks.push(ApplicabilityCheck::failed(
                        "sort_rank_one_required",
                        MathClause::G139P0P1,
                        detail.clone(),
                    ));
                    return undetermined_transfer(
                        coeff_domain,
                        &point_domain,
                        checks,
                        provenance,
                        vec![],
                        DomainRelation::Empty,
                        vec![],
                        vec![],
                        SilenceReason::ApplicabilityConditionNotMet {
                            condition: "sort_rank_one_required".to_owned(),
                            detail,
                        },
                    );
                }
            }
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "sort_rank_one_required",
        MathClause::G139P0P1,
    ));

    if spec.old_word_lifts.iter().any(|o| o.max_length.is_none()) {
        let reason = SilenceReason::UnboundedSearchOutOfScope {
            detail: "old word lift search requires an explicit finite `max_length` bound"
                .to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "explicit_finite_lift_length",
            MathClause::G140G2,
            reason.code(),
        ));
        return undetermined_transfer(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            vec![],
            DomainRelation::Empty,
            vec![],
            vec![],
            reason,
        );
    }

    let param_names: Vec<String> = spec
        .change_spec
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let param_vars = match VarOrder::new(param_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                vec![],
                DomainRelation::Empty,
                vec![],
                vec![],
                map_algebra_silence(e),
            );
        }
    };

    let (obligations, step_diagnostics) =
        match collect_transfer_obligations(&spec.steps, &param_vars, coeff_domain) {
            Ok(data) => data,
            Err(reason) => {
                return undetermined_transfer(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    vec![],
                    DomainRelation::Empty,
                    vec![],
                    vec![],
                    reason,
                );
            }
        };

    let solve_res = solve_obligations_and_evals(
        &obligations,
        &[],
        &eval_refs,
        coeff_domain,
        &point_domain,
        &param_vars,
    );
    checks.extend(solve_res.checks);

    let witness = match solve_res.verdict {
        Verdict::Undetermined(reason) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                DomainRelation::Empty,
                vec![],
                step_diagnostics,
                reason,
            );
        }
        Verdict::Refuted => {
            return refuted_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                solve_res.empty_witness,
                DomainRelation::Empty,
                vec![],
                step_diagnostics,
            );
        }
        Verdict::Established => match solve_res.witness {
            Some(w) => w,
            None => {
                return undetermined_transfer(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    DomainRelation::Empty,
                    vec![],
                    step_diagnostics,
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "witness_present".to_owned(),
                        detail: "missing witness on established transfer".to_owned(),
                    },
                );
            }
        },
    };

    let param_subst = witness.to_param_subst(&param_vars);
    let free_names = witness.unassigned_parameters();
    let free_vars = match VarOrder::new(free_names) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                DomainRelation::Empty,
                vec![],
                step_diagnostics,
                map_algebra_silence(e),
            );
        }
    };

    let re_eval_owned: Vec<EvalCondition> = eval_refs
        .iter()
        .map(|ec| substitute_eval_condition(ec, &param_subst))
        .collect();
    let re_eval_refs: Vec<&EvalCondition> = re_eval_owned.iter().collect();

    let restored_steps = substitute_transfer_steps(&spec.steps, &param_subst);
    let (re_step_obs, re_step_diags) =
        match collect_transfer_obligations(&restored_steps, &free_vars, coeff_domain) {
            Ok(data) => data,
            Err(reason) => {
                return undetermined_transfer(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    DomainRelation::Empty,
                    vec![],
                    step_diagnostics,
                    reason,
                );
            }
        };

    let composed = match compose_and_classify_transfer(
        &restored_steps,
        &free_vars,
        &witness,
        &re_eval_refs,
        coeff_domain,
        &point_domain,
    ) {
        Ok(data) => data,
        Err(reason) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                DomainRelation::Empty,
                vec![],
                re_step_diags,
                reason,
            );
        }
    };

    let mut re_obs = re_step_obs;
    if let Err(reason) = append_composite_transfer_obligations(
        &restored_steps,
        &composed.composed_h,
        &composed.composed_lift,
        &composed.d0k_laws,
        &mut re_obs,
    ) {
        return undetermined_transfer(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            solve_res.residual_display,
            composed.domain_relation,
            composed.d0k_display,
            re_step_diags,
            reason,
        );
    }

    let reeval = match reeval_obligations_and_constraints(
        &re_obs,
        &[],
        &re_eval_refs,
        &witness,
        coeff_domain,
        &point_domain,
        "transfer",
    ) {
        Ok(r) => r,
        Err(reason) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                composed.domain_relation,
                composed.d0k_display,
                re_step_diags,
                reason,
            );
        }
    };
    if !reeval.matched {
        return undetermined_transfer(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            solve_res.residual_display,
            composed.domain_relation,
            composed.d0k_display,
            re_step_diags,
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "restored_model_reevaluation_matched".to_owned(),
                detail: reeval.detail,
            },
        );
    }

    if spec.require_full_domain && composed.domain_relation != DomainRelation::FullIsomorphic {
        checks.push(ApplicabilityCheck::failed(
            "full_domain_isomorphic_required",
            MathClause::G140G3,
            format!("domain relation is `{}`", composed.domain_relation.wire()),
        ));
        return refuted_transfer(
            coeff_domain,
            &point_domain,
            checks,
            provenance,
            composed.d0k_display.clone(),
            None,
            composed.domain_relation,
            composed.d0k_display,
            re_step_diags,
        );
    }

    let mut word_checks = Vec::with_capacity(spec.word_checks.len());
    for wc in &spec.word_checks {
        match check_word_preservation(
            wc,
            &restored_steps,
            &composed.composed_h,
            &composed.composed_lift,
            &composed.d0k_laws,
            &param_subst,
            &free_vars,
            &witness,
            &re_eval_refs,
            coeff_domain,
            &point_domain,
        ) {
            Ok(wres) => word_checks.push(wres),
            Err(reason) => {
                return undetermined_transfer(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    composed.domain_relation,
                    composed.d0k_display,
                    re_step_diags,
                    reason,
                );
            }
        }
    }

    let mut old_word_lifts = Vec::with_capacity(spec.old_word_lifts.len());
    for owl in &spec.old_word_lifts {
        match search_old_word_lift(
            owl,
            &restored_steps,
            &composed.composed_h,
            &composed.composed_lift,
            &composed.d0k_laws,
            &param_subst,
            &free_vars,
            &witness,
            &re_eval_refs,
            coeff_domain,
            &point_domain,
        ) {
            Ok(ores) => old_word_lifts.push(ores),
            Err(reason) => {
                return undetermined_transfer(
                    coeff_domain,
                    &point_domain,
                    checks,
                    provenance,
                    solve_res.residual_display,
                    composed.domain_relation,
                    composed.d0k_display,
                    re_step_diags,
                    reason,
                );
            }
        }
    }

    let restored_transfer = match format_restored_transfer(
        &restored_steps,
        &composed.composed_h,
        &composed.step_lifts,
        &composed.composed_lift,
        &free_vars,
        coeff_domain,
    ) {
        Ok((sc, wt, cl, sl)) => Some(RestoredTransfer {
            parameter_assignments: witness.display_assignments(),
            free_parameters: witness.free_parameters(),
            step_lifts: sl,
            composed_lift: cl,
            composed_state_comparison: sc,
            composed_word_translation: wt,
            reeval,
        }),
        Err(reason) => {
            return undetermined_transfer(
                coeff_domain,
                &point_domain,
                checks,
                provenance,
                solve_res.residual_display,
                composed.domain_relation,
                composed.d0k_display,
                re_step_diags,
                reason,
            );
        }
    };

    checks.push(ApplicabilityCheck::passed(
        "transfer_lift_and_composition_verified",
        MathClause::G140G1,
    ));
    ShigureOutcome {
        verdict: Verdict::Established,
        coeff_domain: coeff_domain.clone(),
        point_domain,
        applicability: checks,
        provenance,
        residual_ideal: solve_res.residual_display,
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: Some(TransferOutcomeDetail {
            domain_relation: composed.domain_relation,
            composed_domain_equations: composed.d0k_display,
            step_diagnostics: re_step_diags,
            restored_transfer,
            word_checks,
            old_word_lifts,
        }),
    }
}

pub(crate) fn step_domain_env(
    step: &TransferStepSpec,
) -> (Vec<String>, BTreeMap<String, PolyExpr>, Vec<PolyExpr>) {
    let empty = BTreeMap::new();
    let src_ph = step
        .comparison
        .before
        .phase(&step.source_phase)
        .expect("checked source_phase");
    let mut sv = Vec::new();
    let mut obs = BTreeMap::new();
    for c in &src_ph.coords {
        match &c.value {
            CoordValue::Symbolic => sv.push(c.name.clone()),
            CoordValue::Observed(lit) => {
                obs.insert(c.name.clone(), PolyExpr::Const(lit.clone()));
            }
            CoordValue::Missing => {}
        }
    }
    let mut laws: Vec<PolyExpr> = src_ph
        .state_laws
        .iter()
        .map(|l| substitute_poly_expr(&l.polynomial, &obs, &empty, &empty))
        .collect();
    for dl in &step.domain_laws {
        laws.push(substitute_poly_expr(&dl.polynomial, &obs, &empty, &empty));
    }
    (sv, obs, laws)
}

fn build_transfer_provenance(
    task: &CheckedTransferTask,
    eval_conds: &[&EvalCondition],
) -> Provenance {
    let spec = task.spec();
    let mut set = BTreeSet::new();
    for o in &spec.provenance.origins {
        set.insert(o.clone());
    }
    for s in &spec.steps {
        if let Some(o) = &s.provenance {
            set.insert(o.clone());
        }
        collect_presentation_origins(&s.comparison.before, &mut set);
        collect_presentation_origins(&s.comparison.after, &mut set);
        for l in &s.domain_laws {
            if let Some(o) = &l.provenance {
                set.insert(o.clone());
            }
        }
    }
    for wc in &spec.word_checks {
        if let Some(o) = &wc.provenance {
            set.insert(o.clone());
        }
    }
    for ol in &spec.old_word_lifts {
        if let Some(o) = &ol.provenance {
            set.insert(o.clone());
        }
    }
    collect_change_and_eval_origins(&spec.change_spec, eval_conds, &mut set);
    Provenance::new(
        set.into_iter().collect(),
        vec![
            MathClause::G139P0P1,
            MathClause::G140P0Dot1,
            MathClause::G140A2,
            MathClause::G140G1,
            MathClause::G140G2,
            MathClause::G140G3,
            MathClause::G140P5Dot3,
            MathClause::G141D1,
            MathClause::G141D4,
            MathClause::G141D5,
        ],
    )
}

#[allow(clippy::too_many_arguments)]
fn undetermined_transfer(
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    domain_relation: DomainRelation,
    composed_domain_equations: Vec<String>,
    step_diagnostics: Vec<TransferStepDiagnostic>,
    reason: SilenceReason,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Undetermined(reason),
        coeff_domain: coeff_domain.clone(),
        point_domain: point_domain.clone(),
        applicability,
        provenance,
        residual_ideal,
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: Some(TransferOutcomeDetail {
            domain_relation,
            composed_domain_equations,
            step_diagnostics,
            restored_transfer: None,
            word_checks: vec![],
            old_word_lifts: vec![],
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn refuted_transfer(
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    residual_ideal: Vec<String>,
    empty_witness: Option<EmptyWitness>,
    domain_relation: DomainRelation,
    composed_domain_equations: Vec<String>,
    step_diagnostics: Vec<TransferStepDiagnostic>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Refuted,
        coeff_domain: coeff_domain.clone(),
        point_domain: point_domain.clone(),
        applicability,
        provenance,
        residual_ideal,
        empty_witness,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: Some(TransferOutcomeDetail {
            domain_relation,
            composed_domain_equations,
            step_diagnostics,
            restored_transfer: None,
            word_checks: vec![],
            old_word_lifts: vec![],
        }),
    }
}
