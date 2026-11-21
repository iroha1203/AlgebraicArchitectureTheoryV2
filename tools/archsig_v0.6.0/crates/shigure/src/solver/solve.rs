//! 意味保存検査・条件付き解空間 F_{a,H,P}・相互作用解析の統合実行器（G-140 / G-141）。

use crate::algebra::{
    AffineSolutionQ, ExprBindings, GroebnerBasis, MonomialOrder, Poly, QuotientStratum, Rat,
    RingCoeff, VarOrder, rabinowitsch_solve, require_closed_for_interaction, solve_affine_q,
};
use crate::ir::change::{EditableTarget, EvalCondition, PointDomain};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{
    ApplicabilityCheck, EmptyWitness, InteractionSummary, RestoredArtifact, ShigureOutcome,
    SilenceReason, Verdict,
};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::CheckedShigureTask;
use crate::solver::ShigureQueryKind;
use crate::solver::domain_solve::{solve_affine_direct_z, solve_over_fp};
use crate::solver::interaction_query::execute_interaction_analysis;
use crate::solver::preservation::{
    PreservationObligation, build_preservation_obligations, collect_all_provenance_origins,
    compute_preservation_locus_q, extract_closed_residuals_z, intersect_strata_lists,
    map_algebra_silence,
};
use crate::solver::restore::{
    extract_affine_substitution_q, find_witness_point_q, polys_to_affine_system_q,
    restore_and_reeval_q,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

/// 実行中の共通メタデータ（係数域・点集合域・適用条件検査・由来）を束ねるコンテキスト。
pub(crate) struct SolveCtx {
    pub coeff_domain: CoeffDomain,
    pub point_domain: PointDomain,
    pub checks: Vec<ApplicabilityCheck>,
    pub provenance: Provenance,
}

impl SolveCtx {
    pub(crate) fn established(
        self,
        residual_ideal: Vec<String>,
        restored: Option<RestoredArtifact>,
        interaction: Option<InteractionSummary>,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Established,
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness: None,
            restored,
            interaction,
        }
    }

    pub(crate) fn refuted(
        self,
        residual_ideal: Vec<String>,
        empty_witness: Option<EmptyWitness>,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Refuted,
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness,
            restored: None,
            interaction: None,
        }
    }

    pub(crate) fn undetermined(
        self,
        residual_ideal: Vec<String>,
        reason: SilenceReason,
    ) -> ShigureOutcome {
        ShigureOutcome {
            verdict: Verdict::Undetermined(reason),
            coeff_domain: self.coeff_domain,
            point_domain: self.point_domain,
            applicability: self.checks,
            provenance: self.provenance,
            residual_ideal,
            empty_witness: None,
            restored: None,
            interaction: None,
        }
    }
}

/// `CheckedShigureTask` に対して指定された問いを実行し、型付き `ShigureOutcome` を返す。
pub fn execute_task(task: &CheckedShigureTask, query: ShigureQueryKind) -> ShigureOutcome {
    let mut ctx = SolveCtx {
        coeff_domain: task.change_spec().coeff_domain.clone(),
        point_domain: resolve_point_domain(task, query),
        checks: Vec::new(),
        provenance: build_outcome_provenance(task, query),
    };

    if let Err(silence) = check_common_applicability(task, query, &mut ctx.checks) {
        return ctx.undetermined(vec![], silence);
    }

    let param_names: Vec<String> = task
        .change_spec()
        .parameters
        .iter()
        .map(|p| p.name.clone())
        .collect();
    let param_vars = match VarOrder::new(param_names) {
        Ok(v) => v,
        Err(e) => {
            let reason = map_algebra_silence(e);
            ctx.checks.push(ApplicabilityCheck::failed(
                "parameter_ring_well_formed",
                MathClause::G141D1,
                reason.code(),
            ));
            return ctx.undetermined(vec![], reason);
        }
    };

    let obligations = match build_preservation_obligations(task.pair()) {
        Ok(obs) => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "finite_preservation_obligations_generated",
                MathClause::G140A2,
            ));
            obs
        }
        Err(reason) => {
            ctx.checks.push(ApplicabilityCheck::failed(
                "finite_preservation_obligations_generated",
                MathClause::G140A2,
                reason.code(),
            ));
            return ctx.undetermined(vec![], reason);
        }
    };

    match query {
        ShigureQueryKind::SemanticPreservation => {
            execute_semantic_preservation(task, &obligations, &param_vars, ctx)
        }
        ShigureQueryKind::ConditionalSolutionSpace => {
            execute_conditional_solution_space(task, &obligations, &param_vars, ctx)
        }
        ShigureQueryKind::InteractionAnalysis => {
            execute_interaction_analysis(task, &obligations, &param_vars, ctx)
        }
    }
}

fn resolve_point_domain(task: &CheckedShigureTask, query: ShigureQueryKind) -> PointDomain {
    if let Some(cond) = task.eval_condition() {
        return cond.point_domain.clone();
    }
    if query == ShigureQueryKind::InteractionAnalysis {
        return PointDomain::UniversalRing;
    }
    match &task.change_spec().coeff_domain {
        CoeffDomain::Q | CoeffDomain::Z => PointDomain::AlgebraicClosure,
        CoeffDomain::Fp(p) => PointDomain::FiniteFieldPoints(p.clone()),
    }
}

fn build_outcome_provenance(task: &CheckedShigureTask, query: ShigureQueryKind) -> Provenance {
    let eval_origins: Vec<_> = task
        .eval_condition()
        .map(|c| {
            let mut out = c.provenance.origins.clone();
            for item in c
                .evaluations
                .iter()
                .chain(&c.equations)
                .chain(&c.invertibles)
            {
                if let Some(o) = &item.provenance {
                    out.push(o.clone());
                }
            }
            out
        })
        .unwrap_or_default();
    let mut change_origins = task.change_spec().provenance.origins.clone();
    for p in &task.change_spec().parameters {
        if let Some(o) = &p.provenance {
            change_origins.push(o.clone());
        }
    }
    let origins = collect_all_provenance_origins(task.pair(), &change_origins, &eval_origins);
    let clauses = match query {
        ShigureQueryKind::SemanticPreservation => vec![
            MathClause::G139P0P1,
            MathClause::G140P0Dot1,
            MathClause::G140A2,
            MathClause::G140P1,
            MathClause::G140P3P5,
            MathClause::G141D5,
        ],
        ShigureQueryKind::ConditionalSolutionSpace => vec![
            MathClause::G139P0P1,
            MathClause::G140A2,
            MathClause::G140E1E2,
            MathClause::G140P6,
            MathClause::G141D1,
            MathClause::G141D4,
            MathClause::G141D5,
        ],
        ShigureQueryKind::InteractionAnalysis => vec![
            MathClause::G139P0P1,
            MathClause::G140A2,
            MathClause::G141D1,
            MathClause::G141F10F12,
        ],
    };
    Provenance::new(origins, clauses)
}

fn check_common_applicability(
    task: &CheckedShigureTask,
    query: ShigureQueryKind,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(), SilenceReason> {
    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return Err(SilenceReason::UnobservedDependency { slots: missing });
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    for pres in [&task.pair().before, &task.pair().after] {
        for sort in &pres.sorts {
            if sort.rank != 1 {
                let detail = format!(
                    "sort `{}` in `{}` has rank {}, but scalar polynomial engine requires rank == 1",
                    sort.name, pres.name, sort.rank
                );
                checks.push(ApplicabilityCheck::failed(
                    "sort_rank_one_required",
                    MathClause::G139P0P1,
                    detail.clone(),
                ));
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "sort_rank_one_required".to_owned(),
                    detail,
                });
            }
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "sort_rank_one_required",
        MathClause::G139P0P1,
    ));

    for target in &task.change_spec().editable {
        let target_pres = match target {
            EditableTarget::OperationExpr { presentation, .. }
            | EditableTarget::RepresentationLaw { presentation, .. } => Some(presentation.as_str()),
            EditableTarget::StateComparisonExpr { .. } => None,
        };
        if target_pres == Some(task.pair().before.name.as_str()) {
            let detail = format!(
                "editable target references fixed reference presentation `{}`",
                task.pair().before.name
            );
            checks.push(ApplicabilityCheck::failed(
                "editable_target_must_be_after",
                MathClause::G140E1E2,
                detail.clone(),
            ));
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "editable_target_must_be_after".to_owned(),
                detail,
            });
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "editable_target_must_be_after",
        MathClause::G140E1E2,
    ));

    if query == ShigureQueryKind::InteractionAnalysis
        && let Some(cond) = task.eval_condition()
        && let Err(reason) = require_closed_for_interaction(!cond.is_purely_closed())
    {
        checks.push(ApplicabilityCheck::failed(
            "closed_condition_for_interaction",
            MathClause::G141F10F12,
            reason.code(),
        ));
        return Err(reason);
    }

    Ok(())
}

fn execute_semantic_preservation(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    match ctx.coeff_domain.clone() {
        CoeffDomain::Fp(modulus) => {
            solve_over_fp(task, obligations, None, param_vars, &modulus, ctx)
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            let locus = match compute_preservation_locus_q(obligations, param_vars) {
                Ok(l) => {
                    ctx.checks.push(ApplicabilityCheck::passed(
                        "quotient_ideal_membership_in_scope",
                        MathClause::G141D5,
                    ));
                    l
                }
                Err(reason) => {
                    ctx.checks.push(ApplicabilityCheck::failed(
                        "quotient_ideal_membership_in_scope",
                        MathClause::G141D5,
                        reason.code(),
                    ));
                    return ctx.undetermined(vec![], reason);
                }
            };

            let residual_display = display_polys(&locus.closure_ideal, param_vars);
            if locus.strata.is_empty() {
                let witness = compute_empty_witness_q(&locus.closure_ideal, &[], param_vars);
                return ctx.refuted(residual_display, witness);
            }

            let (final_eqs, final_invs): (&[Poly<Rat>], &[Poly<Rat>]) = if locus.is_zariski_closed {
                (&locus.closure_ideal, &[])
            } else {
                (&locus.strata[0].equations, &locus.strata[0].invertibles)
            };

            finalize_q_or_z_solution(
                task,
                None,
                final_eqs,
                final_invs,
                param_vars,
                ctx,
                residual_display,
            )
        }
    }
}

fn execute_conditional_solution_space(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let eval_cond = task.eval_condition();
    let param_bind = ExprBindings::params_only(param_vars);

    if let Some(cond) = eval_cond {
        if let Err(reason) = validate_eval_map_expressions(cond, &param_bind, &ctx.coeff_domain) {
            ctx.checks.push(ApplicabilityCheck::failed(
                "evaluation_map_well_formed",
                MathClause::G140E1E2,
                reason.code(),
            ));
            return ctx.undetermined(vec![], reason);
        }
        ctx.checks.push(ApplicabilityCheck::passed(
            "evaluation_map_well_formed",
            MathClause::G140E1E2,
        ));
    }

    match ctx.coeff_domain.clone() {
        CoeffDomain::Fp(modulus) => {
            solve_over_fp(task, obligations, eval_cond, param_vars, &modulus, ctx)
        }
        CoeffDomain::Z if ctx.point_domain == PointDomain::IntegerPoints => {
            if let Ok(Some(z_res)) = extract_closed_residuals_z(obligations, param_vars.vars()) {
                let mut all_eqs_z = z_res;
                let mut invs_z = Vec::new();
                if let Some(cond) = eval_cond {
                    for eq in &cond.equations {
                        match Poly::from_expr_z(&eq.expr, &param_bind) {
                            Ok(p) if !p.is_zero() => all_eqs_z.push(p),
                            Ok(_) => {}
                            Err(e) => return ctx.undetermined(vec![], map_algebra_silence(e)),
                        }
                    }
                    for inv in &cond.invertibles {
                        match Poly::from_expr_z(&inv.expr, &param_bind) {
                            Ok(p) => invs_z.push(p),
                            Err(e) => return ctx.undetermined(vec![], map_algebra_silence(e)),
                        }
                    }
                }
                if all_eqs_z.iter().all(Poly::is_affine) {
                    return solve_affine_direct_z(
                        task, eval_cond, &all_eqs_z, &invs_z, param_vars, ctx,
                    );
                }
            }
            solve_conditional_via_q(task, obligations, eval_cond, param_vars, &param_bind, ctx)
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            solve_conditional_via_q(task, obligations, eval_cond, param_vars, &param_bind, ctx)
        }
    }
}

fn solve_conditional_via_q(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    param_bind: &ExprBindings,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let locus = match compute_preservation_locus_q(obligations, param_vars) {
        Ok(l) => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "quotient_ideal_membership_in_scope",
                MathClause::G141D5,
            ));
            l
        }
        Err(reason) => {
            ctx.checks.push(ApplicabilityCheck::failed(
                "quotient_ideal_membership_in_scope",
                MathClause::G141D5,
                reason.code(),
            ));
            return ctx.undetermined(vec![], reason);
        }
    };

    let closure_disp = display_polys(&locus.closure_ideal, param_vars);
    let mut eval_eqs = Vec::new();
    let mut eval_invs = Vec::new();
    if let Some(cond) = eval_cond {
        for eq in &cond.equations {
            match Poly::from_expr_q(&eq.expr, param_bind) {
                Ok(p) if !p.is_zero() => eval_eqs.push(p),
                Ok(_) => {}
                Err(e) => return ctx.undetermined(closure_disp, map_algebra_silence(e)),
            }
        }
        for inv in &cond.invertibles {
            match Poly::from_expr_q(&inv.expr, param_bind) {
                Ok(p) => eval_invs.push(p),
                Err(e) => return ctx.undetermined(closure_disp, map_algebra_silence(e)),
            }
        }
    }

    if locus.strata.is_empty() {
        let witness = compute_empty_witness_q(&locus.closure_ideal, &[], param_vars);
        return ctx.refuted(closure_disp, witness);
    }

    if locus.is_zariski_closed {
        let mut combined_eqs = locus.closure_ideal.clone();
        combined_eqs.extend(eval_eqs.iter().cloned());
        let rab = match rabinowitsch_solve(&combined_eqs, &eval_invs, param_vars) {
            Ok(r) => r,
            Err(e) => return ctx.undetermined(closure_disp, map_algebra_silence(e)),
        };
        if rab.is_empty_over_closure {
            ctx.checks.push(ApplicabilityCheck::passed(
                "rabinowitsch_emptiness_verified",
                MathClause::G141D5,
            ));
            return ctx.refuted(closure_disp, rab.empty_witness);
        }

        let final_residual = display_polys(&rab.parameter_equations, param_vars);
        return finalize_q_or_z_solution(
            task,
            eval_cond,
            &rab.parameter_equations,
            &eval_invs,
            param_vars,
            ctx,
            final_residual,
        );
    }

    let eval_stratum = vec![QuotientStratum {
        equations: eval_eqs,
        invertibles: eval_invs,
    }];
    let intersected = match intersect_strata_lists(&locus.strata, &eval_stratum, param_vars) {
        Ok(s) => s,
        Err(reason) => return ctx.undetermined(closure_disp, reason),
    };
    if intersected.is_empty() {
        let witness = if locus.strata.len() == 1 {
            let mut eqs = locus.strata[0].equations.clone();
            eqs.extend(eval_stratum[0].equations.iter().cloned());
            let mut invs = locus.strata[0].invertibles.clone();
            invs.extend(eval_stratum[0].invertibles.iter().cloned());
            compute_empty_witness_q(&eqs, &invs, param_vars)
        } else {
            None
        };
        return ctx.refuted(closure_disp, witness);
    }

    let first = &intersected[0];
    let final_residual = display_polys(&first.equations, param_vars);
    finalize_q_or_z_solution(
        task,
        eval_cond,
        &first.equations,
        &first.invertibles,
        param_vars,
        ctx,
        final_residual,
    )
}

fn finalize_q_or_z_solution(
    task: &CheckedShigureTask,
    eval_cond: Option<&EvalCondition>,
    final_eqs: &[Poly<Rat>],
    final_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
    residual_display: Vec<String>,
) -> ShigureOutcome {
    let prefer_z = ctx.coeff_domain == CoeffDomain::Z;
    let all_affine = final_eqs.iter().all(Poly::is_affine);

    match ctx.point_domain.clone() {
        PointDomain::AlgebraicClosure => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "algebraic_closure_nonempty",
                MathClause::G141D5,
            ));
            restore_q_and_finish(
                task,
                eval_cond,
                final_eqs,
                final_invs,
                param_vars,
                prefer_z,
                ctx,
                residual_display,
            )
        }
        PointDomain::UniversalRing => {
            if !final_invs.is_empty() {
                let reason = SilenceReason::ApplicabilityConditionNotMet {
                    condition: "universal_ring_closed_equations_only".to_owned(),
                    detail: "open/invertible conditions cannot be evaluated uniformly over all rings including the zero ring".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "universal_ring_closed_equations_only",
                    MathClause::G141D1,
                    reason.code(),
                ));
                return ctx.undetermined(residual_display, reason);
            }
            restore_q_and_finish(
                task,
                eval_cond,
                final_eqs,
                &[],
                param_vars,
                prefer_z,
                ctx,
                residual_display,
            )
        }
        PointDomain::RationalPoints => {
            if !all_affine {
                let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::RationalPoints,
                    detail: "system is nonempty over algebraic closure, but general rational-point existence for nonlinear equations is out of scope".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "rational_point_existence_decidable",
                    MathClause::G141D4,
                    reason.code(),
                ));
                return ctx.undetermined(residual_display, reason);
            }
            let (mat, rhs) = polys_to_affine_system_q(final_eqs, param_vars.len());
            match solve_affine_q(&mat, &rhs, param_vars.len()) {
                Ok(AffineSolutionQ::Inconsistent { .. }) => {
                    let witness = compute_empty_witness_q(final_eqs, final_invs, param_vars);
                    ctx.refuted(residual_display, witness)
                }
                Ok(AffineSolutionQ::Consistent {
                    particular,
                    kernel_basis,
                    verified: true,
                }) => {
                    if !final_invs.is_empty() {
                        match find_witness_point_q(
                            &particular,
                            &kernel_basis,
                            final_eqs,
                            final_invs,
                        ) {
                            Ok(Some(_)) => ctx.checks.push(ApplicabilityCheck::passed(
                                "rational_open_witness_verified",
                                MathClause::G141D4,
                            )),
                            Ok(None) => {
                                let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
                                    point_domain: PointDomain::RationalPoints,
                                    detail: "no concrete rational point satisfying open conditions was verified within deterministic witness search".to_owned(),
                                };
                                ctx.checks.push(ApplicabilityCheck::failed(
                                    "rational_open_witness_verified",
                                    MathClause::G141D4,
                                    reason.code(),
                                ));
                                return ctx.undetermined(residual_display, reason);
                            }
                            Err(reason) => return ctx.undetermined(residual_display, reason),
                        }
                    }
                    restore_q_and_finish(
                        task,
                        eval_cond,
                        final_eqs,
                        final_invs,
                        param_vars,
                        false,
                        ctx,
                        residual_display,
                    )
                }
                Ok(AffineSolutionQ::Consistent {
                    verified: false, ..
                }) => ctx.undetermined(
                    residual_display,
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "affine_q_verification".to_owned(),
                        detail: "affine Q solution failed independent verification".to_owned(),
                    },
                ),
                Err(e) => ctx.undetermined(residual_display, map_algebra_silence(e)),
            }
        }
        PointDomain::IntegerPoints => {
            if !all_affine {
                let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::IntegerPoints,
                    detail: "system is nonempty over algebraic closure, but general integer-point existence for nonlinear equations is out of scope".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "integer_point_existence_decidable",
                    MathClause::G141D4,
                    reason.code(),
                ));
                return ctx.undetermined(residual_display, reason);
            }
            let eqs_z = clear_denominators_to_z(final_eqs);
            let invs_z = clear_denominators_to_z(final_invs);
            solve_affine_direct_z(task, eval_cond, &eqs_z, &invs_z, param_vars, ctx)
        }
        PointDomain::FiniteFieldPoints(_) => ctx.undetermined(
            residual_display,
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "point_domain_matches_coeff_domain".to_owned(),
                detail: "Fp point domain requires Fp coefficient domain".to_owned(),
            },
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn restore_q_and_finish(
    task: &CheckedShigureTask,
    eval_cond: Option<&EvalCondition>,
    final_eqs: &[Poly<Rat>],
    final_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    prefer_z: bool,
    mut ctx: SolveCtx,
    residual_display: Vec<String>,
) -> ShigureOutcome {
    let extracted = match extract_affine_substitution_q(final_eqs, param_vars, prefer_z) {
        Ok(Some(ext)) => ext,
        Ok(None) => {
            let witness = compute_empty_witness_q(final_eqs, final_invs, param_vars);
            return ctx.refuted(residual_display, witness);
        }
        Err(reason) => return ctx.undetermined(residual_display, reason),
    };
    match restore_and_reeval_q(task.pair(), eval_cond, final_invs, param_vars, &extracted) {
        Ok(artifact) if artifact.reeval.matched => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "restored_model_reevaluation_matched",
                MathClause::G140E1E2,
            ));
            ctx.established(residual_display, Some(artifact), None)
        }
        Ok(artifact) => {
            let detail = artifact.reeval.detail.clone();
            ctx.checks.push(ApplicabilityCheck::failed(
                "restored_model_reevaluation_matched",
                MathClause::G140E1E2,
                detail.clone(),
            ));
            ctx.undetermined(
                residual_display,
                SilenceReason::ApplicabilityConditionNotMet {
                    condition: "restored_model_reevaluation_matched".to_owned(),
                    detail,
                },
            )
        }
        Err(reason) => ctx.undetermined(residual_display, reason),
    }
}

fn validate_eval_map_expressions(
    cond: &EvalCondition,
    param_bind: &ExprBindings,
    domain: &CoeffDomain,
) -> Result<(), SilenceReason> {
    for item in &cond.evaluations {
        match domain {
            CoeffDomain::Q => {
                Poly::from_expr_q(&item.expr, param_bind).map_err(map_algebra_silence)?;
            }
            CoeffDomain::Z => {
                Poly::from_expr_z(&item.expr, param_bind).map_err(map_algebra_silence)?;
            }
            CoeffDomain::Fp(m) => {
                Poly::from_expr_fp(&item.expr, param_bind, m).map_err(map_algebra_silence)?;
            }
        }
    }
    Ok(())
}

fn compute_empty_witness_q(
    eqs: &[Poly<Rat>],
    invs: &[Poly<Rat>],
    param_vars: &VarOrder,
) -> Option<EmptyWitness> {
    if invs.is_empty() {
        let gb = GroebnerBasis::compute(eqs, param_vars.clone(), MonomialOrder::Grevlex).ok()?;
        gb.empty_witness().ok()?
    } else {
        let rab = rabinowitsch_solve(eqs, invs, param_vars).ok()?;
        rab.empty_witness
    }
}

fn clear_denominators_to_z(polys: &[Poly<Rat>]) -> Vec<Poly<BigInt>> {
    polys
        .iter()
        .map(|p| {
            let mut lcm = BigInt::one();
            for coeff in p.terms().values() {
                lcm = lcm.lcm(coeff.den());
            }
            let mut out = Poly::zero(p.num_vars(), BigInt::zero());
            for (mono, coeff) in p.terms() {
                let scaled = coeff.num() * (&lcm / coeff.den());
                out.add_term(mono.clone(), scaled);
            }
            out
        })
        .collect()
}

pub(crate) fn display_polys<C: RingCoeff>(polys: &[Poly<C>], vars: &VarOrder) -> Vec<String> {
    polys
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| p.display(vars, MonomialOrder::Grevlex))
        .collect()
}
