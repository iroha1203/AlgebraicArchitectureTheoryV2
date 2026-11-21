//! 意味保存検査・条件付き解空間 F_{a,H,P}・相互作用解析の統合実行器（G-140 / G-141）。

use crate::algebra::{
    AffineSolutionQ, ExprBindings, GroebnerBasis, MonomialOrder, Poly, QuotientStratum, Rat,
    VarOrder, rabinowitsch_solve, solve_affine_q,
};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::CheckedShigureTask;
use crate::solver::ShigureQueryKind;
use crate::solver::context::{
    SolveCtx, build_outcome_provenance, check_common_applicability, clear_denominators_to_z,
    display_polys, guard_z_quotient_or_universal, resolve_point_domain,
    validate_eval_map_expressions,
};
use crate::solver::domain_solve::{solve_affine_direct_z, solve_over_fp};
use crate::solver::interaction_query::execute_interaction_analysis;
use crate::solver::preservation::{
    PreservationObligation, build_preservation_obligations, compute_preservation_locus_q,
    compute_strata_closure_ideal, extract_closed_residuals_z, intersect_strata_lists,
    is_stratum_covered_by_union, map_algebra_silence,
};
use crate::solver::restore::{
    extract_affine_substitution_q, find_witness_point_q, polys_to_affine_system_q,
    restore_and_reeval_q, restore_and_reeval_q_point,
};

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

fn execute_semantic_preservation(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let has_source_laws = obligations.iter().any(|o| !o.source_laws.is_empty());
    match ctx.coeff_domain.clone() {
        CoeffDomain::Fp(modulus) => {
            solve_over_fp(task, obligations, None, param_vars, &modulus, ctx)
        }
        CoeffDomain::Z if has_source_laws => {
            // Z 上で状態 Law を持つ場合、SemanticPreservation で暗黙に Q 商環へ昇格させない。
            // （代数閉包上での判定を明示要求する場合は ConditionalSolutionSpace + algebraic_closure を用いる。）
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "parametric quotient state-law preservation over Z (with possible Z-torsion) is out of scope; use Q or ConditionalSolutionSpace with explicit algebraic_closure".to_owned(),
            };
            ctx.checks.push(ApplicabilityCheck::failed(
                "z_quotient_out_of_scope",
                MathClause::G141D5,
                reason.code(),
            ));
            ctx.undetermined(vec![], reason)
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
                // F3 対策: 実残差からの空性 witness をそのまま返し、1 = 1*1 を捏造しない。
                return ctx.refuted(residual_display, locus.empty_witness);
            }

            if locus.is_zariski_closed {
                return finalize_q_or_z_solution(
                    task,
                    None,
                    &locus.closure_ideal,
                    &[],
                    &[],
                    param_vars,
                    has_source_laws,
                    ctx,
                    residual_display,
                );
            }

            finalize_non_closed_strata(
                task,
                None,
                &locus.strata,
                &[],
                param_vars,
                has_source_laws,
                ctx,
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
    let has_source_laws = obligations.iter().any(|o| !o.source_laws.is_empty());
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
            if has_source_laws {
                let reason = SilenceReason::QuotientIdealOutOfScope {
                    detail: "parametric quotient state-law membership over Z (with possible Z-torsion) is out of scope; use Q or algebraic_closure".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "z_quotient_out_of_scope",
                    MathClause::G141D5,
                    reason.code(),
                ));
                return ctx.undetermined(vec![], reason);
            }
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
            // 状態 Law 空の非線形 Z 系のみ、Q 上での代数閉包空性判定（1 in I）と沈黙判定へ進む。
            solve_conditional_via_q(
                task,
                obligations,
                eval_cond,
                param_vars,
                &param_bind,
                has_source_laws,
                ctx,
            )
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            if let Some(out) = guard_z_quotient_or_universal(has_source_laws, eval_cond, &ctx) {
                return out;
            }
            solve_conditional_via_q(
                task,
                obligations,
                eval_cond,
                param_vars,
                &param_bind,
                has_source_laws,
                ctx,
            )
        }
    }
}

fn solve_conditional_via_q(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    param_bind: &ExprBindings,
    has_source_laws: bool,
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
        return ctx.refuted(closure_disp, locus.empty_witness);
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
            return ctx.refuted(display_polys(&combined_eqs, param_vars), rab.empty_witness);
        }

        let final_residual = display_polys(&rab.parameter_equations, param_vars);
        return finalize_q_or_z_solution(
            task,
            eval_cond,
            &rab.parameter_equations,
            &eval_invs,
            &eval_invs,
            param_vars,
            has_source_laws,
            ctx,
            final_residual,
        );
    }

    let eval_stratum = vec![QuotientStratum {
        equations: eval_eqs,
        invertibles: eval_invs.clone(),
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

    finalize_non_closed_strata(
        task,
        eval_cond,
        &intersected,
        &eval_invs,
        param_vars,
        has_source_laws,
        ctx,
    )
}

/// 非閉な局所閉層の和集合 `strata` を、開条件を黙って落とさずに全層整合で解決する（F1・F2 対策）。
fn finalize_non_closed_strata(
    task: &CheckedShigureTask,
    eval_cond: Option<&EvalCondition>,
    strata: &[QuotientStratum],
    input_eval_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    has_source_laws: bool,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    if strata.len() == 1 {
        let first = &strata[0];
        let final_residual = display_polys(&first.equations, param_vars);
        return finalize_q_or_z_solution(
            task,
            eval_cond,
            &first.equations,
            &first.invertibles,
            input_eval_invs,
            param_vars,
            has_source_laws,
            ctx,
            final_residual,
        );
    }

    // 交差後に複数層の和集合が閉集合へ回復していれば、単一の閉包 ideal として扱う。
    let inter_closure = match compute_strata_closure_ideal(strata, param_vars) {
        Ok(c) => c,
        Err(reason) => return ctx.undetermined(vec![], reason),
    };
    let inter_disp = display_polys(&inter_closure, param_vars);
    match is_stratum_covered_by_union(&inter_closure, input_eval_invs, strata, param_vars) {
        Ok(true) => {
            return finalize_q_or_z_solution(
                task,
                eval_cond,
                &inter_closure,
                input_eval_invs,
                input_eval_invs,
                param_vars,
                has_source_laws,
                ctx,
                inter_disp,
            );
        }
        Ok(false) => {}
        Err(reason) => return ctx.undetermined(inter_disp, reason),
    }

    match ctx.point_domain {
        PointDomain::RationalPoints => {
            let mut first_undetermined: Option<SilenceReason> = None;
            for stratum in strata {
                let stratum_disp = display_polys(&stratum.equations, param_vars);
                let out = finalize_q_or_z_solution(
                    task,
                    eval_cond,
                    &stratum.equations,
                    &stratum.invertibles,
                    input_eval_invs,
                    param_vars,
                    has_source_laws,
                    ctx.clone(),
                    stratum_disp,
                );
                match out.verdict {
                    Verdict::Established => return out,
                    Verdict::Refuted => {}
                    Verdict::Undetermined(reason) => {
                        if first_undetermined.is_none() {
                            first_undetermined = Some(reason);
                        }
                    }
                }
            }
            if let Some(reason) = first_undetermined {
                ctx.undetermined(inter_disp, reason)
            } else {
                ctx.refuted(inter_disp, None)
            }
        }
        PointDomain::AlgebraicClosure
        | PointDomain::UniversalRing
        | PointDomain::IntegerPoints
        | PointDomain::FiniteFieldPoints(_) => {
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "solution space decomposes into multiple non-closed quotient strata that cannot be merged into a single residual ideal".to_owned(),
            };
            ctx.checks.push(ApplicabilityCheck::failed(
                "single_closed_or_single_stratum_locus",
                MathClause::G141D5,
                reason.code(),
            ));
            ctx.undetermined(inter_disp, reason)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn finalize_q_or_z_solution(
    task: &CheckedShigureTask,
    eval_cond: Option<&EvalCondition>,
    final_eqs: &[Poly<Rat>],
    final_invs: &[Poly<Rat>],
    input_eval_invs: &[Poly<Rat>],
    param_vars: &VarOrder,
    has_source_laws: bool,
    mut ctx: SolveCtx,
    residual_display: Vec<String>,
) -> ShigureOutcome {
    let prefer_z = ctx.coeff_domain == CoeffDomain::Z;
    let all_affine = final_eqs.iter().all(Poly::is_affine);

    // F2 対策: 商環計算により入力 eval_condition に含まれない暗黙の開条件が生じたか判定する。
    let has_implicit_open = if final_invs.is_empty() {
        false
    } else {
        let single = [QuotientStratum {
            equations: final_eqs.to_vec(),
            invertibles: final_invs.to_vec(),
        }];
        match is_stratum_covered_by_union(final_eqs, input_eval_invs, &single, param_vars) {
            Ok(covered) => !covered,
            Err(reason) => return ctx.undetermined(residual_display, reason),
        }
    };

    match ctx.point_domain.clone() {
        PointDomain::AlgebraicClosure => {
            if has_implicit_open {
                let reason = SilenceReason::QuotientIdealOutOfScope {
                    detail: "quotient preservation requires implicit open/invertible conditions not declared in eval_condition; declare D(g) explicitly or solve over a concrete point domain".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "no_unreported_open_condition",
                    MathClause::G141D5,
                    reason.code(),
                ));
                return ctx.undetermined(residual_display, reason);
            }
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
            if let Some(out) = guard_z_quotient_or_universal(has_source_laws, eval_cond, &ctx) {
                return out;
            }
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
                false,
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
            let (mat, rhs) = match polys_to_affine_system_q(final_eqs, param_vars.len()) {
                Ok(sys) => sys,
                Err(reason) => return ctx.undetermined(residual_display, reason),
            };
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
                    let mut witness_pt: Option<Vec<Rat>> = None;
                    if !final_invs.is_empty() {
                        match find_witness_point_q(
                            &particular,
                            &kernel_basis,
                            final_eqs,
                            final_invs,
                        ) {
                            Ok(Some(pt)) => {
                                ctx.checks.push(ApplicabilityCheck::passed(
                                    "rational_open_witness_verified",
                                    MathClause::G141D4,
                                ));
                                witness_pt = Some(pt);
                            }
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
                    // F2 対策: 暗黙の開条件がある場合は具体有理点を捨てず、具体点として復元・検算する。
                    if has_implicit_open && let Some(pt) = witness_pt {
                        return match restore_and_reeval_q_point(
                            task.pair(),
                            eval_cond,
                            param_vars,
                            &pt,
                        ) {
                            Ok(artifact) if artifact.reeval.matched => {
                                ctx.checks.push(ApplicabilityCheck::passed(
                                    "restored_model_reevaluation_matched",
                                    MathClause::G140E1E2,
                                ));
                                ctx.established(residual_display, Some(artifact), None)
                            }
                            Ok(artifact) => ctx.undetermined(
                                residual_display,
                                SilenceReason::ApplicabilityConditionNotMet {
                                    condition: "restored_model_reevaluation_matched".to_owned(),
                                    detail: artifact.reeval.detail,
                                },
                            ),
                            Err(reason) => ctx.undetermined(residual_display, reason),
                        };
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
    let require_strict_ideal = ctx.point_domain == PointDomain::UniversalRing;
    match restore_and_reeval_q(
        task.pair(),
        eval_cond,
        final_invs,
        param_vars,
        &extracted,
        require_strict_ideal,
    ) {
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
