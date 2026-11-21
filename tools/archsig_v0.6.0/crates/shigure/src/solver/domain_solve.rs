//! Z アフィン（Smith 標準形）および F_p 有限全列挙のドメイン特化ソルバ（G-141 D4）。

use crate::algebra::{
    AffineSolutionZ, DEFAULT_MAX_FP_POINTS, ExprBindings, Poly, Rat, VarOrder, rabinowitsch_solve,
    solve_affine_z, solve_fp_enumeration,
};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason};
use crate::ir::validate::CheckedShigureTask;
use crate::solver::preservation::{
    PreservationObligation, extract_closed_residuals_fp, map_algebra_silence,
};
use crate::solver::restore::{
    find_witness_point_z, polys_to_affine_system_z, restore_and_reeval_fp, restore_and_reeval_z,
};
use crate::solver::solve::{SolveCtx, display_polys};
use num_bigint::{BigInt, BigUint};

pub(crate) fn solve_affine_direct_z(
    task: &CheckedShigureTask,
    eval_cond: Option<&EvalCondition>,
    eqs_z: &[Poly<BigInt>],
    invs_z: &[Poly<BigInt>],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let residual_display = display_polys(eqs_z, param_vars);
    let (mat, rhs) = polys_to_affine_system_z(eqs_z, param_vars.len());
    match solve_affine_z(&mat, &rhs, param_vars.len()) {
        Ok(AffineSolutionZ::Inconsistent { verified: true, .. }) => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "smith_normal_form_inconsistency_verified",
                MathClause::G141D4,
            ));
            ctx.refuted(residual_display, None)
        }
        Ok(AffineSolutionZ::Consistent {
            particular,
            kernel_basis,
            verified: true,
            ..
        }) => {
            let chosen = if invs_z.is_empty() {
                Some(particular)
            } else {
                match find_witness_point_z(&particular, &kernel_basis, eqs_z, invs_z) {
                    Ok(pt) => pt,
                    Err(reason) => return ctx.undetermined(residual_display, reason),
                }
            };
            let Some(pt) = chosen else {
                // 自由変数 0（唯一解が不成立）または代数閉包上で空（1 in I）なら確実に Refuted。
                let eqs_q: Vec<Poly<Rat>> = eqs_z.iter().map(lift_z_poly_to_q).collect();
                let invs_q: Vec<Poly<Rat>> = invs_z.iter().map(lift_z_poly_to_q).collect();
                if let Ok(rab) = rabinowitsch_solve(&eqs_q, &invs_q, param_vars)
                    && rab.is_empty_over_closure
                {
                    ctx.checks.push(ApplicabilityCheck::passed(
                        "rabinowitsch_emptiness_verified",
                        MathClause::G141D5,
                    ));
                    return ctx.refuted(residual_display, rab.empty_witness);
                }
                if kernel_basis.is_empty() {
                    ctx.checks.push(ApplicabilityCheck::passed(
                        "unique_integer_point_violates_open_condition",
                        MathClause::G141D4,
                    ));
                    return ctx.refuted(residual_display, None);
                }
                let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::IntegerPoints,
                    detail: "no concrete integer point satisfying open conditions was verified within deterministic witness search".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "integer_open_witness_verified",
                    MathClause::G141D4,
                    reason.code(),
                ));
                return ctx.undetermined(residual_display, reason);
            };
            match restore_and_reeval_z(task.pair(), eval_cond, param_vars, &pt) {
                Ok(artifact) if artifact.reeval.matched => {
                    ctx.checks.push(ApplicabilityCheck::passed(
                        "smith_normal_form_solution_verified",
                        MathClause::G141D4,
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
            }
        }
        Ok(_) => ctx.undetermined(
            residual_display,
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "smith_normal_form_verification".to_owned(),
                detail: "Smith normal form result failed independent verification".to_owned(),
            },
        ),
        Err(e) => ctx.undetermined(residual_display, map_algebra_silence(e)),
    }
}

fn lift_z_poly_to_q(poly: &Poly<BigInt>) -> Poly<Rat> {
    let mut out = Poly::zero(poly.num_vars(), Rat::zero());
    for (mono, coeff) in poly.terms() {
        out.add_term(mono.clone(), Rat::from_int(coeff.clone()));
    }
    out
}

pub(crate) fn solve_over_fp(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    eval_cond: Option<&EvalCondition>,
    param_vars: &VarOrder,
    modulus: &BigUint,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let residuals = match extract_closed_residuals_fp(obligations, param_vars.vars(), modulus) {
        Ok(Some(r)) => r,
        Ok(None) => {
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "parametric quotient state-law stratification over F_p is out of scope"
                    .to_owned(),
            };
            ctx.checks.push(ApplicabilityCheck::failed(
                "fp_quotient_out_of_scope",
                MathClause::G141D4,
                reason.code(),
            ));
            return ctx.undetermined(vec![], reason);
        }
        Err(reason) => return ctx.undetermined(vec![], reason),
    };

    let param_bind = ExprBindings::params_only(param_vars);
    let mut all_eqs = residuals.clone();
    let mut invs = Vec::new();
    if let Some(cond) = eval_cond {
        for eq in &cond.equations {
            match Poly::from_expr_fp(&eq.expr, &param_bind, modulus) {
                Ok(p) => {
                    if !p.is_zero() {
                        all_eqs.push(p);
                    }
                }
                Err(e) => {
                    return ctx.undetermined(
                        display_polys(&residuals, param_vars),
                        map_algebra_silence(e),
                    );
                }
            }
        }
        for inv in &cond.invertibles {
            match Poly::from_expr_fp(&inv.expr, &param_bind, modulus) {
                Ok(p) => invs.push(p),
                Err(e) => {
                    return ctx.undetermined(
                        display_polys(&residuals, param_vars),
                        map_algebra_silence(e),
                    );
                }
            }
        }
    }

    let residual_display = display_polys(&all_eqs, param_vars);
    match solve_fp_enumeration(
        &all_eqs,
        &invs,
        param_vars.len(),
        modulus,
        DEFAULT_MAX_FP_POINTS,
    ) {
        Ok(fp_res) => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "fp_finite_enumeration_complete",
                MathClause::G141D4,
            ));
            if let Some(first) = fp_res.solutions.first() {
                match restore_and_reeval_fp(task.pair(), eval_cond, param_vars, first, modulus) {
                    Ok(artifact) if artifact.reeval.matched => {
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
                }
            } else {
                ctx.refuted(residual_display, None)
            }
        }
        Err(reason) => ctx.undetermined(residual_display, reason),
    }
}
