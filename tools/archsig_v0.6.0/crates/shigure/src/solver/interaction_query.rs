//! 座標面支持による相互作用参加変数数 r と極小不成立部分族の問い実行（G-141 F10–F12 / AC4）。

use crate::algebra::{
    ExprBindings, Poly, RingCoeff, VarOrder, analyze_coordinate_interaction,
    analyze_interaction_on_face,
};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::ir::validate::CheckedShigureTask;
use crate::solver::context::{SolveCtx, display_polys};
use crate::solver::preservation::{
    PreservationObligation, compute_preservation_locus_q, extract_closed_residuals_fp,
    extract_closed_residuals_z, map_algebra_silence, verify_scheme_membership_q,
};
use crate::solver::restore::{
    extract_coordinate_fix_fp, extract_coordinate_fix_q, extract_coordinate_fix_z,
};
use std::collections::BTreeMap;

pub(crate) fn execute_interaction_analysis(
    task: &CheckedShigureTask,
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
) -> ShigureOutcome {
    let param_bind = ExprBindings::params_only(param_vars);

    match ctx.coeff_domain.clone() {
        CoeffDomain::Fp(modulus) => {
            let residuals =
                match extract_closed_residuals_fp(obligations, param_vars.vars(), &modulus) {
                    Ok(Some(r)) => r,
                    Ok(None) => {
                        let detail =
                            "quotient state-law interaction analysis over F_p is out of scope"
                                .to_owned();
                        return ctx.undetermined(
                            vec![],
                            SilenceReason::QuotientIdealOutOfScope { detail },
                        );
                    }
                    Err(reason) => return ctx.undetermined(vec![], reason),
                };
            run_interaction_with_faces(
                task,
                &residuals,
                param_vars,
                ctx,
                |expr| Poly::from_expr_fp(expr, &param_bind, &modulus).map_err(map_algebra_silence),
                |p, eq_name| match extract_coordinate_fix_fp(p, param_vars) {
                    Some(pair) => Ok(pair),
                    None => Err(non_coord_silence(eq_name)),
                },
            )
        }
        CoeffDomain::Z => {
            // Z 上では Q 商環へフォールバックしない（Z-捩れを消さない、G-141 F11）。
            let residuals = match extract_closed_residuals_z(obligations, param_vars.vars()) {
                Ok(Some(r)) => r,
                Ok(None) => {
                    let detail = "quotient state-law interaction analysis over Z (with possible Z-torsion) is out of scope".to_owned();
                    ctx.checks.push(ApplicabilityCheck::failed(
                        "quotient_ideal_membership_in_scope",
                        MathClause::G141F10F12,
                        "quotient_ideal_out_of_scope",
                    ));
                    return ctx
                        .undetermined(vec![], SilenceReason::QuotientIdealOutOfScope { detail });
                }
                Err(reason) => return ctx.undetermined(vec![], reason),
            };
            run_interaction_with_faces(
                task,
                &residuals,
                param_vars,
                ctx,
                |expr| Poly::from_expr_z(expr, &param_bind).map_err(map_algebra_silence),
                |p, eq_name| match extract_coordinate_fix_z(p, param_vars) {
                    Some((name, Some(val))) => Ok((name, val)),
                    Some((name, None)) => Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "integer_coordinate_face_required".to_owned(),
                        detail: format!(
                            "equation `{eq_name}` fixes `{name}` to a non-integer coordinate over Z"
                        ),
                    }),
                    None => Err(non_coord_silence(eq_name)),
                },
            )
        }
        CoeffDomain::Q => {
            let locus = match compute_preservation_locus_q(obligations, param_vars) {
                Ok(l) => l,
                Err(reason) => return ctx.undetermined(vec![], reason),
            };
            let res_disp = display_polys(&locus.closure_ideal, param_vars);
            if !locus.is_zariski_closed {
                let reason = SilenceReason::OpenConditionInInteraction {
                    detail: "preservation locus has genuine open conditions and cannot be rounded to closed coordinate-plane interaction analysis (G-141 F10)".to_owned(),
                };
                ctx.checks.push(ApplicabilityCheck::failed(
                    "closed_condition_for_interaction",
                    MathClause::G141F10F12,
                    reason.code(),
                ));
                return ctx.undetermined(res_disp, reason);
            }
            // F1 対策: 状態 Law がある場合は冪零元を含む全可換 Q-代数上でのスキーム論的所属
            // `ob.target ∈ (ob.source_laws) + (closure_ideal)` を直接検算する（G-141 F11）。
            if obligations.iter().any(|o| !o.source_laws.is_empty()) {
                match verify_scheme_membership_q(obligations, &locus.closure_ideal, param_vars) {
                    Ok(true) => {
                        ctx.checks.push(ApplicabilityCheck::passed(
                            "scheme_theoretic_quotient_membership_verified",
                            MathClause::G141F10F12,
                        ));
                    }
                    Ok(false) => {
                        let reason = SilenceReason::QuotientIdealOutOfScope {
                            detail: "reduced Zariski closure does not imply scheme-theoretic preservation over arbitrary commutative Q-algebras (nilpotent discrepancy)".to_owned(),
                        };
                        ctx.checks.push(ApplicabilityCheck::failed(
                            "scheme_theoretic_quotient_membership_verified",
                            MathClause::G141F10F12,
                            reason.code(),
                        ));
                        return ctx.undetermined(res_disp, reason);
                    }
                    Err(reason) => return ctx.undetermined(res_disp, reason),
                }
            }

            run_interaction_with_faces(
                task,
                &locus.closure_ideal,
                param_vars,
                ctx,
                |expr| Poly::from_expr_q(expr, &param_bind).map_err(map_algebra_silence),
                |p, eq_name| match extract_coordinate_fix_q(p, param_vars) {
                    Some(pair) => Ok(pair),
                    None => Err(non_coord_silence(eq_name)),
                },
            )
        }
    }
}

fn non_coord_silence(eq_name: &str) -> SilenceReason {
    SilenceReason::ApplicabilityConditionNotMet {
        condition: "free_parameter_chart_required".to_owned(),
        detail: format!("equation `{eq_name}` restricts to a non-coordinate subvariety"),
    }
}

fn run_interaction_with_faces<C, Parse, Extract>(
    task: &CheckedShigureTask,
    residuals: &[Poly<C>],
    param_vars: &VarOrder,
    mut ctx: SolveCtx,
    parse_expr: Parse,
    extract_fix: Extract,
) -> ShigureOutcome
where
    C: RingCoeff,
    Parse: Fn(&PolyExpr) -> Result<Poly<C>, SilenceReason>,
    Extract: Fn(&Poly<C>, &str) -> Result<(String, C), SilenceReason>,
{
    let res_disp = display_polys(residuals, param_vars);
    let mut fixed_values: BTreeMap<String, C> = BTreeMap::new();
    if let Some(cond) = task.eval_condition() {
        for eq in &cond.equations {
            let p = match parse_expr(&eq.expr) {
                Ok(p) => p,
                Err(reason) => return ctx.undetermined(res_disp, reason),
            };
            if p.is_zero() {
                continue;
            }
            let (name, val) = match extract_fix(&p, &eq.name) {
                Ok(pair) => pair,
                Err(reason) => return ctx.undetermined(res_disp, reason),
            };
            if let Some(prev) = fixed_values.insert(name.clone(), val.clone())
                && prev != val
            {
                return ctx.undetermined(
                    res_disp,
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "consistent_coordinate_face_required".to_owned(),
                        detail: format!("conflicting fixed values for `{name}`"),
                    },
                );
            }
        }
    }

    let summary = if fixed_values.is_empty() {
        analyze_coordinate_interaction(residuals, param_vars)
    } else {
        analyze_interaction_on_face(residuals, param_vars, &fixed_values)
    };
    match summary {
        Ok(s) => {
            ctx.checks.push(ApplicabilityCheck::passed(
                "closed_condition_for_interaction",
                MathClause::G141F10F12,
            ));
            ctx.established(res_disp, None, Some(s))
        }
        Err(e) => ctx.undetermined(res_disp, map_algebra_silence(e)),
    }
}
