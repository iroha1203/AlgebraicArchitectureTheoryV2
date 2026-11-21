//! 座標面支持による相互作用参加変数数 r と極小不成立部分族の問い実行（G-141 F10–F12 / AC4）。

use crate::algebra::{
    ExprBindings, FpElem, Poly, Rat, VarOrder, analyze_coordinate_interaction,
    analyze_interaction_on_face,
};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason};
use crate::ir::term::CoeffDomain;
use crate::ir::validate::CheckedShigureTask;
use crate::solver::preservation::{
    PreservationObligation, compute_preservation_locus_q, extract_closed_residuals_fp,
    map_algebra_silence,
};
use crate::solver::restore::{extract_coordinate_fix_fp, extract_coordinate_fix_q};
use crate::solver::solve::{SolveCtx, display_polys};
use num_traits::One;
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
            let res_disp = display_polys(&residuals, param_vars);
            let mut fixed_values: BTreeMap<String, FpElem> = BTreeMap::new();
            if let Some(cond) = task.eval_condition() {
                for eq in &cond.equations {
                    let p = match Poly::from_expr_fp(&eq.expr, &param_bind, &modulus) {
                        Ok(p) => p,
                        Err(e) => return ctx.undetermined(res_disp, map_algebra_silence(e)),
                    };
                    if p.is_zero() {
                        continue;
                    }
                    let Some((name, val)) = extract_coordinate_fix_fp(&p, param_vars) else {
                        return ctx.undetermined(
                            res_disp,
                            SilenceReason::ApplicabilityConditionNotMet {
                                condition: "free_parameter_chart_required".to_owned(),
                                detail: format!(
                                    "equation `{}` restricts to a non-coordinate subvariety",
                                    eq.name
                                ),
                            },
                        );
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
                analyze_coordinate_interaction(&residuals, param_vars)
            } else {
                analyze_interaction_on_face(&residuals, param_vars, &fixed_values)
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
        CoeffDomain::Q | CoeffDomain::Z => {
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
            ctx.checks.push(ApplicabilityCheck::passed(
                "closed_condition_for_interaction",
                MathClause::G141F10F12,
            ));

            let mut fixed_values: BTreeMap<String, Rat> = BTreeMap::new();
            if let Some(cond) = task.eval_condition() {
                for eq in &cond.equations {
                    let p = match Poly::from_expr_q(&eq.expr, &param_bind) {
                        Ok(p) => p,
                        Err(e) => return ctx.undetermined(res_disp, map_algebra_silence(e)),
                    };
                    if p.is_zero() {
                        continue;
                    }
                    let Some((name, val)) = extract_coordinate_fix_q(&p, param_vars) else {
                        return ctx.undetermined(
                            res_disp,
                            SilenceReason::ApplicabilityConditionNotMet {
                                condition: "free_parameter_chart_required".to_owned(),
                                detail: format!(
                                    "equation `{}` restricts to a non-coordinate subvariety",
                                    eq.name
                                ),
                            },
                        );
                    };
                    if ctx.coeff_domain == CoeffDomain::Z && !val.den().is_one() {
                        return ctx.undetermined(
                            res_disp,
                            SilenceReason::ApplicabilityConditionNotMet {
                                condition: "integer_coordinate_face_required".to_owned(),
                                detail: format!(
                                    "equation `{}` fixes `{name}` to non-integer `{val}` over Z",
                                    eq.name
                                ),
                            },
                        );
                    }
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
                analyze_coordinate_interaction(&locus.closure_ideal, param_vars)
            } else {
                analyze_interaction_on_face(&locus.closure_ideal, param_vars, &fixed_values)
            };
            match summary {
                Ok(s) => ctx.established(res_disp, None, Some(s)),
                Err(e) => ctx.undetermined(res_disp, map_algebra_silence(e)),
            }
        }
    }
}
