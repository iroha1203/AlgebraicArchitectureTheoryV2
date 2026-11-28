//! 複数解釈族の存在型良否 $E_{\mathrm{exists}}$ における witness 復元と独立再評価検算。

use crate::algebra::{
    AffineSolutionQ, AffineSolutionZ, AlgebraError, ExprBindings, FpElem, GroebnerBasis,
    MonomialOrder, Poly, QuotientStratum, Rat, VarOrder, rabinowitsch_solve, solve_affine_q,
    solve_affine_z, solve_fp_enumeration,
};
use crate::ir::change::{EvalCondition, NamedPoly, PointDomain};
use crate::ir::family::PreservationGoodnessSource;
use crate::ir::result::{EmptyWitness, ReevalCheck, RestoredArtifact, SilenceReason, Verdict};
use crate::ir::result_phase3::{PairEvaluationWitness, RestoredCompletionWitness};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::common_solve::{
    ParamWitness, collect_eval_and_extra, solve_affine_or_nonlinear_z,
};
use crate::solver::context::display_polys;
use crate::solver::family_direct::substitute_preservation_pair;
use crate::solver::family_eval::{
    EnumCandidate, EnumRealization, ScalarVal, build_assignment_map, univariate_rational_roots,
};
use crate::solver::preservation::{
    build_preservation_obligations, compute_preservation_locus_q, extract_closed_residuals_fp,
    extract_closed_residuals_z, intersect_strata_lists, map_algebra_silence, substitute_poly_expr,
};
use crate::solver::restore::{
    extract_affine_substitution_q, find_witness_point_q, find_witness_point_z,
    polys_to_affine_system_q, polys_to_affine_system_z, restore_and_reeval_fp,
    restore_and_reeval_q, restore_and_reeval_q_point, restore_and_reeval_z,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;

fn pass_pair(
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    legal_execution_exists: Option<bool>,
    witness_assignments: BTreeMap<String, String>,
    restored_artifact: Option<RestoredArtifact>,
    reeval: ReevalCheck,
) -> PairEvaluationWitness {
    let passed = reeval.matched;
    PairEvaluationWitness {
        realization: realization.to_witness(),
        candidate_id: candidate.candidate_id.clone(),
        candidate_assignments: candidate.assignments.clone(),
        passed,
        legal_execution_exists,
        residuals: vec![],
        empty_witness: None,
        restored_completion: Some(RestoredCompletionWitness {
            witness_assignments,
            restored_artifact,
            reeval,
        }),
    }
}

fn fail_pair(
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    legal_execution_exists: Option<bool>,
    residuals: Vec<String>,
    empty_witness: Option<EmptyWitness>,
) -> PairEvaluationWitness {
    PairEvaluationWitness {
        realization: realization.to_witness(),
        candidate_id: candidate.candidate_id.clone(),
        candidate_assignments: candidate.assignments.clone(),
        passed: false,
        legal_execution_exists,
        residuals,
        empty_witness,
        restored_completion: None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn evaluate_existential_point(
    equations: &[NamedPoly],
    invertibles: &[NamedPoly],
    preservation: Option<&PreservationGoodnessSource>,
    w_names: &[String],
    uc_subst: &BTreeMap<String, PolyExpr>,
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<PairEvaluationWitness, SilenceReason> {
    let w_vars = VarOrder::new(w_names.to_vec()).map_err(map_algebra_silence)?;
    let w_bind = ExprBindings::params_only(&w_vars);
    let mut w_subst = uc_subst.clone();
    for w in w_names {
        w_subst.insert(w.clone(), PolyExpr::param(w));
    }

    let empty = BTreeMap::new();
    let sub_eqs: Vec<PolyExpr> = equations
        .iter()
        .map(|eq| substitute_poly_expr(&eq.expr, &empty, &empty, &w_subst))
        .collect();
    let sub_invs: Vec<PolyExpr> = invertibles
        .iter()
        .map(|iv| substitute_poly_expr(&iv.expr, &empty, &empty, &w_subst))
        .collect();

    if let Some(pres_src) = preservation {
        return solve_existential_with_preservation(
            pres_src,
            &sub_eqs,
            &sub_invs,
            &w_vars,
            &w_subst,
            realization,
            candidate,
            domain,
            point_domain,
        );
    }

    match domain {
        CoeffDomain::Fp(m) => {
            let eqs: Vec<Poly<FpElem>> = sub_eqs
                .iter()
                .map(|e| Poly::from_expr_fp(e, &w_bind, m))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            let invs: Vec<Poly<FpElem>> = sub_invs
                .iter()
                .map(|e| Poly::from_expr_fp(e, &w_bind, m))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            let sol = solve_fp_enumeration(
                &eqs,
                &invs,
                w_names.len(),
                m,
                crate::limits::active_limits().max_enum_points,
            )
            .map_err(|_| SilenceReason::FiniteEnumerationOutOfScope {
                detail: "existential witness search over Fp exceeded limit".to_owned(),
            })?;
            if let Some(pt) = sol.solutions.into_iter().next() {
                let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Fp).collect();
                return Ok(pass_pair(
                    realization,
                    candidate,
                    None,
                    build_assignment_map(w_names, &vals),
                    None,
                    ReevalCheck {
                        checked: true,
                        matched: true,
                        detail: format!("verified existential Fp({m}) witness"),
                    },
                ));
            }
            Ok(fail_pair(
                realization,
                candidate,
                None,
                display_polys(&eqs, &w_vars),
                None,
            ))
        }
        CoeffDomain::Q | CoeffDomain::Z => evaluate_existential_q_or_z(
            &sub_eqs,
            &sub_invs,
            w_names,
            &w_vars,
            &w_bind,
            realization,
            candidate,
            point_domain,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn evaluate_existential_q_or_z(
    sub_eqs: &[PolyExpr],
    sub_invs: &[PolyExpr],
    w_names: &[String],
    w_vars: &VarOrder,
    w_bind: &ExprBindings,
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    point_domain: &PointDomain,
) -> Result<PairEvaluationWitness, SilenceReason> {
    let eqs_q: Vec<Poly<Rat>> = sub_eqs
        .iter()
        .map(|e| Poly::from_expr_q(e, w_bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let invs_q: Vec<Poly<Rat>> = sub_invs
        .iter()
        .map(|e| Poly::from_expr_q(e, w_bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let rab = rabinowitsch_solve(&eqs_q, &invs_q, w_vars).map_err(map_algebra_silence)?;
    if rab.is_empty_over_closure {
        return Ok(fail_pair(
            realization,
            candidate,
            None,
            display_polys(&eqs_q, w_vars),
            rab.empty_witness,
        ));
    }

    if *point_domain == PointDomain::IntegerPoints {
        let eqs_z: Vec<Poly<BigInt>> = sub_eqs
            .iter()
            .map(|e| Poly::from_expr_z(e, w_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        let invs_z: Vec<Poly<BigInt>> = sub_invs
            .iter()
            .map(|e| Poly::from_expr_z(e, w_bind))
            .collect::<Result<_, _>>()
            .map_err(map_algebra_silence)?;
        if eqs_z.iter().all(Poly::is_affine)
            && let Ok((mat, rhs)) = polys_to_affine_system_z(&eqs_z, w_names.len())
        {
            match solve_affine_z(&mat, &rhs, w_names.len()) {
                Ok(AffineSolutionZ::Consistent {
                    particular,
                    kernel_basis,
                    verified: true,
                    ..
                }) => {
                    if let Some(pt) =
                        find_witness_point_z(&particular, &kernel_basis, &eqs_z, &invs_z)?
                    {
                        let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Z).collect();
                        return Ok(pass_pair(
                            realization,
                            candidate,
                            None,
                            build_assignment_map(w_names, &vals),
                            None,
                            ReevalCheck {
                                checked: true,
                                matched: true,
                                detail: "verified integer existential witness".to_owned(),
                            },
                        ));
                    }
                    if !kernel_basis.is_empty() && !invs_z.is_empty() {
                        return Err(SilenceReason::FiniteEnumerationOutOfScope {
                            detail: "affine Z witness search with invertible constraints exceeded finite search box".to_owned(),
                        });
                    }
                    return Ok(fail_pair(
                        realization,
                        candidate,
                        None,
                        display_polys(&eqs_z, w_vars),
                        None,
                    ));
                }
                Ok(AffineSolutionZ::Inconsistent { verified: true, .. }) => {
                    return Ok(fail_pair(
                        realization,
                        candidate,
                        None,
                        display_polys(&eqs_z, w_vars),
                        None,
                    ));
                }
                Err(e @ AlgebraError::ResourceLimitExceeded { .. }) => {
                    return Err(map_algebra_silence(e));
                }
                _ => {}
            }
        }
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::IntegerPoints,
            detail: "nonlinear integer existential witness outside Smith affine scope".to_owned(),
        });
    }

    if *point_domain == PointDomain::RationalPoints {
        if w_names.len() == 1 {
            let gb = GroebnerBasis::compute(
                &rab.parameter_equations,
                w_vars.clone(),
                MonomialOrder::Grevlex,
            )
            .map_err(map_algebra_silence)?;
            let gens = gb.basis_polys();
            if gens.is_empty() {
                if invs_q.iter().any(Poly::is_zero) {
                    return Ok(fail_pair(
                        realization,
                        candidate,
                        None,
                        display_polys(&eqs_q, w_vars),
                        None,
                    ));
                }
                let max_deg: usize = invs_q.iter().map(|iv| iv.total_degree() as usize).sum();
                for k in 0..=(max_deg + 1) {
                    let r = crate::algebra::Rat::from_int(BigInt::from(k));
                    if invs_q.iter().all(|iv| {
                        iv.eval_at(std::slice::from_ref(&r))
                            .is_ok_and(|v| !v.is_zero())
                    }) {
                        return Ok(pass_pair(
                            realization,
                            candidate,
                            None,
                            BTreeMap::from([(w_names[0].clone(), r.to_string())]),
                            None,
                            ReevalCheck {
                                checked: true,
                                matched: true,
                                detail: "verified rational existential witness on unconstrained 1D fiber".to_owned(),
                            },
                        ));
                    }
                }
                return Ok(fail_pair(
                    realization,
                    candidate,
                    None,
                    display_polys(&eqs_q, w_vars),
                    None,
                ));
            }
            if gens.len() == 1 && !gens[0].is_zero() {
                let (roots, _) = univariate_rational_roots(gens[0])?;
                if let Some(pt_r) = roots.into_iter().find(|r| {
                    invs_q.iter().all(|iv| {
                        iv.eval_at(std::slice::from_ref(r))
                            .is_ok_and(|v| !v.is_zero())
                    })
                }) {
                    return Ok(pass_pair(
                        realization,
                        candidate,
                        None,
                        BTreeMap::from([(w_names[0].clone(), pt_r.to_string())]),
                        None,
                        ReevalCheck {
                            checked: true,
                            matched: true,
                            detail: "verified rational existential witness".to_owned(),
                        },
                    ));
                }
                return Ok(fail_pair(
                    realization,
                    candidate,
                    None,
                    display_polys(&eqs_q, w_vars),
                    None,
                ));
            }
        }
        if invs_q.is_empty() && rab.parameter_equations.iter().all(Poly::is_affine) {
            let (mat, rhs) = polys_to_affine_system_q(&rab.parameter_equations, w_names.len())?;
            if let AffineSolutionQ::Consistent {
                particular,
                verified: true,
                ..
            } = solve_affine_q(&mat, &rhs, w_names.len()).map_err(map_algebra_silence)?
            {
                let vals: Vec<ScalarVal> = particular.into_iter().map(ScalarVal::Q).collect();
                return Ok(pass_pair(
                    realization,
                    candidate,
                    None,
                    build_assignment_map(w_names, &vals),
                    None,
                    ReevalCheck {
                        checked: true,
                        matched: true,
                        detail: "verified rational affine existential witness".to_owned(),
                    },
                ));
            }
        }
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: PointDomain::RationalPoints,
            detail: "nonlinear rational existential witness existence is outside affine/univariate scope".to_owned(),
        });
    }

    let mut witness_assignments = BTreeMap::new();
    if rab.parameter_equations.iter().all(Poly::is_affine)
        && let Ok((mat, rhs)) = polys_to_affine_system_q(&rab.parameter_equations, w_names.len())
    {
        match solve_affine_q(&mat, &rhs, w_names.len()) {
            Ok(AffineSolutionQ::Consistent {
                particular,
                kernel_basis,
                verified: true,
            }) => {
                if let Some(pt) = find_witness_point_q(&particular, &kernel_basis, &eqs_q, &invs_q)?
                {
                    let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Q).collect();
                    witness_assignments = build_assignment_map(w_names, &vals);
                }
            }
            Err(e @ AlgebraError::ResourceLimitExceeded { .. }) => {
                return Err(map_algebra_silence(e));
            }
            _ => {}
        }
    }
    if witness_assignments.is_empty() {
        let disp = display_polys(&rab.parameter_equations, w_vars);
        for w in w_names {
            witness_assignments.insert(w.clone(), format!("algebraic_root({})", disp.join(", ")));
        }
    }
    Ok(pass_pair(
        realization,
        candidate,
        None,
        witness_assignments,
        None,
        ReevalCheck {
            checked: true,
            matched: true,
            detail: "verified algebraic-closure existential witness satisfaction".to_owned(),
        },
    ))
}

#[allow(clippy::too_many_arguments)]
fn solve_existential_with_preservation(
    src: &PreservationGoodnessSource,
    sub_eqs: &[PolyExpr],
    sub_invs: &[PolyExpr],
    w_vars: &VarOrder,
    w_subst: &BTreeMap<String, PolyExpr>,
    realization: &EnumRealization,
    candidate: &EnumCandidate,
    domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<PairEvaluationWitness, SilenceReason> {
    let (pair, _) = substitute_preservation_pair(src, w_subst)?;
    let obligations = build_preservation_obligations(&pair)?;
    let dummy_eval = (!sub_eqs.is_empty() || !sub_invs.is_empty()).then(|| EvalCondition {
        name: "goodness_constraints".to_owned(),
        evaluations: vec![],
        equations: sub_eqs
            .iter()
            .enumerate()
            .map(|(i, e)| NamedPoly::new(format!("eq_{i}"), e.clone()))
            .collect(),
        invertibles: sub_invs
            .iter()
            .enumerate()
            .map(|(i, e)| NamedPoly::new(format!("inv_{i}"), e.clone()))
            .collect(),
        point_domain: point_domain.clone(),
        provenance: src.pair.before.provenance.clone(),
    });
    let cond_ref = dummy_eval.as_ref();

    match domain {
        CoeffDomain::Fp(m) => {
            let Some(mut eqs) = extract_closed_residuals_fp(&obligations, w_vars.vars(), m)? else {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail:
                        "quotient state-law preservation in Fp existential fiber is out of scope"
                            .to_owned(),
                });
            };
            let cond_slice: Vec<&_> = cond_ref.into_iter().collect();
            let (ceqs, cinvs) = collect_eval_and_extra(
                &[],
                &cond_slice,
                &ExprBindings::params_only(w_vars),
                |e, b| Poly::from_expr_fp(e, b, m),
            )?;
            eqs.extend(ceqs);
            let sol = solve_fp_enumeration(
                &eqs,
                &cinvs,
                w_vars.len(),
                m,
                crate::limits::active_limits().max_enum_points,
            )
            .map_err(|_| SilenceReason::FiniteEnumerationOutOfScope {
                detail: "Fp existential preservation witness search exceeded limit".to_owned(),
            })?;
            if let Some(pt) = sol.solutions.into_iter().next() {
                let art = restore_and_reeval_fp(&pair, cond_ref, w_vars, &pt, m)?;
                return Ok(pass_pair(
                    realization,
                    candidate,
                    Some(true),
                    art.parameter_assignments.clone(),
                    Some(art.clone()),
                    art.reeval,
                ));
            }
            Ok(fail_pair(
                realization,
                candidate,
                Some(false),
                display_polys(&eqs, w_vars),
                None,
            ))
        }
        CoeffDomain::Z if *point_domain == PointDomain::IntegerPoints => {
            let Some(mut all_eqs) = extract_closed_residuals_z(&obligations, w_vars.vars())? else {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail: "quotient state-law preservation over Z is out of scope".to_owned(),
                });
            };
            let cond_slice: Vec<&_> = cond_ref.into_iter().collect();
            let (ceqs, cinvs) = collect_eval_and_extra(
                &[],
                &cond_slice,
                &ExprBindings::params_only(w_vars),
                Poly::from_expr_z,
            )?;
            all_eqs.extend(ceqs);
            let sol = solve_affine_or_nonlinear_z(&all_eqs, &cinvs, w_vars, vec![]);
            if let Some(ParamWitness::ZPoint { point, .. }) = sol.witness {
                let art = restore_and_reeval_z(&pair, cond_ref, w_vars, &point)?;
                return Ok(pass_pair(
                    realization,
                    candidate,
                    Some(true),
                    art.parameter_assignments.clone(),
                    Some(art.clone()),
                    art.reeval,
                ));
            }
            if let Verdict::Undetermined(r) = sol.verdict {
                return Err(r);
            }
            Ok(fail_pair(
                realization,
                candidate,
                Some(false),
                sol.residual_display,
                sol.empty_witness,
            ))
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            if *domain == CoeffDomain::Z
                && *point_domain == PointDomain::RationalPoints
                && obligations.iter().any(|o| !o.source_laws.is_empty())
            {
                return Err(SilenceReason::QuotientIdealOutOfScope {
                    detail: "parametric quotient state-law preservation over Z with RationalPoints (possible Z-torsion) is out of scope; use Q or algebraic_closure".to_owned(),
                });
            }
            let locus = compute_preservation_locus_q(&obligations, w_vars)?;
            let cond_slice: Vec<&_> = cond_ref.into_iter().collect();
            let (ceqs, cinvs) = collect_eval_and_extra(
                &[],
                &cond_slice,
                &ExprBindings::params_only(w_vars),
                Poly::from_expr_q,
            )?;
            let mut all_failed_eqs = locus.closure_ideal.clone();
            all_failed_eqs.extend(ceqs.iter().cloned());
            let mut last_empty_witness: Option<EmptyWitness> = None;
            let combined = intersect_strata_lists(
                &locus.strata,
                &[QuotientStratum {
                    equations: ceqs,
                    invertibles: cinvs,
                }],
                w_vars,
            )?;
            let mut deferred_silence: Option<SilenceReason> = None;
            for st in combined {
                let rab = rabinowitsch_solve(&st.equations, &st.invertibles, w_vars)
                    .map_err(map_algebra_silence)?;
                if rab.is_empty_over_closure {
                    if last_empty_witness.is_none() {
                        last_empty_witness = rab.empty_witness;
                    }
                    continue;
                }
                let Some(extracted) =
                    extract_affine_substitution_q(&rab.parameter_equations, w_vars, false)?
                else {
                    if deferred_silence.is_none() {
                        deferred_silence = Some(match point_domain {
                            PointDomain::RationalPoints => {
                                SilenceReason::NonLinearRationalOrIntegerExistence {
                                    point_domain: PointDomain::RationalPoints,
                                    detail: "nonlinear existential preservation fiber without rational extraction".to_owned(),
                                }
                            }
                            _ => SilenceReason::ApplicabilityConditionNotMet {
                                condition: "existential_preservation_substitution".to_owned(),
                                detail: "non-empty existential preservation stratum could not extract witness substitution".to_owned(),
                            },
                        });
                    }
                    continue;
                };
                if *point_domain == PointDomain::RationalPoints
                    && !extracted.remaining_nonlinear.is_empty()
                {
                    return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                        point_domain: PointDomain::RationalPoints,
                        detail: "nonlinear rational existential preservation fiber".to_owned(),
                    });
                }
                let art = if *point_domain == PointDomain::RationalPoints {
                    let pt = match polys_to_affine_system_q(&rab.parameter_equations, w_vars.len())
                    {
                        Ok((mat, rhs)) => match solve_affine_q(&mat, &rhs, w_vars.len()) {
                            Ok(AffineSolutionQ::Consistent {
                                particular,
                                kernel_basis,
                                verified: true,
                            }) => find_witness_point_q(
                                &particular,
                                &kernel_basis,
                                &st.equations,
                                &st.invertibles,
                            )?,
                            Err(e @ AlgebraError::ResourceLimitExceeded { .. }) => {
                                return Err(map_algebra_silence(e));
                            }
                            _ => None,
                        },
                        Err(_) => None,
                    };
                    let Some(pt) = pt else {
                        if deferred_silence.is_none() {
                            deferred_silence = Some(
                                SilenceReason::NonLinearRationalOrIntegerExistence {
                                    point_domain: PointDomain::RationalPoints,
                                    detail: "rational existential preservation could not verify concrete Q witness satisfying open constraints".to_owned(),
                                },
                            );
                        }
                        continue;
                    };
                    restore_and_reeval_q_point(&pair, cond_ref, w_vars, &pt)?
                } else if extracted.remaining_nonlinear.is_empty()
                    && let Ok((mat, rhs)) =
                        polys_to_affine_system_q(&rab.parameter_equations, w_vars.len())
                {
                    let pt = match solve_affine_q(&mat, &rhs, w_vars.len()) {
                        Ok(AffineSolutionQ::Consistent {
                            particular,
                            kernel_basis,
                            verified: true,
                        }) => find_witness_point_q(
                            &particular,
                            &kernel_basis,
                            &st.equations,
                            &st.invertibles,
                        )?,
                        Err(e @ AlgebraError::ResourceLimitExceeded { .. }) => {
                            return Err(map_algebra_silence(e));
                        }
                        _ => None,
                    };
                    if let Some(pt) = pt {
                        restore_and_reeval_q_point(&pair, cond_ref, w_vars, &pt)?
                    } else {
                        restore_and_reeval_q(
                            &pair,
                            cond_ref,
                            &st.invertibles,
                            w_vars,
                            &extracted,
                            false,
                        )?
                    }
                } else {
                    restore_and_reeval_q(
                        &pair,
                        cond_ref,
                        &st.invertibles,
                        w_vars,
                        &extracted,
                        false,
                    )?
                };
                if !art.reeval.matched {
                    if deferred_silence.is_none() {
                        deferred_silence = Some(SilenceReason::ApplicabilityConditionNotMet {
                            condition: "existential_reevaluation_matched".to_owned(),
                            detail: art.reeval.detail.clone(),
                        });
                    }
                    continue;
                }
                return Ok(pass_pair(
                    realization,
                    candidate,
                    Some(true),
                    art.parameter_assignments.clone(),
                    Some(art.clone()),
                    art.reeval,
                ));
            }
            if let Some(reason) = deferred_silence {
                return Err(reason);
            }
            let residuals = display_polys(&all_failed_eqs, w_vars);
            let ew = last_empty_witness.or(locus.empty_witness).or_else(|| {
                rabinowitsch_solve(&all_failed_eqs, &[], w_vars)
                    .ok()
                    .and_then(|r| r.empty_witness)
            });
            Ok(fail_pair(
                realization,
                candidate,
                Some(false),
                residuals,
                ew,
            ))
        }
    }
}
