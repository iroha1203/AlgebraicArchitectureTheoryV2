//! Phase 2 Q／代数閉包・商環層別・具体点／アフィン代入ソルバ。

use crate::algebra::{
    AffineSolutionQ, DEFAULT_MAX_FP_POINTS, ExprBindings, GroebnerBasis, MonomialOrder, Poly,
    QuotientStratum, Rat, VarOrder, rabinowitsch_solve, solve_affine_q, solve_fp_enumeration,
};
use crate::ir::change::{EvalCondition, PointDomain};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, SilenceReason, Verdict};
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::common_solve::{
    ParamWitness, SystemSolveOutcome, collect_eval_and_extra, refuted_system,
    solve_affine_or_nonlinear_z, undetermined_system,
};
use crate::solver::context::{clear_denominators_to_z, display_polys};
use crate::solver::preservation::{
    PreservationObligation, compute_preservation_locus_q, compute_strata_closure_ideal,
    intersect_strata_lists, is_stratum_covered_by_union, map_algebra_silence,
};
use crate::solver::restore::{
    extract_affine_substitution_q, find_witness_point_q, polys_to_affine_system_q,
};

pub(crate) fn solve_q_system(
    obligations: &[PreservationObligation],
    extra_param_eqs: &[PolyExpr],
    eval_conds: &[&EvalCondition],
    point_domain: &PointDomain,
    param_vars: &VarOrder,
    prefer_z: bool,
    mut checks: Vec<ApplicabilityCheck>,
) -> SystemSolveOutcome {
    if matches!(point_domain, PointDomain::FiniteFieldPoints(_)) {
        return undetermined_system(
            checks,
            vec![],
            SilenceReason::ApplicabilityConditionNotMet {
                condition: "point_domain_matches_coeff_domain".to_owned(),
                detail: "Fp point domain requires Fp coefficient domain".to_owned(),
            },
        );
    }

    let has_source_laws = obligations.iter().any(|o| !o.source_laws.is_empty());
    if *point_domain == PointDomain::UniversalRing {
        if has_source_laws {
            let reason = SilenceReason::QuotientIdealOutOfScope {
                detail: "quotient ideal membership over arbitrary non-reduced commutative rings (UniversalRing) is out of scope; use algebraic_closure".to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "universal_ring_quotient_out_of_scope",
                MathClause::G141D5,
                reason.code(),
            ));
            return undetermined_system(checks, vec![], reason);
        }
        if eval_conds.iter().any(|c| !c.invertibles.is_empty()) {
            let reason = SilenceReason::ApplicabilityConditionNotMet {
                condition: "universal_ring_closed_equations_only".to_owned(),
                detail: "open/invertible conditions cannot be evaluated uniformly over all rings including the zero ring".to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "universal_ring_closed_equations_only",
                MathClause::G141D1,
                reason.code(),
            ));
            return undetermined_system(checks, vec![], reason);
        }
    }

    let locus = match compute_preservation_locus_q(obligations, param_vars) {
        Ok(l) => l,
        Err(reason) => return undetermined_system(checks, vec![], reason),
    };
    if locus.strata.is_empty() {
        let witness = locus
            .empty_witness
            .or_else(|| derive_obligation_empty_witness_q(obligations, param_vars));
        return refuted_system(
            checks,
            display_polys(&locus.closure_ideal, param_vars),
            witness,
        );
    }

    let param_bind = ExprBindings::params_only(param_vars);
    let (base_eqs, base_invs) =
        match collect_eval_and_extra(extra_param_eqs, eval_conds, &param_bind, Poly::from_expr_q) {
            Ok(pair) => pair,
            Err(r) => return undetermined_system(checks, vec![], r),
        };
    let base_strata = vec![QuotientStratum {
        equations: base_eqs.clone(),
        invertibles: base_invs.clone(),
    }];
    let combined = match intersect_strata_lists(&locus.strata, &base_strata, param_vars) {
        Ok(s) => s,
        Err(reason) => return undetermined_system(checks, vec![], reason),
    };

    let mut nonempty_strata = Vec::new();
    let mut first_witness = None;
    for st in combined {
        match rabinowitsch_solve(&st.equations, &st.invertibles, param_vars) {
            Ok(rab) => {
                if rab.is_empty_over_closure {
                    if first_witness.is_none() {
                        first_witness = rab.empty_witness;
                    }
                } else {
                    nonempty_strata.push(st);
                }
            }
            Err(e) => return undetermined_system(checks, vec![], map_algebra_silence(e)),
        }
    }

    if nonempty_strata.is_empty() {
        checks.push(ApplicabilityCheck::passed(
            "rabinowitsch_emptiness_verified",
            MathClause::G141D5,
        ));
        if first_witness.is_none() {
            if locus.strata.len() == 1 {
                let mut eqs = locus.strata[0].equations.clone();
                eqs.extend(base_eqs.iter().cloned());
                let mut invs = locus.strata[0].invertibles.clone();
                for iv in &base_invs {
                    if !invs.contains(iv) {
                        invs.push(iv.clone());
                    }
                }
                first_witness = compute_empty_witness_q(&eqs, &invs, param_vars);
            } else {
                let mut eqs = locus.closure_ideal.clone();
                eqs.extend(base_eqs.iter().cloned());
                first_witness = compute_empty_witness_q(&eqs, &base_invs, param_vars);
            }
        }
        let mut combined_disp = locus.closure_ideal.clone();
        combined_disp.extend(base_eqs);
        let disp =
            GroebnerBasis::compute(&combined_disp, param_vars.clone(), MonomialOrder::Grevlex)
                .map(|gb| {
                    let basis: Vec<Poly<Rat>> = gb.basis_polys().into_iter().cloned().collect();
                    display_polys(&basis, param_vars)
                })
                .unwrap_or_else(|_| display_polys(&combined_disp, param_vars));
        return refuted_system(checks, disp, first_witness);
    }

    let chosen_stratum = if nonempty_strata.len() == 1 {
        nonempty_strata.into_iter().next().expect("nonempty")
    } else {
        let inter_closure = match compute_strata_closure_ideal(&nonempty_strata, param_vars) {
            Ok(c) => c,
            Err(r) => return undetermined_system(checks, vec![], r),
        };
        let inter_disp = display_polys(&inter_closure, param_vars);
        match is_stratum_covered_by_union(&inter_closure, &base_invs, &nonempty_strata, param_vars)
        {
            Ok(true) => QuotientStratum {
                equations: inter_closure,
                invertibles: base_invs.clone(),
            },
            Ok(false) => {
                if matches!(
                    point_domain,
                    PointDomain::RationalPoints | PointDomain::IntegerPoints
                ) {
                    let mut first_undetermined = None;
                    for st in &nonempty_strata {
                        let st_disp = display_polys(&st.equations, param_vars);
                        let out = solve_single_stratum_q(
                            st,
                            &base_invs,
                            &st_disp,
                            &first_witness,
                            point_domain,
                            param_vars,
                            prefer_z,
                            checks.clone(),
                        );
                        match out.verdict {
                            Verdict::Established => return out,
                            Verdict::Refuted => {}
                            Verdict::Undetermined(r) => {
                                if first_undetermined.is_none() {
                                    first_undetermined = Some(r);
                                }
                            }
                        }
                    }
                    return if let Some(r) = first_undetermined {
                        undetermined_system(checks, inter_disp, r)
                    } else {
                        refuted_system(checks, inter_disp, None)
                    };
                }
                let reason = SilenceReason::QuotientIdealOutOfScope {
                    detail: "solution space decomposes into multiple non-closed quotient strata"
                        .to_owned(),
                };
                checks.push(ApplicabilityCheck::failed(
                    "single_closed_or_single_stratum_locus",
                    MathClause::G141D5,
                    reason.code(),
                ));
                return undetermined_system(checks, inter_disp, reason);
            }
            Err(r) => return undetermined_system(checks, inter_disp, r),
        }
    };

    let residual_display = display_polys(&chosen_stratum.equations, param_vars);
    solve_single_stratum_q(
        &chosen_stratum,
        &base_invs,
        &residual_display,
        &first_witness,
        point_domain,
        param_vars,
        prefer_z,
        checks,
    )
}

#[allow(clippy::too_many_arguments)]
fn solve_single_stratum_q(
    chosen: &QuotientStratum,
    input_eval_invs: &[Poly<Rat>],
    residual_display: &[String],
    first_witness: &Option<EmptyWitness>,
    point_domain: &PointDomain,
    param_vars: &VarOrder,
    prefer_z: bool,
    mut checks: Vec<ApplicabilityCheck>,
) -> SystemSolveOutcome {
    let residual_display = residual_display.to_vec();
    let all_affine = chosen.equations.iter().all(Poly::is_affine);

    let has_implicit_open = if chosen.invertibles.is_empty() {
        false
    } else {
        let single = [chosen.clone()];
        match is_stratum_covered_by_union(&chosen.equations, input_eval_invs, &single, param_vars) {
            Ok(covered) => !covered,
            Err(r) => return undetermined_system(checks, residual_display, r),
        }
    };

    match point_domain {
        PointDomain::UniversalRing => {
            if !chosen.invertibles.is_empty() {
                let reason = SilenceReason::ApplicabilityConditionNotMet {
                    condition: "universal_ring_closed_equations_only".to_owned(),
                    detail: "open/invertible conditions cannot be evaluated uniformly over all rings including the zero ring".to_owned(),
                };
                checks.push(ApplicabilityCheck::failed(
                    "universal_ring_closed_equations_only",
                    MathClause::G141D1,
                    reason.code(),
                ));
                return undetermined_system(checks, residual_display, reason);
            }
        }
        PointDomain::AlgebraicClosure => {
            if has_implicit_open {
                let reason = SilenceReason::QuotientIdealOutOfScope {
                    detail: "quotient preservation requires implicit open/invertible conditions not declared in eval_condition; declare D(g) explicitly or solve over a concrete point domain".to_owned(),
                };
                checks.push(ApplicabilityCheck::failed(
                    "no_unreported_open_condition",
                    MathClause::G141D5,
                    reason.code(),
                ));
                return undetermined_system(checks, residual_display, reason);
            }
            checks.push(ApplicabilityCheck::passed(
                "algebraic_closure_nonempty",
                MathClause::G141D5,
            ));
        }
        PointDomain::IntegerPoints => {
            if !all_affine {
                return undetermined_system(
                    checks,
                    residual_display,
                    SilenceReason::NonLinearRationalOrIntegerExistence {
                        point_domain: PointDomain::IntegerPoints,
                        detail: "general integer-point existence for nonlinear equations is out of scope".to_owned(),
                    },
                );
            }
            let eqs_z = clear_denominators_to_z(&chosen.equations);
            let invs_z = clear_denominators_to_z(&chosen.invertibles);
            return solve_affine_or_nonlinear_z(&eqs_z, &invs_z, param_vars, checks);
        }
        PointDomain::RationalPoints => {
            if !all_affine {
                return undetermined_system(
                    checks,
                    residual_display,
                    SilenceReason::NonLinearRationalOrIntegerExistence {
                        point_domain: PointDomain::RationalPoints,
                        detail: "nonlinear rational point existence is out of scope".to_owned(),
                    },
                );
            }
            let Ok((mat, rhs)) = polys_to_affine_system_q(&chosen.equations, param_vars.len())
            else {
                return undetermined_system(
                    checks,
                    residual_display,
                    SilenceReason::ApplicabilityConditionNotMet {
                        condition: "affine_system_expected".to_owned(),
                        detail: "failed to convert Q equations to matrix".to_owned(),
                    },
                );
            };
            match solve_affine_q(&mat, &rhs, param_vars.len()) {
                Ok(AffineSolutionQ::Consistent {
                    particular,
                    kernel_basis,
                    verified: true,
                }) => {
                    let pt = if chosen.invertibles.is_empty() {
                        particular
                    } else {
                        match find_witness_point_q(
                            &particular,
                            &kernel_basis,
                            &chosen.equations,
                            &chosen.invertibles,
                        ) {
                            Ok(Some(p)) => p,
                            Ok(None) => {
                                if kernel_basis.is_empty() {
                                    return refuted_system(
                                        checks,
                                        residual_display,
                                        compute_empty_witness_q(
                                            &chosen.equations,
                                            &chosen.invertibles,
                                            param_vars,
                                        ),
                                    );
                                }
                                return undetermined_system(
                                    checks,
                                    residual_display,
                                    SilenceReason::NonLinearRationalOrIntegerExistence {
                                        point_domain: PointDomain::RationalPoints,
                                        detail: "no rational witness point found".to_owned(),
                                    },
                                );
                            }
                            Err(r) => return undetermined_system(checks, residual_display, r),
                        }
                    };
                    let assignments = param_vars
                        .vars()
                        .iter()
                        .zip(&pt)
                        .map(|(n, v)| (n.clone(), v.to_string()))
                        .collect();
                    checks.push(ApplicabilityCheck::passed(
                        "rational_point_solution_verified",
                        MathClause::G141D4,
                    ));
                    return SystemSolveOutcome {
                        verdict: Verdict::Established,
                        checks,
                        residual_display,
                        empty_witness: None,
                        witness: Some(ParamWitness::QPoint {
                            point: pt,
                            assignments,
                        }),
                    };
                }
                Ok(AffineSolutionQ::Inconsistent { .. }) => {
                    return refuted_system(
                        checks,
                        residual_display,
                        compute_empty_witness_q(&chosen.equations, &chosen.invertibles, param_vars),
                    );
                }
                Ok(_) => {
                    return undetermined_system(
                        checks,
                        residual_display,
                        SilenceReason::ApplicabilityConditionNotMet {
                            condition: "affine_verification".to_owned(),
                            detail: "affine Q verification failed".to_owned(),
                        },
                    );
                }
                Err(e) => {
                    return undetermined_system(checks, residual_display, map_algebra_silence(e));
                }
            }
        }
        PointDomain::FiniteFieldPoints(_) => {
            return undetermined_system(
                checks,
                residual_display,
                SilenceReason::ApplicabilityConditionNotMet {
                    condition: "point_domain_matches_coeff_domain".to_owned(),
                    detail: "Fp point domain requires Fp coefficient domain".to_owned(),
                },
            );
        }
    }

    match extract_affine_substitution_q(&chosen.equations, param_vars, prefer_z) {
        Ok(Some(subst)) => {
            checks.push(ApplicabilityCheck::passed(
                "closure_stratum_nonempty_verified",
                MathClause::G141D5,
            ));
            SystemSolveOutcome {
                verdict: Verdict::Established,
                checks,
                residual_display,
                empty_witness: None,
                witness: Some(ParamWitness::QSubst { subst }),
            }
        }
        Ok(None) => refuted_system(checks, residual_display, first_witness.clone()),
        Err(reason) => undetermined_system(checks, residual_display, reason),
    }
}

fn derive_obligation_empty_witness_q(
    obligations: &[PreservationObligation],
    param_vars: &VarOrder,
) -> Option<EmptyWitness> {
    if !param_vars.is_empty() {
        return None;
    }
    for ob in obligations {
        let Ok((order, bind)) = ExprBindings::from_slices(&ob.state_vars, &ob.arg_vars, &[]) else {
            continue;
        };
        let Ok(t_poly) = Poly::from_expr_q(&ob.target, &bind) else {
            continue;
        };
        let mut src_polys = Vec::with_capacity(ob.source_laws.len());
        let mut ok = true;
        for l in &ob.source_laws {
            match Poly::from_expr_q(l, &bind) {
                Ok(p) if !p.is_zero() => src_polys.push(p),
                Ok(_) => {}
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        if !src_polys.is_empty()
            && let Ok(src_gb) =
                GroebnerBasis::compute(&src_polys, order.clone(), MonomialOrder::Grevlex)
            && src_gb.contains_one()
        {
            continue;
        }
        src_polys.push(t_poly);
        if let Ok(full_gb) = GroebnerBasis::compute(&src_polys, order, MonomialOrder::Grevlex)
            && let Ok(Some(ew)) = full_gb.empty_witness()
        {
            return Some(ew);
        }
    }
    None
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

/// 共通定義域・状態定義域イデアル `(laws)` が係数域・点域・評価開条件のもとで非空かを厳密判定する。
#[allow(clippy::too_many_arguments)]
pub(crate) fn is_ideal_nonempty(
    laws: &[PolyExpr],
    state_vars: &[String],
    arg_vars: &[String],
    free_vars: &VarOrder,
    witness: &ParamWitness,
    eval_conds: &[&EvalCondition],
    coeff_domain: &CoeffDomain,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    let (order, bind) = ExprBindings::from_slices(state_vars, arg_vars, free_vars.vars())
        .map_err(map_algebra_silence)?;
    let sa = state_vars.len() + arg_vars.len();
    let param_bind = ExprBindings::params_only(free_vars);
    match coeff_domain {
        CoeffDomain::Z if *point_domain == PointDomain::UniversalRing => {
            Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "universal_ring_solution_space_out_of_scope".to_owned(),
                detail: "UniversalRing non-emptiness over Z cannot be decided by Q-sections"
                    .to_owned(),
            })
        }
        CoeffDomain::Q | CoeffDomain::Z => {
            if matches!(point_domain, PointDomain::FiniteFieldPoints(_)) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "point_domain_matches_coeff_domain".to_owned(),
                    detail: "Fp point domain requires Fp coefficient domain".to_owned(),
                });
            }
            if *coeff_domain == CoeffDomain::Z && *point_domain == PointDomain::IntegerPoints {
                let mut eqs_z: Vec<Poly<num_bigint::BigInt>> = laws
                    .iter()
                    .map(|l| Poly::from_expr_z(l, &bind).map_err(map_algebra_silence))
                    .collect::<Result<Vec<_>, _>>()?;
                let (ev_eqs, ev_invs) =
                    collect_eval_and_extra(&[], eval_conds, &param_bind, Poly::from_expr_z)?;
                for eq in ev_eqs {
                    eqs_z.push(eq.lift_vars(sa));
                }
                let invs_z: Vec<Poly<num_bigint::BigInt>> =
                    ev_invs.into_iter().map(|iv| iv.lift_vars(sa)).collect();
                for nl in clear_denominators_to_z(witness.remaining_nonlinear()) {
                    eqs_z.push(nl.lift_vars(sa));
                }
                let eqs_nz: Vec<_> = eqs_z.into_iter().filter(|p| !p.is_zero()).collect();
                let res = solve_affine_or_nonlinear_z(&eqs_nz, &invs_z, &order, vec![]);
                return match res.verdict {
                    Verdict::Established => Ok(true),
                    Verdict::Refuted => Ok(false),
                    Verdict::Undetermined(r) => Err(r),
                };
            }
            let mut eqs_q: Vec<Poly<Rat>> = laws
                .iter()
                .map(|l| Poly::from_expr_q(l, &bind).map_err(map_algebra_silence))
                .collect::<Result<Vec<_>, _>>()?;
            for nl in witness.remaining_nonlinear() {
                eqs_q.push(nl.lift_vars(sa));
            }
            let (ev_eqs, ev_invs) =
                collect_eval_and_extra(&[], eval_conds, &param_bind, Poly::from_expr_q)?;
            for eq in ev_eqs {
                eqs_q.push(eq.lift_vars(sa));
            }
            let invs_q: Vec<Poly<Rat>> = ev_invs.into_iter().map(|iv| iv.lift_vars(sa)).collect();
            is_q_system_nonempty_on_point_domain(&eqs_q, &invs_q, &order, point_domain)
        }
        CoeffDomain::Fp(m) => {
            if *point_domain != PointDomain::FiniteFieldPoints(m.clone()) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "point_domain_matches_coeff_domain".to_owned(),
                    detail: format!("point domain `{point_domain}` cannot be decided over Fp({m})"),
                });
            }
            let mut eqs_fp: Vec<Poly<_>> = laws
                .iter()
                .map(|l| Poly::from_expr_fp(l, &bind, m).map_err(map_algebra_silence))
                .filter(|r| r.as_ref().map_or(true, |p| !p.is_zero()))
                .collect::<Result<Vec<_>, _>>()?;
            let (ev_eqs, ev_invs) =
                collect_eval_and_extra(&[], eval_conds, &param_bind, |e, b| {
                    Poly::from_expr_fp(e, b, m)
                })?;
            for eq in ev_eqs {
                if !eq.is_zero() {
                    eqs_fp.push(eq.lift_vars(sa));
                }
            }
            let invs_fp: Vec<Poly<_>> = ev_invs.into_iter().map(|iv| iv.lift_vars(sa)).collect();
            let res =
                solve_fp_enumeration(&eqs_fp, &invs_fp, order.len(), m, DEFAULT_MAX_FP_POINTS)?;
            Ok(!res.solutions.is_empty())
        }
    }
}

fn is_q_system_nonempty_on_point_domain(
    eqs_q: &[Poly<Rat>],
    invs_q: &[Poly<Rat>],
    order: &VarOrder,
    point_domain: &PointDomain,
) -> Result<bool, SilenceReason> {
    if *point_domain == PointDomain::UniversalRing && !invs_q.is_empty() {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "universal_ring_closed_equations_only".to_owned(),
            detail: "open/invertible conditions cannot be evaluated uniformly over all rings including the zero ring".to_owned(),
        });
    }
    let rab = rabinowitsch_solve(eqs_q, invs_q, order).map_err(map_algebra_silence)?;
    if rab.is_empty_over_closure {
        return Ok(false);
    }
    match point_domain {
        PointDomain::UniversalRing | PointDomain::AlgebraicClosure => Ok(true),
        PointDomain::RationalPoints => {
            if !rab.parameter_equations.iter().all(Poly::is_affine) {
                return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::RationalPoints,
                    detail: "nonlinear rational point existence is out of scope".to_owned(),
                });
            }
            let (mat, rhs) = polys_to_affine_system_q(&rab.parameter_equations, order.len())?;
            match solve_affine_q(&mat, &rhs, order.len()).map_err(map_algebra_silence)? {
                AffineSolutionQ::Consistent {
                    particular,
                    kernel_basis,
                    verified: true,
                } => {
                    if invs_q.is_empty() {
                        return Ok(true);
                    }
                    match find_witness_point_q(
                        &particular,
                        &kernel_basis,
                        &rab.parameter_equations,
                        invs_q,
                    )? {
                        Some(_) => Ok(true),
                        None if kernel_basis.is_empty() => Ok(false),
                        None => Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                            point_domain: PointDomain::RationalPoints,
                            detail: "no rational witness point found".to_owned(),
                        }),
                    }
                }
                AffineSolutionQ::Inconsistent { .. } => Ok(false),
                _ => Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "affine_verification".to_owned(),
                    detail: "affine Q verification failed".to_owned(),
                }),
            }
        }
        PointDomain::IntegerPoints => {
            if !rab.parameter_equations.iter().all(Poly::is_affine) {
                return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::IntegerPoints,
                    detail:
                        "general integer-point existence for nonlinear equations is out of scope"
                            .to_owned(),
                });
            }
            let eqs_z = clear_denominators_to_z(&rab.parameter_equations);
            let invs_z = clear_denominators_to_z(invs_q);
            let res = solve_affine_or_nonlinear_z(&eqs_z, &invs_z, order, vec![]);
            match res.verdict {
                Verdict::Established => Ok(true),
                Verdict::Refuted => Ok(false),
                Verdict::Undetermined(r) => Err(r),
            }
        }
        PointDomain::FiniteFieldPoints(_) => Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "point_domain_matches_coeff_domain".to_owned(),
            detail: "Fp point domain requires Fp coefficient domain".to_owned(),
        }),
    }
}
