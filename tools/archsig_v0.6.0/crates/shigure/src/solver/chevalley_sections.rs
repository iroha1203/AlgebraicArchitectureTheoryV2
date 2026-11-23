//! Mixed witness pair extraction, rational fiber probes (W5),
//! and Laurent Newton-polygon global regular section obstruction checks.

use crate::algebra::{
    AffineSolutionQ, ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder,
    rabinowitsch_solve, solve_affine_q,
};
use crate::ir::change::PointDomain;
use crate::ir::family::{CheckedFamilySpec, GoodnessSpec, RealizationSpace};
use crate::ir::provenance::{OriginKind, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_phase3::{
    GlobalRegularSectionResult, MixedWitnessPair, PairEvaluationWitness, RationalFiberProbeResult,
    RealizationWitness,
};
use crate::ir::robustness::RationalFiberProbe;
use crate::ir::term::{CoeffDomain, PolyExpr};
use crate::solver::chevalley::{FamilyConstructibleSets, default_candidate_origin, slice_set_at_c};
use crate::solver::context::display_polys;
use crate::solver::family_direct::evaluate_goodness_at_point;
use crate::solver::family_eval::{
    EnumCandidate, EnumRealization, ScalarVal, build_assignment_map, univariate_rational_roots,
};
use crate::solver::preservation::{map_algebra_silence, substitute_poly_expr};
use crate::solver::restore::{find_witness_point_q, polys_to_affine_system_q};
use num_integer::Integer;
use num_traits::One;
use std::collections::BTreeMap;

pub(crate) fn pick_rational_point_in_stratum(
    st: &crate::algebra::LocallyClosedStratum,
    vars: &VarOrder,
) -> Result<Option<Vec<Rat>>, SilenceReason> {
    let rab =
        rabinowitsch_solve(&st.equations, &st.invertibles, vars).map_err(map_algebra_silence)?;
    if rab.is_empty_over_closure {
        return Ok(None);
    }
    let n = vars.len();
    if n == 0 {
        return Ok(Some(vec![]));
    }
    if rab.parameter_equations.iter().all(Poly::is_affine) {
        let (mat, rhs) = polys_to_affine_system_q(&rab.parameter_equations, n)?;
        if let AffineSolutionQ::Consistent {
            particular,
            kernel_basis,
            verified: true,
        } = solve_affine_q(&mat, &rhs, n).map_err(map_algebra_silence)?
            && let Some(pt) =
                find_witness_point_q(&particular, &kernel_basis, &st.equations, &st.invertibles)?
        {
            return Ok(Some(pt));
        }
    }
    for cand in [1i64, -1, 2, -2, 0, 3, -3] {
        let pt = vec![Rat::from_int(cand); n];
        let eq_ok = st
            .equations
            .iter()
            .all(|e| e.eval_at(&pt).is_ok_and(|v| v.is_zero()));
        let inv_ok = st
            .invertibles
            .iter()
            .all(|iv| iv.eval_at(&pt).is_ok_and(|v| !v.is_zero()));
        if eq_ok && inv_ok {
            return Ok(Some(pt));
        }
    }
    if n == 1 {
        let gb = GroebnerBasis::compute(
            &rab.parameter_equations,
            vars.clone(),
            MonomialOrder::Grevlex,
        )
        .map_err(map_algebra_silence)?;
        let gens = gb.basis_polys();
        if gens.len() == 1 && !gens[0].is_zero() {
            let (roots, _) = univariate_rational_roots(gens[0])?;
            for r in roots {
                let pt = vec![r];
                if st
                    .invertibles
                    .iter()
                    .all(|iv| iv.eval_at(&pt).is_ok_and(|v| !v.is_zero()))
                {
                    return Ok(Some(pt));
                }
            }
        }
    }
    Ok(None)
}

pub(super) fn build_mixed_witness_pair(
    family: &CheckedFamilySpec,
    sets: &FamilyConstructibleSets,
    chosen_cand: Option<&EnumCandidate>,
) -> Result<Option<MixedWitnessPair>, SilenceReason> {
    if sets.mixed.is_empty() {
        return Ok(None);
    }
    let chosen_in_mixed = if let Some(c) = chosen_cand {
        let pt: Vec<Rat> = c.values.iter().map(ScalarVal::as_rat).collect();
        sets.mixed.contains_point(&pt)?.then(|| c.clone())
    } else {
        None
    };
    let cand = if let Some(c) = chosen_in_mixed {
        c
    } else if let Some(first_st) = sets.mixed.strata().first()
        && let Some(pt) = pick_rational_point_in_stratum(first_st, &sets.c_vars)?
    {
        let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Q).collect();
        EnumCandidate {
            candidate_id: None,
            assignments: build_assignment_map(family.c_vars(), &vals),
            values: vals,
            origin: default_candidate_origin(
                &family.inner().candidates.space,
                &family.inner().provenance,
            ),
        }
    } else {
        return Ok(None);
    };

    let u_pass_set = slice_set_at_c(&sets.w_pass, &sets.c_vars, &cand, &sets.u_vars)?;
    let u_fail_set = slice_set_at_c(&sets.w_fail, &sets.c_vars, &cand, &sets.u_vars)?;
    let pass_witness = build_u_witness_from_slice(family, &sets.u_vars, &u_pass_set, &cand, true)?;
    let fail_witness = build_u_witness_from_slice(family, &sets.u_vars, &u_fail_set, &cand, false)?;
    let (Some(pw), Some(fw)) = (pass_witness, fail_witness) else {
        return Ok(None);
    };
    Ok(Some(MixedWitnessPair {
        candidate_id: cand.candidate_id,
        candidate_assignments: cand.assignments,
        pass_witness: pw,
        fail_witness: fw,
    }))
}

fn build_u_witness_from_slice(
    family: &CheckedFamilySpec,
    u_vars: &VarOrder,
    slice: &crate::algebra::ConstructibleSet,
    cand: &EnumCandidate,
    expected_pass: bool,
) -> Result<Option<PairEvaluationWitness>, SilenceReason> {
    let Some(st) = slice.strata().first() else {
        return Ok(None);
    };
    let domain = family.coeff_domain();
    let origin = match &family.inner().realizations.space {
        RealizationSpace::FiniteMembers(ms) => ms
            .first()
            .map(|m| m.origin.clone())
            .unwrap_or_else(|| SourceRef::new("realization", OriginKind::StaticAnalysis)),
        RealizationSpace::PolynomialScheme { origin, .. } => origin.clone(),
    };
    if let Some(pt_q) = pick_rational_point_in_stratum(st, u_vars)? {
        let vals: Vec<ScalarVal> = pt_q
            .into_iter()
            .map(|r| match domain {
                CoeffDomain::Z if r.den().is_one() => ScalarVal::Z(r.num().clone()),
                _ => ScalarVal::Q(r),
            })
            .collect();
        let enum_u = EnumRealization {
            member_id: None,
            assignments: build_assignment_map(u_vars.vars(), &vals),
            values: vals,
            is_raw_candidate: false,
            origin: origin.clone(),
            presentation: None,
        };
        if let Ok(w) =
            evaluate_goodness_at_point(family, &enum_u, cand, &PointDomain::AlgebraicClosure)
            && w.passed == expected_pass
        {
            return Ok(Some(w));
        }
    }
    let eq_disp = display_polys(&st.equations, u_vars);
    let mut assign = BTreeMap::new();
    for u in u_vars.vars() {
        assign.insert(
            u.clone(),
            format!("geom_point({u}; {} = 0)", eq_disp.join(", ")),
        );
    }
    Ok(Some(PairEvaluationWitness {
        realization: RealizationWitness {
            member_id: None,
            assignments: assign,
            is_raw_candidate: false,
            origin,
        },
        candidate_id: cand.candidate_id.clone(),
        candidate_assignments: cand.assignments.clone(),
        passed: expected_pass,
        legal_execution_exists: None,
        residuals: if expected_pass { vec![] } else { eq_disp },
        empty_witness: None,
        restored_completion: None,
    }))
}

pub(super) fn resolve_universal_candidate(
    family: &CheckedFamilySpec,
    sets: &FamilyConstructibleSets,
    chosen: Option<&EnumCandidate>,
) -> Result<Option<EnumCandidate>, SilenceReason> {
    if let Some(c) = chosen {
        return Ok(Some(c.clone()));
    }
    if family.c_vars().is_empty() {
        return Ok(Some(EnumCandidate {
            candidate_id: None,
            values: vec![],
            assignments: BTreeMap::new(),
            origin: default_candidate_origin(
                &family.inner().candidates.space,
                &family.inner().provenance,
            ),
        }));
    }
    if let Some(st) = sets.c_space.strata().first()
        && let Some(pt) = pick_rational_point_in_stratum(st, &sets.c_vars)?
    {
        let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Q).collect();
        return Ok(Some(EnumCandidate {
            candidate_id: None,
            assignments: build_assignment_map(family.c_vars(), &vals),
            values: vals,
            origin: default_candidate_origin(
                &family.inner().candidates.space,
                &family.inner().provenance,
            ),
        }));
    }
    Ok(None)
}

pub(super) fn run_rational_fiber_probes(
    family: &CheckedFamilySpec,
    probes: &[RationalFiberProbe],
) -> Result<Vec<RationalFiberProbeResult>, SilenceReason> {
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let c_names = family.c_vars();
    let w_names = family.witness_vars();
    let empty = BTreeMap::new();
    let mut results = Vec::with_capacity(probes.len());

    for probe in probes {
        let mut fixed_subst = BTreeMap::new();
        let mut u_disp = BTreeMap::new();
        let mut c_disp = BTreeMap::new();
        for (k, lit) in &probe.u_assignments {
            let sv = ScalarVal::from_lit(lit, domain)?;
            u_disp.insert(k.clone(), sv.to_display());
            fixed_subst.insert(k.clone(), sv.to_expr());
        }
        for (k, lit) in &probe.c_assignments {
            let sv = ScalarVal::from_lit(lit, domain)?;
            c_disp.insert(k.clone(), sv.to_display());
            fixed_subst.insert(k.clone(), sv.to_expr());
        }

        let mut rem_vars: Vec<String> = Vec::new();
        for v in u_names.iter().chain(c_names).chain(w_names) {
            if !fixed_subst.contains_key(v) {
                rem_vars.push(v.clone());
            }
        }
        for v in &rem_vars {
            fixed_subst.insert(v.clone(), PolyExpr::param(v));
        }

        let rem_order = VarOrder::new(rem_vars.clone()).map_err(map_algebra_silence)?;
        let rem_bind = ExprBindings::params_only(&rem_order);
        let (good_eqs, good_invs) = match &family.inner().goodness {
            GoodnessSpec::Direct {
                equations,
                invertibles,
                ..
            }
            | GoodnessSpec::Existential {
                equations,
                invertibles,
                ..
            } => (equations, invertibles),
        };
        let mut eqs: Vec<Poly<Rat>> = Vec::new();
        let mut invs: Vec<Poly<Rat>> = Vec::new();
        for eq in good_eqs {
            let sub = substitute_poly_expr(&eq.expr, &empty, &empty, &fixed_subst);
            let p = Poly::from_expr_q(&sub, &rem_bind).map_err(map_algebra_silence)?;
            if !p.is_zero() {
                eqs.push(p);
            }
        }
        for inv in good_invs {
            let sub = substitute_poly_expr(&inv.expr, &empty, &empty, &fixed_subst);
            invs.push(Poly::from_expr_q(&sub, &rem_bind).map_err(map_algebra_silence)?);
        }

        let (verdict, rational_witness, detail) = if rem_vars.is_empty() {
            let eq_ok = eqs.iter().all(|p| p.constant_value().is_zero());
            let inv_ok = invs.iter().all(|p| !p.constant_value().is_zero());
            if eq_ok && inv_ok {
                (
                    Verdict::Established,
                    Some(BTreeMap::new()),
                    "probe equations and invertibles satisfied".to_owned(),
                )
            } else {
                (
                    Verdict::Refuted,
                    None,
                    "probe equations or invertibles failed over Q".to_owned(),
                )
            }
        } else if rem_vars.len() == 1 {
            let gb = GroebnerBasis::compute(&eqs, rem_order.clone(), MonomialOrder::Grevlex)
                .map_err(map_algebra_silence)?;
            if gb.contains_one() {
                (
                    Verdict::Refuted,
                    None,
                    "probe ideal contains 1; no Q points exist".to_owned(),
                )
            } else {
                let gens = gb.basis_polys();
                if gens.len() == 1 && !gens[0].is_zero() {
                    match univariate_rational_roots(gens[0]) {
                        Ok((roots, _)) => {
                            if let Some(root) = roots.into_iter().find(|r| {
                                invs.iter().all(|iv| {
                                    iv.eval_at(std::slice::from_ref(r))
                                        .is_ok_and(|v| !v.is_zero())
                                })
                            }) {
                                let w = BTreeMap::from([(rem_vars[0].clone(), root.to_string())]);
                                (
                                    Verdict::Established,
                                    Some(w),
                                    "verified rational root in fiber over Q".to_owned(),
                                )
                            } else {
                                (
                                    Verdict::Refuted,
                                    None,
                                    format!(
                                        "no rational root for {} = 0 in Q (Rational Root Theorem)",
                                        gens[0].display(&rem_order, MonomialOrder::Grevlex)
                                    ),
                                )
                            }
                        }
                        Err(reason) => (
                            Verdict::Undetermined(reason.clone()),
                            None,
                            reason.code().to_owned(),
                        ),
                    }
                } else {
                    (
                        Verdict::Established,
                        Some(BTreeMap::from([(rem_vars[0].clone(), "0".to_owned())])),
                        "unconstrained 1D rational fiber".to_owned(),
                    )
                }
            }
        } else {
            let rab = rabinowitsch_solve(&eqs, &invs, &rem_order).map_err(map_algebra_silence)?;
            if rab.is_empty_over_closure {
                (
                    Verdict::Refuted,
                    None,
                    "empty fiber over algebraic closure and Q".to_owned(),
                )
            } else {
                let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::RationalPoints,
                    detail:
                        "multivariate rational fiber probe outside univariate/affine Q decision"
                            .to_owned(),
                };
                (
                    Verdict::Undetermined(reason.clone()),
                    None,
                    reason.code().to_owned(),
                )
            }
        };

        results.push(RationalFiberProbeResult {
            probe_name: probe.name.clone(),
            u_assignments: u_disp,
            c_assignments: c_disp,
            verdict,
            rational_witness,
            detail,
        });
    }
    Ok(results)
}

/// 一般 Laurent 多項式環 $k[t, t^{-1}]$ 上の Newton 多角形傾き整数性検定による大域正則切断検査（W5）。
pub(super) fn check_laurent_global_section(
    family: &CheckedFamilySpec,
    u_vars: &VarOrder,
    c_vars: &VarOrder,
) -> GlobalRegularSectionResult {
    let w_vars = family.witness_vars();
    let section_var = if w_vars.len() == 1 {
        w_vars[0].clone()
    } else if c_vars.len() == 1 {
        c_vars.vars()[0].clone()
    } else {
        return GlobalRegularSectionResult {
            checked: true,
            exists: None,
            obstruction_detail: None,
            silence_reason: Some(SilenceReason::ApplicabilityConditionNotMet {
                condition: "1d_base_and_section_variable_required".to_owned(),
                detail: "Newton polygon Laurent global-section check requires 1 base coordinate and 1 section coordinate".to_owned(),
            }),
        };
    };
    if u_vars.len() != 1 {
        return GlobalRegularSectionResult {
            checked: true,
            exists: None,
            obstruction_detail: None,
            silence_reason: Some(SilenceReason::ApplicabilityConditionNotMet {
                condition: "1d_base_and_section_variable_required".to_owned(),
                detail: "Newton polygon Laurent global-section check requires 1 base variable t"
                    .to_owned(),
            }),
        };
    }
    let t_name = &u_vars.vars()[0];
    let ts_vars = match VarOrder::new(vec![t_name.clone(), section_var.clone()]) {
        Ok(v) => v,
        Err(e) => {
            return GlobalRegularSectionResult {
                checked: true,
                exists: None,
                obstruction_detail: None,
                silence_reason: Some(map_algebra_silence(e)),
            };
        }
    };
    let ts_bind = ExprBindings::params_only(&ts_vars);
    let good_eqs = match &family.inner().goodness {
        GoodnessSpec::Direct { equations, .. } | GoodnessSpec::Existential { equations, .. } => {
            equations
        }
    };
    for eq in good_eqs {
        let Ok(p) = Poly::from_expr_q(&eq.expr, &ts_bind) else {
            continue;
        };
        if let Some(obs_detail) = laurent_newton_polygon_obstruction(&p, t_name, &section_var) {
            return GlobalRegularSectionResult {
                checked: true,
                exists: Some(false),
                obstruction_detail: Some(obs_detail),
                silence_reason: None,
            };
        }
    }
    GlobalRegularSectionResult {
        checked: true,
        exists: None,
        obstruction_detail: None,
        silence_reason: Some(SilenceReason::ApplicabilityConditionNotMet {
            condition: "laurent_global_section_undetermined".to_owned(),
            detail: "Newton polygon at t = 0 admits integer valuation slopes; explicit global regular section not excluded".to_owned(),
        }),
    }
}

fn laurent_newton_polygon_obstruction(
    poly: &Poly<Rat>,
    t_name: &str,
    s_name: &str,
) -> Option<String> {
    if poly.is_zero() {
        return None;
    }
    let mut min_t_by_s: BTreeMap<u32, u32> = BTreeMap::new();
    for mono in poly.terms().keys() {
        let e_t = mono.exps()[0];
        let e_s = mono.exps()[1];
        min_t_by_s
            .entry(e_s)
            .and_modify(|m| *m = (*m).min(e_t))
            .or_insert(e_t);
    }
    if !min_t_by_s.contains_key(&0) || min_t_by_s.len() < 2 {
        return None;
    }
    let pts: Vec<(i64, i64)> = min_t_by_s
        .into_iter()
        .map(|(d, v)| (i64::from(d), i64::from(v)))
        .collect();
    let mut hull: Vec<(i64, i64)> = Vec::new();
    for pt in pts {
        while hull.len() >= 2 {
            let (x1, y1) = hull[hull.len() - 2];
            let (x2, y2) = hull[hull.len() - 1];
            let (x3, y3) = pt;
            let cross = (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1);
            if cross <= 0 {
                hull.pop();
            } else {
                break;
            }
        }
        hull.push(pt);
    }
    let mut non_int_reqs = Vec::new();
    for w in hull.windows(2) {
        let (d1, v1) = w[0];
        let (d2, v2) = w[1];
        let dd = d2 - d1;
        let dv = v1 - v2;
        if dv % dd == 0 {
            return None;
        }
        let g = dd.gcd(&dv.abs());
        non_int_reqs.push(format!("{}*n = {}", dd / g, dv / g));
    }
    if non_int_reqs.is_empty() {
        None
    } else {
        Some(format!(
            "no global regular section {s_name} in k[{t_name}, {t_name}^(-1)]: Newton polygon edge valuations require {} (no integer n in Z)",
            non_int_reqs.join(" or ")
        ))
    }
}
