//! Mixed witness pair extraction, rational fiber probes (W5),
//! and Laurent Newton-polygon global regular section obstruction checks.

use crate::algebra::{
    AffineSolutionQ, ExprBindings, GroebnerBasis, MonomialOrder, Poly, Rat, VarOrder,
    rabinowitsch_solve, solve_affine_q,
};
use crate::ir::change::PointDomain;
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, GoodnessSpec, RealizationSpace};
use crate::ir::provenance::{OriginKind, SourceRef};
use crate::ir::result::{SilenceReason, Verdict};
use crate::ir::result_phase3::{
    GlobalRegularSectionResult, MixedWitnessPair, PairEvaluationWitness, RationalFiberProbeResult,
    RealizationWitness,
};
use crate::ir::robustness::RationalFiberProbe;
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::chevalley::{FamilyConstructibleSets, default_candidate_origin, slice_set_at_c};
use crate::solver::context::display_polys;
use crate::solver::family_direct::{evaluate_goodness_at_point, substitute_preservation_pair};
use crate::solver::family_eval::{
    EnumCandidate, EnumRealization, ScalarVal, build_assignment_map, map_scalar_assignments,
    univariate_rational_roots,
};
use crate::solver::preservation::{
    build_preservation_obligations, compute_preservation_locus_q, map_algebra_silence,
    substitute_poly_expr,
};
use crate::solver::restore::{find_witness_point_q, polys_to_affine_system_q};
use num_bigint::BigInt;
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
        let mut enum_u = EnumRealization {
            member_id: None,
            assignments: build_assignment_map(u_vars.vars(), &vals),
            values: vals.clone(),
            is_raw_candidate: false,
            origin: origin.clone(),
            presentation: None,
        };
        if let RealizationSpace::FiniteMembers(ms) = &family.inner().realizations.space {
            for m in ms {
                if let Ok((m_vals, _)) =
                    map_scalar_assignments(u_vars.vars(), &m.assignments, domain)
                    && m_vals == vals
                {
                    enum_u.member_id = Some(m.id.clone());
                    enum_u.is_raw_candidate = m.is_raw_candidate;
                    enum_u.origin = m.origin.clone();
                    enum_u.presentation = m.presentation.clone();
                    break;
                }
            }
        }
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
    for st in sets
        .robust_all_pass
        .strata()
        .iter()
        .chain(sets.c_space.strata())
    {
        if let Some(pt) = pick_rational_point_in_stratum(st, &sets.c_vars)? {
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
    }
    Ok(None)
}

type ProbeStratumOutcome = (Verdict, Option<BTreeMap<String, String>>, String);
type EqInvPair = (Vec<Poly<Rat>>, Vec<Poly<Rat>>);

fn solve_probe_stratum(
    eqs: &[Poly<Rat>],
    invs: &[Poly<Rat>],
    rem_vars: &[String],
    rem_order: &VarOrder,
) -> Result<ProbeStratumOutcome, SilenceReason> {
    if invs.iter().any(Poly::is_zero) {
        return Ok((
            Verdict::Refuted,
            None,
            "zero invertible constraint cannot hold over Q".to_owned(),
        ));
    }
    if rem_vars.is_empty() {
        let eq_ok = eqs.iter().all(|p| p.constant_value().is_zero());
        let inv_ok = invs.iter().all(|p| !p.constant_value().is_zero());
        return Ok(if eq_ok && inv_ok {
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
        });
    }
    if rem_vars.len() == 1 {
        let gb = GroebnerBasis::compute(eqs, rem_order.clone(), MonomialOrder::Grevlex)
            .map_err(map_algebra_silence)?;
        if gb.contains_one() {
            return Ok((
                Verdict::Refuted,
                None,
                "probe ideal contains 1; no Q points exist".to_owned(),
            ));
        }
        let gens = gb.basis_polys();
        if gens.len() == 1 && !gens[0].is_zero() {
            return match univariate_rational_roots(gens[0]) {
                Ok((roots, _)) => {
                    if let Some(root) = roots.into_iter().find(|r| {
                        invs.iter().all(|iv| {
                            iv.eval_at(std::slice::from_ref(r))
                                .is_ok_and(|v| !v.is_zero())
                        })
                    }) {
                        let w = BTreeMap::from([(rem_vars[0].clone(), root.to_string())]);
                        Ok((
                            Verdict::Established,
                            Some(w),
                            "verified rational root in fiber over Q".to_owned(),
                        ))
                    } else {
                        Ok((
                            Verdict::Refuted,
                            None,
                            format!(
                                "no rational root for {} = 0 in Q (Rational Root Theorem)",
                                gens[0].display(rem_order, MonomialOrder::Grevlex)
                            ),
                        ))
                    }
                }
                Err(reason) => Ok((
                    Verdict::Undetermined(reason.clone()),
                    None,
                    reason.code().to_owned(),
                )),
            };
        }
        let max_deg: usize = invs.iter().map(|iv| iv.total_degree() as usize).sum();
        for k in 0..=(max_deg + 1) {
            let r = Rat::from_int(BigInt::from(k));
            if invs.iter().all(|iv| {
                iv.eval_at(std::slice::from_ref(&r))
                    .is_ok_and(|v| !v.is_zero())
            }) {
                return Ok((
                    Verdict::Established,
                    Some(BTreeMap::from([(rem_vars[0].clone(), r.to_string())])),
                    "verified rational witness on unconstrained 1D Q fiber".to_owned(),
                ));
            }
        }
        return Ok((
            Verdict::Refuted,
            None,
            "invertible constraints failed across 1D fiber over Q".to_owned(),
        ));
    }

    let rab = rabinowitsch_solve(eqs, invs, rem_order).map_err(map_algebra_silence)?;
    if rab.is_empty_over_closure {
        return Ok((
            Verdict::Refuted,
            None,
            "empty fiber over algebraic closure and Q".to_owned(),
        ));
    }
    if rab.parameter_equations.iter().all(Poly::is_affine) {
        let (mat, rhs) = polys_to_affine_system_q(&rab.parameter_equations, rem_vars.len())?;
        if let AffineSolutionQ::Consistent {
            particular,
            kernel_basis,
            verified: true,
        } = solve_affine_q(&mat, &rhs, rem_vars.len()).map_err(map_algebra_silence)?
            && let Some(pt) = find_witness_point_q(&particular, &kernel_basis, eqs, invs)?
        {
            let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Q).collect();
            return Ok((
                Verdict::Established,
                Some(build_assignment_map(rem_vars, &vals)),
                "verified affine rational fiber witness over Q".to_owned(),
            ));
        }
    }
    let reason = SilenceReason::NonLinearRationalOrIntegerExistence {
        point_domain: PointDomain::RationalPoints,
        detail: "multivariate rational fiber probe outside univariate/affine Q decision".to_owned(),
    };
    Ok((
        Verdict::Undetermined(reason.clone()),
        None,
        reason.code().to_owned(),
    ))
}

pub(super) fn run_rational_fiber_probes(
    family: &CheckedFamilySpec,
    base_value: Option<&[ScalarLit]>,
    probes: &[RationalFiberProbe],
) -> Result<Vec<RationalFiberProbeResult>, SilenceReason> {
    let domain = family.coeff_domain();
    let u_names = family.u_vars();
    let c_names = family.c_vars();
    let w_names = family.witness_vars();
    let empty = BTreeMap::new();
    let mut results = Vec::with_capacity(probes.len());

    let (good_eqs, good_invs, pres_opt) = match &family.inner().goodness {
        GoodnessSpec::Direct {
            raw_sequence: Some(_),
            ..
        } => {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "probe_raw_sequence_unsupported".to_owned(),
                detail: "rational fiber probes do not support raw_sequence presentations"
                    .to_owned(),
            });
        }
        GoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence: None,
        }
        | GoodnessSpec::Existential {
            equations,
            invertibles,
            preservation,
            ..
        } => (equations, invertibles, preservation.as_ref()),
    };

    for probe in probes {
        for k in probe.u_assignments.keys() {
            if !u_names.iter().any(|u| u == k) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "probe_variable_declared".to_owned(),
                    detail: format!(
                        "unknown realization variable `{k}` in probe `{}`",
                        probe.name
                    ),
                });
            }
        }
        for k in probe.c_assignments.keys() {
            if !c_names.iter().any(|c| c == k) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "probe_variable_declared".to_owned(),
                    detail: format!("unknown candidate variable `{k}` in probe `{}`", probe.name),
                });
            }
        }

        let mut base_subst = BTreeMap::new();
        let mut u_disp = BTreeMap::new();
        let mut c_disp = BTreeMap::new();
        for (k, lit) in &probe.u_assignments {
            let sv = ScalarVal::from_lit(lit, domain)?;
            u_disp.insert(k.clone(), sv.to_display());
            base_subst.insert(k.clone(), sv.to_expr());
        }
        for (k, lit) in &probe.c_assignments {
            let sv = ScalarVal::from_lit(lit, domain)?;
            c_disp.insert(k.clone(), sv.to_display());
            base_subst.insert(k.clone(), sv.to_expr());
        }

        let u_branches: Vec<BTreeMap<String, PolyExpr>> = match &family.inner().realizations.space {
            RealizationSpace::PolynomialScheme { .. } => vec![BTreeMap::new()],
            RealizationSpace::FiniteMembers(ms) => {
                let mut out = Vec::new();
                for m in ms {
                    let (vals, _) = map_scalar_assignments(u_names, &m.assignments, domain)?;
                    let mut m_map = BTreeMap::new();
                    let mut ok = true;
                    for (name, sv) in u_names.iter().zip(&vals) {
                        if let Some(lit) = probe.u_assignments.get(name)
                            && ScalarVal::from_lit(lit, domain)? != *sv
                        {
                            ok = false;
                            break;
                        }
                        m_map.insert(name.clone(), sv.to_expr());
                    }
                    if ok {
                        out.push(m_map);
                    }
                }
                out
            }
        };
        let c_branches: Vec<BTreeMap<String, PolyExpr>> = match &family.inner().candidates.space {
            CandidateSpace::PolynomialScheme { .. } => vec![BTreeMap::new()],
            CandidateSpace::FiniteMembers(ms) if c_names.is_empty() && ms.is_empty() => {
                vec![BTreeMap::new()]
            }
            CandidateSpace::FiniteMembers(ms) => {
                let mut out = Vec::new();
                for m in ms {
                    let (vals, _) = map_scalar_assignments(c_names, &m.assignments, domain)?;
                    let mut m_map = BTreeMap::new();
                    let mut ok = true;
                    for (name, sv) in c_names.iter().zip(&vals) {
                        if let Some(lit) = probe.c_assignments.get(name)
                            && ScalarVal::from_lit(lit, domain)? != *sv
                        {
                            ok = false;
                            break;
                        }
                        m_map.insert(name.clone(), sv.to_expr());
                    }
                    if ok {
                        out.push(m_map);
                    }
                }
                out
            }
        };

        let mut agg_verdict = Verdict::Refuted;
        let mut agg_witness = None;
        let mut agg_detail =
            "probe constraints not satisfied in realization/candidate fiber over Q".to_owned();
        let mut undetermined_reason: Option<(SilenceReason, String)> = None;

        'branch_loop: for u_b in &u_branches {
            for c_b in &c_branches {
                let mut fixed_subst = base_subst.clone();
                for (k, v) in u_b.iter().chain(c_b) {
                    fixed_subst.insert(k.clone(), v.clone());
                }
                let rem_vars: Vec<String> = u_names
                    .iter()
                    .chain(c_names)
                    .chain(w_names)
                    .filter(|v| !fixed_subst.contains_key(*v))
                    .cloned()
                    .collect();
                for v in &rem_vars {
                    fixed_subst.insert(v.clone(), PolyExpr::param(v));
                }
                let rem_order = VarOrder::new(rem_vars.clone()).map_err(map_algebra_silence)?;
                let rem_bind = ExprBindings::params_only(&rem_order);

                let mut eq_exprs: Vec<PolyExpr> = good_eqs.iter().map(|e| e.expr.clone()).collect();
                let mut inv_exprs: Vec<PolyExpr> =
                    good_invs.iter().map(|i| i.expr.clone()).collect();
                if let RealizationSpace::PolynomialScheme {
                    equations,
                    invertibles,
                    ..
                } = &family.inner().realizations.space
                {
                    eq_exprs.extend(equations.iter().map(|e| e.expr.clone()));
                    inv_exprs.extend(invertibles.iter().map(|i| i.expr.clone()));
                }
                if let CandidateSpace::PolynomialScheme {
                    equations,
                    invertibles,
                    ..
                } = &family.inner().candidates.space
                {
                    eq_exprs.extend(equations.iter().map(|e| e.expr.clone()));
                    inv_exprs.extend(invertibles.iter().map(|i| i.expr.clone()));
                }
                if let Some(bv) = base_value {
                    for (qe, bl) in family.inner().realizations.reading_q.iter().zip(bv) {
                        eq_exprs.push(PolyExpr::diff(qe.clone(), PolyExpr::Const(bl.clone())));
                    }
                    for (pe, bl) in family.inner().candidates.pi.iter().zip(bv) {
                        eq_exprs.push(PolyExpr::diff(pe.clone(), PolyExpr::Const(bl.clone())));
                    }
                } else {
                    for (qe, pe) in family
                        .inner()
                        .realizations
                        .reading_q
                        .iter()
                        .zip(&family.inner().candidates.pi)
                    {
                        eq_exprs.push(PolyExpr::diff(qe.clone(), pe.clone()));
                    }
                }

                let mut base_eqs: Vec<Poly<Rat>> = Vec::new();
                for expr in &eq_exprs {
                    let sub = substitute_poly_expr(expr, &empty, &empty, &fixed_subst);
                    let p = Poly::from_expr_q(&sub, &rem_bind).map_err(map_algebra_silence)?;
                    if !p.is_zero() {
                        base_eqs.push(p);
                    }
                }
                let mut base_invs: Vec<Poly<Rat>> = Vec::new();
                for expr in &inv_exprs {
                    let sub = substitute_poly_expr(expr, &empty, &empty, &fixed_subst);
                    base_invs
                        .push(Poly::from_expr_q(&sub, &rem_bind).map_err(map_algebra_silence)?);
                }

                let pres_strata: Vec<EqInvPair> = if let Some(psrc) = pres_opt {
                    let (pair, _) = substitute_preservation_pair(psrc, &fixed_subst)?;
                    let obs = build_preservation_obligations(&pair)?;
                    let locus = compute_preservation_locus_q(&obs, &rem_order)?;
                    if locus.strata.is_empty() {
                        continue;
                    }
                    locus
                        .strata
                        .into_iter()
                        .map(|st| (st.equations, st.invertibles))
                        .collect()
                } else {
                    vec![(vec![], vec![])]
                };

                for (peqs, pinvs) in pres_strata {
                    let mut eqs = base_eqs.clone();
                    eqs.extend(peqs);
                    let mut invs = base_invs.clone();
                    invs.extend(pinvs);
                    let (v, w, det) = solve_probe_stratum(&eqs, &invs, &rem_vars, &rem_order)?;
                    match v {
                        Verdict::Established => {
                            let mut full_w = BTreeMap::new();
                            for (k, val_str) in w.unwrap_or_default() {
                                full_w.insert(k, val_str);
                            }
                            agg_verdict = Verdict::Established;
                            agg_witness = Some(full_w);
                            agg_detail = det;
                            break 'branch_loop;
                        }
                        Verdict::Undetermined(r) => {
                            if undetermined_reason.is_none() {
                                undetermined_reason = Some((r, det));
                            }
                        }
                        Verdict::Refuted => {
                            agg_detail = det;
                        }
                    }
                }
            }
        }

        if agg_verdict != Verdict::Established
            && let Some((r, det)) = undetermined_reason
        {
            agg_verdict = Verdict::Undetermined(r);
            agg_detail = det;
        }

        results.push(RationalFiberProbeResult {
            probe_name: probe.name.clone(),
            u_assignments: u_disp,
            c_assignments: c_disp,
            verdict: agg_verdict,
            rational_witness: agg_witness,
            detail: agg_detail,
        });
    }
    Ok(results)
}

/// 一般 Laurent 多項式環 $k[t, t^{-1}]$ 上の Newton 多角形傾き整数性検定による大域正則切断検査（W5）。
pub(super) fn check_laurent_global_section(
    family: &CheckedFamilySpec,
    base_value: Option<&[ScalarLit]>,
    u_vars: &VarOrder,
    c_vars: &VarOrder,
) -> GlobalRegularSectionResult {
    let not_applicable = |condition: &str, detail: String| GlobalRegularSectionResult {
        checked: true,
        exists: None,
        obstruction_detail: None,
        silence_reason: Some(SilenceReason::ApplicabilityConditionNotMet {
            condition: condition.to_owned(),
            detail,
        }),
    };

    if base_value.is_some() || !family.b_vars().is_empty() {
        return not_applicable(
            "laurent_unrestricted_1d_base_required",
            "Laurent global-section check requires base-unrestricted 1D base curve (empty b_vars / base_value)".to_owned(),
        );
    }
    let RealizationSpace::PolynomialScheme {
        equations,
        invertibles,
        ..
    } = &family.inner().realizations.space
    else {
        return not_applicable(
            "laurent_polynomial_scheme_base_required",
            "Laurent global-section check requires PolynomialScheme base curve, not FiniteMembers"
                .to_owned(),
        );
    };
    if !equations.is_empty() {
        return not_applicable(
            "laurent_unclosed_1d_base_required",
            "Laurent global-section check requires an open curve in A^1 without closed base equations".to_owned(),
        );
    }
    let u_bind = ExprBindings::params_only(u_vars);
    for inv in invertibles {
        match Poly::from_expr_q(&inv.expr, &u_bind) {
            Ok(p) if !p.is_zero() => {}
            _ => {
                return not_applicable(
                    "laurent_nonempty_open_base_required",
                    "Laurent global-section check requires non-zero base invertible constraints"
                        .to_owned(),
                );
            }
        }
    }

    let w_vars = family.witness_vars();
    let section_var = if w_vars.len() == 1 {
        w_vars[0].clone()
    } else if c_vars.len() == 1 {
        let CandidateSpace::PolynomialScheme {
            equations: c_eqs, ..
        } = &family.inner().candidates.space
        else {
            return not_applicable(
                "laurent_free_section_coordinate_required",
                "Laurent global-section check for candidate section requires unconstrained PolynomialScheme candidate space".to_owned(),
            );
        };
        if !c_eqs.is_empty() {
            return not_applicable(
                "laurent_free_section_coordinate_required",
                "Laurent global-section check requires candidate section equation-free".to_owned(),
            );
        }
        c_vars.vars()[0].clone()
    } else {
        return not_applicable(
            "1d_base_and_section_variable_required",
            "Newton polygon Laurent global-section check requires 1 base coordinate and 1 section coordinate".to_owned(),
        );
    };
    if u_vars.len() != 1 {
        return not_applicable(
            "1d_base_and_section_variable_required",
            "Newton polygon Laurent global-section check requires 1 base variable t".to_owned(),
        );
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
        GoodnessSpec::Direct {
            equations,
            preservation: None,
            raw_sequence: None,
            ..
        }
        | GoodnessSpec::Existential {
            equations,
            preservation: None,
            ..
        } => equations,
        _ => {
            return not_applicable(
                "laurent_pure_polynomial_equations_required",
                "Laurent global-section Newton check requires pure polynomial goodness without preservation/raw_sequence".to_owned(),
            );
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
    not_applicable(
        "laurent_global_section_undetermined",
        "Newton polygon at t = 0 admits integer valuation slopes; explicit global regular section not excluded".to_owned(),
    )
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
