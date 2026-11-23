//! 代数閉包上の正次元・記号スキーム族に対する 3 量化階層と
//! 存在型 witness 復元・再評価検算（M4 / Minor #1 対応）。

use crate::algebra::{
    ConstructibleSet, LocallyClosedStratum, Monomial, Poly, Rat, VarOrder,
    project_constructible_set,
};
use crate::ir::change::PointDomain;
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, GoodnessSpec, RealizationSpace};
use crate::ir::provenance::{OriginKind, SourceRef};
use crate::ir::result::SilenceReason;
use crate::ir::result_phase3::{
    CommonQuantifierResult, DesignatedValidityResult, PairEvaluationWitness,
    PointwiseQuantifierResult, RealizationWitness,
};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::chevalley::{
    FamilyConstructibleSets, build_family_constructible_sets, default_candidate_origin,
    slice_set_at_c,
};
use crate::solver::chevalley_sections::pick_rational_point_in_stratum;
use crate::solver::context::display_polys;
use crate::solver::family_direct::evaluate_goodness_at_point;
use crate::solver::family_eval::{
    EnumCandidate, EnumRealization, ScalarVal, build_assignment_map, map_scalar_assignments,
    scalar_eq,
};
use crate::solver::preservation::map_algebra_silence;
use num_traits::One;
use std::collections::BTreeMap;

pub(super) type QuantifiersTuple = (
    Option<DesignatedValidityResult>,
    PointwiseQuantifierResult,
    CommonQuantifierResult,
    Option<EnumCandidate>,
);

fn default_realization_origin(family: &CheckedFamilySpec) -> SourceRef {
    match &family.inner().realizations.space {
        RealizationSpace::PolynomialScheme { origin, .. } => origin.clone(),
        RealizationSpace::FiniteMembers(ms) => ms
            .first()
            .map(|m| m.origin.clone())
            .or_else(|| family.inner().provenance.origins.first().cloned())
            .unwrap_or_else(|| SourceRef::new("realization", OriginKind::StaticAnalysis)),
    }
}

fn swap_uc_to_cu(
    set: &ConstructibleSet,
    u_len: usize,
    cu_vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let n_tot = cu_vars.len();
    let swap_poly = |p: &Poly<Rat>| -> Poly<Rat> {
        let mut out = Poly::zero(n_tot, Rat::zero());
        for (mono, coeff) in p.terms() {
            let exps = mono.exps();
            let mut reordered = Vec::with_capacity(n_tot);
            reordered.extend_from_slice(&exps[u_len..]);
            reordered.extend_from_slice(&exps[..u_len]);
            out.add_term(Monomial::from_exps(reordered), coeff.clone());
        }
        out
    };
    let strata = set
        .strata()
        .iter()
        .map(|st| LocallyClosedStratum {
            equations: st.equations.iter().map(swap_poly).collect(),
            invertibles: st.invertibles.iter().map(swap_poly).collect(),
        })
        .collect();
    ConstructibleSet::from_strata(cu_vars.clone(), strata)
}

fn rat_to_scalar_vals(pts: Vec<Rat>, domain: &CoeffDomain) -> Vec<ScalarVal> {
    pts.into_iter()
        .map(|r| match domain {
            CoeffDomain::Z if r.den().is_one() => ScalarVal::Z(r.num().clone()),
            _ => ScalarVal::Q(r),
        })
        .collect()
}

fn format_stratum_desc(st: &LocallyClosedStratum, vars: &VarOrder) -> String {
    let eqs = display_polys(&st.equations, vars);
    let invs = display_polys(&st.invertibles, vars);
    match (eqs.is_empty(), invs.is_empty()) {
        (true, true) => "unconstrained".to_owned(),
        (false, true) => format!("{} = 0", eqs.join(", ")),
        (true, false) => format!("{} != 0", invs.join(", ")),
        (false, false) => format!("{} = 0; {} != 0", eqs.join(", "), invs.join(", ")),
    }
}

fn stratum_geom_assignments(
    strata: &[LocallyClosedStratum],
    vars: &VarOrder,
) -> BTreeMap<String, String> {
    let desc = strata
        .first()
        .map(|st| format_stratum_desc(st, vars))
        .unwrap_or_else(|| "empty".to_owned());
    vars.vars()
        .iter()
        .map(|v| (v.clone(), format!("geom_point({v}; {desc})")))
        .collect()
}

fn match_realization_meta(
    family: &CheckedFamilySpec,
    vals: &[ScalarVal],
    fallback_origin: &SourceRef,
) -> (Option<String>, bool, SourceRef) {
    match &family.inner().realizations.space {
        RealizationSpace::FiniteMembers(ms) => {
            for m in ms {
                if let Ok((mv, _)) =
                    map_scalar_assignments(family.u_vars(), &m.assignments, family.coeff_domain())
                    && mv.len() == vals.len()
                    && mv.iter().zip(vals).all(|(a, b)| scalar_eq(a, b))
                {
                    return (Some(m.id.clone()), m.is_raw_candidate, m.origin.clone());
                }
            }
            (None, false, fallback_origin.clone())
        }
        RealizationSpace::PolynomialScheme {
            is_raw_candidate,
            origin,
            ..
        } => (None, *is_raw_candidate, origin.clone()),
    }
}

fn match_candidate_meta(
    family: &CheckedFamilySpec,
    vals: &[ScalarVal],
    fallback_origin: &SourceRef,
) -> (Option<String>, SourceRef) {
    match &family.inner().candidates.space {
        CandidateSpace::FiniteMembers(ms) => {
            for m in ms {
                if let Ok((mv, _)) =
                    map_scalar_assignments(family.c_vars(), &m.assignments, family.coeff_domain())
                    && mv.len() == vals.len()
                    && mv.iter().zip(vals).all(|(a, b)| scalar_eq(a, b))
                {
                    return (Some(m.id.clone()), m.origin.clone());
                }
            }
            (None, fallback_origin.clone())
        }
        CandidateSpace::PolynomialScheme { origin, .. } => (None, origin.clone()),
    }
}

fn extract_u_witness_for_cand(
    family: &CheckedFamilySpec,
    slice: &ConstructibleSet,
    u_vars: &VarOrder,
    cand: &EnumCandidate,
    expected_pass: bool,
    origin: &SourceRef,
) -> Result<Option<PairEvaluationWitness>, SilenceReason> {
    let domain = family.coeff_domain();
    for st in slice.strata() {
        if let Some(pt_q) = pick_rational_point_in_stratum(st, u_vars)? {
            let vals = rat_to_scalar_vals(pt_q, domain);
            let (member_id, is_raw_candidate, mem_origin) =
                match_realization_meta(family, &vals, origin);
            let mut enum_u = EnumRealization {
                member_id,
                assignments: build_assignment_map(u_vars.vars(), &vals),
                values: vals,
                is_raw_candidate,
                origin: mem_origin,
                presentation: None,
            };
            if let RealizationSpace::FiniteMembers(ms) = &family.inner().realizations.space
                && let Some(id) = &enum_u.member_id
                && let Some(m) = ms.iter().find(|m| &m.id == id)
            {
                enum_u.presentation = m.presentation.clone();
            }
            let w =
                evaluate_goodness_at_point(family, &enum_u, cand, &PointDomain::AlgebraicClosure)?;
            if w.passed == expected_pass {
                return Ok(Some(w));
            }
        }
    }
    Ok(None)
}

fn extract_uc_witness(
    family: &CheckedFamilySpec,
    uc_set: &ConstructibleSet,
    u_vars: &VarOrder,
    c_vars: &VarOrder,
    uc_vars: &VarOrder,
    u_origin: &SourceRef,
    c_origin: &SourceRef,
) -> Result<Option<PairEvaluationWitness>, SilenceReason> {
    let u_len = u_vars.len();
    for st in uc_set.strata() {
        if let Some(pt_q) = pick_rational_point_in_stratum(st, uc_vars)? {
            let u_vals = rat_to_scalar_vals(pt_q[..u_len].to_vec(), family.coeff_domain());
            let c_vals = rat_to_scalar_vals(pt_q[u_len..].to_vec(), family.coeff_domain());
            let (u_id, u_raw, u_mem_origin) = match_realization_meta(family, &u_vals, u_origin);
            let mut enum_u = EnumRealization {
                member_id: u_id,
                assignments: build_assignment_map(u_vars.vars(), &u_vals),
                values: u_vals,
                is_raw_candidate: u_raw,
                origin: u_mem_origin,
                presentation: None,
            };
            if let RealizationSpace::FiniteMembers(ms) = &family.inner().realizations.space
                && let Some(id) = &enum_u.member_id
                && let Some(m) = ms.iter().find(|m| &m.id == id)
            {
                enum_u.presentation = m.presentation.clone();
            }
            let (c_id, c_mem_origin) = match_candidate_meta(family, &c_vals, c_origin);
            let enum_c = EnumCandidate {
                candidate_id: c_id,
                assignments: build_assignment_map(c_vars.vars(), &c_vals),
                values: c_vals,
                origin: c_mem_origin,
            };
            let w = evaluate_goodness_at_point(
                family,
                &enum_u,
                &enum_c,
                &PointDomain::AlgebraicClosure,
            )?;
            if w.passed {
                return Ok(Some(w));
            }
        }
    }
    Ok(None)
}

fn require_existential_restored_witness(
    witness_opt: Option<PairEvaluationWitness>,
    context: &str,
) -> Result<Vec<PairEvaluationWitness>, SilenceReason> {
    if let Some(w) = witness_opt
        && w.restored_completion
            .as_ref()
            .is_some_and(|rc| rc.reeval.matched)
    {
        return Ok(vec![w]);
    }
    Err(SilenceReason::NonLinearRationalOrIntegerExistence {
        point_domain: PointDomain::RationalPoints,
        detail: format!(
            "existential symbolic {context} satisfied over algebraic closure, but concrete witness restoration/reevaluation could not extract a rational sample point"
        ),
    })
}

pub(super) fn eval_symbolic_closure_quantifiers(
    family: &CheckedFamilySpec,
    base_value: &[ScalarLit],
    designated: Option<&EnumCandidate>,
    point_domain: &PointDomain,
) -> Result<QuantifiersTuple, SilenceReason> {
    if *point_domain != PointDomain::AlgebraicClosure {
        return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain: point_domain.clone(),
            detail: "symbolic positive-dimensional quantifier evaluation requires AlgebraicClosure"
                .to_owned(),
        });
    }
    let sets: FamilyConstructibleSets = build_family_constructible_sets(family, Some(base_value))?;
    let real_origin = default_realization_origin(family);
    let cand_origin =
        default_candidate_origin(&family.inner().candidates.space, &family.inner().provenance);
    let is_existential = matches!(family.inner().goodness, GoodnessSpec::Existential { .. });

    let valid_des = if let Some(dc) = designated {
        let pt: Vec<Rat> = dc.values.iter().map(ScalarVal::as_rat).collect();
        let sat = sets.robust_all_pass.contains_point(&pt)?;
        let supporting_witnesses = if sat && is_existential {
            let pass_slice = slice_set_at_c(&sets.w_pass, &sets.c_vars, dc, &sets.u_vars)?;
            let w_opt = extract_u_witness_for_cand(
                family,
                &pass_slice,
                &sets.u_vars,
                dc,
                true,
                &real_origin,
            )?;
            require_existential_restored_witness(w_opt, "designated validity")?
        } else {
            vec![]
        };
        let counterexample = if !sat {
            let fail_slice = slice_set_at_c(&sets.w_fail, &sets.c_vars, dc, &sets.u_vars)?;
            if let Some(w) = extract_u_witness_for_cand(
                family,
                &fail_slice,
                &sets.u_vars,
                dc,
                false,
                &real_origin,
            )? {
                Some(w)
            } else {
                let res = fail_slice
                    .strata()
                    .first()
                    .map(|st| vec![format_stratum_desc(st, &sets.u_vars)])
                    .unwrap_or_else(|| vec!["W_fail non-empty".to_owned()]);
                Some(PairEvaluationWitness {
                    realization: RealizationWitness {
                        member_id: None,
                        assignments: stratum_geom_assignments(fail_slice.strata(), &sets.u_vars),
                        is_raw_candidate: false,
                        origin: real_origin.clone(),
                    },
                    candidate_id: dc.candidate_id.clone(),
                    candidate_assignments: dc.assignments.clone(),
                    passed: false,
                    legal_execution_exists: None,
                    residuals: res,
                    empty_witness: None,
                    restored_completion: None,
                })
            }
        } else {
            None
        };
        Some(DesignatedValidityResult {
            candidate_id: dc.candidate_id.clone(),
            candidate_assignments: dc.assignments.clone(),
            satisfied: sat,
            vacuously_true_empty_fiber: false,
            supporting_witnesses,
            counterexample,
        })
    } else {
        None
    };

    let mut cu_names = sets.c_vars.vars().to_vec();
    cu_names.extend(sets.u_vars.vars().iter().cloned());
    let cu_vars = VarOrder::new(cu_names).map_err(map_algebra_silence)?;
    let w_pass_cu = swap_uc_to_cu(&sets.w_pass, sets.u_vars.len(), &cu_vars)?;
    let u_proj_pass = project_constructible_set(&w_pass_cu, sets.c_vars.len(), &sets.u_vars)?;
    let pw_uncovered = sets.u_space.difference(&u_proj_pass)?;
    let pw_sat = pw_uncovered.is_empty();

    let pw_witnesses = if pw_sat && is_existential {
        let w_opt = extract_uc_witness(
            family,
            &sets.w_pass,
            &sets.u_vars,
            &sets.c_vars,
            &sets.uc_vars,
            &real_origin,
            &cand_origin,
        )?;
        require_existential_restored_witness(w_opt, "pointwise quantifier")?
    } else {
        vec![]
    };
    let pw_counterexample = if !pw_sat {
        let (member_id, is_raw_candidate, ce_origin, assign) = if let Some(first_st) =
            pw_uncovered.strata().first()
            && let Some(pt) = pick_rational_point_in_stratum(first_st, &sets.u_vars)?
        {
            let vals = rat_to_scalar_vals(pt, family.coeff_domain());
            let (id, is_raw, orig) = match_realization_meta(family, &vals, &real_origin);
            (
                id,
                is_raw,
                orig,
                build_assignment_map(sets.u_vars.vars(), &vals),
            )
        } else {
            (
                None,
                false,
                real_origin.clone(),
                stratum_geom_assignments(pw_uncovered.strata(), &sets.u_vars),
            )
        };
        Some(RealizationWitness {
            member_id,
            assignments: assign,
            is_raw_candidate,
            origin: ce_origin,
        })
    } else {
        None
    };
    let pointwise = PointwiseQuantifierResult {
        satisfied: pw_sat,
        vacuously_true_empty_fiber: false,
        witnesses: pw_witnesses,
        counterexample: pw_counterexample,
    };

    let common_sat = !sets.robust_all_pass.is_empty();
    let mut common_cand_opt: Option<EnumCandidate> = None;
    let cand_assign = if common_sat {
        if sets.c_vars.is_empty() {
            common_cand_opt = Some(EnumCandidate {
                candidate_id: None,
                values: vec![],
                assignments: BTreeMap::new(),
                origin: cand_origin.clone(),
            });
            Some(BTreeMap::new())
        } else {
            let mut extracted_cand = None;
            for st in sets.robust_all_pass.strata() {
                if let Some(pt) = pick_rational_point_in_stratum(st, &sets.c_vars)? {
                    let vals = rat_to_scalar_vals(pt, family.coeff_domain());
                    let assign = build_assignment_map(sets.c_vars.vars(), &vals);
                    let (id, orig) = match_candidate_meta(family, &vals, &cand_origin);
                    extracted_cand = Some(EnumCandidate {
                        candidate_id: id,
                        values: vals,
                        assignments: assign.clone(),
                        origin: orig,
                    });
                    break;
                }
            }
            if let Some(ec) = extracted_cand {
                let assign = ec.assignments.clone();
                common_cand_opt = Some(ec);
                Some(assign)
            } else if is_existential {
                return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                    point_domain: PointDomain::RationalPoints,
                    detail: "existential symbolic common candidate could not extract rational c witness for restoration/reeval".to_owned(),
                });
            } else {
                Some(stratum_geom_assignments(
                    sets.robust_all_pass.strata(),
                    &sets.c_vars,
                ))
            }
        }
    } else {
        None
    };

    let common_witnesses = if common_sat && is_existential {
        let Some(ref cc) = common_cand_opt else {
            return Err(SilenceReason::NonLinearRationalOrIntegerExistence {
                point_domain: PointDomain::RationalPoints,
                detail: "existential common quantifier could not extract concrete candidate"
                    .to_owned(),
            });
        };
        let pass_slice = slice_set_at_c(&sets.w_pass, &sets.c_vars, cc, &sets.u_vars)?;
        let w_opt =
            extract_u_witness_for_cand(family, &pass_slice, &sets.u_vars, cc, true, &real_origin)?;
        require_existential_restored_witness(w_opt, "common candidate")?
    } else {
        vec![]
    };
    let common = CommonQuantifierResult {
        satisfied: common_sat,
        vacuously_true_empty_fiber: false,
        candidate_id: common_cand_opt
            .as_ref()
            .and_then(|c| c.candidate_id.clone()),
        candidate_assignments: cand_assign,
        witnesses: common_witnesses,
        counterexample_witnesses: vec![],
        counterexample_detail: (!common_sat)
            .then(|| "Chevalley robust_all_pass (P_+ \\ P_-) is empty over closure".to_owned()),
    };

    Ok((valid_des, pointwise, common, common_cand_opt))
}
