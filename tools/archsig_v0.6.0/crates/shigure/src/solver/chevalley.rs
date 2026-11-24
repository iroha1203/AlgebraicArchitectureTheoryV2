//! 構成可能集合上の幾何的像（G-141 D6）と Chevalley 四分類（G-141 D7 / G-142 G7）、
//! 有理点 fiber プローブ、および Laurent 環 $k[t, t^{-1}]$ 上の大域正則切断非存在検定。

use crate::algebra::{
    ConstructibleSet, ExprBindings, LocallyClosedStratum, Monomial, Poly, Rat, VarOrder,
    project_constructible_set,
};
use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{
    CandidateSpace, CheckedFamilySpec, GoodnessSpec, PreservationGoodnessSource, RealizationSpace,
};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    ChevalleyOutcomeDetail, ChevalleyRegionSummary, UniversalRingStabilityResult,
};
use crate::ir::robustness::{CandidateSelector, CheckedChevalleyTask};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::solver::chevalley_sections::{
    build_mixed_witness_pair, check_laurent_global_section, resolve_universal_candidate,
    run_rational_fiber_probes,
};
use crate::solver::context::display_polys;
use crate::solver::family_direct::{
    check_family_presentations_applicability, evaluate_goodness_at_point,
    substitute_preservation_pair,
};
use crate::solver::family_eval::{
    EnumCandidate, EnumRealization, ScalarVal, collect_family_origins, eval_expr_at,
    map_scalar_assignments,
};
use crate::solver::preservation::{
    build_preservation_obligations, compute_preservation_locus_q, map_algebra_silence,
};
use crate::solver::robustness_universal::evaluate_universal_ring;
use std::collections::{BTreeMap, BTreeSet};

/// `shigure_chevalley` の計算核入口（G-141 D6–D7 / G-142 G7）。
pub fn solve_chevalley_task(task: &CheckedChevalleyTask) -> ShigureOutcome {
    let family = task.family();
    let coeff_domain = family.coeff_domain().clone();
    let point_domain = task.point_domain().clone();
    let mut origins = collect_family_origins(family);
    for src in &task.provenance().origins {
        if !origins.contains(src) {
            origins.push(src.clone());
        }
    }
    let provenance = Provenance::new(
        origins,
        vec![MathClause::G141D6, MathClause::G141D7, MathClause::G142G7],
    );
    let mut checks = Vec::new();

    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return undetermined_chevalley(
            coeff_domain,
            point_domain,
            checks,
            provenance,
            SilenceReason::UnobservedDependency { slots: missing },
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    if point_domain != PointDomain::AlgebraicClosure
        || !matches!(coeff_domain, CoeffDomain::Q | CoeffDomain::Z)
    {
        let reason = SilenceReason::ApplicabilityConditionNotMet {
            condition: "chevalley_q_algebraic_closure_required".to_owned(),
            detail: format!(
                "Chevalley constructible classification requires AlgebraicClosure over Q/Z, got `{coeff_domain}` / `{point_domain}`"
            ),
        };
        checks.push(ApplicabilityCheck::failed(
            "chevalley_q_algebraic_closure_required",
            MathClause::G141D6,
            reason.code(),
        ));
        return undetermined_chevalley(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "chevalley_q_algebraic_closure_required",
        MathClause::G141D6,
    ));

    if let Err(reason) = check_family_presentations_applicability(family, &mut checks) {
        return undetermined_chevalley(coeff_domain, point_domain, checks, provenance, reason);
    }

    let sets = match build_family_constructible_sets(family, task.base_value()) {
        Ok(s) => s,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "d6_constructible_projection",
                MathClause::G141D6,
                reason.code(),
            ));
            return undetermined_chevalley(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "d6_constructible_projection",
        MathClause::G141D6,
    ));

    let p_plus_sum = summarize_region(&sets.p_plus, &sets.c_vars);
    let p_minus_sum = summarize_region(&sets.p_minus, &sets.c_vars);
    let robust_sum = summarize_region(&sets.robust_all_pass, &sets.c_vars);
    let fail_sum = summarize_region(&sets.all_fail, &sets.c_vars);
    let mixed_sum = summarize_region(&sets.mixed, &sets.c_vars);
    let empty_sum = summarize_region(&sets.empty_realizations, &sets.c_vars);
    let eff_sum = sets
        .effective_image_e
        .as_ref()
        .map(|s| summarize_region(s, &sets.uc_vars));

    let (designated_cls, chosen_cand) =
        match resolve_designated_candidate(family, &sets, task.designated_candidate()) {
            Ok(pair) => pair,
            Err(reason) => {
                checks.push(ApplicabilityCheck::failed(
                    "designated_candidate_resolved",
                    MathClause::G142G7,
                    reason.code(),
                ));
                return undetermined_chevalley(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    reason,
                );
            }
        };

    let mixed_witness_pair = match build_mixed_witness_pair(family, &sets, chosen_cand.as_ref()) {
        Ok(mw) => mw,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "mixed_witness_pair_extracted",
                MathClause::G142G7,
                reason.code(),
            ));
            return undetermined_chevalley(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let probes =
        match run_rational_fiber_probes(family, task.base_value(), task.rational_fiber_probes()) {
            Ok(p) => p,
            Err(reason) => {
                return undetermined_chevalley(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    reason,
                );
            }
        };

    let global_section = if task.check_global_regular_section() {
        Some(check_laurent_global_section(
            family,
            task.base_value(),
            &sets.u_vars,
            &sets.c_vars,
        ))
    } else {
        None
    };

    let universal_contrast = if task.check_universal_ring() {
        match resolve_universal_candidate(family, &sets, chosen_cand.as_ref()) {
            Ok(Some(cand)) => {
                let effective_bv: Vec<ScalarLit> = if let Some(bv) = task.base_value() {
                    bv.to_vec()
                } else {
                    let mut out = Vec::with_capacity(family.inner().candidates.pi.len());
                    for pi_expr in &family.inner().candidates.pi {
                        let sv = match eval_expr_at(
                            pi_expr,
                            &sets.c_vars,
                            &cand.values,
                            &coeff_domain,
                        ) {
                            Ok(v) => v,
                            Err(reason) => {
                                return undetermined_chevalley(
                                    coeff_domain,
                                    point_domain,
                                    checks,
                                    provenance,
                                    reason,
                                );
                            }
                        };
                        out.push(sv.to_lit());
                    }
                    out
                };
                let nonempty_for_c =
                    match slice_set_at_c(&sets.w_total, &sets.c_vars, &cand, &sets.u_vars) {
                        Ok(sliced) => !sliced.is_empty(),
                        Err(reason) => {
                            return undetermined_chevalley(
                                coeff_domain,
                                point_domain,
                                checks,
                                provenance,
                                reason,
                            );
                        }
                    };
                match evaluate_universal_ring(family, &effective_bv, &cand, nonempty_for_c) {
                    Ok(ur) => Some(ur),
                    Err(reason) => {
                        return undetermined_chevalley(
                            coeff_domain,
                            point_domain,
                            checks,
                            provenance,
                            reason,
                        );
                    }
                }
            }
            Ok(None) => Some(UniversalRingStabilityResult {
                evaluated: false,
                stable: None,
                inhabited_stable: None,
                counterexample_ring: None,
                counterexample_point: BTreeMap::new(),
                counterexample_residuals: vec![],
                dual_number_counterexample: None,
                silence_reason: Some(SilenceReason::UniversalRingOutOfScope {
                    detail: if sets.c_space.is_empty() {
                        "candidate space C_b is empty; no universal-ring test candidate exists"
                            .to_owned()
                    } else {
                        "cannot select rational universal-ring test candidate in non-rational candidate scheme".to_owned()
                    },
                }),
            }),
            Err(reason) => {
                return undetermined_chevalley(
                    coeff_domain,
                    point_domain,
                    checks,
                    provenance,
                    reason,
                );
            }
        }
    } else {
        None
    };

    let verdict = match designated_cls.as_deref() {
        Some("robust_all_pass") => Verdict::Established,
        Some(_) => Verdict::Refuted,
        None if sets.robust_all_pass.is_empty() => Verdict::Refuted,
        None => Verdict::Established,
    };

    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain: PointDomain::AlgebraicClosure,
        applicability: checks,
        provenance,
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: Some(ChevalleyOutcomeDetail {
            goodness_kind: family.inner().goodness.kind(),
            point_domain: PointDomain::AlgebraicClosure,
            effective_image_e: eff_sum,
            p_plus: p_plus_sum,
            p_minus: p_minus_sum,
            robust_all_pass: robust_sum,
            all_fail: fail_sum,
            mixed: mixed_sum,
            empty_realizations: empty_sum,
            designated_candidate_class: designated_cls,
            mixed_witness_pair,
            rational_fiber_probes: probes,
            global_regular_section: global_section,
            universal_ring_contrast: universal_contrast,
        }),
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    }
}

fn undetermined_chevalley(
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    reason: SilenceReason,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict: Verdict::Undetermined(reason),
        coeff_domain,
        point_domain,
        applicability,
        provenance,
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: None,
        chevalley: None,
        observations: None,
        lift: None,
        artin: None,
        diagnostics: None,
        atlas: None,
    }
}

/// Family 全体の構成可能集合分解（`chevalley` と `robustness` 記号経路で共用）。
pub(crate) struct FamilyConstructibleSets {
    pub u_vars: VarOrder,
    pub c_vars: VarOrder,
    pub uc_vars: VarOrder,
    pub u_space: ConstructibleSet,
    pub c_space: ConstructibleSet,
    pub w_total: ConstructibleSet,
    pub effective_image_e: Option<ConstructibleSet>,
    pub w_pass: ConstructibleSet,
    pub w_fail: ConstructibleSet,
    pub p_plus: ConstructibleSet,
    pub p_minus: ConstructibleSet,
    pub robust_all_pass: ConstructibleSet,
    pub all_fail: ConstructibleSet,
    pub mixed: ConstructibleSet,
    pub empty_realizations: ConstructibleSet,
}

pub(crate) fn build_family_constructible_sets(
    family: &CheckedFamilySpec,
    base_value: Option<&[ScalarLit]>,
) -> Result<FamilyConstructibleSets, SilenceReason> {
    let inner = family.inner();
    let domain = family.coeff_domain();
    let u_vars = VarOrder::new(family.u_vars().to_vec()).map_err(map_algebra_silence)?;
    let c_vars = VarOrder::new(family.c_vars().to_vec()).map_err(map_algebra_silence)?;
    let mut uc_names = family.u_vars().to_vec();
    uc_names.extend_from_slice(family.c_vars());
    let uc_vars = VarOrder::new(uc_names).map_err(map_algebra_silence)?;

    let u_bind = ExprBindings::params_only(&u_vars);
    let c_bind = ExprBindings::params_only(&c_vars);

    let mut u_base_eqs = Vec::new();
    let mut c_base_eqs = Vec::new();
    if let Some(bv) = base_value {
        for (q_expr, b_lit) in inner.realizations.reading_q.iter().zip(bv) {
            u_base_eqs.push(
                Poly::from_expr_q(
                    &PolyExpr::diff(q_expr.clone(), PolyExpr::Const(b_lit.clone())),
                    &u_bind,
                )
                .map_err(map_algebra_silence)?,
            );
        }
        for (pi_expr, b_lit) in inner.candidates.pi.iter().zip(bv) {
            c_base_eqs.push(
                Poly::from_expr_q(
                    &PolyExpr::diff(pi_expr.clone(), PolyExpr::Const(b_lit.clone())),
                    &c_bind,
                )
                .map_err(map_algebra_silence)?,
            );
        }
    }

    let u_set = match &inner.realizations.space {
        RealizationSpace::FiniteMembers(members) => {
            let mut acc = ConstructibleSet::empty(u_vars.clone());
            for m in members {
                let (vals, _) = map_scalar_assignments(family.u_vars(), &m.assignments, domain)?;
                let mut eqs: Vec<Poly<Rat>> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        Poly::var(u_vars.len(), i, Rat::zero())
                            .sub(&Poly::constant(u_vars.len(), v.as_rat()))
                    })
                    .collect();
                eqs.extend(u_base_eqs.clone());
                let st = ConstructibleSet::closed(u_vars.clone(), eqs)?;
                acc = acc.union(&st)?;
            }
            acc
        }
        RealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            ..
        } => {
            let mut eqs: Vec<Poly<Rat>> = equations
                .iter()
                .map(|e| Poly::from_expr_q(&e.expr, &u_bind))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            eqs.extend(u_base_eqs);
            let invs: Vec<Poly<Rat>> = invertibles
                .iter()
                .map(|i| Poly::from_expr_q(&i.expr, &u_bind))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            ConstructibleSet::locally_closed(u_vars.clone(), eqs, invs)?
        }
    };

    let c_space = match &inner.candidates.space {
        CandidateSpace::FiniteMembers(members) => {
            let mut acc = ConstructibleSet::empty(c_vars.clone());
            for m in members {
                let (vals, _) = map_scalar_assignments(family.c_vars(), &m.assignments, domain)?;
                let mut eqs: Vec<Poly<Rat>> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        Poly::var(c_vars.len(), i, Rat::zero())
                            .sub(&Poly::constant(c_vars.len(), v.as_rat()))
                    })
                    .collect();
                eqs.extend(c_base_eqs.clone());
                acc = acc.union(&ConstructibleSet::closed(c_vars.clone(), eqs)?)?;
            }
            acc
        }
        CandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            ..
        } => {
            let mut eqs: Vec<Poly<Rat>> = equations
                .iter()
                .map(|e| Poly::from_expr_q(&e.expr, &c_bind))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            eqs.extend(c_base_eqs);
            let invs: Vec<Poly<Rat>> = invertibles
                .iter()
                .map(|i| Poly::from_expr_q(&i.expr, &c_bind))
                .collect::<Result<_, _>>()
                .map_err(map_algebra_silence)?;
            ConstructibleSet::locally_closed(c_vars.clone(), eqs, invs)?
        }
    };

    let u_in_uc = embed_append(&u_set, c_vars.len(), uc_vars.clone())?;
    let c_in_uc = embed_prepend(&c_space, u_vars.len(), uc_vars.clone())?;
    let mut w_total = u_in_uc.intersect(&c_in_uc)?;
    if base_value.is_none() && !inner.realizations.reading_q.is_empty() {
        let uc_bind = ExprBindings::params_only(&uc_vars);
        let mut pull_eqs = Vec::with_capacity(inner.realizations.reading_q.len());
        for (q_expr, pi_expr) in inner
            .realizations
            .reading_q
            .iter()
            .zip(&inner.candidates.pi)
        {
            pull_eqs.push(
                Poly::from_expr_q(&PolyExpr::diff(q_expr.clone(), pi_expr.clone()), &uc_bind)
                    .map_err(map_algebra_silence)?,
            );
        }
        w_total = w_total.intersect(&ConstructibleSet::closed(uc_vars.clone(), pull_eqs)?)?;
    }

    let (e_in_uc, effective_image_e) = match &inner.goodness {
        GoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
        } => {
            let mut e_set = build_direct_constructible(
                equations,
                invertibles,
                preservation.as_ref(),
                &uc_vars,
            )?;
            if raw_sequence.is_some() {
                // raw_sequence が存在する場合は FiniteMembers 上の全判定点を展開して交わる。
                let pt_set = finite_raw_pass_set(family, &w_total, &uc_vars)?;
                e_set = e_set.intersect(&pt_set)?;
            }
            (e_set, None)
        }
        GoodnessSpec::Existential {
            witness_vars,
            equations,
            invertibles,
            preservation,
        } => {
            let mut wuc_names = witness_vars.clone();
            wuc_names.extend(uc_vars.vars().iter().cloned());
            let wuc_vars = VarOrder::new(wuc_names).map_err(map_algebra_silence)?;
            let f_direct = build_direct_constructible(
                equations,
                invertibles,
                preservation.as_ref(),
                &wuc_vars,
            )?;
            let w_lifted = embed_prepend(&w_total, witness_vars.len(), wuc_vars)?;
            let f_total = f_direct.intersect(&w_lifted)?;
            let e_proj = project_constructible_set(&f_total, witness_vars.len(), &uc_vars)?;
            (e_proj.clone(), Some(e_proj))
        }
    };

    let w_pass = w_total.intersect(&e_in_uc)?;
    let w_fail = w_total.difference(&e_in_uc)?;
    let p_plus = project_constructible_set(&w_pass, u_vars.len(), &c_vars)?;
    let p_minus = project_constructible_set(&w_fail, u_vars.len(), &c_vars)?;
    let robust_all_pass = p_plus.difference(&p_minus)?;
    let all_fail = p_minus.difference(&p_plus)?;
    let mixed = p_plus.intersect(&p_minus)?;
    let covered = p_plus.union(&p_minus)?;
    let empty_realizations = c_space.difference(&covered)?;

    Ok(FamilyConstructibleSets {
        u_vars,
        c_vars,
        uc_vars,
        u_space: u_set,
        c_space,
        w_total,
        effective_image_e,
        w_pass,
        w_fail,
        p_plus,
        p_minus,
        robust_all_pass,
        all_fail,
        mixed,
        empty_realizations,
    })
}

fn build_direct_constructible(
    equations: &[NamedPoly],
    invertibles: &[NamedPoly],
    preservation: Option<&PreservationGoodnessSource>,
    vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let bind = ExprBindings::params_only(vars);
    let eqs: Vec<Poly<Rat>> = equations
        .iter()
        .map(|e| Poly::from_expr_q(&e.expr, &bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let invs: Vec<Poly<Rat>> = invertibles
        .iter()
        .map(|i| Poly::from_expr_q(&i.expr, &bind))
        .collect::<Result<_, _>>()
        .map_err(map_algebra_silence)?;
    let base = ConstructibleSet::locally_closed(vars.clone(), eqs, invs)?;
    if let Some(pres_src) = preservation {
        let mut subst = BTreeMap::new();
        for v in vars.vars() {
            subst.insert(v.clone(), PolyExpr::param(v));
        }
        let (pair, _) = substitute_preservation_pair(pres_src, &subst)?;
        let obligations = build_preservation_obligations(&pair)?;
        let locus = compute_preservation_locus_q(&obligations, vars)?;
        let strata: Vec<LocallyClosedStratum> = locus
            .strata
            .into_iter()
            .map(|st| LocallyClosedStratum {
                equations: st.equations,
                invertibles: st.invertibles,
            })
            .collect();
        let pres_set = ConstructibleSet::from_strata(vars.clone(), strata)?;
        return base.intersect(&pres_set);
    }
    Ok(base)
}

fn finite_raw_pass_set(
    family: &CheckedFamilySpec,
    _w_total: &ConstructibleSet,
    uc_vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let RealizationSpace::FiniteMembers(u_ms) = &family.inner().realizations.space else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "raw_sequence_finite_members".to_owned(),
            detail: "raw_sequence Chevalley requires FiniteMembers realizations".to_owned(),
        });
    };
    let domain = family.coeff_domain();
    let mut acc = ConstructibleSet::empty(uc_vars.clone());
    let u_len = family.u_vars().len();
    let mut seen_u_coords: BTreeSet<Vec<Rat>> = BTreeSet::new();
    let zero_vars = VarOrder::new(vec![]).map_err(map_algebra_silence)?;
    let c_list: Vec<EnumCandidate> = match &family.inner().candidates.space {
        CandidateSpace::FiniteMembers(c_ms) => {
            let mut out = Vec::with_capacity(c_ms.len());
            for cm in c_ms {
                let (c_vals, c_disp) =
                    map_scalar_assignments(family.c_vars(), &cm.assignments, domain)?;
                out.push(EnumCandidate {
                    candidate_id: Some(cm.id.clone()),
                    values: c_vals,
                    assignments: c_disp,
                    origin: cm.origin.clone(),
                });
            }
            out
        }
        CandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
        } if family.c_vars().is_empty() => {
            let mut eq_ok = true;
            for eq in equations {
                if !eval_expr_at(&eq.expr, &zero_vars, &[], domain)?.is_zero() {
                    eq_ok = false;
                    break;
                }
            }
            let mut inv_ok = eq_ok;
            if inv_ok {
                for inv in invertibles {
                    if eval_expr_at(&inv.expr, &zero_vars, &[], domain)?.is_zero() {
                        inv_ok = false;
                        break;
                    }
                }
            }
            if inv_ok {
                vec![EnumCandidate {
                    candidate_id: None,
                    values: vec![],
                    assignments: BTreeMap::new(),
                    origin: origin.clone(),
                }]
            } else {
                vec![]
            }
        }
        CandidateSpace::PolynomialScheme { .. } => {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "raw_sequence_finite_candidates".to_owned(),
                detail: "raw_sequence Chevalley with candidate coordinates requires FiniteMembers candidates".to_owned(),
            });
        }
    };
    for um in u_ms {
        let (u_vals, u_disp) = map_scalar_assignments(family.u_vars(), &um.assignments, domain)?;
        let u_rats: Vec<Rat> = u_vals.iter().map(ScalarVal::as_rat).collect();
        if !seen_u_coords.insert(u_rats) {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "raw_sequence_distinct_realization_coords".to_owned(),
                detail: "Chevalley raw_sequence requires distinct realization u coordinates per member presentation".to_owned(),
            });
        }
        let enum_u = EnumRealization {
            member_id: Some(um.id.clone()),
            values: u_vals.clone(),
            assignments: u_disp,
            is_raw_candidate: um.is_raw_candidate,
            origin: um.origin.clone(),
            presentation: um.presentation.clone(),
        };
        for cand in &c_list {
            let w =
                evaluate_goodness_at_point(family, &enum_u, cand, &PointDomain::AlgebraicClosure)?;
            if w.passed {
                let mut eqs: Vec<Poly<Rat>> = (0..u_len)
                    .map(|i| {
                        Poly::var(uc_vars.len(), i, Rat::zero())
                            .sub(&Poly::constant(uc_vars.len(), u_vals[i].as_rat()))
                    })
                    .collect();
                for (j, cv) in cand.values.iter().enumerate() {
                    eqs.push(
                        Poly::var(uc_vars.len(), u_len + j, Rat::zero())
                            .sub(&Poly::constant(uc_vars.len(), cv.as_rat())),
                    );
                }
                acc = acc.union(&ConstructibleSet::closed(uc_vars.clone(), eqs)?)?;
            }
        }
    }
    Ok(acc)
}

fn embed_append(
    set: &ConstructibleSet,
    tail_vars: usize,
    target_vars: VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let n_new = target_vars.len();
    let lift_poly = |p: &Poly<Rat>| -> Poly<Rat> {
        let mut out = Poly::zero(n_new, Rat::zero());
        for (mono, c) in p.terms() {
            let mut exps = mono.exps().to_vec();
            exps.extend(std::iter::repeat_n(0u32, tail_vars));
            out.add_term(Monomial::from_exps(exps), c.clone());
        }
        out
    };
    let strata = set
        .strata()
        .iter()
        .map(|s| LocallyClosedStratum {
            equations: s.equations.iter().map(lift_poly).collect(),
            invertibles: s.invertibles.iter().map(lift_poly).collect(),
        })
        .collect();
    ConstructibleSet::from_strata(target_vars, strata)
}

fn embed_prepend(
    set: &ConstructibleSet,
    head_vars: usize,
    target_vars: VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let strata = set
        .strata()
        .iter()
        .map(|s| LocallyClosedStratum {
            equations: s.equations.iter().map(|p| p.lift_vars(head_vars)).collect(),
            invertibles: s
                .invertibles
                .iter()
                .map(|p| p.lift_vars(head_vars))
                .collect(),
        })
        .collect();
    ConstructibleSet::from_strata(target_vars, strata)
}

fn summarize_region(set: &ConstructibleSet, vars: &VarOrder) -> ChevalleyRegionSummary {
    let strata = set
        .strata()
        .iter()
        .map(|s| {
            (
                display_polys(&s.equations, vars),
                display_polys(&s.invertibles, vars),
            )
        })
        .collect();
    ChevalleyRegionSummary {
        strata,
        is_empty: set.is_empty(),
    }
}

fn resolve_designated_candidate(
    family: &CheckedFamilySpec,
    sets: &FamilyConstructibleSets,
    selector: Option<&CandidateSelector>,
) -> Result<(Option<String>, Option<EnumCandidate>), SilenceReason> {
    let Some(sel) = selector else {
        return Ok((None, None));
    };
    let cand = resolve_candidate_selector(family, sel)?;
    let pt: Vec<Rat> = cand.values.iter().map(ScalarVal::as_rat).collect();
    let cls = if sets.robust_all_pass.contains_point(&pt)? {
        "robust_all_pass"
    } else if sets.all_fail.contains_point(&pt)? {
        "all_fail"
    } else if sets.mixed.contains_point(&pt)? {
        "mixed"
    } else if sets.empty_realizations.contains_point(&pt)? {
        "empty_realizations"
    } else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "designated_candidate_in_candidate_space".to_owned(),
            detail: "designated candidate does not belong to candidate fiber C".to_owned(),
        });
    };
    Ok((Some(cls.to_owned()), Some(cand)))
}

pub(crate) fn resolve_candidate_selector(
    family: &CheckedFamilySpec,
    sel: &CandidateSelector,
) -> Result<EnumCandidate, SilenceReason> {
    let domain = family.coeff_domain();
    match sel {
        CandidateSelector::ById(id) => {
            if let CandidateSpace::FiniteMembers(ms) = &family.inner().candidates.space
                && let Some(m) = ms.iter().find(|m| m.id == *id)
            {
                let (vals, disp) = map_scalar_assignments(family.c_vars(), &m.assignments, domain)?;
                return Ok(EnumCandidate {
                    candidate_id: Some(m.id.clone()),
                    values: vals,
                    assignments: disp,
                    origin: m.origin.clone(),
                });
            }
            Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_candidate_exists".to_owned(),
                detail: format!("unknown candidate id `{id}`"),
            })
        }
        CandidateSelector::ByValues(map) => {
            let mut vals = Vec::with_capacity(family.c_vars().len());
            let mut disp = BTreeMap::new();
            for cname in family.c_vars() {
                let lit =
                    map.get(cname)
                        .ok_or_else(|| SilenceReason::ApplicabilityConditionNotMet {
                            condition: "designated_candidate_complete".to_owned(),
                            detail: format!("missing candidate value `{cname}`"),
                        })?;
                let sv = ScalarVal::from_lit(lit, domain)?;
                disp.insert(cname.clone(), sv.to_display());
                vals.push(sv);
            }
            let origin = default_candidate_origin(
                &family.inner().candidates.space,
                &family.inner().provenance,
            );
            Ok(EnumCandidate {
                candidate_id: None,
                values: vals,
                assignments: disp,
                origin,
            })
        }
    }
}

pub(super) fn default_candidate_origin(space: &CandidateSpace, fallback: &Provenance) -> SourceRef {
    match space {
        CandidateSpace::PolynomialScheme { origin, .. } => origin.clone(),
        CandidateSpace::FiniteMembers(ms) => ms
            .first()
            .map(|m| m.origin.clone())
            .or_else(|| fallback.origins.first().cloned())
            .unwrap_or_else(|| SourceRef::new("candidate", OriginKind::StaticAnalysis)),
    }
}

pub(crate) fn slice_set_at_c(
    uc_set: &ConstructibleSet,
    c_vars: &VarOrder,
    cand: &EnumCandidate,
    u_vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let n_u = u_vars.len();
    let fixed: BTreeMap<usize, Rat> = (0..c_vars.len())
        .map(|j| (n_u + j, cand.values[j].as_rat()))
        .collect();
    let drop_tail = |p: &Poly<Rat>| -> Poly<Rat> {
        let sub = p.partial_eval(&fixed);
        let mut out = Poly::zero(n_u, Rat::zero());
        for (mono, coeff) in sub.terms() {
            out.add_term(
                Monomial::from_exps(mono.exps()[..n_u].to_vec()),
                coeff.clone(),
            );
        }
        out
    };
    let strata = uc_set
        .strata()
        .iter()
        .map(|s| LocallyClosedStratum {
            equations: s.equations.iter().map(drop_tail).collect(),
            invertibles: s.invertibles.iter().map(drop_tail).collect(),
        })
        .collect();
    ConstructibleSet::from_strata(u_vars.clone(), strata)
}
