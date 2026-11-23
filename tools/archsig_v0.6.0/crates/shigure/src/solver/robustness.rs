//! 複数解釈族上の非空性分離・3 量化・全係数移送 $\mathcal{R}(R)$・reading 比較計算核（G-140 E3–E5.1・P7 / G-142 G1–G4）。

use crate::algebra::{ConstructibleSet, LocallyClosedStratum, Poly, Rat, VarOrder};
use crate::ir::change::PointDomain;
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, GoodnessSpec, RealizationSpace};
use crate::ir::provenance::{MathClause, OriginKind, Provenance, SourceRef};
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    CommonQuantifierResult, DesignatedValidityResult, FiberNonEmptinessResult,
    PairEvaluationWitness, PointwiseQuantifierResult, RealizationWitness, RobustnessOutcomeDetail,
};
use crate::ir::robustness::CheckedRobustnessTask;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::chevalley::{
    FamilyConstructibleSets, build_family_constructible_sets, resolve_candidate_selector,
};
use crate::solver::chevalley_sections::pick_rational_point_in_stratum;
use crate::solver::context::collect_presentation_params;
use crate::solver::family_direct::evaluate_goodness_at_point;
use crate::solver::family_eval::{
    CandidateFiberEnum, DEFAULT_MAX_ENUM_POINTS, EnumCandidate, EnumRealization,
    RealizationFiberEnum, ScalarVal, build_assignment_map, enumerate_candidates_for_base,
    enumerate_realizations_for_base, eval_expr_at,
};
use crate::solver::preservation::map_algebra_silence;
use crate::solver::robustness_reading::compute_reading_comparison;
use crate::solver::robustness_universal::evaluate_universal_ring;
use std::collections::BTreeMap;

/// `shigure_robustness` の計算核入口（G-140 E3–E5.1・P7 / G-142 G1–G4）。
pub fn solve_robustness_task(task: &CheckedRobustnessTask) -> ShigureOutcome {
    let family = task.family();
    let coeff_domain = family.coeff_domain().clone();
    let point_domain = task.point_domain().clone();
    let mut provenance = build_robustness_provenance(family);
    let mut checks = Vec::new();

    if let Err(reason) = check_robustness_applicability(task, &mut checks) {
        return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
    }

    let (real_enum, empty_w) = match enumerate_realizations_for_base(
        family,
        task.base_value(),
        &point_domain,
        DEFAULT_MAX_ENUM_POINTS,
    ) {
        Ok(res) => res,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "realization_fiber_decidable",
                MathClause::G140E4,
                reason.code(),
            ));
            return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let cand_enum = match enumerate_candidates_for_base(
        family,
        task.base_value(),
        &point_domain,
        DEFAULT_MAX_ENUM_POINTS,
    ) {
        Ok(res) => res,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "candidate_fiber_decidable",
                MathClause::G140E4,
                reason.code(),
            ));
            return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let designated = match task.designated_candidate() {
        Some(sel) => {
            match resolve_and_check_cand_fiber(family, task.base_value(), sel, &point_domain) {
                Ok(c) => {
                    if !provenance.origins.contains(&c.origin) {
                        provenance.origins.push(c.origin.clone());
                    }
                    Some(c)
                }
                Err(reason) => {
                    checks.push(ApplicabilityCheck::failed(
                        "designated_candidate_in_fiber",
                        MathClause::G140E4,
                        reason.code(),
                    ));
                    return undetermined_robustness(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        reason,
                    );
                }
            }
        }
        None => None,
    };

    // 1. 整合実現 fiber の非空性を独立分離して判定（空虚な真との混同防止）。
    let fiber_non_empty = build_fiber_non_emptiness(&real_enum, empty_w);
    if fiber_non_empty.non_empty {
        checks.push(ApplicabilityCheck::passed(
            "realization_fiber_non_empty",
            MathClause::G142G2,
        ));
    } else {
        checks.push(ApplicabilityCheck::failed(
            "realization_fiber_non_empty",
            MathClause::G142G2,
            "empty_realizations",
        ));
    }

    // 2. 空 fiber の場合: 3 量化と全係数移送を計算して記録し、全体判定は必ず Refuted とする。
    if !fiber_non_empty.non_empty {
        return finish_empty_fiber_outcome(
            task,
            family,
            coeff_domain,
            point_domain,
            checks,
            provenance,
            fiber_non_empty,
            &cand_enum,
            designated.as_ref(),
        );
    }

    // 3. 有限列挙 fiber か代数閉包記号 scheme かで 3 量化を算出する。
    let (valid_des, pointwise, common, symbolic_silenced) = match (&real_enum, &cand_enum) {
        (RealizationFiberEnum::Finite(u_list), CandidateFiberEnum::Finite(c_list)) => {
            match eval_finite_quantifiers(
                family,
                u_list,
                c_list,
                designated.as_ref(),
                &point_domain,
            ) {
                Ok((vd, pw, cm)) => (vd, Some(pw), Some(cm), None),
                Err(reason) => (None, None, None, Some(reason)),
            }
        }
        _ => match eval_symbolic_closure_quantifiers(
            family,
            task.base_value(),
            designated.as_ref(),
            &point_domain,
        ) {
            Ok((vd, pw, cm)) => (vd, Some(pw), Some(cm), None),
            Err(reason) => (None, None, None, Some(reason)),
        },
    };
    if let Some(reason) = symbolic_silenced {
        return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
    }

    // 4. 全係数移送安定性 R(R) / R_dec(R)（G-140 E5 / G-142 G3 / W6）。
    let universal_ring = if task.check_universal_ring() {
        let ur_cand = designated.clone().or_else(|| match &cand_enum {
            CandidateFiberEnum::Finite(cs) if cs.len() == 1 => Some(cs[0].clone()),
            _ => None,
        });
        if let Some(cand) = ur_cand {
            match evaluate_universal_ring(family, task.base_value(), &cand, true) {
                Ok(ur) => Some(ur),
                Err(reason) => {
                    return undetermined_robustness(
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
        }
    } else {
        None
    };

    // 5. 粗/細 reading 比較・P7 raw 残差（E5.1 / G4 / P7）。
    let reading_comparison = match compute_reading_comparison(
        task,
        family,
        &real_enum,
        &cand_enum,
        designated.as_ref(),
        &valid_des,
        &common,
        &point_domain,
    ) {
        Ok(rc) => rc,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "reading_comparison_valid",
                MathClause::G140E5Dot1,
                reason.code(),
            ));
            return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    // 6. 全体の Verdict 統合。
    if let Some(ur) = &universal_ring
        && ur.silence_reason.is_some()
        && let Some(sr) = ur.silence_reason.clone()
    {
        return undetermined_robustness(coeff_domain, point_domain, checks, provenance, sr);
    }
    let ur_failed = universal_ring
        .as_ref()
        .is_some_and(|ur| ur.stable == Some(false));
    let verdict = if ur_failed {
        Verdict::Refuted
    } else if let Some(vd) = &valid_des {
        if vd.satisfied {
            Verdict::Established
        } else {
            Verdict::Refuted
        }
    } else if let Some(cm) = &common {
        if cm.satisfied {
            Verdict::Established
        } else {
            Verdict::Refuted
        }
    } else {
        Verdict::Refuted
    };

    ShigureOutcome {
        verdict,
        coeff_domain,
        point_domain,
        applicability: checks,
        provenance,
        residual_ideal: vec![],
        empty_witness: None,
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: Some(RobustnessOutcomeDetail {
            goodness_kind: family.inner().goodness.kind(),
            fiber_non_empty,
            valid_designated: valid_des,
            pointwise,
            common_candidate: common,
            universal_ring,
            reading_comparison,
        }),
        chevalley: None,
        observations: None,
    }
}

fn build_robustness_provenance(family: &CheckedFamilySpec) -> Provenance {
    let mut origins = family.inner().provenance.origins.clone();
    match &family.inner().realizations.space {
        RealizationSpace::FiniteMembers(ms) => {
            for m in ms {
                origins.push(m.origin.clone());
            }
        }
        RealizationSpace::PolynomialScheme { origin, .. } => origins.push(origin.clone()),
    }
    let mut clauses = vec![
        MathClause::G140E3,
        MathClause::G140E4,
        MathClause::G142G1,
        MathClause::G142G2,
    ];
    if family.reading_comparison().is_some() {
        clauses.push(MathClause::G140E5Dot1);
        clauses.push(MathClause::G142G4);
    }
    Provenance::new(origins, clauses)
}

fn check_robustness_applicability(
    task: &CheckedRobustnessTask,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(), SilenceReason> {
    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return Err(SilenceReason::UnobservedDependency { slots: missing });
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::G140P0Dot1,
    ));

    if let RealizationSpace::FiniteMembers(ms) = &task.family().inner().realizations.space {
        for m in ms {
            if let Some(pres) = &m.presentation {
                for s in &pres.sorts {
                    if s.rank != 1 {
                        return Err(SilenceReason::ApplicabilityConditionNotMet {
                            condition: "sort_rank_one_required".to_owned(),
                            detail: format!("sort `{}` in `{}` has rank != 1", s.name, pres.name),
                        });
                    }
                }
            }
        }
    }
    if let GoodnessSpec::Direct {
        preservation: Some(src),
        ..
    }
    | GoodnessSpec::Existential {
        preservation: Some(src),
        ..
    } = &task.family().inner().goodness
    {
        for pres in [&src.pair.before, &src.pair.after] {
            for s in &pres.sorts {
                if s.rank != 1 {
                    return Err(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "sort_rank_one_required".to_owned(),
                        detail: format!("sort `{}` in `{}` has rank != 1", s.name, pres.name),
                    });
                }
            }
        }
        if !collect_presentation_params(&src.pair.before).is_empty() {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "before_presentation_must_be_parameter_free".to_owned(),
                detail: "reference presentation `before` must not contain search parameters"
                    .to_owned(),
            });
        }
    }
    checks.push(ApplicabilityCheck::passed(
        "family_presentations_well_formed",
        MathClause::G139P0P1,
    ));
    Ok(())
}

fn undetermined_robustness(
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
    }
}

fn resolve_and_check_cand_fiber(
    family: &CheckedFamilySpec,
    base_value: &[ScalarLit],
    sel: &crate::ir::robustness::CandidateSelector,
    point_domain: &PointDomain,
) -> Result<EnumCandidate, SilenceReason> {
    let cand = resolve_candidate_selector(family, sel)?;
    let domain = family.coeff_domain();
    let c_vars = VarOrder::new(family.c_vars().to_vec()).map_err(map_algebra_silence)?;
    let target_b: Vec<ScalarVal> = base_value
        .iter()
        .map(|l| ScalarVal::from_lit(l, domain))
        .collect::<Result<_, _>>()?;
    for (pi_expr, b_val) in family.inner().candidates.pi.iter().zip(&target_b) {
        if &eval_expr_at(pi_expr, &c_vars, &cand.values, domain)? != b_val {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_candidate_in_base_fiber".to_owned(),
                detail: "designated candidate projection pi(c) does not match base_value"
                    .to_owned(),
            });
        }
    }
    if let CandidateSpace::PolynomialScheme {
        equations,
        invertibles,
        ..
    } = &family.inner().candidates.space
    {
        for eq in equations {
            if !eval_expr_at(&eq.expr, &c_vars, &cand.values, domain)?.is_zero() {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "designated_candidate_in_candidate_space".to_owned(),
                    detail: format!(
                        "designated candidate violates candidate equation `{}`",
                        eq.name
                    ),
                });
            }
        }
        for inv in invertibles {
            let v = eval_expr_at(&inv.expr, &c_vars, &cand.values, domain)?;
            let ok = match point_domain {
                PointDomain::IntegerPoints => v.is_unit(),
                _ => !v.is_zero(),
            };
            if !ok {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "designated_candidate_in_candidate_space".to_owned(),
                    detail: format!(
                        "designated candidate violates candidate invertible `{}`",
                        inv.name
                    ),
                });
            }
        }
    }
    Ok(cand)
}

fn build_fiber_non_emptiness(
    real_enum: &RealizationFiberEnum,
    empty_witness: Option<EmptyWitness>,
) -> FiberNonEmptinessResult {
    match real_enum {
        RealizationFiberEnum::Finite(list) => {
            if let Some(first) = list.first() {
                FiberNonEmptinessResult {
                    non_empty: true,
                    status: "non_empty".to_owned(),
                    witness: Some(first.to_witness()),
                    empty_witness: None,
                }
            } else {
                FiberNonEmptinessResult {
                    non_empty: false,
                    status: "empty_realizations".to_owned(),
                    witness: None,
                    empty_witness,
                }
            }
        }
        RealizationFiberEnum::NonFiniteScheme { sample_witness } => FiberNonEmptinessResult {
            non_empty: true,
            status: "non_empty".to_owned(),
            witness: sample_witness.clone(),
            empty_witness: None,
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_empty_fiber_outcome(
    task: &CheckedRobustnessTask,
    family: &CheckedFamilySpec,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    fiber_non_empty: FiberNonEmptinessResult,
    cand_enum: &CandidateFiberEnum,
    designated: Option<&EnumCandidate>,
) -> ShigureOutcome {
    let valid_designated = designated.map(|c| DesignatedValidityResult {
        candidate_id: c.candidate_id.clone(),
        candidate_assignments: c.assignments.clone(),
        satisfied: true,
        vacuously_true_empty_fiber: true,
        supporting_witnesses: vec![],
        counterexample: None,
    });
    let pointwise = Some(PointwiseQuantifierResult {
        satisfied: true,
        vacuously_true_empty_fiber: true,
        witnesses: vec![],
        counterexample: None,
    });
    let first_cand = match cand_enum {
        CandidateFiberEnum::Finite(cs) => cs.first().cloned(),
        CandidateFiberEnum::NonFiniteScheme => designated.cloned(),
    };
    let common_candidate = Some(CommonQuantifierResult {
        satisfied: first_cand.is_some() || matches!(cand_enum, CandidateFiberEnum::NonFiniteScheme),
        vacuously_true_empty_fiber: true,
        candidate_id: first_cand.as_ref().and_then(|c| c.candidate_id.clone()),
        candidate_assignments: first_cand.map(|c| c.assignments),
        witnesses: vec![],
        counterexample_witnesses: vec![],
        counterexample_detail: if matches!(cand_enum, CandidateFiberEnum::Finite(cs) if cs.is_empty())
        {
            Some("candidate fiber C_b is empty".to_owned())
        } else {
            None
        },
    });
    let universal_ring = if task.check_universal_ring()
        && let Some(cand) = designated
    {
        evaluate_universal_ring(family, task.base_value(), cand, false).ok()
    } else {
        None
    };

    ShigureOutcome {
        verdict: Verdict::Refuted,
        coeff_domain,
        point_domain,
        applicability: checks,
        provenance,
        residual_ideal: vec![],
        empty_witness: fiber_non_empty.empty_witness.clone(),
        restored: None,
        interaction: None,
        diagram: None,
        path: None,
        transfer: None,
        robustness: Some(RobustnessOutcomeDetail {
            goodness_kind: family.inner().goodness.kind(),
            fiber_non_empty,
            valid_designated,
            pointwise,
            common_candidate,
            universal_ring,
            reading_comparison: None,
        }),
        chevalley: None,
        observations: None,
    }
}

type QuantifiersTuple = (
    Option<DesignatedValidityResult>,
    PointwiseQuantifierResult,
    CommonQuantifierResult,
);

fn eval_finite_quantifiers(
    family: &CheckedFamilySpec,
    u_list: &[EnumRealization],
    c_list: &[EnumCandidate],
    designated: Option<&EnumCandidate>,
    point_domain: &PointDomain,
) -> Result<QuantifiersTuple, SilenceReason> {
    let valid_des = if let Some(dc) = designated {
        let mut witnesses = Vec::with_capacity(u_list.len());
        let mut first_fail = None;
        for u in u_list {
            let w = evaluate_goodness_at_point(family, u, dc, point_domain)?;
            if !w.passed && first_fail.is_none() {
                first_fail = Some(w.clone());
            }
            witnesses.push(w);
        }
        Some(DesignatedValidityResult {
            candidate_id: dc.candidate_id.clone(),
            candidate_assignments: dc.assignments.clone(),
            satisfied: first_fail.is_none(),
            vacuously_true_empty_fiber: false,
            supporting_witnesses: witnesses.into_iter().filter(|w| w.passed).collect(),
            counterexample: first_fail,
        })
    } else {
        None
    };

    let mut pw_witnesses = Vec::with_capacity(u_list.len());
    let mut pw_fail = None;
    for u in u_list {
        let mut found = None;
        for c in c_list {
            let w = evaluate_goodness_at_point(family, u, c, point_domain)?;
            if w.passed {
                found = Some(w);
                break;
            }
        }
        if let Some(w) = found {
            pw_witnesses.push(w);
        } else {
            pw_fail = Some(u.to_witness());
            break;
        }
    }
    let pointwise = PointwiseQuantifierResult {
        satisfied: pw_fail.is_none(),
        vacuously_true_empty_fiber: false,
        witnesses: if pw_fail.is_none() {
            pw_witnesses
        } else {
            vec![]
        },
        counterexample: pw_fail,
    };

    let mut chosen_common: Option<(&EnumCandidate, Vec<PairEvaluationWitness>)> = None;
    let mut cand_fails = Vec::new();
    for c in c_list {
        let mut all_w = Vec::with_capacity(u_list.len());
        let mut failed_w = None;
        for u in u_list {
            let w = evaluate_goodness_at_point(family, u, c, point_domain)?;
            if !w.passed {
                failed_w = Some(w);
                break;
            }
            all_w.push(w);
        }
        if let Some(fw) = failed_w {
            cand_fails.push(fw);
        } else {
            chosen_common = Some((c, all_w));
            break;
        }
    }

    let common = if let Some((c, ws)) = chosen_common {
        CommonQuantifierResult {
            satisfied: true,
            vacuously_true_empty_fiber: false,
            candidate_id: c.candidate_id.clone(),
            candidate_assignments: Some(c.assignments.clone()),
            witnesses: ws,
            counterexample_witnesses: vec![],
            counterexample_detail: None,
        }
    } else {
        CommonQuantifierResult {
            satisfied: false,
            vacuously_true_empty_fiber: false,
            candidate_id: None,
            candidate_assignments: None,
            witnesses: vec![],
            counterexample_witnesses: cand_fails,
            counterexample_detail: Some(if c_list.is_empty() {
                "candidate fiber C_b is empty".to_owned()
            } else {
                "no candidate in C_b succeeds across all realizations in U_b".to_owned()
            }),
        }
    };

    Ok((valid_des, pointwise, common))
}

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
            out.add_term(
                crate::algebra::Monomial::from_exps(reordered),
                coeff.clone(),
            );
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

fn eval_symbolic_closure_quantifiers(
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

    let valid_des = if let Some(dc) = designated {
        let pt: Vec<Rat> = dc.values.iter().map(ScalarVal::as_rat).collect();
        let sat = sets.robust_all_pass.contains_point(&pt)?;
        Some(DesignatedValidityResult {
            candidate_id: dc.candidate_id.clone(),
            candidate_assignments: dc.assignments.clone(),
            satisfied: sat,
            vacuously_true_empty_fiber: false,
            supporting_witnesses: vec![],
            counterexample: (!sat).then(|| PairEvaluationWitness {
                realization: RealizationWitness {
                    member_id: None,
                    assignments: BTreeMap::from([(
                        "fiber".to_owned(),
                        "non-passing geometric point exists in W_fail".to_owned(),
                    )]),
                    is_raw_candidate: false,
                    origin: real_origin.clone(),
                },
                candidate_id: dc.candidate_id.clone(),
                candidate_assignments: dc.assignments.clone(),
                passed: false,
                legal_execution_exists: None,
                residuals: vec!["W_fail non-empty for designated candidate".to_owned()],
                empty_witness: None,
                restored_completion: None,
            }),
        })
    } else {
        None
    };

    // W_total, W_pass は [u_vars, c_vars] 順なので [c_vars, u_vars] へ並べ替えて先頭 |C| 変数を消去する。
    let mut cu_names = sets.c_vars.vars().to_vec();
    cu_names.extend(sets.u_vars.vars().iter().cloned());
    let cu_vars = VarOrder::new(cu_names).map_err(map_algebra_silence)?;
    let w_total_cu = swap_uc_to_cu(&sets.w_total, sets.u_vars.len(), &cu_vars)?;
    let w_pass_cu = swap_uc_to_cu(&sets.w_pass, sets.u_vars.len(), &cu_vars)?;
    let u_proj_total =
        crate::algebra::project_constructible_set(&w_total_cu, sets.c_vars.len(), &sets.u_vars)?;
    let u_proj_pass =
        crate::algebra::project_constructible_set(&w_pass_cu, sets.c_vars.len(), &sets.u_vars)?;
    let pw_uncovered = u_proj_total.difference(&u_proj_pass)?;

    let pointwise = PointwiseQuantifierResult {
        satisfied: pw_uncovered.is_empty(),
        vacuously_true_empty_fiber: false,
        witnesses: vec![],
        counterexample: (!pw_uncovered.is_empty()).then(|| RealizationWitness {
            member_id: None,
            assignments: BTreeMap::from([(
                "uncovered_u".to_owned(),
                "geometric u exists without satisfying c".to_owned(),
            )]),
            is_raw_candidate: false,
            origin: real_origin,
        }),
    };

    let common_sat = !sets.robust_all_pass.is_empty();
    let cand_assign = if common_sat {
        if sets.c_vars.is_empty() {
            Some(BTreeMap::new())
        } else if let Some(first_st) = sets.robust_all_pass.strata().first()
            && let Some(pt) = pick_rational_point_in_stratum(first_st, &sets.c_vars)?
        {
            let vals: Vec<ScalarVal> = pt.into_iter().map(ScalarVal::Q).collect();
            Some(build_assignment_map(sets.c_vars.vars(), &vals))
        } else {
            let geom: BTreeMap<String, String> = sets
                .c_vars
                .vars()
                .iter()
                .map(|c| (c.clone(), format!("geom_point({c})")))
                .collect();
            Some(geom)
        }
    } else {
        None
    };
    let common = CommonQuantifierResult {
        satisfied: common_sat,
        vacuously_true_empty_fiber: false,
        candidate_id: None,
        candidate_assignments: cand_assign,
        witnesses: vec![],
        counterexample_witnesses: vec![],
        counterexample_detail: (!common_sat)
            .then(|| "Chevalley robust_all_pass (P_+ \\ P_-) is empty over closure".to_owned()),
    };

    Ok((valid_des, pointwise, common))
}
