//! 複数解釈族上の非空性分離・3 量化・全係数移送 $\mathcal{R}(R)$・reading 比較計算核（G-140 E3–E5.1・P7 / G-142 G1–G4）。

use crate::algebra::VarOrder;
use crate::ir::change::PointDomain;
use crate::ir::family::{CandidateSpace, CheckedFamilySpec};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, EmptyWitness, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    CommonQuantifierResult, DesignatedValidityResult, FiberNonEmptinessResult,
    PairEvaluationWitness, PointwiseQuantifierResult, RobustnessOutcomeDetail,
    UniversalRingStabilityResult,
};
use crate::ir::robustness::CheckedRobustnessTask;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::solver::chevalley::resolve_candidate_selector;
use crate::solver::family_direct::{
    check_family_presentations_applicability, evaluate_goodness_at_point,
};
use crate::solver::family_eval::{
    CandidateFiberEnum, DEFAULT_MAX_ENUM_POINTS, EnumCandidate, EnumRealization,
    RealizationFiberEnum, ScalarVal, collect_family_origins, enumerate_candidates_for_base,
    enumerate_realizations_for_base, eval_expr_at, map_scalar_assignments, scalar_eq,
};
use crate::solver::preservation::map_algebra_silence;
use crate::solver::robustness_reading::compute_reading_comparison;
use crate::solver::robustness_symbolic::{QuantifiersTuple, eval_symbolic_closure_quantifiers};
use crate::solver::robustness_universal::evaluate_universal_ring;

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
            &real_enum,
            &cand_enum,
            designated.as_ref(),
        );
    }

    // 3. 有限列挙 fiber か代数閉包記号 scheme かで 3 量化を算出する。
    let (valid_des, pointwise, common, common_cand, symbolic_silenced) =
        match (&real_enum, &cand_enum) {
            (RealizationFiberEnum::Finite(u_list), CandidateFiberEnum::Finite(c_list)) => {
                match eval_finite_quantifiers(
                    family,
                    u_list,
                    c_list,
                    designated.as_ref(),
                    &point_domain,
                ) {
                    Ok((vd, pw, cm, cc_opt)) => (vd, Some(pw), Some(cm), cc_opt, None),
                    Err(reason) => (None, None, None, None, Some(reason)),
                }
            }
            _ => match eval_symbolic_closure_quantifiers(
                family,
                task.base_value(),
                designated.as_ref(),
                &point_domain,
            ) {
                Ok((vd, pw, cm, cc_opt)) => (vd, Some(pw), Some(cm), cc_opt, None),
                Err(reason) => (None, None, None, None, Some(reason)),
            },
        };
    if let Some(reason) = symbolic_silenced {
        return undetermined_robustness(coeff_domain, point_domain, checks, provenance, reason);
    }

    // 4. 全係数移送安定性 R(R) / R_dec(R)（G-140 E5 / G-142 G3 / W6 / M3）。
    let universal_ring = if task.check_universal_ring() {
        match evaluate_universal_for_task(
            family,
            task.base_value(),
            &cand_enum,
            designated.as_ref(),
            true,
        ) {
            Ok(ur) => ur,
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
        common_cand.as_ref(),
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
    let origins = collect_family_origins(family);
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
    if *task.point_domain() == PointDomain::UniversalRing {
        let reason = SilenceReason::UniversalRingOutOfScope {
            detail: "shigure_robustness point quantifiers cannot run with point_domain = universal_ring; use check_universal_ring: true for R(R) base-change stability".to_owned(),
        };
        checks.push(ApplicabilityCheck::failed(
            "point_quantifier_domain_concrete",
            MathClause::G140E5,
            reason.code(),
        ));
        return Err(reason);
    }
    check_family_presentations_applicability(task.family(), checks)
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
        if !scalar_eq(
            &eval_expr_at(pi_expr, &c_vars, &cand.values, domain)?,
            b_val,
        ) {
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
    } else if let CandidateSpace::FiniteMembers(ms) = &family.inner().candidates.space
        && matches!(sel, crate::ir::robustness::CandidateSelector::ByValues(_))
    {
        let matched = ms.iter().any(|m| {
            map_scalar_assignments(family.c_vars(), &m.assignments, domain).is_ok_and(
                |(vals, _)| {
                    vals.len() == cand.values.len()
                        && vals.iter().zip(&cand.values).all(|(a, b)| scalar_eq(a, b))
                },
            )
        });
        if !matched {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "designated_candidate_in_candidate_space".to_owned(),
                detail: "designated candidate values do not match any FiniteMembers candidate"
                    .to_owned(),
            });
        }
    }
    Ok(cand)
}

fn evaluate_universal_for_task(
    family: &CheckedFamilySpec,
    base_value: &[crate::ir::term::ScalarLit],
    cand_enum: &CandidateFiberEnum,
    designated: Option<&EnumCandidate>,
    fiber_non_empty: bool,
) -> Result<Option<UniversalRingStabilityResult>, SilenceReason> {
    if let Some(dc) = designated {
        return evaluate_universal_ring(family, base_value, dc, fiber_non_empty).map(Some);
    }
    match cand_enum {
        CandidateFiberEnum::Finite(cs) if cs.is_empty() => Ok(None),
        CandidateFiberEnum::Finite(cs) => {
            let mut first_fail: Option<UniversalRingStabilityResult> = None;
            for c in cs {
                let ur = evaluate_universal_ring(family, base_value, c, fiber_non_empty)?;
                if let Some(sr) = &ur.silence_reason {
                    return Err(sr.clone());
                }
                if ur.stable == Some(true) {
                    return Ok(Some(ur));
                }
                if first_fail.is_none() {
                    first_fail = Some(ur);
                }
            }
            Ok(first_fail)
        }
        CandidateFiberEnum::NonFiniteScheme => Err(SilenceReason::UniversalRingOutOfScope {
            detail: "check_universal_ring with non-finite candidate scheme requires explicit designated_candidate".to_owned(),
        }),
    }
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
    mut checks: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    fiber_non_empty: FiberNonEmptinessResult,
    real_enum: &RealizationFiberEnum,
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
    let universal_ring = if task.check_universal_ring() {
        match evaluate_universal_for_task(family, task.base_value(), cand_enum, designated, false) {
            Ok(ur) => ur,
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
    };
    if let Some(ur) = &universal_ring
        && let Some(sr) = ur.silence_reason.clone()
    {
        return undetermined_robustness(coeff_domain, point_domain, checks, provenance, sr);
    }

    let reading_comparison = match compute_reading_comparison(
        task,
        family,
        real_enum,
        cand_enum,
        designated,
        &valid_designated,
        &common_candidate,
        None,
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
            reading_comparison,
        }),
        chevalley: None,
        observations: None,
    }
}

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

    let (common, common_cand_out) = if let Some((c, ws)) = chosen_common {
        (
            CommonQuantifierResult {
                satisfied: true,
                vacuously_true_empty_fiber: false,
                candidate_id: c.candidate_id.clone(),
                candidate_assignments: Some(c.assignments.clone()),
                witnesses: ws,
                counterexample_witnesses: vec![],
                counterexample_detail: None,
            },
            Some(c.clone()),
        )
    } else {
        (
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
            },
            None,
        )
    };

    Ok((valid_des, pointwise, common, common_cand_out))
}
