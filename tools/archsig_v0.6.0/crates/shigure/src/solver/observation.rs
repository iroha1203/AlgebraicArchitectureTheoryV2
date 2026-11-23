//! 追加観測の kernel 条件検査・全包含極小十分観測集合の列挙計算核（G-142 G5–G6 / W4・W6）。

use crate::algebra::VarOrder;
use crate::ir::change::PointDomain;
use crate::ir::family::{FamilySpec, RealizationSpace};
use crate::ir::observation::CheckedObservationTask;
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase3::{
    CostRankedObservationSet, DistinguishingPairSummary, InsufficiencyWitness,
    LawReadoutAdequacyComparison, MinimalObservationSet, ObservationOutcomeDetail,
    RemovalCounterexample,
};
use crate::ir::term::CoeffDomain;
use crate::solver::family_direct::{
    check_family_presentations_applicability, evaluate_goodness_at_point,
};
use crate::solver::family_eval::{
    CandidateFiberEnum, EnumRealization, RealizationFiberEnum, ScalarVal,
    enumerate_candidates_for_base, enumerate_realizations_for_base, eval_expr_at,
};
use crate::solver::preservation::map_algebra_silence;
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::BTreeMap;

pub const DEFAULT_MAX_OBS_REALIZATIONS: usize = 256;
pub const DEFAULT_MAX_OBS_CANDIDATES: usize = 256;
pub const DEFAULT_MAX_OBS_INDICES: usize = 16;
pub const DEFAULT_MAX_SUBSET_STEPS: usize = 65_536;

/// `shigure_observations` の計算核入口（G-142 G5–G6）。
pub fn solve_observation_task(task: &CheckedObservationTask) -> ShigureOutcome {
    let family = task.family();
    let coeff_domain = family.coeff_domain().clone();
    let point_domain = task.point_domain().clone();
    let provenance = build_obs_provenance(task, family.inner());
    let mut checks = Vec::new();

    let missing = task.unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::G140P0Dot1,
            format!("missing slots: {}", missing.join(", ")),
        ));
        return undetermined_obs(
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

    if task.observations().len() > DEFAULT_MAX_OBS_INDICES {
        let reason = SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!(
                "candidate observation count {} exceeds enumeration index limit ({DEFAULT_MAX_OBS_INDICES})",
                task.observations().len()
            ),
        };
        checks.push(ApplicabilityCheck::failed(
            "observation_indices_within_limit",
            MathClause::G142G6,
            reason.code(),
        ));
        return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
    }
    checks.push(ApplicabilityCheck::passed(
        "observation_indices_within_limit",
        MathClause::G142G6,
    ));

    if let Err(reason) = check_family_presentations_applicability(family, &mut checks) {
        return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
    }

    let u_list = match enumerate_realizations_for_base(
        family,
        task.base_value(),
        &point_domain,
        DEFAULT_MAX_OBS_REALIZATIONS,
    ) {
        Ok((RealizationFiberEnum::Finite(us), _)) => us,
        Ok((RealizationFiberEnum::NonFiniteScheme { .. }, _)) => {
            let reason = SilenceReason::FiniteEnumerationOutOfScope {
                detail: "minimal observation enumeration requires a finitely enumerable realization fiber U_b".to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "realization_fiber_finite",
                MathClause::G142G6,
                reason.code(),
            ));
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "realization_fiber_finite",
                MathClause::G142G6,
                reason.code(),
            ));
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let c_list = match enumerate_candidates_for_base(
        family,
        task.base_value(),
        &point_domain,
        DEFAULT_MAX_OBS_CANDIDATES,
    ) {
        Ok(CandidateFiberEnum::Finite(cs)) => cs,
        Ok(CandidateFiberEnum::NonFiniteScheme) => {
            let reason = SilenceReason::FiniteEnumerationOutOfScope {
                detail: "minimal observation enumeration requires a finitely enumerable candidate fiber C_b".to_owned(),
            };
            checks.push(ApplicabilityCheck::failed(
                "candidate_fiber_finite",
                MathClause::G142G6,
                reason.code(),
            ));
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "candidate_fiber_finite",
                MathClause::G142G6,
                reason.code(),
            ));
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "finite_enumeration_within_limit",
        MathClause::G142G6,
    ));

    let u_vars = match VarOrder::new(family.u_vars().to_vec()) {
        Ok(v) => v,
        Err(e) => {
            return undetermined_obs(
                coeff_domain,
                point_domain,
                checks,
                provenance,
                map_algebra_silence(e),
            );
        }
    };

    let obs_decls = task.observations();
    let m_obs = obs_decls.len();
    let mut obs_matrix: Vec<Vec<Vec<ScalarVal>>> = Vec::with_capacity(u_list.len());
    for u in &u_list {
        let mut row = Vec::with_capacity(m_obs);
        for decl in obs_decls {
            let vals = match decl
                .components
                .iter()
                .map(|c| eval_expr_at(&c.expr, &u_vars, &u.values, &coeff_domain))
                .collect::<Result<Vec<_>, _>>()
            {
                Ok(v) => v,
                Err(reason) => {
                    return undetermined_obs(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        reason,
                    );
                }
            };
            row.push(vals);
        }
        obs_matrix.push(row);
    }

    let mut chi_table: Vec<Vec<bool>> = vec![vec![false; c_list.len()]; u_list.len()];
    for (ui, u) in u_list.iter().enumerate() {
        for (ci, c) in c_list.iter().enumerate() {
            match evaluate_goodness_at_point(family, u, c, &point_domain) {
                Ok(w) => chi_table[ui][ci] = w.passed,
                Err(reason) => {
                    return undetermined_obs(
                        coeff_domain,
                        point_domain,
                        checks,
                        provenance,
                        reason,
                    );
                }
            }
        }
    }

    // 異判定対 D_R と各対の分離添字ビットマスク D_d を生成する。
    let mut pairs: Vec<(u16, DistinguishingPairSummary)> = Vec::new();
    let mut first_insuff: Option<(usize, usize, DistinguishingPairSummary)> = None;
    for ci in 0..c_list.len() {
        for ua in 0..u_list.len() {
            for ub in (ua + 1)..u_list.len() {
                if chi_table[ua][ci] == chi_table[ub][ci] {
                    continue;
                }
                let (pass_idx, fail_idx) = if chi_table[ua][ci] {
                    (ua, ub)
                } else {
                    (ub, ua)
                };
                let mut d_mask: u16 = 0;
                let mut sep_ids = Vec::new();
                for (oi, decl) in obs_decls.iter().enumerate() {
                    if obs_matrix[pass_idx][oi] != obs_matrix[fail_idx][oi] {
                        d_mask |= 1u16 << oi;
                        sep_ids.push(decl.id.clone());
                    }
                }
                let summary = DistinguishingPairSummary {
                    u_pass: u_list[pass_idx].to_witness(),
                    u_fail: u_list[fail_idx].to_witness(),
                    candidate_id: c_list[ci].candidate_id.clone(),
                    candidate_assignments: c_list[ci].assignments.clone(),
                    separating_observations: sep_ids,
                };
                if d_mask == 0 && first_insuff.is_none() {
                    first_insuff = Some((pass_idx, fail_idx, summary.clone()));
                }
                pairs.push((d_mask, summary));
            }
        }
    }

    let law_readout_cmp = match compute_law_readout_comparison(
        task,
        &u_vars,
        &u_list,
        &coeff_domain,
        pairs.is_empty(),
    ) {
        Ok(cmp) => cmp,
        Err(reason) => {
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let pair_summaries: Vec<DistinguishingPairSummary> =
        pairs.iter().map(|(_, s)| s.clone()).collect();

    if let Some((pass_idx, _fail_idx, ins_pair)) = first_insuff {
        let identical = obs_decls
            .iter()
            .enumerate()
            .map(|(oi, decl)| {
                let strs = obs_matrix[pass_idx][oi]
                    .iter()
                    .map(ScalarVal::to_display)
                    .collect();
                (decl.id.clone(), strs)
            })
            .collect();
        return ShigureOutcome {
            verdict: Verdict::Refuted,
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
            robustness: None,
            chevalley: None,
            observations: Some(ObservationOutcomeDetail {
                sufficient: false,
                distinguishing_pair_count: pairs.len(),
                distinguishing_pairs: pair_summaries,
                insufficiency_witness: Some(InsufficiencyWitness {
                    pair: ins_pair,
                    identical_observation_values: identical,
                }),
                minimal_sufficient_sets: vec![],
                cost_ranked_sets: vec![],
                law_readout_comparison: law_readout_cmp,
            }),
        };
    }

    let has_costs = !obs_decls.is_empty() && obs_decls.iter().all(|o| o.cost.is_some());
    if pairs.is_empty() {
        let zero_cost = has_costs.then(|| "0".to_owned());
        let empty_set = MinimalObservationSet {
            observations: vec![],
            total_cost: zero_cost.clone(),
            removal_counterexamples: vec![],
        };
        let ranked = zero_cost
            .map(|c| {
                vec![CostRankedObservationSet {
                    rank: 1,
                    observations: vec![],
                    total_cost: c,
                }]
            })
            .unwrap_or_default();
        return ShigureOutcome {
            verdict: Verdict::Established,
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
            robustness: None,
            chevalley: None,
            observations: Some(ObservationOutcomeDetail {
                sufficient: true,
                distinguishing_pair_count: 0,
                distinguishing_pairs: vec![],
                insufficiency_witness: None,
                minimal_sufficient_sets: vec![empty_set],
                cost_ranked_sets: ranked,
                law_readout_comparison: law_readout_cmp,
            }),
        };
    }

    // 重複分離集合ビットマスクを圧縮し、代表の異判定対を保持する。
    let mut mask_to_pair: BTreeMap<u16, DistinguishingPairSummary> = BTreeMap::new();
    for (d_mask, summary) in &pairs {
        mask_to_pair
            .entry(*d_mask)
            .or_insert_with(|| summary.clone());
    }
    let unique_masks: Vec<u16> = mask_to_pair.keys().copied().collect();

    let minimal_masks = match enumerate_all_minimal_hitting_sets(m_obs, &unique_masks) {
        Ok(ms) => ms,
        Err(reason) => {
            checks.push(ApplicabilityCheck::failed(
                "subset_enumeration_within_limit",
                MathClause::G142G6,
                reason.code(),
            ));
            return undetermined_obs(coeff_domain, point_domain, checks, provenance, reason);
        }
    };

    let mut minimal_sets = Vec::with_capacity(minimal_masks.len());
    let mut ranked_entries: Vec<(BigInt, Vec<String>)> = Vec::new();
    for &mask in &minimal_masks {
        let mut obs_ids = Vec::new();
        let mut removals = Vec::new();
        let mut cost_sum = BigInt::zero();
        for (oi, decl) in obs_decls.iter().enumerate() {
            let bit = 1u16 << oi;
            if (mask & bit) == 0 {
                continue;
            }
            obs_ids.push(decl.id.clone());
            if let Some(c) = &decl.cost {
                cost_sum += c;
            }
            let reduced = mask & !bit;
            let unsep = unique_masks
                .iter()
                .find(|&&dm| (dm & reduced) == 0)
                .and_then(|dm| mask_to_pair.get(dm))
                .expect("minimality guarantees at least one unseparated pair upon single removal")
                .clone();
            removals.push(RemovalCounterexample {
                removed_observation: decl.id.clone(),
                unseparated_pair: unsep,
            });
        }
        let total_cost_str = has_costs.then(|| cost_sum.to_string());
        if has_costs {
            ranked_entries.push((cost_sum, obs_ids.clone()));
        }
        minimal_sets.push(MinimalObservationSet {
            observations: obs_ids,
            total_cost: total_cost_str,
            removal_counterexamples: removals,
        });
    }

    ranked_entries.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    let cost_ranked_sets = ranked_entries
        .into_iter()
        .enumerate()
        .map(|(idx, (cost, obs_ids))| CostRankedObservationSet {
            rank: idx + 1,
            observations: obs_ids,
            total_cost: cost.to_string(),
        })
        .collect();

    ShigureOutcome {
        verdict: Verdict::Established,
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
        robustness: None,
        chevalley: None,
        observations: Some(ObservationOutcomeDetail {
            sufficient: true,
            distinguishing_pair_count: pairs.len(),
            distinguishing_pairs: pair_summaries,
            insufficiency_witness: None,
            minimal_sufficient_sets: minimal_sets,
            cost_ranked_sets,
            law_readout_comparison: law_readout_cmp,
        }),
    }
}

fn enumerate_all_minimal_hitting_sets(
    m_obs: usize,
    unique_masks: &[u16],
) -> Result<Vec<u16>, SilenceReason> {
    let mut minimal_masks: Vec<u16> = Vec::new();
    let mut visited = 0usize;
    for size in 1..=m_obs {
        let mut indices: Vec<usize> = (0..size).collect();
        loop {
            visited += 1;
            if visited > DEFAULT_MAX_SUBSET_STEPS {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!(
                        "minimal observation subset search exceeded step limit ({DEFAULT_MAX_SUBSET_STEPS})"
                    ),
                });
            }
            let mut mask: u16 = 0;
            for &idx in &indices {
                mask |= 1u16 << idx;
            }
            if minimal_masks.iter().all(|&min| (mask & min) != min)
                && unique_masks.iter().all(|&dm| (dm & mask) != 0)
            {
                minimal_masks.push(mask);
            }
            if !next_combination(&mut indices, m_obs) {
                break;
            }
        }
    }
    Ok(minimal_masks)
}

fn next_combination(indices: &mut [usize], n: usize) -> bool {
    let k = indices.len();
    for i in (0..k).rev() {
        if indices[i] < n - k + i {
            indices[i] += 1;
            for j in (i + 1)..k {
                indices[j] = indices[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

fn compute_law_readout_comparison(
    task: &CheckedObservationTask,
    u_vars: &VarOrder,
    u_list: &[EnumRealization],
    domain: &CoeffDomain,
    no_distinguishing_pairs: bool,
) -> Result<Option<LawReadoutAdequacyComparison>, SilenceReason> {
    let Some(lr) = task.law_readout() else {
        return Ok(None);
    };
    let mut first_val: Option<Vec<ScalarVal>> = None;
    let mut constant_on_fiber = true;
    for u in u_list {
        let val: Vec<ScalarVal> = lr
            .components
            .iter()
            .map(|c| eval_expr_at(&c.expr, u_vars, &u.values, domain))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(prev) = &first_val {
            if prev != &val {
                constant_on_fiber = false;
                break;
            }
        } else {
            first_val = Some(val);
        }
    }
    let detail = if constant_on_fiber && !no_distinguishing_pairs {
        format!(
            "coarse reading is adequate for constant Law readout `{}` on U_b, but insufficient for shared decision chi_E without separating observations",
            lr.name
        )
    } else if constant_on_fiber && no_distinguishing_pairs {
        format!(
            "coarse reading is adequate for both Law readout `{}` and decision chi_E on U_b",
            lr.name
        )
    } else {
        format!(
            "coarse reading is NOT constant on Law readout `{}` across U_b",
            lr.name
        )
    };
    Ok(Some(LawReadoutAdequacyComparison {
        readout_name: lr.name.clone(),
        coarse_adequate_for_law_readout: constant_on_fiber,
        coarse_adequate_for_decision: no_distinguishing_pairs,
        detail,
    }))
}

fn build_obs_provenance(task: &CheckedObservationTask, family: &FamilySpec) -> Provenance {
    let mut origins = family.provenance.origins.clone();
    origins.extend(task.provenance().origins.clone());
    for o in task.observations() {
        origins.push(o.origin.clone());
    }
    if let RealizationSpace::FiniteMembers(ms) = &family.realizations.space {
        for m in ms {
            origins.push(m.origin.clone());
        }
    }
    Provenance::new(origins, vec![MathClause::G142G5, MathClause::G142G6])
}

fn undetermined_obs(
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
