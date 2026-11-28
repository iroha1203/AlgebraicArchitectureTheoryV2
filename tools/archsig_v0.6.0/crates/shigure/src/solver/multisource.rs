//! AAT 第19章後半（多源統合と高次構造衝突・最小由来支持・費用最小化・採用後安定性・検証不一致再評価）
//! の計算核（`shigure_multisource`）。

use crate::algebra::hitting_set::{
    HittingSetInput, HittingSetOutcome, enumerate_minimal_hitting_sets, verify_minimal_hitting_sets,
};
use crate::algebra::scalar::{Rat, RingCoeff};
use crate::ir::change::PointDomain;
use crate::ir::multisource::{
    CandidateRecordSpec, CheckedMultisourceTask, SupportGoalFormula, SupportGoalSpec,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ReevalCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase5_rev::{MultisourceOutcomeDetail, SupportCostEntry, SupportGoalDetail};
use crate::ir::revision::{RevisionConstraintSpec, RevisionCoordSpec};
use crate::ir::term::CoeffDomain;
use crate::solver::partial_affine::scalar_to_rat;
use crate::solver::revision::{NormScalar, enumerate_coord_completions, point_domain_for};
use std::collections::{BTreeMap, BTreeSet};

const DEFAULT_SUPPORT_MAX_COMPLETIONS: usize = 4_096;

/// `shigure_multisource`（第19章後半）の計算核入口。
pub fn solve_multisource_task(task: &CheckedMultisourceTask) -> ShigureOutcome {
    let provenance = with_ch19_multi_clauses(task.provenance());
    let coeff_domain = task.coeff_domain().clone();
    let point_domain = point_domain_for(&coeff_domain);
    let mut checks = Vec::new();

    let missing = task.undeclared_unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::AatCh19Thm19Dot9,
            format!("undeclared unobserved slots: {}", missing.join(", ")),
        ));
        return build_outcome(
            Verdict::Undetermined(SilenceReason::UnobservedDependency {
                slots: missing.to_vec(),
            }),
            coeff_domain,
            point_domain,
            checks,
            provenance,
            None,
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::AatCh19Thm19Dot9,
    ));

    match solve_multisource_inner(task, &coeff_domain, &mut checks) {
        Ok((verdict, detail)) => build_outcome(
            verdict,
            coeff_domain,
            point_domain,
            checks,
            provenance,
            Some(detail),
        ),
        Err(reason) => build_outcome(
            Verdict::Undetermined(reason),
            coeff_domain,
            point_domain,
            checks,
            provenance,
            None,
        ),
    }
}

struct NormalizedSource {
    id: String,
    assignments: Vec<(String, NormScalar)>,
    forbidden: Vec<(String, NormScalar)>,
    extra_constraints: Vec<RevisionConstraintSpec>,
}

fn solve_multisource_inner(
    task: &CheckedMultisourceTask,
    domain: &CoeffDomain,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<(Verdict, MultisourceOutcomeDetail), SilenceReason> {
    let mut norm_sources = Vec::with_capacity(task.sources().len());
    for src in task.sources() {
        let assignments = src
            .assignments
            .iter()
            .map(|(k, v)| Ok((k.clone(), NormScalar::from_lit(v, domain)?)))
            .collect::<Result<Vec<_>, SilenceReason>>()?;
        let forbidden = src
            .forbidden_values
            .iter()
            .map(|(k, v)| Ok((k.clone(), NormScalar::from_lit(v, domain)?)))
            .collect::<Result<Vec<_>, SilenceReason>>()?;
        norm_sources.push(NormalizedSource {
            id: src.source_id.clone(),
            assignments,
            forbidden,
            extra_constraints: src.extra_constraints.clone(),
        });
    }

    let check_subset_consistent = |indices: &[usize]| -> Result<bool, SilenceReason> {
        let mut assigns = Vec::new();
        let mut forbids = Vec::new();
        let mut cons: Vec<&RevisionConstraintSpec> = task.background_constraints().iter().collect();
        for &idx in indices {
            let s = &norm_sources[idx];
            assigns.extend(s.assignments.iter().cloned());
            forbids.extend(s.forbidden.iter().cloned());
            cons.extend(s.extra_constraints.iter());
        }
        let comps = enumerate_coord_completions(
            task.coords(),
            &assigns,
            &forbids,
            &cons,
            domain,
            DEFAULT_SUPPORT_MAX_COMPLETIONS,
        )?;
        Ok(!comps.is_empty())
    };

    // 定理 19.9: サイズ昇順（k = 0..=m）で包含極小衝突集合を有限列挙する
    let m = norm_sources.len();
    let max_steps = task.max_sources_subset_steps();
    let max_results = task.max_results();
    let mut steps = 0usize;
    let mut minimal_conflict_idx: Vec<Vec<usize>> = Vec::new();

    for size in 0..=m {
        let mut current = Vec::with_capacity(size);
        let mut size_conflicts = Vec::new();
        enumerate_size_subsets(
            0,
            m,
            size,
            &mut current,
            &mut steps,
            max_steps,
            max_results,
            &minimal_conflict_idx,
            &check_subset_consistent,
            &mut size_conflicts,
        )?;
        minimal_conflict_idx.extend(size_conflicts);
    }

    let mut minimal_conflict_sets: Vec<Vec<String>> = minimal_conflict_idx
        .iter()
        .map(|idxs| {
            let mut ids: Vec<String> = idxs.iter().map(|&i| norm_sources[i].id.clone()).collect();
            ids.sort();
            ids
        })
        .collect();
    minimal_conflict_sets.sort();

    // 独立検証: 全報告衝突集合は不整合であり、各 1 要素除去は整合する
    let mut minimal_conflicts_verified = true;
    for c_idx in &minimal_conflict_idx {
        if check_subset_consistent(c_idx)? {
            minimal_conflicts_verified = false;
            break;
        }
        for pos in 0..c_idx.len() {
            let sub: Vec<usize> = c_idx
                .iter()
                .enumerate()
                .filter(|(p, _)| *p != pos)
                .map(|(_, &v)| v)
                .collect();
            if !check_subset_consistent(&sub)? {
                minimal_conflicts_verified = false;
                break;
            }
        }
    }

    let all_sources_consistent = minimal_conflict_idx.is_empty();
    let pairwise_consistent = !minimal_conflict_idx.iter().any(|c| c.len() <= 2);

    checks.push(ApplicabilityCheck::passed(
        "multisource_minimal_conflicts_enumerated",
        MathClause::AatCh19Thm19Dot9,
    ));

    let support_goal = match task.support_goal() {
        Some(sg) => Some(analyze_support_goal(task, sg, domain, checks)?),
        None => None,
    };

    let support_failed = support_goal.as_ref().is_some_and(|sg| {
        sg.minimal_supports.is_empty() || !sg.reevaluation.as_ref().is_none_or(|r| r.matched)
    });

    let verdict = if !all_sources_consistent || !minimal_conflicts_verified || support_failed {
        Verdict::Refuted
    } else {
        Verdict::Established
    };

    Ok((
        verdict,
        MultisourceOutcomeDetail {
            pairwise_consistent,
            all_sources_consistent,
            minimal_conflict_sets,
            minimal_conflicts_verified,
            support_goal,
        },
    ))
}

#[allow(clippy::too_many_arguments)]
fn enumerate_size_subsets<F>(
    start: usize,
    n: usize,
    remaining: usize,
    cur: &mut Vec<usize>,
    steps: &mut usize,
    max_steps: usize,
    max_results: usize,
    discovered: &[Vec<usize>],
    is_consistent: &F,
    out: &mut Vec<Vec<usize>>,
) -> Result<(), SilenceReason>
where
    F: Fn(&[usize]) -> Result<bool, SilenceReason>,
{
    if remaining == 0 {
        // 既出の極小衝突集合を含む超集合は包含極小でないため枝刈り
        let cur_set: BTreeSet<usize> = cur.iter().copied().collect();
        if discovered
            .iter()
            .any(|prev| prev.iter().all(|x| cur_set.contains(x)))
        {
            return Ok(());
        }
        *steps += 1;
        if *steps > max_steps {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!("source subset enumeration exceeded max_steps ({max_steps})"),
            });
        }
        if !is_consistent(cur)? {
            if discovered.len() + out.len() >= max_results {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: format!("minimal conflict sets exceeded max_results ({max_results})"),
                });
            }
            out.push(cur.clone());
        }
        return Ok(());
    }
    if start + remaining > n {
        return Ok(());
    }
    for i in start..=(n - remaining) {
        cur.push(i);
        enumerate_size_subsets(
            i + 1,
            n,
            remaining - 1,
            cur,
            steps,
            max_steps,
            max_results,
            discovered,
            is_consistent,
            out,
        )?;
        cur.pop();
    }
    Ok(())
}

struct NormalizedCandidate {
    spec: CandidateRecordSpec,
    norm_val: NormScalar,
    cost_rat: Option<Rat>,
}

fn analyze_support_goal(
    task: &CheckedMultisourceTask,
    sg: &SupportGoalSpec,
    domain: &CoeffDomain,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<SupportGoalDetail, SilenceReason> {
    let trusted: Vec<(String, NormScalar)> = sg
        .trusted_assignments
        .iter()
        .map(|(k, v)| Ok((k.clone(), NormScalar::from_lit(v, domain)?)))
        .collect::<Result<_, SilenceReason>>()?;

    let cands: Vec<NormalizedCandidate> = sg
        .candidates
        .iter()
        .map(|c| {
            let norm_val = NormScalar::from_lit(&c.value, domain)?;
            let cost_rat = c.cost.as_ref().map(scalar_to_rat);
            Ok(NormalizedCandidate {
                spec: c.clone(),
                norm_val,
                cost_rat,
            })
        })
        .collect::<Result<_, SilenceReason>>()?;

    let (
        all_candidates_consistent,
        minimal_supports,
        min_cost_supports,
        insufficiency_witness,
        reeval_matched,
        reeval_detail,
    ) = solve_support_instance(
        task.coords(),
        task.background_constraints(),
        &trusted,
        &cands,
        &sg.goal,
        sg.expected_truth,
        sg.check_post_adoption_stability,
        domain,
        task.max_sources_subset_steps(),
        task.max_results(),
    )?;

    checks.push(ApplicabilityCheck::passed(
        "minimal_provenance_support_computed",
        MathClause::AatCh19Thm19Dot11,
    ));

    // 命題 19.12: verified_actual_value が候補と異なる場合は実測値で改訂再計算
    let mut post_verification_reeval_needed = false;
    let mut revised_trusted = trusted.clone();
    let mut remaining_cands = Vec::new();
    for nc in &cands {
        if let Some(actual) = &nc.spec.verified_actual_value {
            let actual_norm = NormScalar::from_lit(actual, domain)?;
            if actual_norm != nc.norm_val {
                post_verification_reeval_needed = true;
                revised_trusted.push((nc.spec.coord.clone(), actual_norm));
            } else {
                // 一致して検証済みとなった候補も改訂後 T' へ固定
                revised_trusted.push((nc.spec.coord.clone(), actual_norm));
            }
        } else {
            remaining_cands.push(NormalizedCandidate {
                spec: nc.spec.clone(),
                norm_val: nc.norm_val.clone(),
                cost_rat: nc.cost_rat.clone(),
            });
        }
    }

    let post_verification_minimal_supports = if post_verification_reeval_needed {
        let (_, post_min, _, _, _, _) = solve_support_instance(
            task.coords(),
            task.background_constraints(),
            &revised_trusted,
            &remaining_cands,
            &sg.goal,
            sg.expected_truth,
            sg.check_post_adoption_stability,
            domain,
            task.max_sources_subset_steps(),
            task.max_results(),
        )?;
        Some(post_min)
    } else {
        None
    };

    Ok(SupportGoalDetail {
        all_candidates_consistent,
        minimal_supports,
        min_cost_supports,
        insufficiency_witness,
        post_verification_reeval_needed,
        post_verification_minimal_supports,
        reevaluation: Some(ReevalCheck {
            checked: true,
            matched: reeval_matched,
            detail: reeval_detail,
        }),
    })
}

type SupportRunOutput = (
    bool,
    Vec<SupportCostEntry>,
    Vec<SupportCostEntry>,
    Option<BTreeMap<String, String>>,
    bool,
    String,
);

#[allow(clippy::too_many_arguments)]
fn solve_support_instance(
    coords: &[RevisionCoordSpec],
    bg_constraints: &[RevisionConstraintSpec],
    trusted: &[(String, NormScalar)],
    cands: &[NormalizedCandidate],
    goal: &SupportGoalFormula,
    expected_truth: bool,
    check_stability: bool,
    domain: &CoeffDomain,
    max_steps: usize,
    max_results: usize,
) -> Result<SupportRunOutput, SilenceReason> {
    let cons_refs: Vec<&RevisionConstraintSpec> = bg_constraints.iter().collect();

    let mut all_assigns = trusted.to_vec();
    for c in cands {
        all_assigns.push((c.spec.coord.clone(), c.norm_val.clone()));
    }
    let comp_ti = enumerate_coord_completions(
        coords,
        &all_assigns,
        &[],
        &cons_refs,
        domain,
        DEFAULT_SUPPORT_MAX_COMPLETIONS,
    )?;
    let all_candidates_consistent = !comp_ti.is_empty();

    let comp_t = enumerate_coord_completions(
        coords,
        trusted,
        &[],
        &cons_refs,
        domain,
        DEFAULT_SUPPORT_MAX_COMPLETIONS,
    )?;
    if comp_t.is_empty() {
        return Ok((
            all_candidates_consistent,
            vec![],
            vec![],
            None,
            true,
            "trusted base presentation is inconsistent; goal holds vacuously".to_owned(),
        ));
    }

    let mut hyperedges = Vec::new();
    let mut insufficiency_witness = None;
    for a in &comp_t {
        if eval_goal(goal, a, domain)? != expected_truth {
            let edge: Vec<String> = cands
                .iter()
                .filter(|c| a.get(&c.spec.coord) != Some(&c.norm_val))
                .map(|c| c.spec.id.clone())
                .collect();
            if edge.is_empty() && insufficiency_witness.is_none() {
                insufficiency_witness = Some(
                    a.iter()
                        .map(|(k, v)| (k.clone(), v.display_str()))
                        .collect(),
                );
            }
            hyperedges.push(edge);
        }
    }

    let universe: Vec<String> = cands.iter().map(|c| c.spec.id.clone()).collect();
    let hs = enumerate_minimal_hitting_sets(&HittingSetInput {
        universe,
        hyperedges: hyperedges.clone(),
        weights: None,
        max_steps,
        max_results,
    })
    .map_err(|e| SilenceReason::FiniteEnumerationOutOfScope {
        detail: format!("{e:?}"),
    })?;

    let raw_sets = match hs {
        HittingSetOutcome::EmptyHyperedge { .. } => vec![],
        HittingSetOutcome::Enumerated {
            minimal_sets,
            verified,
            ..
        } => {
            if !verified || !verify_minimal_hitting_sets(&hyperedges, &minimal_sets) {
                return Err(SilenceReason::FiniteEnumerationOutOfScope {
                    detail: "minimal hitting sets verification failed for support goal".to_owned(),
                });
            }
            minimal_sets
        }
    };

    let cand_by_id: BTreeMap<&str, &NormalizedCandidate> =
        cands.iter().map(|c| (c.spec.id.as_str(), c)).collect();

    let eval_support = |support: &[String]| -> Result<(bool, bool), SilenceReason> {
        let mut s_assigns = trusted.to_vec();
        for sid in support {
            let nc = cand_by_id[sid.as_str()];
            s_assigns.push((nc.spec.coord.clone(), nc.norm_val.clone()));
        }
        let comps = enumerate_coord_completions(
            coords,
            &s_assigns,
            &[],
            &cons_refs,
            domain,
            DEFAULT_SUPPORT_MAX_COMPLETIONS,
        )?;
        if comps.is_empty() {
            return Ok((false, false));
        }
        for a in &comps {
            if eval_goal(goal, a, domain)? != expected_truth {
                return Ok((true, false));
            }
        }
        Ok((true, true))
    };

    let mut minimal_supports = Vec::new();
    let mut cost_pairs: Vec<(Option<Rat>, usize)> = Vec::new();
    let mut reeval_matched = true;

    for s in raw_sets {
        let (nonempty, goal_ok) = eval_support(&s)?;
        if !nonempty {
            // 候補全体が非整合のとき、空補完となる支持は採用しない（第19章 式 19.7 ただし書き）
            continue;
        }
        if !goal_ok {
            reeval_matched = false;
        }
        // 包含極小性の独立検算: いずれの 1 要素削除でも目標確定性が崩れること
        for pos in 0..s.len() {
            let reduced: Vec<String> = s
                .iter()
                .enumerate()
                .filter(|(p, _)| *p != pos)
                .map(|(_, id)| id.clone())
                .collect();
            let (r_nonempty, r_goal) = eval_support(&reduced)?;
            if r_nonempty && r_goal {
                reeval_matched = false;
            }
        }

        let stability_verified = if check_stability {
            verify_post_adoption_stability(
                coords,
                trusted,
                &cons_refs,
                cands,
                &cand_by_id,
                &s,
                goal,
                expected_truth,
                domain,
                max_steps,
            )?
        } else {
            goal_ok
        };
        if check_stability && !stability_verified {
            reeval_matched = false;
        }

        let total_cost_rat = if !cands.is_empty() && cands.iter().all(|c| c.cost_rat.is_some()) {
            let mut sum = Rat::zero();
            for sid in &s {
                if let Some(r) = &cand_by_id[sid.as_str()].cost_rat {
                    sum = sum.add_ref(r);
                }
            }
            Some(sum)
        } else {
            None
        };
        let total_cost = total_cost_rat.as_ref().map(ToString::to_string);
        cost_pairs.push((total_cost_rat, minimal_supports.len()));
        minimal_supports.push(SupportCostEntry {
            support: s,
            total_cost,
            stability_verified,
        });
    }

    let min_cost_supports = if let Some(min_r) = cost_pairs
        .iter()
        .filter_map(|(r, _)| r.as_ref())
        .min()
        .cloned()
    {
        cost_pairs
            .iter()
            .filter_map(|(r, idx)| {
                r.as_ref()
                    .filter(|v| **v == min_r)
                    .map(|_| minimal_supports[*idx].clone())
            })
            .collect()
    } else {
        minimal_supports.clone()
    };

    let detail = format!(
        "minimal_supports={}, all_candidates_consistent={all_candidates_consistent}, reeval_matched={reeval_matched}",
        minimal_supports.len()
    );
    Ok((
        all_candidates_consistent,
        minimal_supports,
        min_cost_supports,
        insufficiency_witness,
        reeval_matched,
        detail,
    ))
}

#[allow(clippy::too_many_arguments)]
fn verify_post_adoption_stability(
    coords: &[RevisionCoordSpec],
    trusted: &[(String, NormScalar)],
    cons_refs: &[&RevisionConstraintSpec],
    cands: &[NormalizedCandidate],
    cand_by_id: &BTreeMap<&str, &NormalizedCandidate>,
    support: &[String],
    goal: &SupportGoalFormula,
    expected_truth: bool,
    domain: &CoeffDomain,
    max_steps: usize,
) -> Result<bool, SilenceReason> {
    let support_set: BTreeSet<&str> = support.iter().map(String::as_str).collect();
    let mut base_assigns = trusted.to_vec();
    for sid in support {
        let nc = cand_by_id[sid.as_str()];
        base_assigns.push((nc.spec.coord.clone(), nc.norm_val.clone()));
    }
    let rem: Vec<&NormalizedCandidate> = cands
        .iter()
        .filter(|c| !support_set.contains(c.spec.id.as_str()))
        .collect();

    // 残余候補の 3 状態（不問 / 成立採用 / 不成立反証）について整合する範囲ですべて安定性を検証
    let mut states_checked = 0usize;
    let mut extra_pos = Vec::new();
    let mut extra_neg = Vec::new();
    check_stability_rec(
        0,
        &rem,
        coords,
        &base_assigns,
        cons_refs,
        goal,
        expected_truth,
        domain,
        max_steps,
        &mut states_checked,
        &mut extra_pos,
        &mut extra_neg,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_stability_rec(
    idx: usize,
    rem: &[&NormalizedCandidate],
    coords: &[RevisionCoordSpec],
    base_assigns: &[(String, NormScalar)],
    cons_refs: &[&RevisionConstraintSpec],
    goal: &SupportGoalFormula,
    expected_truth: bool,
    domain: &CoeffDomain,
    max_steps: usize,
    states_checked: &mut usize,
    extra_pos: &mut Vec<(String, NormScalar)>,
    extra_neg: &mut Vec<(String, NormScalar)>,
) -> Result<bool, SilenceReason> {
    if idx == rem.len() {
        *states_checked += 1;
        if *states_checked > max_steps {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!("post-adoption stability checks exceeded max_steps ({max_steps})"),
            });
        }
        let mut assigns = base_assigns.to_vec();
        assigns.extend(extra_pos.iter().cloned());
        let comps = enumerate_coord_completions(
            coords,
            &assigns,
            extra_neg,
            cons_refs,
            domain,
            DEFAULT_SUPPORT_MAX_COMPLETIONS,
        )?;
        for a in &comps {
            if eval_goal(goal, a, domain)? != expected_truth {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    // 0: 撤回・不問, 1: 成立確認, 2: 不成立反証
    if !check_stability_rec(
        idx + 1,
        rem,
        coords,
        base_assigns,
        cons_refs,
        goal,
        expected_truth,
        domain,
        max_steps,
        states_checked,
        extra_pos,
        extra_neg,
    )? {
        return Ok(false);
    }
    let c = rem[idx];
    extra_pos.push((c.spec.coord.clone(), c.norm_val.clone()));
    let pos_ok = check_stability_rec(
        idx + 1,
        rem,
        coords,
        base_assigns,
        cons_refs,
        goal,
        expected_truth,
        domain,
        max_steps,
        states_checked,
        extra_pos,
        extra_neg,
    )?;
    extra_pos.pop();
    if !pos_ok {
        return Ok(false);
    }

    extra_neg.push((c.spec.coord.clone(), c.norm_val.clone()));
    let neg_ok = check_stability_rec(
        idx + 1,
        rem,
        coords,
        base_assigns,
        cons_refs,
        goal,
        expected_truth,
        domain,
        max_steps,
        states_checked,
        extra_pos,
        extra_neg,
    )?;
    extra_neg.pop();
    Ok(neg_ok)
}

fn eval_goal(
    goal: &SupportGoalFormula,
    env: &BTreeMap<String, NormScalar>,
    domain: &CoeffDomain,
) -> Result<bool, SilenceReason> {
    match goal {
        SupportGoalFormula::CoordEquality(a, b) => Ok(env.get(a) == env.get(b)),
        SupportGoalFormula::CoordEqualsConst(c, lit) => {
            Ok(env.get(c) == Some(&NormScalar::from_lit(lit, domain)?))
        }
    }
}

fn with_ch19_multi_clauses(base: &Provenance) -> Provenance {
    let mut prov = base.clone();
    for clause in [MathClause::AatCh19Thm19Dot9, MathClause::AatCh19Thm19Dot11] {
        if !prov.clauses.contains(&clause) {
            prov.clauses.push(clause);
        }
    }
    prov
}

fn build_outcome(
    verdict: Verdict,
    coeff_domain: CoeffDomain,
    point_domain: PointDomain,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    multisource: Option<MultisourceOutcomeDetail>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
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
        occurrence: None,
        partial: None,
        revision: None,
        multisource,
    }
}
