//! AAT 第17章（出現同定・使用文脈同値・補助属性の最小値域）の計算核
//! （`shigure_occurrence`）。

use crate::algebra::congruence::{
    CongruenceInput, CongruenceSort, PredicateRecord, PredicateRecordKind,
    compute_congruence_closure,
};
use crate::algebra::partition::{
    BaseReading, PartialOpTable, PartialRelTable, PartitionRefinementResult, RefinementInput,
    enumerate_set_partitions, partition_refines, refine_partition,
};
use crate::ir::change::PointDomain;
use crate::ir::occurrence::{
    CheckedOccurrenceTask, OccurrenceOpSpec, OccurrenceReadingSpec, OccurrenceRelSpec,
};
use crate::ir::provenance::{MathClause, Provenance};
use crate::ir::result::{ApplicabilityCheck, ShigureOutcome, SilenceReason, Verdict};
use crate::ir::result_phase5_obs::{
    OccurrenceCollisionDetail, OccurrenceOutcomeDetail, SeparatingContextDetail,
};
use crate::ir::term::CoeffDomain;
use crate::solver::occurrence_attr::{
    build_class_lookup, compute_attribute_failure_with_eval_kappa, compute_attribute_realization,
    format_collision, format_separating_witness,
};
use std::collections::{BTreeMap, BTreeSet};

/// `shigure_occurrence`（第17章）の計算核入口。
pub fn solve_occurrence_task(task: &CheckedOccurrenceTask) -> ShigureOutcome {
    let provenance = with_ch17_clauses(task.provenance());
    let mut checks = Vec::new();

    let missing = task.undeclared_unobserved_slots();
    if !missing.is_empty() {
        checks.push(ApplicabilityCheck::failed(
            "unobserved_slots_absent",
            MathClause::AatCh17Thm17Dot2,
            format!("undeclared unobserved slots: {}", missing.join(", ")),
        ));
        return build_outcome(
            Verdict::Undetermined(SilenceReason::UnobservedDependency {
                slots: missing.to_vec(),
            }),
            checks,
            provenance,
            None,
        );
    }
    checks.push(ApplicabilityCheck::passed(
        "unobserved_slots_absent",
        MathClause::AatCh17Thm17Dot2,
    ));

    // Step (a): 定理 17.2・命題 17.3 の最小機能閉包と衝突検算（定義 17.1 の G_e^+ => D_p^+ を補完）
    let cong_input = build_congruence_input(task);
    let cong = match compute_congruence_closure(&cong_input) {
        Ok(res) => res,
        Err(err) => {
            let reason = map_algebra_error_to_silence(&format!("{err:?}"));
            checks.push(ApplicabilityCheck::failed(
                "congruence_closure_within_bound",
                MathClause::AatCh17Thm17Dot2,
                format!("{err:?}"),
            ));
            return build_outcome(Verdict::Undetermined(reason), checks, provenance, None);
        }
    };
    checks.push(ApplicabilityCheck::passed(
        "minimal_functional_closure_computed",
        MathClause::AatCh17Thm17Dot2,
    ));

    let formatted_collisions: Vec<OccurrenceCollisionDetail> =
        cong.collisions.iter().map(format_collision).collect();

    if !cong.collisions.is_empty() {
        checks.push(ApplicabilityCheck::passed(
            "collision_witness_derivation_verified",
            MathClause::AatCh17Thm17Dot2,
        ));
        let empty_ctx: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();
        let attr_fail = if !task.initial_readouts().is_empty() {
            Some(compute_attribute_failure_with_eval_kappa(
                task,
                &empty_ctx,
                "functional congruence closure collided before finding a sound attribute realization",
            ))
        } else {
            None
        };
        let detail = OccurrenceOutcomeDetail {
            minimal_functional_classes: cong.classes,
            collisions: formatted_collisions,
            derivation_verified: cong.derivation_verified,
            context_closed_17_5: task.context_closed_17_5(),
            context_equivalence_classes: BTreeMap::new(),
            separating_contexts: vec![],
            sound_identifications_count: Some(0),
            coarsest_sound_exists: false,
            coarsest_sound_classes: None,
            attribute_realization: attr_fail,
        };
        return build_outcome(Verdict::Refuted, checks, provenance, Some(detail));
    }

    // Step (b): 設定 17.5 の反復細分（定理 17.6・命題 17.8）または一般有限健全同定の全列挙（例 17.7）
    let sound_analysis = if task.context_closed_17_5() {
        analyze_setting_17_5(task, &mut checks)
    } else {
        analyze_general_finite(task, &mut checks)
    };

    let sound = match sound_analysis {
        Ok(s) => s,
        Err(silence) => {
            let detail = OccurrenceOutcomeDetail {
                minimal_functional_classes: cong.classes,
                collisions: vec![],
                derivation_verified: cong.derivation_verified,
                context_closed_17_5: task.context_closed_17_5(),
                context_equivalence_classes: BTreeMap::new(),
                separating_contexts: vec![],
                sound_identifications_count: None,
                coarsest_sound_exists: false,
                coarsest_sound_classes: None,
                attribute_realization: None,
            };
            return build_outcome(
                Verdict::Undetermined(silence),
                checks,
                provenance,
                Some(detail),
            );
        }
    };

    let mut collisions = formatted_collisions;
    collisions.extend(sound.extra_collisions);

    if sound.sound_partitions.is_empty() {
        let attr_fail = if !task.initial_readouts().is_empty() {
            Some(compute_attribute_failure_with_eval_kappa(
                task,
                &sound.context_equivalence_classes,
                "no sound identification satisfies both identity requests and context separation",
            ))
        } else {
            None
        };
        let detail = OccurrenceOutcomeDetail {
            minimal_functional_classes: cong.classes,
            collisions,
            derivation_verified: cong.derivation_verified,
            context_closed_17_5: task.context_closed_17_5(),
            context_equivalence_classes: sound.context_equivalence_classes,
            separating_contexts: sound.separating_contexts,
            sound_identifications_count: Some(0),
            coarsest_sound_exists: false,
            coarsest_sound_classes: None,
            attribute_realization: attr_fail,
        };
        return build_outcome(Verdict::Refuted, checks, provenance, Some(detail));
    }

    // Step (c): 設定 17.9 の最小補助属性値域サイズ・属性構成（例 17.12・例 17.13）
    let attribute_realization = if !task.initial_readouts().is_empty() {
        checks.push(ApplicabilityCheck::passed(
            "initial_readouts_attribute_realization_checked",
            MathClause::AatCh17Thm17Dot11,
        ));
        Some(compute_attribute_realization(
            task,
            &sound.context_equivalence_classes,
            &sound.sound_partitions,
        ))
    } else {
        None
    };

    let attr_failed = attribute_realization.as_ref().is_some_and(|a| {
        !a.sound_identification_exists || a.reevaluation.as_ref().is_some_and(|r| !r.matched)
    });
    let verdict = if attr_failed {
        Verdict::Refuted
    } else {
        Verdict::Established
    };

    let detail = OccurrenceOutcomeDetail {
        minimal_functional_classes: cong.classes,
        collisions,
        derivation_verified: cong.derivation_verified,
        context_closed_17_5: task.context_closed_17_5(),
        context_equivalence_classes: sound.context_equivalence_classes,
        separating_contexts: sound.separating_contexts,
        sound_identifications_count: Some(sound.sound_partitions.len()),
        coarsest_sound_exists: sound.coarsest_sound_classes.is_some(),
        coarsest_sound_classes: sound.coarsest_sound_classes,
        attribute_realization,
    };
    build_outcome(verdict, checks, provenance, Some(detail))
}

struct SoundAnalysisOutcome {
    context_equivalence_classes: BTreeMap<String, Vec<Vec<String>>>,
    separating_contexts: Vec<SeparatingContextDetail>,
    sound_partitions: Vec<BTreeMap<String, Vec<Vec<String>>>>,
    coarsest_sound_classes: Option<BTreeMap<String, Vec<Vec<String>>>>,
    extra_collisions: Vec<OccurrenceCollisionDetail>,
}

fn with_ch17_clauses(base: &Provenance) -> Provenance {
    let mut prov = base.clone();
    for clause in [
        MathClause::AatCh17Thm17Dot2,
        MathClause::AatCh17Def17Dot4,
        MathClause::AatCh17Thm17Dot6,
        MathClause::AatCh17Ex17Dot7,
        MathClause::AatCh17Thm17Dot10,
        MathClause::AatCh17Thm17Dot11,
    ] {
        if !prov.clauses.contains(&clause) {
            prov.clauses.push(clause);
        }
    }
    prov
}

fn build_outcome(
    verdict: Verdict,
    applicability: Vec<ApplicabilityCheck>,
    provenance: Provenance,
    occurrence: Option<OccurrenceOutcomeDetail>,
) -> ShigureOutcome {
    ShigureOutcome {
        verdict,
        coeff_domain: CoeffDomain::Z,
        point_domain: PointDomain::RationalPoints,
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
        occurrence,
        partial: None,
        revision: None,
        multisource: None,
    }
}

fn map_algebra_error_to_silence(detail: &str) -> SilenceReason {
    SilenceReason::FiniteEnumerationOutOfScope {
        detail: detail.to_owned(),
    }
}

/// 定義 17.1 の含意（正のグラフ記録 $G_e^+(\bar{a}, y)$ は定義域記録 $D_p^+(\bar{a})$ を伴う）を
/// 補完して最小機能閉包用入力を構築する。
fn build_congruence_input(task: &CheckedOccurrenceTask) -> CongruenceInput {
    let sorts = task
        .sorts()
        .iter()
        .map(|s| CongruenceSort {
            name: s.name.clone(),
            elements: s.elements.clone(),
            is_fixed_value: s.is_fixed_value,
        })
        .collect();

    let mut pred_records = task.pred_records().to_vec();
    let mut existing_pos_dom: BTreeSet<(String, Vec<String>)> = pred_records
        .iter()
        .filter(|r| r.positive && r.kind == PredicateRecordKind::Domain)
        .map(|r| (r.name.clone(), r.args.clone()))
        .collect();

    for rec in task.op_records().iter().filter(|r| r.positive) {
        let key = (rec.op_name.clone(), rec.args.clone());
        if existing_pos_dom.insert(key) {
            pred_records.push(PredicateRecord {
                kind: PredicateRecordKind::Domain,
                name: rec.op_name.clone(),
                arg_sorts: rec.arg_sorts.clone(),
                args: rec.args.clone(),
                positive: true,
            });
        }
    }

    CongruenceInput {
        sorts,
        requests: task.identity_requests().to_vec(),
        op_records: task.op_records().to_vec(),
        predicate_records: pred_records,
        max_steps: task.max_congruence_steps(),
    }
}

fn analyze_setting_17_5(
    task: &CheckedOccurrenceTask,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<SoundAnalysisOutcome, SilenceReason> {
    if let Some(neg_op) = task.op_records().iter().find(|rec| !rec.positive) {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "setting_17_5_no_negative_output_records".to_owned(),
            detail: format!(
                "negative output record `{}`({}) != `{}` violates Setting 17.5 (G_e^- = empty)",
                neg_op.op_name,
                neg_op.args.join(", "),
                neg_op.output
            ),
        });
    }

    let sort_map: BTreeMap<String, Vec<String>> = task
        .sorts()
        .iter()
        .map(|s| (s.name.clone(), s.elements.clone()))
        .collect();
    let fixed_sorts: BTreeSet<String> = task
        .sorts()
        .iter()
        .filter(|s| s.is_fixed_value)
        .map(|s| s.name.clone())
        .collect();
    let base_readings: Vec<BaseReading> = task
        .base_readings()
        .iter()
        .chain(task.explicit_contexts())
        .map(|r| BaseReading {
            name: r.name.clone(),
            sort: r.sort.clone(),
            values: r.values.clone(),
        })
        .collect();

    let mut ops = Vec::new();
    for op in task.operations() {
        let entries = build_setting_17_5_op_entries(op, &sort_map, task)?;
        ops.push(PartialOpTable {
            name: op.name.clone(),
            arg_sorts: op.arg_sorts.clone(),
            out_sort: op.out_sort.clone(),
            entries,
        });
    }

    let mut rels = Vec::new();
    for rel in task.relations() {
        let entries = build_setting_17_5_rel_entries(rel, &sort_map, task)?;
        rels.push(PartialRelTable {
            name: rel.name.clone(),
            arg_sorts: rel.arg_sorts.clone(),
            entries,
        });
    }

    let ref_res: PartitionRefinementResult = refine_partition(&RefinementInput {
        sorts: sort_map.clone(),
        fixed_sorts: fixed_sorts.clone(),
        base_readings: base_readings.clone(),
        ops: ops.clone(),
        rels: rels.clone(),
        max_iterations: task.max_partitions(),
    })
    .map_err(|err| SilenceReason::ApplicabilityConditionNotMet {
        condition: "setting_17_5_closed".to_owned(),
        detail: format!("{err:?}"),
    })?;

    checks.push(ApplicabilityCheck::passed(
        "setting_17_5_context_refinement_computed",
        MathClause::AatCh17Thm17Dot6,
    ));

    let separating_contexts: Vec<SeparatingContextDetail> = ref_res
        .witnesses
        .iter()
        .map(format_separating_witness)
        .collect();

    let mut extra_collisions = Vec::new();
    let class_of = build_class_lookup(&ref_res.classes);
    for (s, lhs, rhs) in task.identity_requests() {
        let cl = class_of[s.as_str()][lhs.as_str()];
        let cr = class_of[s.as_str()][rhs.as_str()];
        if cl != cr {
            let rep_l = ref_res.classes[s.as_str()][cl][0].as_str();
            let rep_r = ref_res.classes[s.as_str()][cr][0].as_str();
            let witness_expr = ref_res
                .witnesses
                .iter()
                .find(|w| {
                    w.sort == *s
                        && (((w.lhs == *lhs && w.rhs == *rhs) || (w.lhs == *rhs && w.rhs == *lhs))
                            || ((w.lhs == rep_l && w.rhs == rep_r)
                                || (w.lhs == rep_r && w.rhs == rep_l)))
                })
                .map(|w| w.context_expr.clone())
                .unwrap_or_else(|| "context_mismatch".to_owned());
            extra_collisions.push(OccurrenceCollisionDetail {
                kind: "context_separation_conflict".to_owned(),
                detail: format!(
                    "identity request ({lhs}, {rhs}) on sort `{s}` is separated by context `{witness_expr}`"
                ),
                derivation_steps: vec![format!("[sep:{witness_expr}] {s}: {lhs} != {rhs}")],
            });
        }
    }

    let all_readings: Vec<OccurrenceReadingSpec> = task
        .base_readings()
        .iter()
        .chain(task.explicit_contexts())
        .cloned()
        .collect();
    if !extra_collisions.is_empty() || !is_partition_sound(task, &all_readings, &class_of) {
        return Ok(SoundAnalysisOutcome {
            context_equivalence_classes: ref_res.classes,
            separating_contexts,
            sound_partitions: vec![],
            coarsest_sound_classes: None,
            extra_collisions,
        });
    }

    let mut sound_partitions = vec![ref_res.classes.clone()];
    if !task.initial_readouts().is_empty() {
        let mut init_readings = base_readings;
        for ro in task.initial_readouts() {
            let mut values = BTreeMap::new();
            for e in &sort_map[ro.sort.as_str()] {
                values.insert(e.clone(), ro.values.get(e).cloned());
            }
            init_readings.push(BaseReading {
                name: format!("__initial_readout_{}", ro.sort),
                sort: ro.sort.clone(),
                values,
            });
        }
        if let Ok(kerp_res) = refine_partition(&RefinementInput {
            sorts: sort_map,
            fixed_sorts,
            base_readings: init_readings,
            ops,
            rels,
            max_iterations: task.max_partitions(),
        }) {
            let kerp_lookup = build_class_lookup(&kerp_res.classes);
            if kerp_res.classes != ref_res.classes
                && is_partition_sound(task, &all_readings, &kerp_lookup)
            {
                sound_partitions.push(kerp_res.classes);
            }
        }
    }

    Ok(SoundAnalysisOutcome {
        context_equivalence_classes: ref_res.classes.clone(),
        separating_contexts,
        sound_partitions,
        coarsest_sound_classes: Some(ref_res.classes),
        extra_collisions,
    })
}

fn build_setting_17_5_op_entries(
    op: &OccurrenceOpSpec,
    sort_map: &BTreeMap<String, Vec<String>>,
    task: &CheckedOccurrenceTask,
) -> Result<BTreeMap<Vec<String>, Option<String>>, SilenceReason> {
    let mut entries = BTreeMap::new();
    for rec in task.op_records() {
        if rec.positive
            && rec.op_name == op.name
            && rec.arg_sorts == op.arg_sorts
            && let Some(prev) = entries.insert(rec.args.clone(), Some(rec.output.clone()))
            && prev.as_deref() != Some(rec.output.as_str())
        {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "setting_17_5_functional_op".to_owned(),
                detail: format!(
                    "operation `{}` has conflicting outputs on ({})",
                    op.name,
                    rec.args.join(", ")
                ),
            });
        }
    }
    for rec in task.pred_records() {
        if !rec.positive
            && rec.kind == PredicateRecordKind::Domain
            && rec.name == op.name
            && rec.arg_sorts == op.arg_sorts
        {
            if op.is_total {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "setting_17_5_total_op".to_owned(),
                    detail: format!(
                        "total operation `{}` has absent domain record on ({})",
                        op.name,
                        rec.args.join(", ")
                    ),
                });
            }
            if let Some(Some(prev_out)) = entries.insert(rec.args.clone(), None) {
                return Err(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "setting_17_5_consistent_op_domain".to_owned(),
                    detail: format!(
                        "operation `{}` has both output `{prev_out}` and absent domain on ({})",
                        op.name,
                        rec.args.join(", ")
                    ),
                });
            }
        }
    }

    let expected = count_arg_product(&op.arg_sorts, sort_map);
    if entries.len() != expected {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "setting_17_5_closed".to_owned(),
            detail: format!(
                "operation `{}` defines {} of {} tuples (incomplete domain under setting 17.5)",
                op.name,
                entries.len(),
                expected
            ),
        });
    }
    Ok(entries)
}

fn build_setting_17_5_rel_entries(
    rel: &OccurrenceRelSpec,
    sort_map: &BTreeMap<String, Vec<String>>,
    task: &CheckedOccurrenceTask,
) -> Result<BTreeMap<Vec<String>, bool>, SilenceReason> {
    let mut entries = BTreeMap::new();
    for rec in task.pred_records() {
        if rec.kind == PredicateRecordKind::Relation
            && rec.name == rel.name
            && rec.arg_sorts == rel.arg_sorts
            && let Some(prev) = entries.insert(rec.args.clone(), rec.positive)
            && prev != rec.positive
        {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "setting_17_5_consistent_rel".to_owned(),
                detail: format!(
                    "relation `{}` has conflicting records on ({})",
                    rel.name,
                    rec.args.join(", ")
                ),
            });
        }
    }

    let expected = count_arg_product(&rel.arg_sorts, sort_map);
    if entries.len() != expected {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "setting_17_5_closed".to_owned(),
            detail: format!(
                "relation `{}` defines {} of {} tuples (incomplete relation table under setting 17.5)",
                rel.name,
                entries.len(),
                expected
            ),
        });
    }
    Ok(entries)
}

fn count_arg_product(arg_sorts: &[String], sort_map: &BTreeMap<String, Vec<String>>) -> usize {
    arg_sorts
        .iter()
        .map(|s| sort_map[s].len())
        .try_fold(1usize, |acc, x| acc.checked_mul(x))
        .unwrap_or(usize::MAX)
}

fn analyze_general_finite(
    task: &CheckedOccurrenceTask,
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<SoundAnalysisOutcome, SilenceReason> {
    let mut per_sort_partitions: Vec<(String, Vec<Vec<Vec<String>>>)> = Vec::new();
    let max_part = task.max_partitions();
    for sort in task.sorts() {
        let parts = if sort.is_fixed_value {
            vec![sort.elements.iter().map(|e| vec![e.clone()]).collect()]
        } else {
            enumerate_set_partitions(&sort.elements, max_part)
                .map_err(|e| map_algebra_error_to_silence(&format!("{e:?}")))?
        };
        per_sort_partitions.push((sort.name.clone(), parts));
    }

    let mut combinations = vec![BTreeMap::new()];
    for (s_name, parts) in &per_sort_partitions {
        let mut next = Vec::new();
        for base in &combinations {
            for p in parts {
                if next.len() >= max_part {
                    return Err(SilenceReason::FiniteEnumerationOutOfScope {
                        detail: format!(
                            "product of sound partition candidates exceeds max_partitions ({max_part})"
                        ),
                    });
                }
                let mut m = base.clone();
                m.insert(s_name.clone(), p.clone());
                next.push(m);
            }
        }
        combinations = next;
    }

    let all_readings: Vec<OccurrenceReadingSpec> = task
        .base_readings()
        .iter()
        .chain(task.explicit_contexts())
        .cloned()
        .collect();

    let mut sound_partitions = Vec::new();
    for cand in combinations {
        let lookup = build_class_lookup(&cand);
        if is_partition_sound(task, &all_readings, &lookup) {
            sound_partitions.push(cand);
        }
    }

    checks.push(ApplicabilityCheck::passed(
        "general_finite_sound_identifications_enumerated",
        MathClause::AatCh17Ex17Dot7,
    ));

    let coarsest_sound_classes = sound_partitions
        .iter()
        .find(|cand| {
            sound_partitions.iter().all(|other| {
                task.sorts()
                    .iter()
                    .all(|s| partition_refines(&other[&s.name], &cand[&s.name]))
            })
        })
        .cloned();

    let mut ctx_classes = coarsest_sound_classes
        .clone()
        .or_else(|| sound_partitions.first().cloned())
        .unwrap_or_default();
    if ctx_classes.is_empty() {
        for s in task.sorts() {
            ctx_classes.insert(
                s.name.clone(),
                s.elements.iter().map(|e| vec![e.clone()]).collect(),
            );
        }
    }

    Ok(SoundAnalysisOutcome {
        context_equivalence_classes: ctx_classes,
        separating_contexts: vec![],
        sound_partitions,
        coarsest_sound_classes,
        extra_collisions: vec![],
    })
}

pub(super) fn is_partition_sound(
    task: &CheckedOccurrenceTask,
    readings: &[OccurrenceReadingSpec],
    class_of: &BTreeMap<&str, BTreeMap<&str, usize>>,
) -> bool {
    for (s, lhs, rhs) in task.identity_requests() {
        if class_of[s.as_str()][lhs.as_str()] != class_of[s.as_str()][rhs.as_str()] {
            return false;
        }
    }

    for s in task.sorts().iter().filter(|s| s.is_fixed_value) {
        let seen: BTreeSet<usize> = s
            .elements
            .iter()
            .map(|e| class_of[s.name.as_str()][e.as_str()])
            .collect();
        if seen.len() != s.elements.len() {
            return false;
        }
    }

    let preserve_set: BTreeSet<&str> = task
        .preserve_full_domains()
        .iter()
        .map(String::as_str)
        .collect();
    let preserve_all = preserve_set.contains("*");
    for r in readings {
        let mut class_val: BTreeMap<usize, Option<&str>> = BTreeMap::new();
        for (elem, val_opt) in &r.values {
            let cid = class_of[r.sort.as_str()][elem.as_str()];
            let v = val_opt.as_deref();
            if let Some(prev) = class_val.get(&cid) {
                if *prev != v {
                    return false;
                }
            } else {
                class_val.insert(cid, v);
            }
        }
    }

    let pos_ops: Vec<_> = task.op_records().iter().filter(|r| r.positive).collect();
    let neg_ops: Vec<_> = task.op_records().iter().filter(|r| !r.positive).collect();
    let tuple_cids = |arg_sorts: &[String], args: &[String]| -> Vec<usize> {
        arg_sorts
            .iter()
            .zip(args)
            .map(|(s, a)| class_of[s.as_str()][a.as_str()])
            .collect()
    };

    for i in 0..pos_ops.len() {
        let r1 = pos_ops[i];
        let c1 = tuple_cids(&r1.arg_sorts, &r1.args);
        let o1 = class_of[r1.out_sort.as_str()][r1.output.as_str()];
        for r2 in &pos_ops[i + 1..] {
            if r1.op_name == r2.op_name
                && r1.arg_sorts == r2.arg_sorts
                && r1.out_sort == r2.out_sort
                && c1 == tuple_cids(&r2.arg_sorts, &r2.args)
                && o1 != class_of[r2.out_sort.as_str()][r2.output.as_str()]
            {
                return false;
            }
        }
        for neg in &neg_ops {
            if r1.op_name == neg.op_name
                && r1.arg_sorts == neg.arg_sorts
                && r1.out_sort == neg.out_sort
                && c1 == tuple_cids(&neg.arg_sorts, &neg.args)
                && o1 == class_of[neg.out_sort.as_str()][neg.output.as_str()]
            {
                return false;
            }
        }
    }

    let mut pos_preds: Vec<(&PredicateRecordKind, &str, &[String], &[String])> = task
        .pred_records()
        .iter()
        .filter(|r| r.positive)
        .map(|r| {
            (
                &r.kind,
                r.name.as_str(),
                r.arg_sorts.as_slice(),
                r.args.as_slice(),
            )
        })
        .collect();
    for r in &pos_ops {
        pos_preds.push((
            &PredicateRecordKind::Domain,
            r.op_name.as_str(),
            r.arg_sorts.as_slice(),
            r.args.as_slice(),
        ));
    }

    for neg in task.pred_records().iter().filter(|r| !r.positive) {
        let nc = tuple_cids(&neg.arg_sorts, &neg.args);
        for &(pk, pn, pas, pa) in &pos_preds {
            if *pk == neg.kind
                && pn == neg.name
                && pas == neg.arg_sorts.as_slice()
                && tuple_cids(pas, pa) == nc
            {
                return false;
            }
        }
    }

    let unique_preds: BTreeSet<(&PredicateRecordKind, &str, &[String])> = pos_preds
        .iter()
        .map(|(pk, pn, pas, _)| (*pk, *pn, *pas))
        .collect();
    for (pk, pn, pas) in unique_preds {
        let want_full = preserve_all || preserve_set.contains(pn);
        if !want_full {
            continue;
        }
        let pos_cid_tuples: BTreeSet<Vec<usize>> = pos_preds
            .iter()
            .filter(|(k, n, s, _)| *k == pk && *n == pn && *s == pas)
            .map(|(_, _, s, a)| tuple_cids(s, a))
            .collect();
        let pos_arg_tuples: BTreeSet<Vec<&str>> = pos_preds
            .iter()
            .filter(|(k, n, s, _)| *k == pk && *n == pn && *s == pas)
            .map(|(_, _, _, a)| a.iter().map(String::as_str).collect())
            .collect();
        let mut all_tuples = vec![vec![]];
        for s_name in pas {
            let elems = &task
                .sorts()
                .iter()
                .find(|s| s.name == *s_name)
                .expect("validated sort")
                .elements;
            let mut next = Vec::new();
            for prefix in &all_tuples {
                for e in elems {
                    let mut row = prefix.clone();
                    row.push(e.as_str());
                    next.push(row);
                }
            }
            all_tuples = next;
        }
        for tup in all_tuples {
            if !pos_arg_tuples.contains(&tup) {
                let cids: Vec<usize> = pas
                    .iter()
                    .zip(&tup)
                    .map(|(s, a)| class_of[s.as_str()][*a])
                    .collect();
                if pos_cid_tuples.contains(&cids) {
                    return false;
                }
            }
        }
    }

    true
}
