//! AAT 第17章後半（衝突・分離文脈の整形、および命題 17.11 補助属性の最小値域構成・再評価検算）。

use crate::algebra::congruence::{
    CollisionKind, CollisionWitness, DerivationReason, DerivationStep,
};
use crate::algebra::partition::SeparatingWitness;
use crate::ir::occurrence::{CheckedOccurrenceTask, OccurrenceReadingSpec};
use crate::ir::result::ReevalCheck;
use crate::ir::result_phase5_obs::{
    AttributeRealizationDetail, OccurrenceCollisionDetail, SeparatingContextDetail,
};
use crate::solver::occurrence::is_partition_sound;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn format_collision(w: &CollisionWitness) -> OccurrenceCollisionDetail {
    let (kind, detail) = match &w.kind {
        CollisionKind::FixedValueCollision { sort, lhs, rhs } => (
            "fixed_value_collision".to_owned(),
            format!("fixed sort `{sort}` elements `{lhs}` != `{rhs}` became equivalent"),
        ),
        CollisionKind::OutputRecordCollision {
            op_name,
            pos_args,
            pos_out,
            neg_args,
            neg_out,
        } => (
            "output_record_collision".to_owned(),
            format!(
                "positive `{op_name}({}) = {pos_out}` contradicts negative `{op_name}({}) != {neg_out}`",
                pos_args.join(", "),
                neg_args.join(", ")
            ),
        ),
        CollisionKind::DomainRecordCollision {
            op_name,
            pos_args,
            neg_args,
        } => (
            "domain_record_collision".to_owned(),
            format!(
                "positive domain `{op_name}({})` contradicts absent domain `{op_name}({})`",
                pos_args.join(", "),
                neg_args.join(", ")
            ),
        ),
        CollisionKind::RelationRecordCollision {
            rel_name,
            pos_args,
            neg_args,
        } => (
            "relation_record_collision".to_owned(),
            format!(
                "positive relation `{rel_name}({})` contradicts negative `{rel_name}({})`",
                pos_args.join(", "),
                neg_args.join(", ")
            ),
        ),
    };
    let derivation_steps = w.derivation.iter().map(format_derivation_step).collect();
    OccurrenceCollisionDetail {
        kind,
        detail,
        derivation_steps,
    }
}

fn format_derivation_step(step: &DerivationStep) -> String {
    match &step.reason {
        DerivationReason::IdentityRequest { sort, lhs, rhs } => {
            format!("[req] {sort}: {lhs} ~ {rhs}")
        }
        DerivationReason::Reflexivity { sort, elem } => {
            format!("[refl] {sort}: {elem} ~ {elem}")
        }
        DerivationReason::Symmetry { sort, lhs, rhs } => {
            format!("[sym] {sort}: {lhs} ~ {rhs}")
        }
        DerivationReason::Transitivity { sort, a, b, c } => {
            format!("[trans] {sort}: {a} ~ {b} ~ {c}")
        }
        DerivationReason::Functionality {
            op_name,
            args_a,
            args_b,
            out_a,
            out_b,
        } => format!(
            "[func:{op_name}] ({}) ~ ({}) => {out_a} ~ {out_b}",
            args_a.join(", "),
            args_b.join(", ")
        ),
    }
}

pub(super) fn format_separating_witness(w: &SeparatingWitness) -> SeparatingContextDetail {
    SeparatingContextDetail {
        sort: w.sort.clone(),
        lhs: w.lhs.clone(),
        rhs: w.rhs.clone(),
        context_expr: w.context_expr.clone(),
        lhs_value: w.lhs_value.clone(),
        rhs_value: w.rhs_value.clone(),
        verified: w.verified,
    }
}

type ClassPartitionMap = BTreeMap<String, Vec<Vec<String>>>;
type KappaPartitionList<'a> = Vec<(BTreeMap<String, usize>, &'a ClassPartitionMap)>;

pub(super) fn build_class_lookup(
    classes: &ClassPartitionMap,
) -> BTreeMap<&str, BTreeMap<&str, usize>> {
    let mut out = BTreeMap::new();
    for (sort, cls_list) in classes {
        let mut m = BTreeMap::new();
        for (cid, cls) in cls_list.iter().enumerate() {
            for elem in cls {
                m.insert(elem.as_str(), cid);
            }
        }
        out.insert(sort.as_str(), m);
    }
    out
}

fn fiber_key_for<'a>(task: &'a CheckedOccurrenceTask, sort_name: &str, elem: &str) -> &'a str {
    task.initial_readouts()
        .iter()
        .find(|ro| ro.sort == sort_name)
        .and_then(|ro| ro.values.get(elem))
        .map(String::as_str)
        .unwrap_or("_")
}

/// 評価分離のみ（操作非保存）に対する各 sort の最小補助属性値域サイズ $\kappa_s(\mathcal{S})$ を求める。
pub(super) fn compute_eval_separation_kappa(
    task: &CheckedOccurrenceTask,
) -> BTreeMap<String, usize> {
    let mut eval_kappa = BTreeMap::new();
    for sort in task.sorts() {
        if sort.is_fixed_value {
            let mut per_fiber: BTreeMap<&str, usize> = BTreeMap::new();
            for elem in &sort.elements {
                let fk = fiber_key_for(task, &sort.name, elem);
                *per_fiber.entry(fk).or_insert(0) += 1;
            }
            eval_kappa.insert(
                sort.name.clone(),
                per_fiber.into_values().max().unwrap_or(1),
            );
            continue;
        }
        let mut per_fiber: BTreeMap<&str, BTreeSet<Vec<Option<&str>>>> = BTreeMap::new();
        for elem in &sort.elements {
            let sig: Vec<Option<&str>> = task
                .base_readings()
                .iter()
                .chain(task.explicit_contexts())
                .filter(|r| r.sort == sort.name)
                .map(|r| r.values.get(elem).and_then(|v| v.as_deref()))
                .collect();
            let fk = fiber_key_for(task, &sort.name, elem);
            per_fiber.entry(fk).or_default().insert(sig);
        }
        eval_kappa.insert(
            sort.name.clone(),
            per_fiber.into_values().map(|s| s.len()).max().unwrap_or(1),
        );
    }
    eval_kappa
}

pub(super) fn compute_attribute_failure_with_eval_kappa(
    task: &CheckedOccurrenceTask,
    reason: &str,
) -> AttributeRealizationDetail {
    AttributeRealizationDetail {
        eval_separation_kappa: compute_eval_separation_kappa(task),
        sound_identification_exists: false,
        minimal_sound_kappa_tuples: vec![],
        selected_attribute_assignment: BTreeMap::new(),
        failure_reason: Some(reason.to_owned()),
        reevaluation: None,
    }
}

/// 命題 17.11: 全健全同定から各 sort のファイバ別最大クラス数 $\kappa_s(\equiv)$ を計算し、
/// パレート極小な組とその属性実現 $\alpha_s$ を構成・再評価検算する。
pub(super) fn compute_attribute_realization(
    task: &CheckedOccurrenceTask,
    sound_partitions: &[BTreeMap<String, Vec<Vec<String>>>],
) -> AttributeRealizationDetail {
    let eval_separation_kappa = compute_eval_separation_kappa(task);
    let mut kappa_with_part: KappaPartitionList<'_> = Vec::new();

    for part in sound_partitions {
        let lookup = build_class_lookup(part);
        let mut tuple = BTreeMap::new();
        for sort in task.sorts() {
            let mut per_fiber: BTreeMap<&str, BTreeSet<usize>> = BTreeMap::new();
            for elem in &sort.elements {
                let fk = fiber_key_for(task, &sort.name, elem);
                let cid = lookup[sort.name.as_str()][elem.as_str()];
                per_fiber.entry(fk).or_default().insert(cid);
            }
            tuple.insert(
                sort.name.clone(),
                per_fiber.into_values().map(|s| s.len()).max().unwrap_or(1),
            );
        }
        kappa_with_part.push((tuple, part));
    }

    let mut minimal_pairs: KappaPartitionList<'_> = Vec::new();
    for &(ref kt, part) in &kappa_with_part {
        let dominated = kappa_with_part.iter().any(|(other, _)| {
            other != kt
                && kt.keys().all(|k| other[k] <= kt[k])
                && kt.keys().any(|k| other[k] < kt[k])
        });
        if !dominated && !minimal_pairs.iter().any(|(m, _)| m == kt) {
            minimal_pairs.push((kt.clone(), part));
        }
    }
    minimal_pairs.sort_by_key(|(kt, _)| kt.values().sum::<usize>());

    let minimal_sound_kappa_tuples: Vec<BTreeMap<String, usize>> =
        minimal_pairs.iter().map(|(kt, _)| kt.clone()).collect();

    let Some((_, best_part)) = minimal_pairs.first() else {
        return compute_attribute_failure_with_eval_kappa(
            task,
            "no minimal auxiliary attribute realization exists",
        );
    };

    let best_lookup = build_class_lookup(best_part);
    let mut selected_attribute_assignment: BTreeMap<String, BTreeMap<String, usize>> =
        BTreeMap::new();
    let mut recovered_classes: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();

    for sort in task.sorts() {
        let mut fiber_cids: BTreeMap<&str, BTreeMap<usize, usize>> = BTreeMap::new();
        let mut assign = BTreeMap::new();
        let mut by_pair: BTreeMap<(&str, usize), Vec<String>> = BTreeMap::new();
        for elem in &sort.elements {
            let fk = fiber_key_for(task, &sort.name, elem);
            let cid = best_lookup[sort.name.as_str()][elem.as_str()];
            let map = fiber_cids.entry(fk).or_default();
            let next_id = map.len();
            let aux_val = *map.entry(cid).or_insert(next_id);
            assign.insert(elem.clone(), aux_val);
            by_pair.entry((fk, aux_val)).or_default().push(elem.clone());
        }
        selected_attribute_assignment.insert(sort.name.clone(), assign);
        let mut cls: Vec<Vec<String>> = by_pair
            .into_values()
            .map(|mut g| {
                g.sort();
                g
            })
            .collect();
        cls.sort();
        recovered_classes.insert(sort.name.clone(), cls);
    }

    let mut expected_norm = (*best_part).clone();
    for cls in expected_norm.values_mut() {
        for g in cls.iter_mut() {
            g.sort();
        }
        cls.sort();
    }
    let rec_lookup = build_class_lookup(&recovered_classes);
    let all_readings: Vec<OccurrenceReadingSpec> = task
        .base_readings()
        .iter()
        .chain(task.explicit_contexts())
        .cloned()
        .collect();
    let matches_part = recovered_classes == expected_norm;
    let sound_ok = is_partition_sound(task, &all_readings, &rec_lookup);
    let reeval = ReevalCheck {
        checked: true,
        matched: matches_part && sound_ok,
        detail: if matches_part && sound_ok {
            "recovered equivalence from (p_s, alpha_s) matches sound quotient and preserves all requests/ops/readings"
                .to_owned()
        } else {
            format!("attribute recovery mismatch (part_eq={matches_part}, sound={sound_ok})")
        },
    };

    AttributeRealizationDetail {
        eval_separation_kappa,
        sound_identification_exists: true,
        minimal_sound_kappa_tuples,
        selected_attribute_assignment,
        failure_reason: None,
        reevaluation: Some(reeval),
    }
}
