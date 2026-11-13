//! 保存結果には値の参照グラフを残し、導出グラフを公開しない。
use super::{EvidenceClass, Node, NodeRef, NodeType};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
};
use archsig_input::result::Signal;
use std::{
    collections::{BTreeMap, BTreeSet, hash_map::DefaultHasher},
    hash::Hasher,
    io::{self, Write},
};

fn refs(
    value: &Json,
    into: &mut BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(point)?;
        match value {
            Json::Obj(fields) => {
                if fields.len() == 1
                    && let Some(Json::Str(id)) = fields.get("node")
                {
                    into.insert(id.clone());
                } else {
                    for value in fields.values() {
                        refs(value, into, control, point)?;
                    }
                }
            }
            Json::Arr(items) => {
                for value in items {
                    refs(value, into, control, point)?;
                }
            }
            Json::NodeReferences(items) => {
                for index in items {
                    control.checkpoint(point)?;
                    into.insert(format!("n{index}"));
                }
            }
            _ => {}
        }
        control.checkpoint(point)?;
        Ok(())
    })
}

// Compress only the completed public projection. Native wire and input objects keep their shape.
fn compact_reference_arrays(
    value: &mut Json,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(point)?;
        match value {
            Json::Arr(items) => {
                let mut indices = Vec::new();
                for item in items.iter() {
                    control.checkpoint(point)?;
                    let Some(index) = item.exact_node_reference() else {
                        break;
                    };
                    indices.push(index);
                }
                if !items.is_empty() && indices.len() == items.len() {
                    *value = Json::NodeReferences(indices);
                } else {
                    // Release a successful prefix before traversing the mixed array.
                    drop(indices);
                    // Mixed/malformed arrays retain every original value and its spelling.
                    for item in items {
                        compact_reference_arrays(item, control, point)?;
                    }
                }
            }
            Json::Obj(fields) => {
                for item in fields.values_mut() {
                    compact_reference_arrays(item, control, point)?;
                }
            }
            _ => {}
        }
        control.checkpoint(point)?;
        Ok(())
    })
}
fn reference(value: Option<&Json>) -> Option<NodeRef> {
    let Json::Obj(fields) = value? else {
        return None;
    };
    if fields.len() != 1 {
        return None;
    }
    let Json::Str(id) = fields.get("node")? else {
        return None;
    };
    Some(NodeRef(id.strip_prefix('n')?.parse().ok()?))
}
// 商の実像・核の包含は写像データ。導出arguments全体を保存へ戻さない。
fn quotient_maps(
    node: &Json,
    native: &[Node],
    into: &mut BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    let Json::Obj(fields) = node else {
        return Ok(());
    };
    let Some(Json::Obj(value)) = fields.get("value") else {
        return Ok(());
    };
    let Some(Json::Obj(representation)) = value.get("representation") else {
        return Ok(());
    };
    if !matches!(representation.get("kind"), Some(Json::Str(kind)) if kind == "affine") {
        return Ok(());
    }
    let (Some(image), Some(kernel), Some(linear), Some(projection)) = (
        reference(representation.get("image")),
        reference(representation.get("kernel")),
        reference(representation.get("map")),
        reference(value.get("projection")),
    ) else {
        return Ok(());
    };
    let Some(Node {
        ty: NodeType::ModuleMap(source, target),
        ..
    }) = native.get(linear.0)
    else {
        return Ok(());
    };
    let Some(projection) = native.get(projection.0) else {
        return Ok(());
    };
    if !matches!(
        projection.ty,
        NodeType::Construction(super::super::construction_result::ConstructionType::StateMap)
    ) {
        return Ok(());
    }
    for argument in &projection.arguments {
        control.checkpoint(point)?;
        if let Some(Node {
            ty: NodeType::ModuleMap(from, to),
            ..
        }) = native.get(argument.0)
            && ((*from == image && to == target) || (*from == kernel && to == source))
        {
            into.insert(format!("n{}", argument.0));
        }
    }
    Ok(())
}
fn rename(
    value: &mut Json,
    ids: &BTreeMap<String, String>,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(point)?;
        match value {
            Json::Obj(fields) => {
                if fields.len() == 1
                    && let Some(Json::Str(id)) = fields.get_mut("node")
                {
                    *id = ids[id].clone();
                } else {
                    for value in fields.values_mut() {
                        rename(value, ids, control, point)?;
                    }
                }
            }
            Json::Arr(items) => {
                for value in items {
                    rename(value, ids, control, point)?;
                }
            }
            Json::NodeReferences(items) => {
                for index in items {
                    control.checkpoint(point)?;
                    // Both maps are built here from canonical numeric node identities.
                    *index = ids[&format!("n{index}")]
                        .strip_prefix('n')
                        .unwrap()
                        .parse()
                        .unwrap();
                }
            }
            _ => {}
        }
        control.checkpoint(point)?;
        Ok(())
    })
}
fn retain_evidence(
    fields: &mut archsig_common::canonical::JsonObject,
    examples: &BTreeSet<String>,
    completions: &BTreeSet<String>,
) {
    let Some(mut evidence) = fields.remove("evidence") else {
        return;
    };
    let Json::Arr(values) = &mut evidence else {
        return;
    };
    let mut counters = vec![];
    let mut witnesses = vec![];
    for value in std::mem::take(values) {
        let Json::Obj(reference) = &value else {
            continue;
        };
        let Some(Json::Str(id)) = reference.get("node") else {
            continue;
        };
        if examples.contains(id) {
            counters.push(value);
        } else if completions.contains(id) {
            witnesses.push(value);
        }
    }
    if !counters.is_empty() {
        fields.insert("counterexamples".into(), Json::Arr(counters));
    }
    if !witnesses.is_empty() {
        fields.insert("evidence".into(), Json::Arr(witnesses));
    }
}
/// 同じ観測要求を使用箇所ごとに繰り返さない。補う対象は missing に残す。
pub(in crate::observed) fn concise_reasons(reasons: &mut Vec<Json>) {
    let mut seen = BTreeSet::new();
    reasons.retain_mut(|reason| {
        if let Json::Obj(fields) = reason
            && matches!(fields.get("code"), Some(Json::Str(code)) if code == "missing_observation")
            && let Some(Json::Arr(missing)) = fields.get_mut("missing")
            && !missing.is_empty()
        {
            missing.sort_by_cached_key(Json::canonical);
            missing.dedup();
            fields.remove("location");
        }
        seen.insert(reason.canonical())
    });
}
fn cleaned_node(
    native: &[Node],
    index: usize,
    control: &Control,
    point: Checkpoint,
) -> Result<Json, Signal> {
    control.checkpoint(point)?;
    // Path/compound の既出 Ref 解決には元の全 prior と arguments を使う。
    let mut node = native[index].wire_with_support(index, &native[..index], false, control)?;
    control.checkpoint(point)?;
    clean_reasons(&mut node, control, point)?;
    Ok(node)
}
fn public_raw_node(
    native: &[Node],
    index: usize,
    proofs: &BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<Json, Signal> {
    let mut node = cleaned_node(native, index, control, point)?;
    remove_proof_refs(&mut node, proofs);
    Ok(node)
}
// answerはEvaluation全体でなく適用可否と後続環境だけを読む。
fn evaluation_answer_fields(
    native: &[Node],
    index: usize,
    proofs: &BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<Option<archsig_common::canonical::JsonObject>, Signal> {
    if let Some(payload) = &native[index].payload
        && matches!(payload, super::Payload::Evaluation { .. })
    {
        control.checkpoint(point)?;
        let mut value = Json::Obj(
            payload
                .evaluation_output_fields(false)
                .expect("Evaluation欄"),
        );
        control.checkpoint(point)?;
        clean_reasons(&mut value, control, point)?;
        remove_proof_refs(&mut value, proofs);
        let Json::Obj(fields) = &mut value else {
            unreachable!()
        };
        return Ok(Some(std::mem::take(fields)));
    }
    // 一般のraw表示入口の挙動は維持する。型を取り違えたRefも新たに解釈しない。
    let mut node = public_raw_node(native, index, proofs, control, point)?;
    let Json::Obj(fields) = &mut node else {
        return Ok(None);
    };
    let Some(Json::Obj(value)) = fields.get_mut("value") else {
        return Ok(None);
    };
    value.retain(|key, _| matches!(key.as_str(), "applicability" | "environment"));
    Ok(Some(std::mem::take(value)))
}
fn law_claim(
    reference: &Json,
    native: &[Node],
    proofs: &BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<bool, Signal> {
    let Json::Obj(reference) = reference else {
        return Ok(false);
    };
    let Some(Json::Str(id)) = reference.get("node") else {
        return Ok(false);
    };
    let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
    control.checkpoint(point)?;
    if let Some(super::Payload::Construction(value)) = &native[index].payload
        && let Some(Json::Obj(fields)) = value.retained_wire()
    {
        let is_law = matches!(fields.get("predicate"), Some(Json::Str(predicate)) if predicate == "law_holds");
        control.checkpoint(point)?;
        return Ok(is_law);
    }
    let node = public_raw_node(native, index, proofs, control, point)?;
    let Json::Obj(fields) = &node else {
        return Ok(false);
    };
    let Some(Json::Obj(value)) = fields.get("value") else {
        return Ok(false);
    };
    Ok(matches!(value.get("predicate"), Some(Json::Str(predicate)) if predicate == "law_holds"))
}
fn project_node(
    native: &[Node],
    index: usize,
    proofs: &BTreeSet<String>,
    examples: &BTreeSet<String>,
    completions: &BTreeSet<String>,
    control: &Control,
    point: Checkpoint,
) -> Result<Json, Signal> {
    control.checkpoint(point)?;
    let mut node = native[index].project_wire(index, &native[..index]);
    control.checkpoint(point)?;
    clean_reasons(&mut node, control, point)?;
    remove_proof_refs(&mut node, proofs);
    let Json::Obj(fields) = &mut node else {
        unreachable!()
    };
    if let Some(Json::Obj(judgment)) = fields.get_mut("judgment") {
        retain_evidence(judgment, examples, completions);
    }
    if examples.contains(&format!("n{index}")) {
        fields.insert("type".into(), Json::str("Counterexample"));
    }
    if matches!(native[index].ty, NodeType::Evaluation(_)) {
        fields.insert("type".into(), Json::str("EvaluationResult"));
    }
    if let Some(Json::Obj(value)) = fields.get_mut("value") {
        match native[index].ty {
            NodeType::Evaluation(_) => {
                // 適用可否、引数、値、後続要求が使う環境だけが結果。
                // 子評価や式の出現位置は内部の検査用グラフに留める。
                value.retain(|key, _| {
                    matches!(
                        key.as_str(),
                        "applicability" | "bindings" | "value" | "environment"
                    )
                });
            }
            NodeType::LawInstance => {
                if let Some(Json::Obj(body)) = value.get("body") {
                    let Some(Json::Str(id)) = body.get("node") else {
                        unreachable!()
                    };
                    let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
                    if let Some(payload) = &native[index].payload
                        && let Json::Obj(body) = &payload.wire()
                        && let Some(parameters) = body.get("parameters")
                    {
                        value.insert("parameters".into(), parameters.clone());
                    }
                }
                value.retain(|key, _| {
                    matches!(key.as_str(), "name" | "role" | "bindings" | "parameters")
                });
            }
            NodeType::Construction(_) => {
                value.remove("construction");
            }
            NodeType::Evidence => {
                value.remove("evaluation");
            }
            _ => {}
        }
    }
    control.checkpoint(point)?;
    Ok(node)
}

#[cfg(test)]
mod notice_tests {
    use super::*;
    #[test]
    fn repeated_missing_uses_keep_distinct_targets_and_other_reasons() {
        let reason = |subject: &str, field: &str, location: u64| {
            Json::obj([
                ("code", Json::str("missing_observation")),
                (
                    "missing",
                    Json::Arr(vec![Json::obj([
                        ("subject", Json::str(subject)),
                        ("field", Json::str(field)),
                    ])]),
                ),
                ("location", Json::Nat(location)),
            ])
        };
        let other = Json::obj([
            ("code", Json::str("condition_failed")),
            ("location", Json::Nat(3)),
        ]);
        let empty = Json::obj([
            ("code", Json::str("missing_observation")),
            ("missing", Json::Arr(vec![])),
            ("location", Json::Nat(4)),
        ]);
        let mut reasons = vec![
            reason("p", "x", 1),
            reason("p", "x", 2),
            reason("q", "x", 1),
            reason("p", "y", 1),
            other.clone(),
            empty.clone(),
        ];
        concise_reasons(&mut reasons);
        assert_eq!(reasons.len(), 5);
        assert_eq!(reasons[3], other);
        assert_eq!(reasons[4], empty);
        let targets: Vec<_> = reasons[..3]
            .iter()
            .map(|reason| {
                let Json::Obj(fields) = reason else { panic!() };
                assert!(!fields.contains_key("location"));
                fields["missing"].canonical()
            })
            .collect();
        assert_eq!(targets.iter().collect::<BTreeSet<_>>().len(), 3);
    }
}
pub(super) fn clean_reasons(
    value: &mut Json,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(point)?;
        match value {
            Json::Obj(fields) => {
                if fields.contains_key("code") && fields.contains_key("message") {
                    fields.insert("dependencies".into(), Json::Arr(vec![]));
                    if let Some(Json::Obj(details)) = fields.get_mut("details") {
                        let mut removed = Vec::new();
                        for (key, value) in details.iter() {
                            let mut references = BTreeSet::new();
                            refs(value, &mut references, control, point)?;
                            if !references.is_empty() {
                                removed.push(key.clone());
                            }
                        }
                        for key in removed {
                            details.remove(&key);
                        }
                    }
                }
                for value in fields.values_mut() {
                    clean_reasons(value, control, point)?;
                }
                if let Some(Json::Arr(reasons)) = fields.get_mut("reasons") {
                    concise_reasons(reasons);
                }
            }
            Json::Arr(items) => {
                for value in items {
                    clean_reasons(value, control, point)?;
                }
            }
            _ => {}
        }
        control.checkpoint(point)?;
        Ok(())
    })
}
fn remove_proof_refs(value: &mut Json, proofs: &BTreeSet<String>) -> bool {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.len() == 1
                && let Some(Json::Str(id)) = fields.get("node")
            {
                return !proofs.contains(id);
            }
            fields.retain(|_, value| remove_proof_refs(value, proofs));
            true
        }
        // This helper runs only on raw native wire, before reference-array compression.
        Json::NodeReferences(_) => unreachable!("proof filtering precedes result compression"),
        Json::Arr(items) => {
            items.retain_mut(|value| remove_proof_refs(value, proofs));
            true
        }
        _ => true,
    })
}
// Feed the same write_u8 sequence for the same canonical byte stream. Hasher::write
// chunk boundaries are not assumed to be invisible to a Hasher implementation.
struct FingerprintWriter(DefaultHasher);
impl Write for FingerprintWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        for byte in bytes {
            self.0.write_u8(*byte);
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
pub(in crate::observed) fn canonical_fingerprint(value: &Json) -> u64 {
    let mut sink = FingerprintWriter(DefaultHasher::new());
    value
        .write_canonical(&mut sink)
        .expect("in-memory fingerprint sink");
    sink.0.finish()
}
// Accepted nodes retain their root id. Only that field is ignored; all child
// values use Json's exact Eq, including compact-reference/array equivalence.
fn same_public_record(a: &Json, b: &Json) -> bool {
    let (Json::Obj(a), Json::Obj(b)) = (a, b) else {
        return false;
    };
    a.iter()
        .filter(|(key, _)| key.as_str() != "id")
        .eq(b.iter().filter(|(key, _)| key.as_str() != "id"))
}
fn shared_position(
    mut positions: impl Iterator<Item = usize>,
    nodes: &[Json],
    candidate: &Json,
) -> Option<usize> {
    positions.find(|position| same_public_record(candidate, &nodes[*position]))
}

fn dedup_plan_dependents(
    node: &mut Json,
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    let Json::Obj(fields) = node else {
        return Ok(());
    };
    let Some(Json::Obj(value)) = fields.get_mut("value") else {
        return Ok(());
    };
    let Some(Json::Arr(requirements)) = value.get_mut("requirements") else {
        return Ok(());
    };
    for requirement in requirements {
        control.checkpoint(point)?;
        let Json::Obj(requirement) = requirement else {
            continue;
        };
        if let Some(Json::NodeReferences(dependents)) = requirement.get_mut("dependents") {
            let mut seen = BTreeSet::new();
            let mut unique = Vec::new();
            for &reference in dependents.iter() {
                control.checkpoint(point)?;
                if seen.insert(reference) {
                    unique.push(reference);
                }
            }
            *dependents = unique;
        }
    }
    Ok(())
}
fn share_projected(
    projected: BTreeMap<usize, Json>,
    native: &[Node],
    ids: &mut BTreeMap<String, String>,
    control: &Control,
    point: Checkpoint,
) -> Result<Vec<Json>, Signal> {
    let mut values = BTreeMap::<u64, Vec<(usize, usize)>>::new();
    let mut nodes = Vec::new();
    // 到達順でなく元の数値 index 順が canonical 共有の代表と番号を決める。
    for (index, mut node) in projected {
        control.checkpoint(point)?;
        let old_id = format!("n{index}");
        rename(&mut node, ids, control, point)?;
        if native[index].ty == NodeType::ObservationPlan {
            // 共有で同じ参照になったときだけ、同じ必要slotの参照をまとめる。
            dedup_plan_dependents(&mut node, control, point)?;
        }
        // 環・基底・関係を含む表示全体の一致だけを共有する。同型は推測しない。
        let shared = matches!(
            native[index].ty,
            NodeType::Value(_)
                | NodeType::Expression(_)
                | NodeType::Vector(_)
                | NodeType::ModuleMap(_, _)
                | NodeType::Domain
                | NodeType::Construction(
                    super::super::construction_result::ConstructionType::StateMap
                        | super::super::construction_result::ConstructionType::Ring
                        | super::super::construction_result::ConstructionType::Module
                )
        );
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.remove("id");
        let key = shared.then(|| canonical_fingerprint(&node));
        if let Some(position) = key.and_then(|key| values.get(&key)).and_then(|positions| {
            let same_types = positions.iter().filter_map(|&(position, original)| {
                // 保存表で Expression の結果型は省略されるため、核の型も照合する。
                let same_type = !matches!(native[index].ty, NodeType::Expression(_))
                    || native[original].ty == native[index].ty;
                same_type.then_some(position)
            });
            shared_position(same_types, &nodes, &node)
        }) {
            let Json::Obj(existing) = &nodes[position] else {
                unreachable!()
            };
            let Json::Str(existing_id) = &existing["id"] else {
                unreachable!()
            };
            ids.insert(old_id, existing_id.clone());
            continue;
        }
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.insert("id".into(), Json::str(&old_id));
        if let Some(key) = key {
            values.entry(key).or_default().push((nodes.len(), index));
        }
        nodes.push(node);
    }
    // No fingerprint positions survive the final node renumbering.
    drop(values);
    Ok(nodes)
}

pub(super) fn compact(
    result: &mut Json,
    native: &[Node],
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    clean_reasons(result, control, point)?;
    let Json::Obj(document) = result else {
        unreachable!()
    };
    let mut examples = BTreeSet::new();
    let mut completions = BTreeSet::new();
    let mut proofs = BTreeSet::new();
    // 分類は未到達の証拠も含むが、表示は一つずつ読み、保持しない。
    for (index, node) in native.iter().enumerate() {
        control.checkpoint(point)?;
        if node.ty != NodeType::Evidence {
            continue;
        }
        // 従来の表示前後と同じ停止点を保ち、分類には表示を構築しない。
        control.checkpoint(point)?;
        let class = node.evidence_class();
        control.checkpoint(point)?;
        let id = format!("n{index}");
        match class {
            EvidenceClass::Certificate => {}
            EvidenceClass::Example => {
                examples.insert(id);
            }
            EvidenceClass::Completion => {
                completions.insert(id);
            }
            EvidenceClass::Proof => {
                proofs.insert(id);
            }
        }
    }
    // 証明への参照は evidence 欄以外（例: 解集合の certificate）にもある。
    // ノード型で全経路を除き、実値の反例だけを残す。
    for value in document.values_mut() {
        remove_proof_refs(value, &proofs);
    }
    let Json::Arr(answers) = document.get_mut("answers").unwrap() else {
        unreachable!()
    };
    for answer in answers {
        let Json::Obj(answer) = answer else {
            unreachable!()
        };
        retain_evidence(answer, &examples, &completions);
        if let Some(reference) = answer.get("claim")
            && law_claim(reference, native, &proofs, control, point)?
        {
            answer.remove("claim");
        }
        let Some(Json::Obj(outputs)) = answer.get_mut("outputs") else {
            unreachable!()
        };
        if let Some(reference) = outputs.get("proposition")
            && law_claim(reference, native, &proofs, control, point)?
        {
            outputs.remove("proposition");
        }
        let evaluation = outputs.remove("evaluation");
        let mut applicability = None;
        if let Some(Json::Obj(reference)) = &evaluation
            && let Some(Json::Str(id)) = reference.get("node")
        {
            let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
            if let Some(mut value) =
                evaluation_answer_fields(native, index, &proofs, control, point)?
            {
                applicability = value.remove("applicability");
                if let Some(environment) = value.remove("environment") {
                    outputs.insert("environment".into(), environment);
                }
            }
        }
        if let Some(applicability) = applicability {
            answer.insert("applicability".into(), applicability);
        }
    }
    let mut reachable = BTreeSet::new();
    for value in document.values() {
        refs(value, &mut reachable, control, point)?;
    }
    // 部分結果の理由には後続の診断への参照もある。到達順を計算順と同一視しない。
    let mut pending: Vec<_> = reachable.iter().cloned().collect();
    // 旧全ノード JSON 配列を、到達した表示だけの呼出し内作業領域へ置き換える。
    let mut projected = BTreeMap::new();
    while let Some(id) = pending.pop() {
        control.checkpoint(point)?;
        let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
        let mut children = BTreeSet::new();
        let mut node = project_node(
            native,
            index,
            &proofs,
            &examples,
            &completions,
            control,
            point,
        )?;
        compact_reference_arrays(&mut node, control, point)?;
        refs(&node, &mut children, control, point)?;
        if matches!(
            native[index].ty,
            NodeType::Construction(super::super::construction_result::ConstructionType::Quotient)
        ) {
            quotient_maps(&node, native, &mut children, control, point)?;
        }
        projected.insert(index, node);
        for child in children {
            if reachable.insert(child.clone()) {
                pending.push(child);
            }
        }
    }
    let mut ids: BTreeMap<_, _> = reachable
        .iter()
        .map(|id| (id.clone(), id.clone()))
        .collect();
    let mut nodes = share_projected(projected, native, &mut ids, control, point)?;
    let numbered: BTreeMap<String, String> = nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let Json::Obj(fields) = node else {
                unreachable!()
            };
            let Json::Str(id) = &fields["id"] else {
                unreachable!()
            };
            (id.clone(), format!("n{index}"))
        })
        .collect();
    for id in ids.values_mut() {
        *id = numbered[id].clone();
    }
    for node in &mut nodes {
        rename(node, &ids, control, point)?;
        let Json::Obj(fields) = node else {
            unreachable!()
        };
        let Json::Str(id) = fields.get_mut("id").unwrap() else {
            unreachable!()
        };
        *id = numbered[id].clone();
    }
    for value in document.values_mut() {
        rename(value, &ids, control, point)?;
    }
    document.insert("nodes".into(), Json::Arr(nodes));
    Ok(())
}

#[cfg(test)]
mod reference_array_tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};
    fn plain(indices: &[usize]) -> Json {
        Json::Arr(indices.iter().map(|n| NodeRef(*n).wire()).collect())
    }
    fn exercise(operation: impl Fn(&Control) -> Result<(), Signal>) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        operation(&Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        }))
        .unwrap();
        assert!(count.get() > 3);
        for signal in [Signal::Int, Signal::Term] {
            for at in 1..=count.get() {
                let mut visits = 0;
                let control = Control::new(move |_| {
                    visits += 1;
                    (visits == at).then_some(signal)
                });
                assert_eq!(operation(&control), Err(signal));
            }
        }
    }
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../../tests/common/finite_law_family_data.rs");
    }
    #[allow(dead_code)]
    mod partial_fixture {
        include!("../../../../../tests/common/answer_projections.rs");
    }
    #[test]
    fn partial_projection_keeps_completed_values_and_unknown_reasons_after_display_stop() {
        let result = crate::observed::evaluate_observed_bytes(
            partial_fixture::input("stop", "r1"),
            &[
                "seed=evaluate(Applications.abSeed)",
                "prior=check(Applications.abPrior)",
                "missing=evaluate(Applications.adMissing,p=@v/p)",
                "nested=evaluate(Applications.apNested)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "partial");
        let inspection = result.wire();
        let expected = result.result_wire();
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        });
        assert_eq!(
            result
                .result_wire_controlled(&control, Checkpoint::Expression)
                .unwrap(),
            expected
        );
        let at = count.get() / 2;
        let mut visits = 0;
        let control = Control::new(move |_| {
            visits += 1;
            (visits >= at).then_some(Signal::Term)
        });
        assert_eq!(
            result.result_wire_controlled(&control, Checkpoint::Expression),
            Err(Signal::Term)
        );
        assert_eq!(result.result_wire(), expected);
        assert_eq!(result.wire(), inspection);
    }

    fn count_compact(value: &Json) -> usize {
        match value {
            Json::NodeReferences(items) => items.len(),
            Json::Arr(items) => items.iter().map(count_compact).sum(),
            Json::Obj(fields) => fields.values().map(count_compact).sum(),
            _ => 0,
        }
    }
    #[test]
    fn saved_finite_projection_keeps_inspection_and_completed_native_data_after_stop() {
        use crate::observed::{evaluate_observed, prepare_shared_observed};
        for missing in [false, true] {
            let prepared = prepare_shared_observed(
                fixture::inputs(missing, "law required zero(c:Part):c.quantity=0;"),
                &["b=build(Selected,on=@v/root)"],
                &Control::unlimited(),
            )
            .unwrap();
            let result = evaluate_observed(prepared, &Control::unlimited()).unwrap();
            let inspection = result.wire();
            assert_eq!(count_compact(&inspection), 0);
            let expected = result.result_wire();
            // Public bytes remain ordinary JSON; the input parser does not create compact variants.
            let parsed = archsig_common::json::parse(expected.canonical().as_bytes()).unwrap();
            assert!(matches!(parsed.value, archsig_common::json::JValue::Obj(_)));
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let control = Control::new(move |_| {
                seen.set(seen.get() + 1);
                None
            });
            assert_eq!(
                result
                    .result_wire_controlled(&control, Checkpoint::Expression)
                    .unwrap(),
                expected
            );
            for signal in [Signal::Int, Signal::Term] {
                for at in [1, count.get() / 2, count.get()] {
                    let mut visits = 0;
                    let control = Control::new(move |_| {
                        visits += 1;
                        (visits >= at).then_some(signal)
                    });
                    assert_eq!(
                        result.result_wire_controlled(&control, Checkpoint::Expression),
                        Err(signal)
                    );
                    assert_eq!(result.wire(), inspection);
                    assert_eq!(result.result_wire(), expected);
                }
            }
        }
    }

    #[test]
    fn projected_ref_arrays_preserve_repeated_ordered_values_and_two_renames() {
        let mut value = Json::obj([("values", plain(&[8, 4, 8]))]);
        compact_reference_arrays(&mut value, &Control::unlimited(), Checkpoint::Expression)
            .unwrap();
        let Json::Obj(fields) = &value else { panic!() };
        assert!(matches!(fields.get("values"), Some(Json::NodeReferences(v)) if v == &[8, 4, 8]));
        let mut reachable = BTreeSet::new();
        refs(
            &value,
            &mut reachable,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        assert_eq!(reachable, BTreeSet::from(["n4".into(), "n8".into()]));
        let shared = BTreeMap::from([("n8".into(), "n3".into()), ("n4".into(), "n4".into())]);
        rename(
            &mut value,
            &shared,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        let numbered = BTreeMap::from([("n3".into(), "n0".into()), ("n4".into(), "n1".into())]);
        rename(
            &mut value,
            &numbered,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        assert_eq!(
            value.canonical(),
            r#"{"values":[{"node":"n0"},{"node":"n1"},{"node":"n0"}]}"#
        );
    }
    #[test]
    fn compression_keeps_empty_mixed_and_invalid_reference_values_unchanged() {
        for value in [
            Json::Arr(vec![]),
            Json::Arr(vec![NodeRef(1).wire(), Json::Nat(2)]),
            Json::Arr(vec![
                NodeRef(1).wire(),
                Json::obj([("node", Json::str("n01"))]),
            ]),
            Json::Arr(vec![Json::obj([("node", Json::str("n+1"))])]),
            Json::Arr(vec![Json::obj([
                ("node", Json::str("n1")),
                ("extra", Json::Bool(true)),
            ])]),
        ] {
            let expected = value.canonical();
            let mut value = value;
            compact_reference_arrays(&mut value, &Control::unlimited(), Checkpoint::Expression)
                .unwrap();
            assert!(matches!(value, Json::Arr(_)));
            assert_eq!(value.canonical(), expected);
        }
    }
    #[test]
    fn compression_reachability_and_renaming_stop_at_each_boundary() {
        let original = Json::obj([("pairs", Json::Arr(vec![plain(&[8, 4]), plain(&[4, 8])]))]);
        let ids = BTreeMap::from([("n8".into(), "n3".into()), ("n4".into(), "n4".into())]);
        exercise(|control| {
            let mut local = original.clone();
            compact_reference_arrays(&mut local, control, Checkpoint::Expression)
        });
        let mut compact = original.clone();
        compact_reference_arrays(&mut compact, &Control::unlimited(), Checkpoint::Expression)
            .unwrap();
        exercise(|control| {
            refs(
                &compact,
                &mut BTreeSet::new(),
                control,
                Checkpoint::Expression,
            )
        });
        exercise(|control| rename(&mut compact.clone(), &ids, control, Checkpoint::Expression));
        // Stops only discard local display work, never mutate the completed source value.
        assert_eq!(
            original.canonical(),
            r#"{"pairs":[[{"node":"n8"},{"node":"n4"}],[{"node":"n4"},{"node":"n8"}]]}"#
        );
    }
}

#[cfg(test)]
mod projection_tests;

#[cfg(test)]
mod dedup_key_tests;

#[cfg(test)]
mod expression_sharing_tests {
    use super::*;
    use archsig_common::types::Type;

    #[test]
    fn expression_sharing_checks_saved_record_and_native_result_type() {
        let original = |ty| Node {
            ty,
            payload: None,
            rule: super::super::Rule::Construction("expression"),
            arguments: vec![],
            support: Default::default(),
            scope: Default::default(),
            evidence: vec![],
            judgment: None,
            reasons: vec![],
        };
        let mut native = vec![original(NodeType::Value(Type::Z))];
        let mut projected = BTreeMap::from([(
            0,
            Json::obj([
                ("id", NodeRef(0).wire()),
                ("type", Json::str("Z")),
                ("value", Json::str("0")),
            ]),
        )]);
        for index in 1..=8 {
            let ty = if index == 8 { Type::Q } else { Type::Z };
            native.push(original(NodeType::Expression(ty)));
            let value = Json::obj([
                ("kind", Json::str("source")),
                (
                    "location",
                    Json::obj([(
                        "span",
                        Json::Arr(vec![
                            Json::Nat(if index == 3 { 2 } else { 1 }),
                            Json::Nat(3),
                        ]),
                    )]),
                ),
                (
                    "bindings",
                    if index == 4 {
                        Json::Arr(vec![Json::obj([
                            ("name", Json::str("x")),
                            ("value", NodeRef(0).wire()),
                        ])])
                    } else {
                        Json::Arr(vec![])
                    },
                ),
                (
                    "parameters",
                    if index == 5 {
                        Json::Arr(vec![Json::obj([
                            ("name", Json::str("x")),
                            ("type", Type::Z.wire()),
                        ])])
                    } else {
                        Json::Arr(vec![])
                    },
                ),
            ]);
            projected.insert(
                index,
                Json::obj([
                    ("id", NodeRef(index).wire()),
                    ("type", Json::str("Expression")),
                    ("value", value),
                    (
                        "conditions",
                        Json::Arr(if index == 6 {
                            vec![NodeRef(0).wire()]
                        } else {
                            vec![]
                        }),
                    ),
                    (
                        "reasons",
                        Json::Arr(if index == 7 {
                            vec![Json::obj([("code", Json::str("missing_observation"))])]
                        } else {
                            vec![]
                        }),
                    ),
                ]),
            );
        }
        let mut ids = (0..=8)
            .map(|i| (format!("n{i}"), format!("n{i}")))
            .collect();
        let shared = share_projected(
            projected,
            &native,
            &mut ids,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        assert_eq!(shared.len(), 8);
        assert_eq!(ids["n2"], "n1");
        for index in 3..=8 {
            let id = format!("n{index}");
            assert_eq!(ids[&id], id);
        }
    }
}
