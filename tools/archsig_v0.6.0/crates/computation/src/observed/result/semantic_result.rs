//! 保存結果には値の参照グラフを残し、導出グラフを公開しない。
use super::{EvidenceClass, Node, NodeRef, NodeType};
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
};
use archsig_input::result::Signal;
use std::collections::{BTreeMap, BTreeSet};

fn refs(value: &Json, into: &mut BTreeSet<String>) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.len() == 1
                && let Some(Json::Str(id)) = fields.get("node")
            {
                into.insert(id.clone());
            } else {
                for value in fields.values() {
                    refs(value, into);
                }
            }
        }
        Json::Arr(items) => {
            for value in items {
                refs(value, into);
            }
        }
        _ => {}
    });
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
fn rename(value: &mut Json, ids: &BTreeMap<String, String>) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.len() == 1
                && let Some(Json::Str(id)) = fields.get_mut("node")
            {
                *id = ids[id].clone();
            } else {
                for value in fields.values_mut() {
                    rename(value, ids);
                }
            }
        }
        Json::Arr(items) => {
            for value in items {
                rename(value, ids);
            }
        }
        _ => {}
    });
}
fn retain_evidence(
    fields: &mut BTreeMap<String, Json>,
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
    let mut node = native[index].wire_with_support(index, &native[..index], false);
    control.checkpoint(point)?;
    clean_reasons(&mut node);
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
    let mut node = public_raw_node(native, index, proofs, control, point)?;
    let Json::Obj(fields) = &mut node else {
        unreachable!()
    };
    for key in ["rule", "arguments", "evidence", "scope", "support"] {
        fields.remove(key);
    }
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
fn clean_reasons(value: &mut Json) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => {
            if fields.contains_key("code") && fields.contains_key("message") {
                fields.insert("dependencies".into(), Json::Arr(vec![]));
                if let Some(Json::Obj(details)) = fields.get_mut("details") {
                    details.retain(|_, value| {
                        let mut references = BTreeSet::new();
                        refs(value, &mut references);
                        references.is_empty()
                    });
                }
            }
            for value in fields.values_mut() {
                clean_reasons(value);
            }
            if let Some(Json::Arr(reasons)) = fields.get_mut("reasons") {
                concise_reasons(reasons);
            }
        }
        Json::Arr(items) => {
            for value in items {
                clean_reasons(value);
            }
        }
        _ => {}
    });
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
        Json::Arr(items) => {
            items.retain_mut(|value| remove_proof_refs(value, proofs));
            true
        }
        _ => true,
    })
}
pub(super) fn compact(
    result: &mut Json,
    native: &[Node],
    control: &Control,
    point: Checkpoint,
) -> Result<(), Signal> {
    clean_reasons(result);
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
            let node = public_raw_node(native, index, &proofs, control, point)?;
            if let Json::Obj(node) = &node
                && let Some(Json::Obj(value)) = node.get("value")
            {
                applicability = value.get("applicability").cloned();
                if let Some(environment) = value.get("environment") {
                    outputs.insert("environment".into(), environment.clone());
                }
            }
        }
        if let Some(applicability) = applicability {
            answer.insert("applicability".into(), applicability);
        }
    }
    let mut reachable = BTreeSet::new();
    for value in document.values() {
        refs(value, &mut reachable);
    }
    // 部分結果の理由には後続の診断への参照もある。到達順を計算順と同一視しない。
    let mut pending: Vec<_> = reachable.iter().cloned().collect();
    // 旧全ノード JSON 配列を、到達した表示だけの呼出し内作業領域へ置き換える。
    let mut projected = BTreeMap::new();
    while let Some(id) = pending.pop() {
        control.checkpoint(point)?;
        let index: usize = id.strip_prefix('n').unwrap().parse().unwrap();
        let mut children = BTreeSet::new();
        let node = project_node(
            native,
            index,
            &proofs,
            &examples,
            &completions,
            control,
            point,
        )?;
        refs(&node, &mut children);
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
    let mut values = BTreeMap::<String, String>::new();
    let mut nodes = Vec::new();
    // 到達順でなく元の数値 index 順が canonical 共有の代表と番号を決める。
    for (index, mut node) in projected {
        control.checkpoint(point)?;
        let old_id = format!("n{index}");
        rename(&mut node, &ids);
        // 環・基底・関係を含む表示全体の一致だけを共有する。同型は推測しない。
        let shared = matches!(
            native[index].ty,
            NodeType::Value(_)
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
        let key = shared.then(|| node.canonical());
        if let Some(existing) = key.as_ref().and_then(|key| values.get(key)) {
            ids.insert(old_id, existing.clone());
            continue;
        }
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.insert("id".into(), Json::str(&old_id));
        if let Some(key) = key {
            values.insert(key, old_id.clone());
        }
        nodes.push(node);
    }
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
        rename(node, &ids);
        let Json::Obj(fields) = node else {
            unreachable!()
        };
        let Json::Str(id) = fields.get_mut("id").unwrap() else {
            unreachable!()
        };
        *id = numbered[id].clone();
    }
    for value in document.values_mut() {
        rename(value, &ids);
    }
    document.insert("nodes".into(), Json::Arr(nodes));
    Ok(())
}
