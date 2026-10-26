//! 保存を依頼していないrunの回答表示。計算・後続参照には元の型付き結果を使う。
use super::result::{Decision, NodeRef, NodeType, ObservedEvaluation, ReasonKind};
use crate::canonical::Json;
use std::collections::BTreeMap;

fn fields(value: &Json) -> Option<&BTreeMap<String, Json>> {
    match value {
        Json::Obj(fields) => Some(fields),
        _ => None,
    }
}
fn has_reference(value: &Json) -> bool {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Obj(fields) => fields.contains_key("node") || fields.values().any(has_reference),
        Json::Arr(items) => items.iter().any(has_reference),
        _ => false,
    })
}
fn notice(value: &Json) -> Json {
    let Some(source) = fields(value) else {
        return value.clone();
    };
    Json::Obj(
        source
            .iter()
            .filter(|(key, value)| key.as_str() != "dependencies" && !has_reference(value))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect(),
    )
}
impl ObservedEvaluation {
    pub(crate) fn summary_wire(&self, status: &str, code: u8, issues: &[Json]) -> Json {
        let answers = self
            .answers
            .iter()
            .map(|answer| {
                let request = self
                    .prepared
                    .requests()
                    .requests()
                    .iter()
                    .find(|request| request.id == answer.id)
                    .expect("回答の元の問い");
                let mut row = BTreeMap::from([
                    ("id".into(), Json::str(&answer.id)),
                    ("question".into(), Json::str(request.kind.wire())),
                    ("status".into(), Json::str(answer.status.wire())),
                    (
                        "outputs".into(),
                        Json::Obj(
                            answer
                                .outputs
                                .iter()
                                .filter(|(name, _)| {
                                    !matches!(name.as_str(), "evaluation" | "proposition")
                                })
                                .map(|(name, reference)| {
                                    (name.clone(), self.summary_node(*reference, 2))
                                })
                                .collect(),
                        ),
                    ),
                ]);
                if let Some(reference) = answer.outputs.get("evaluation") {
                    let node = &self.nodes[reference.0];
                    if let Some(super::result::Payload::Evaluation { applicability, .. }) =
                        &node.payload
                    {
                        row.insert("applicability".into(), Json::str(*applicability));
                    }
                }
                let mut reasons = answer
                    .reasons
                    .iter()
                    .filter(|reason| {
                        answer.status == Decision::Undetermined
                            || !matches!(reason.kind, ReasonKind::Missing)
                    })
                    .map(|reason| notice(&reason.wire()))
                    .collect::<Vec<_>>();
                super::result::concise_reasons(&mut reasons);
                if !reasons.is_empty() {
                    row.insert("reasons".into(), Json::Arr(reasons));
                }
                Json::Obj(row)
            })
            .collect();
        let mut result = BTreeMap::from([
            ("format".into(), Json::str("archsig.summary/1")),
            ("status".into(), Json::str(status)),
            ("exit_code".into(), Json::Nat(code.into())),
            ("answers".into(), Json::Arr(answers)),
            (
                "save".into(),
                Json::str("値・写像・解集合を保存するには --out DIR を指定してください"),
            ),
        ]);
        if code >= 64 && !issues.is_empty() {
            result.insert(
                "issues".into(),
                Json::Arr(issues.iter().map(notice).collect()),
            );
        }
        Json::Obj(result)
    }
    fn summary_node(&self, reference: NodeRef, depth: usize) -> Json {
        let node = &self.nodes[reference.0];
        let wire = node.wire(reference.0, &self.nodes[..reference.0]);
        let source = fields(&wire).expect("型付きノードの表示");
        let ty = match &node.ty {
            NodeType::Vector(_) => Json::str("Vector"),
            NodeType::ModuleMap(_, _) => Json::str("ModuleMap"),
            _ => source["type"].clone(),
        };
        let mut brief = BTreeMap::from([("type".into(), ty)]);
        if let Some(judgment) = &node.judgment {
            brief.insert("status".into(), Json::str(judgment.status.wire()));
        }
        let Some(value) = source.get("value") else {
            brief.insert("state".into(), Json::str("blocked"));
            return Json::Obj(brief);
        };
        if matches!(node.ty, NodeType::Value(_)) && !has_reference(value) {
            let bytes = value.canonical().len();
            if bytes <= 256 {
                brief.insert("value".into(), value.clone());
            } else {
                brief.insert("value_bytes".into(), Json::Nat(bytes as u64));
            }
            return Json::Obj(brief);
        }
        if let Some(value) = fields(value) {
            for key in [
                "kind",
                "side",
                "degree",
                "predicate",
                "declaration",
                "free_rank",
                "torsion",
            ] {
                if let Some(item) = value.get(key)
                    && !has_reference(item)
                {
                    brief.insert(key.into(), item.clone());
                }
            }
            for key in [
                "elements", "contexts", "covers", "readings", "laws", "pairs",
            ] {
                if let Some(Json::Arr(items)) = value.get(key) {
                    brief.insert(format!("{key}_count"), Json::Nat(items.len() as u64));
                }
            }
            if depth > 0 {
                for key in [
                    "domain",
                    "space",
                    "module",
                    "global",
                    "matching",
                    "class",
                    "coordinates",
                    "kernel",
                    "cokernel",
                ] {
                    if let Some(Json::Obj(item)) = value.get(key)
                        && let Some(Json::Str(id)) = item.get("node")
                        && let Some(reference) = node
                            .arguments
                            .iter()
                            .find(|reference| id == &format!("n{}", reference.0))
                    {
                        brief.insert(key.into(), self.summary_node(*reference, depth - 1));
                    }
                }
            }
        }
        Json::Obj(brief)
    }
}
