//! 保存を依頼していないrunの回答表示。計算・後続参照には元の型付き結果を使う。
use super::result::{
    Binding, Decision, Fact, Node, NodeRef, NodeType, ObservedEvaluation, Payload, ReasonKind,
};
use crate::canonical::Json;
use std::collections::BTreeMap;

const EXAMPLE_LIMIT: usize = 3;
const ITEM_LIMIT: usize = 3;

// 型付き反例は元の参照を借りる。native構成の表示記録だけを変換対象として区別する。
enum Counterexample<'a> {
    Comparison {
        bindings: &'a [Binding],
        left: NodeRef,
        right: NodeRef,
        facts: &'a [Fact],
    },
    Native(Json),
}
impl<'a> Counterexample<'a> {
    fn from_payload(payload: &'a Payload) -> Option<Self> {
        match payload {
            Payload::Counterexample {
                bindings,
                left,
                right,
                facts,
            }
            | Payload::TermCounterexample {
                bindings,
                left,
                right,
                facts,
            }
            | Payload::PathCounterexample {
                bindings,
                left,
                right,
                facts,
            }
            | Payload::OwnedCallCounterexample {
                bindings,
                left,
                right,
                facts,
            } => Some(Self::Comparison {
                bindings,
                left: *left,
                right: *right,
                facts,
            }),
            Payload::ProjectionCounterexample { left, right, facts } => Some(Self::Comparison {
                bindings: &[],
                left: *left,
                right: *right,
                facts,
            }),
            Payload::Construction(value) => Self::from_native(value.wire()),
            _ => None,
        }
    }

    fn from_native(mut value: Json) -> Option<Self> {
        let Json::Obj(wire) = &mut value else {
            return None;
        };
        if !matches!(wire.get("kind"), Some(Json::Str(kind)) if matches!(kind.as_str(), "counterexample" | "separating_pair"))
        {
            return None;
        }
        Some(Self::Native(
            wire.remove("data").expect("native counterexample data"),
        ))
    }
}

// native構成が保持する表示記録の参照を読む。型付きPayloadには使用しない。
fn node_reference(value: &Json) -> NodeRef {
    let Json::Str(id) = &fields(value).expect("counterexample reference")["node"] else {
        unreachable!("counterexample node ID")
    };
    NodeRef(
        id.strip_prefix('n')
            .expect("counterexample node prefix")
            .parse()
            .expect("counterexample node number"),
    )
}

fn brief_text(fields: &mut BTreeMap<String, Json>, key: &str, value: &str) {
    if value.len() <= 256 {
        fields.insert(key.into(), Json::str(value));
    } else {
        fields.insert(format!("{key}_bytes"), Json::Nat(value.len() as u64));
    }
}

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
                if request.kind == crate::observed::request::QuestionKind::Solve
                    && answer.status == Decision::Undetermined
                    && let Some(reference) = answer.outputs.get("proposition")
                    && let Some(judgment) = &self.nodes[reference.0].judgment
                {
                    row.insert("existence".into(), Json::str(judgment.status.wire()));
                }
                if request.kind == crate::observed::request::QuestionKind::Repair
                    && let Some(reference) = answer.claim
                    && let Some(Payload::Construction(value)) = &self.nodes[reference.0].payload
                    && let crate::observed::construction_result::ConstructionData::Change(data) =
                        &value.data
                    && let Some(status) = data.completion_uniqueness()
                {
                    row.insert("uniqueness".into(), Json::str(status.wire()));
                }
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
                if answer.status == Decision::Refuted {
                    let examples: Vec<_> = answer
                        .evidence
                        .iter()
                        .filter_map(|reference| {
                            let node = &self.nodes[reference.0];
                            if node.ty != NodeType::Evidence {
                                return None;
                            }
                            Some((node, Counterexample::from_payload(node.payload.as_ref()?)?))
                        })
                        .collect();
                    if !examples.is_empty() {
                        row.insert(
                            "counterexamples_total".into(),
                            Json::Nat(examples.len() as u64),
                        );
                        row.insert(
                            "counterexamples".into(),
                            Json::Arr(
                                examples
                                    .into_iter()
                                    .take(EXAMPLE_LIMIT)
                                    .map(|(node, data)| self.summary_counterexample(node, data))
                                    .collect(),
                            ),
                        );
                    }
                }
                Json::Obj(row)
            })
            .collect();
        let mut result = BTreeMap::from([
            ("format".into(), Json::str("archsig.summary/1")),
            ("status".into(), Json::str(status)),
            ("exit_code".into(), Json::Nat(code.into())),
            ("answers".into(), Json::Arr(answers)),
        ]);
        if code >= 64 && !issues.is_empty() {
            result.insert(
                "issues".into(),
                Json::Arr(issues.iter().map(notice).collect()),
            );
        }
        Json::Obj(result)
    }

    fn summary_counterexample(&self, node: &Node, data: Counterexample<'_>) -> Json {
        match data {
            Counterexample::Comparison {
                bindings,
                left,
                right,
                facts,
            } => self.summary_comparison(
                node,
                left,
                right,
                bindings
                    .iter()
                    .map(|binding| (binding.name.as_str(), binding.value)),
                facts.iter().map(Fact::wire),
            ),
            Counterexample::Native(data) => self.summary_native_counterexample(node, &data),
        }
    }

    fn summary_native_counterexample(&self, node: &Node, data: &Json) -> Json {
        let data = fields(data).expect("counterexample data object");
        if let Some(Json::Arr(values)) = data.get("law_values") {
            return Json::obj([
                ("kind", Json::str("separating_pair")),
                ("first", self.summary_value(node_reference(&data["first"]))),
                (
                    "second",
                    self.summary_value(node_reference(&data["second"])),
                ),
                ("left", self.summary_value(node_reference(&values[0]))),
                ("right", self.summary_value(node_reference(&values[1]))),
            ]);
        }
        let Json::Arr(bindings) = &data["bindings"] else {
            unreachable!("counterexample bindings")
        };
        let Json::Arr(facts) = &data["facts"] else {
            unreachable!("counterexample facts")
        };
        self.summary_comparison(
            node,
            node_reference(&data["left"]),
            node_reference(&data["right"]),
            bindings.iter().map(|binding| {
                let binding = fields(binding).expect("counterexample binding");
                let Json::Str(name) = &binding["name"] else {
                    unreachable!("binding name")
                };
                (name.as_str(), node_reference(&binding["value"]))
            }),
            facts.iter().cloned(),
        )
    }

    fn summary_comparison<'a>(
        &self,
        node: &Node,
        left: NodeRef,
        right: NodeRef,
        bindings: impl ExactSizeIterator<Item = (&'a str, NodeRef)>,
        facts: impl ExactSizeIterator<Item = Json>,
    ) -> Json {
        let mut row = BTreeMap::from([
            ("bindings_total".into(), Json::Nat(bindings.len() as u64)),
            (
                "bindings".into(),
                Json::Arr(
                    bindings
                        .take(ITEM_LIMIT)
                        .map(|(name, value)| {
                            let mut row =
                                BTreeMap::from([("value".into(), self.summary_value(value))]);
                            brief_text(&mut row, "name", name);
                            Json::Obj(row)
                        })
                        .collect(),
                ),
            ),
            ("left".into(), self.summary_value(left)),
            ("right".into(), self.summary_value(right)),
            ("facts_total".into(), Json::Nat(facts.len() as u64)),
            (
                "facts".into(),
                Json::Arr(
                    facts
                        .take(ITEM_LIMIT)
                        .map(|fact| {
                            let mut row = BTreeMap::new();
                            for (key, value) in fields(&fact).expect("counterexample fact") {
                                let Json::Str(value) = value else {
                                    unreachable!("fact identifier")
                                };
                                brief_text(&mut row, key, value);
                            }
                            Json::Obj(row)
                        })
                        .collect(),
                ),
            ),
        ]);
        // 比較の左右がそのまま採られる、guardなしの直接のLaw比較だけを表示する。
        for argument in &node.arguments {
            if let Some(Payload::LawInstance {
                name, guard: None, ..
            }) = &self.nodes[argument.0].payload
                && let Some(declaration) = self.prepared.inputs().law().declarations.get(name)
                && let crate::law::model::Signature::Law {
                    body, guard: None, ..
                } = &declaration.signature
                && let crate::law::ast::ExprKind::Binary { op, .. } =
                    self.prepared.inputs().law().exprs[*body].kind
            {
                use crate::law::ast::BinOp;
                let operator = match op {
                    BinOp::Eq => Some("="),
                    BinOp::Ne => Some("!="),
                    BinOp::Lt => Some("<"),
                    BinOp::Le => Some("<="),
                    BinOp::Gt => Some(">"),
                    BinOp::Ge => Some(">="),
                    _ => None,
                };
                if let Some(operator) = operator {
                    row.insert("operator".into(), Json::str(operator));
                }
            }
        }
        Json::Obj(row)
    }

    fn summary_value(&self, mut reference: NodeRef) -> Json {
        while let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &self.nodes[reference.0].payload
        {
            reference = *value;
        }
        let value = self.summary_node(reference, 0);
        let bytes = value.canonical().len();
        if bytes <= 512 {
            value
        } else {
            Json::obj([("summary_bytes", Json::Nat(bytes as u64))])
        }
    }
    fn summary_node(&self, reference: NodeRef, depth: usize) -> Json {
        let node = &self.nodes[reference.0];
        let ty = match &node.ty {
            NodeType::Vector(_) => Json::str("Vector"),
            NodeType::ModuleMap(_, _) => Json::str("ModuleMap"),
            _ => node.ty.wire(),
        };
        let mut brief = BTreeMap::from([("type".into(), ty)]);
        if let Some(judgment) = &node.judgment {
            brief.insert("status".into(), Json::str(judgment.status.wire()));
        }
        let value = match &node.payload {
            None => None,
            Some(Payload::Construction(value)) if value.is_blocked() => None,
            Some(Payload::Scalar(value)) => Some(
                super::path_value::wire(
                    value,
                    &self.nodes[..reference.0],
                    &node.arguments,
                    &crate::control::Control::new(crate::control::Limits::default(), |_| {
                        crate::control::Usage::default()
                    }),
                )
                .expect("挿入時に検査した値の既出 Ref 表示"),
            ),
            Some(payload) => Some(payload.wire()),
        };
        let Some(value) = value.as_ref() else {
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

#[cfg(test)]
mod tests;
