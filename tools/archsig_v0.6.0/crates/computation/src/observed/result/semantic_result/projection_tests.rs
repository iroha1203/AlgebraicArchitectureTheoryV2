use super::super::{Decision, Judgment, Payload, Quantifier, Rule, Scalar, Scope};
use super::*;
use archsig_common::control::quiet;

#[allow(dead_code)]
mod path_fixture {
    include!("../../../../../../tests/common/identity_paths.rs");
}

// 保存投影前の全欄生成→削除という変更前の経路をoracleとして固定する。
fn legacy_project_node(
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

fn classes(nodes: &[Node]) -> (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>) {
    let mut proofs = BTreeSet::new();
    let mut examples = BTreeSet::new();
    let mut completions = BTreeSet::new();
    for (index, node) in nodes.iter().enumerate() {
        if node.ty != NodeType::Evidence {
            continue;
        }
        let id = format!("n{index}");
        match node.evidence_class() {
            EvidenceClass::Proof => {
                proofs.insert(id);
            }
            EvidenceClass::Example => {
                examples.insert(id);
            }
            EvidenceClass::Completion => {
                completions.insert(id);
            }
        }
    }
    (proofs, examples, completions)
}

#[test]
fn saved_projection_keeps_legacy_bytes_for_checked_paths_and_nested_values() {
    use crate::observed::evaluate_observed_bytes;
    let result = evaluate_observed_bytes(
        path_fixture::input(false),
        &[
            "other=evaluate(Walk.id,x=@w/a)",
            "target=evaluate(Walk.maybe_value,x=@v/a)",
            "nested=evaluate(Walk.nested,x=@v/b)",
        ],
        &quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete");
    let nodes = &result.nodes;
    let (proofs, examples, completions) = classes(nodes);
    let mut legacy = Vec::new();
    let mut projected = Vec::new();
    for index in 0..nodes.len() {
        legacy.push(
            legacy_project_node(
                nodes,
                index,
                &proofs,
                &examples,
                &completions,
                &quiet(),
                Checkpoint::Expression,
            )
            .unwrap(),
        );
        projected.push(
            project_node(
                nodes,
                index,
                &proofs,
                &examples,
                &completions,
                &quiet(),
                Checkpoint::Expression,
            )
            .unwrap(),
        );
    }
    assert_eq!(
        Json::Arr(projected).canonical().into_bytes(),
        Json::Arr(legacy).canonical().into_bytes()
    );
    // このfixtureはPath/compound表示を実際に通す。
    assert!(
        nodes
            .iter()
            .any(|node| matches!(node.payload, Some(Payload::Scalar(Scalar::Path(_)))))
    );
}

fn node(ty: NodeType, payload: Payload, arguments: Vec<NodeRef>) -> Node {
    Node {
        ty,
        payload: Some(payload),
        rule: Rule::Construction("projection_fixture"),
        arguments,
        support: vec![].into(),
        evidence: vec![],
        judgment: None,
        scope: Scope::default(),
        reasons: vec![],
    }
}

#[test]
fn projection_keeps_payload_quantifiers_and_prunes_proofs_without_changing_full_wire() {
    use archsig_common::issue::Location;
    use archsig_common::types::Type;
    use archsig_input::law::ast::QuantKind;
    let mut nodes = vec![
        node(
            NodeType::Value(Type::Bool),
            Payload::Scalar(Scalar::Bool(true)),
            vec![],
        ),
        node(
            NodeType::Value(Type::Bool),
            Payload::Scalar(Scalar::Bool(false)),
            vec![],
        ),
        node(
            NodeType::Domain,
            Payload::Domain {
                ty: Type::Bool,
                elements: vec![NodeRef(0), NodeRef(1)],
            },
            vec![NodeRef(0), NodeRef(1)],
        ),
        node(
            NodeType::Expression(Type::Bool),
            Payload::Expression {
                location: Location::Law { span: (0, 1) },
                parameters: vec![("x".into(), Type::Bool)],
                bindings: vec![],
            },
            vec![NodeRef(2)],
        ),
        node(
            NodeType::LawInstance,
            Payload::LawInstance {
                name: "Fixture.rule".into(),
                role: "required",
                bindings: vec![],
                guard: None,
                body: NodeRef(3),
                occurrence: Location::Law { span: (0, 1) },
            },
            vec![NodeRef(3)],
        ),
        node(
            NodeType::Evidence,
            Payload::FiniteExhaustion {
                domain: NodeRef(2),
                checked: 2,
                instances: vec![NodeRef(4)],
            },
            vec![NodeRef(2), NodeRef(4)],
        ),
        node(
            NodeType::Evidence,
            Payload::Counterexample {
                bindings: vec![],
                left: NodeRef(0),
                right: NodeRef(1),
                facts: vec![],
            },
            vec![NodeRef(0), NodeRef(1)],
        ),
        node(
            NodeType::Proposition,
            Payload::Proposition {
                instance: NodeRef(4),
            },
            vec![NodeRef(4)],
        ),
    ];
    nodes[7].scope.quantifiers.push(Quantifier {
        kind: QuantKind::Forall,
        name: "x".into(),
        ty: Type::Bool,
        domain: Some(NodeRef(2)),
        occurrence: (0, 0),
        context: None,
    });
    nodes[7].scope.readings.insert("Fixture".into());
    nodes[7].evidence = vec![NodeRef(5), NodeRef(6)];
    nodes[7].judgment = Some(Judgment {
        status: Decision::Refuted,
        evidence: nodes[7].evidence.clone(),
        reasons: vec![],
    });
    let (proofs, examples, completions) = classes(&nodes);
    assert!(proofs.contains("n5"));
    assert!(examples.contains("n6"));
    let before = nodes[7].wire(7, &nodes[..7]).canonical();
    for index in 0..nodes.len() {
        let actual = project_node(
            &nodes,
            index,
            &proofs,
            &examples,
            &completions,
            &quiet(),
            Checkpoint::Expression,
        )
        .unwrap();
        let expected = legacy_project_node(
            &nodes,
            index,
            &proofs,
            &examples,
            &completions,
            &quiet(),
            Checkpoint::Expression,
        )
        .unwrap();
        assert_eq!(
            actual.canonical().into_bytes(),
            expected.canonical().into_bytes(),
            "node {index}"
        );
    }
    let projected = project_node(
        &nodes,
        7,
        &proofs,
        &examples,
        &completions,
        &quiet(),
        Checkpoint::Expression,
    )
    .unwrap();
    let Json::Obj(fields) = &projected else {
        panic!()
    };
    for key in ["rule", "arguments", "evidence", "scope", "support"] {
        assert!(!fields.contains_key(key));
    }
    let Json::Obj(payload) = &fields["value"] else {
        panic!()
    };
    let Json::Arr(quantifiers) = &payload["quantifiers"] else {
        panic!()
    };
    assert_eq!(quantifiers.len(), 1);
    let Json::Obj(judgment) = &fields["judgment"] else {
        panic!()
    };
    assert_eq!(
        judgment["counterexamples"],
        Json::Arr(vec![NodeRef(6).wire()])
    );
    assert!(!judgment.contains_key("evidence"));
    let mut references = BTreeSet::new();
    refs(&projected, &mut references);
    assert!(!references.contains("n5"));
    assert!(references.contains("n6"));
    assert!(references.contains("n2"));
    assert_eq!(nodes[7].wire(7, &nodes[..7]).canonical(), before);
    // full rendererも引き続き四欄を持つ。project専用入口からは生成されない。
    let full = public_raw_node(&nodes, 7, &proofs, &quiet(), Checkpoint::Expression).unwrap();
    let Json::Obj(full) = &full else { panic!() };
    let minimal = nodes[7].project_wire(7, &nodes[..7]);
    let Json::Obj(minimal) = &minimal else {
        panic!()
    };
    for key in ["rule", "arguments", "evidence", "scope"] {
        assert!(full.contains_key(key));
        assert!(!minimal.contains_key(key));
    }
}

#[test]
fn projection_preserves_checkpoint_stop_and_freezes_control() {
    let nodes = vec![node(
        NodeType::Value(archsig_common::types::Type::Bool),
        Payload::Scalar(Scalar::Bool(true)),
        vec![],
    )];
    for at in 1..=3 {
        // 各checkpointで届いた停止を、projectionが成功へ変換しない。
        let count = std::rc::Rc::new(std::cell::Cell::new(0));
        let calls = count.clone();
        let control = Control::new(move |point| {
            if point == Checkpoint::Expression {
                calls.set(calls.get() + 1);
            }
            (calls.get() >= at).then_some(Signal::Term)
        });
        assert!(matches!(
            project_node(
                &nodes,
                0,
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &control,
                Checkpoint::Expression
            ),
            Err(Signal::Term)
        ));
        let before = count.get();
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(Signal::Term)
        );
        assert_eq!(count.get(), before);
    }
}
