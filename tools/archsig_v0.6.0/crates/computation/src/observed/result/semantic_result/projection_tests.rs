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
            EvidenceClass::Certificate => {}
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
    let full_before = result.wire().canonical();
    let full = result.wire();
    let Json::Obj(full) = &full else { panic!() };
    let Json::Arr(inspected) = &full["nodes"] else {
        panic!()
    };
    let mut evaluations = 0;
    for (native, inspected) in result.nodes.iter().zip(inspected) {
        if matches!(native.payload, Some(Payload::Evaluation { .. })) {
            evaluations += 1;
            let Json::Obj(fields) = inspected else {
                panic!()
            };
            let Json::Obj(payload) = &fields["value"] else {
                panic!()
            };
            assert!(payload.contains_key("parts") && payload.contains_key("expression"));
        }
    }
    assert!(evaluations > 0);
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
    assert_eq!(result.wire().canonical(), full_before);
    // このfixtureはPath/compound表示を実際に通す。
    assert!(
        nodes
            .iter()
            .any(|node| matches!(node.scalar_payload(), Some(Scalar::Path(_))))
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
            Payload::scalar(Scalar::Bool(true)),
            vec![],
        ),
        node(
            NodeType::Value(Type::Bool),
            Payload::scalar(Scalar::Bool(false)),
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
        assembly_instance: None,
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
    refs(
        &projected,
        &mut references,
        &quiet(),
        Checkpoint::Expression,
    )
    .unwrap();
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
        Payload::scalar(Scalar::Bool(true)),
        vec![],
    )];
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let visits = count.clone();
    let control = Control::new(move |_| {
        visits.set(visits.get() + 1);
        None
    });
    project_node(
        &nodes,
        0,
        &BTreeSet::new(),
        &BTreeSet::new(),
        &BTreeSet::new(),
        &control,
        Checkpoint::Expression,
    )
    .unwrap();
    let total = count.get();
    assert!(total >= 3);
    for at in 1..=total {
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

fn evaluation_nodes(environment: Option<NodeRef>, value: Option<NodeRef>) -> Vec<Node> {
    use super::super::{Binding, Part};
    use archsig_common::{issue::Location, types::Type};
    let mut nodes = vec![
        node(
            NodeType::Value(Type::Bool),
            Payload::scalar(Scalar::Bool(true)),
            vec![],
        ),
        node(
            NodeType::Expression(Type::Bool),
            Payload::Expression {
                location: Location::Law { span: (0, 1) },
                parameters: vec![],
                bindings: vec![],
            },
            vec![],
        ),
        node(
            NodeType::Evidence,
            Payload::FiniteExhaustion {
                domain: NodeRef(0),
                checked: 1,
                instances: vec![],
            },
            vec![NodeRef(0)],
        ),
        node(
            NodeType::Evaluation(Type::Bool),
            Payload::Evaluation {
                environment,
                expression: NodeRef(1),
                bindings: vec![
                    Binding {
                        name: "x".into(),
                        value: NodeRef(0),
                        ty: Type::Bool,
                    },
                    Binding {
                        name: "proof".into(),
                        value: NodeRef(2),
                        ty: Type::Bool,
                    },
                ],
                parts: vec![Part {
                    location: Location::Law { span: (0, 1) },
                    value: Some(NodeRef(0)),
                    residual: Some(NodeRef(0)),
                    children: vec![NodeRef(1)],
                }],
                value,
                applicability: "applicable",
            },
            vec![NodeRef(1), NodeRef(0)],
        ),
    ];
    nodes[3].reasons.push(super::super::Reason {
        kind: super::super::ReasonKind::Missing,
        request: "a".into(),
        dependencies: vec![NodeRef(0), NodeRef(2)],
        missing: vec![],
        location: Some(Location::Law { span: (0, 1) }),
    });
    nodes
}
// 本体の部分helperを使わず、旧full描画から必要欄を読む。
fn legacy_answer_fields(
    native: &[Node],
    index: usize,
    proofs: &BTreeSet<String>,
) -> Option<archsig_common::canonical::JsonObject> {
    let mut raw = public_raw_node(native, index, proofs, &quiet(), Checkpoint::Expression).unwrap();
    let Json::Obj(fields) = &mut raw else {
        return None;
    };
    let Some(Json::Obj(value)) = fields.get_mut("value") else {
        return None;
    };
    value.retain(|key, _| matches!(key.as_str(), "applicability" | "environment"));
    Some(std::mem::take(value))
}
#[test]
fn evaluation_projection_keeps_four_fields_and_exact_proof_pruning() {
    for environment in [None, Some(NodeRef(0)), Some(NodeRef(2))] {
        for value in [None, Some(NodeRef(0)), Some(NodeRef(2))] {
            let nodes = evaluation_nodes(environment, value);
            let (proofs, examples, completions) = classes(&nodes);
            let full_before = nodes[3].wire(3, &nodes[..3]).canonical();
            let actual = project_node(
                &nodes,
                3,
                &proofs,
                &examples,
                &completions,
                &quiet(),
                Checkpoint::Expression,
            )
            .unwrap();
            let legacy = legacy_project_node(
                &nodes,
                3,
                &proofs,
                &examples,
                &completions,
                &quiet(),
                Checkpoint::Expression,
            )
            .unwrap();
            assert_eq!(
                actual.canonical().into_bytes(),
                legacy.canonical().into_bytes()
            );
            let Json::Obj(fields) = &actual else { panic!() };
            assert_eq!(fields["type"], Json::str("EvaluationResult"));
            assert_eq!(fields["conditions"], Json::Arr(vec![]));
            let Json::Arr(reasons) = &fields["reasons"] else {
                panic!()
            };
            assert_eq!(reasons.len(), 1);
            let Json::Obj(reason) = &reasons[0] else {
                panic!()
            };
            assert_eq!(reason["code"], Json::str("missing_observation"));
            assert_eq!(reason["dependencies"], Json::Arr(vec![]));
            let Json::Obj(payload) = &fields["value"] else {
                panic!()
            };
            let mut expected = archsig_common::canonical::JsonObject::from([
                ("applicability".into(), Json::str("applicable")),
                (
                    "bindings".into(),
                    Json::Arr(vec![
                        Json::obj([("name", Json::str("x")), ("value", NodeRef(0).wire())]),
                        Json::obj([("name", Json::str("proof"))]),
                    ]),
                ),
            ]);
            if environment == Some(NodeRef(0)) {
                expected.insert("environment".into(), NodeRef(0).wire());
            }
            if value == Some(NodeRef(0)) {
                expected.insert("value".into(), NodeRef(0).wire());
            }
            assert_eq!(payload, &expected);
            assert!(!payload.contains_key("parts") && !payload.contains_key("expression"));
            let full = nodes[3].wire(3, &nodes[..3]);
            assert_eq!(full.canonical(), full_before);
            let Json::Obj(full) = &full else { panic!() };
            let Json::Obj(payload) = &full["value"] else {
                panic!()
            };
            assert!(payload.contains_key("parts") && payload.contains_key("expression"));
            for key in ["rule", "arguments", "evidence", "scope", "support"] {
                assert!(full.contains_key(key));
            }
        }
    }
}
#[test]
fn evaluation_answer_reads_only_two_fields_and_retains_general_fallback() {
    for environment in [None, Some(NodeRef(0)), Some(NodeRef(2))] {
        let mut nodes = evaluation_nodes(environment, Some(NodeRef(0)));
        for applicability in ["applicable", "not_applicable", "undetermined"] {
            let Some(Payload::Evaluation {
                applicability: actual,
                ..
            }) = &mut nodes[3].payload
            else {
                panic!()
            };
            *actual = applicability;
            let (proofs, _, _) = classes(&nodes);
            let fields =
                evaluation_answer_fields(&nodes, 3, &proofs, &quiet(), Checkpoint::Expression)
                    .unwrap();
            assert_eq!(fields, legacy_answer_fields(&nodes, 3, &proofs));
            let mut expected = archsig_common::canonical::JsonObject::from([(
                "applicability".into(),
                Json::str(applicability),
            )]);
            if environment == Some(NodeRef(0)) {
                expected.insert("environment".into(), NodeRef(0).wire());
            }
            assert_eq!(fields, Some(expected));
        }
        // 非Evaluationのobject payload / scalar payload / absent payloadの旧挙動。
        nodes.push(Node {
            payload: None,
            ..nodes[0].clone()
        });
        for index in [0, 1, 4] {
            let (proofs, _, _) = classes(&nodes);
            assert_eq!(
                evaluation_answer_fields(&nodes, index, &proofs, &quiet(), Checkpoint::Expression)
                    .unwrap(),
                legacy_answer_fields(&nodes, index, &proofs)
            );
        }
    }
}
#[test]
fn compact_keeps_existing_answer_environment_when_evaluation_environment_is_absent_or_pruned() {
    for environment in [None, Some(NodeRef(2)), Some(NodeRef(0))] {
        let nodes = evaluation_nodes(environment, Some(NodeRef(0)));
        let mut document = Json::obj([(
            "answers",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("a")),
                (
                    "outputs",
                    Json::obj([
                        ("evaluation", NodeRef(3).wire()),
                        ("environment", NodeRef(1).wire()),
                    ]),
                ),
            ])]),
        )]);
        compact(&mut document, &nodes, &quiet(), Checkpoint::Expression).unwrap();
        let Json::Obj(document) = &document else {
            panic!()
        };
        let Json::Arr(answers) = &document["answers"] else {
            panic!()
        };
        let Json::Obj(answer) = &answers[0] else {
            panic!()
        };
        assert_eq!(answer["applicability"], Json::str("applicable"));
        let Json::Obj(outputs) = &answer["outputs"] else {
            panic!()
        };
        assert!(!outputs.contains_key("evaluation"));
        // 各caseで唯一到達した環境は保存番号n0。保持した元型も区別して検査する。
        assert_eq!(outputs["environment"], NodeRef(0).wire());
        let Json::Arr(saved) = &document["nodes"] else {
            panic!()
        };
        assert_eq!(saved.len(), 1);
        let Json::Obj(saved) = &saved[0] else {
            panic!()
        };
        assert_eq!(
            saved["type"],
            if environment == Some(NodeRef(0)) {
                Json::str("Bool")
            } else {
                Json::str("Expression")
            }
        );
    }
}
#[test]
fn evaluation_answer_stop_propagates_at_every_reachable_checkpoint() {
    let nodes = evaluation_nodes(Some(NodeRef(0)), Some(NodeRef(0)));
    let (proofs, _, _) = classes(&nodes);
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let visits = count.clone();
    let control = Control::new(move |_| {
        visits.set(visits.get() + 1);
        None
    });
    evaluation_answer_fields(&nodes, 3, &proofs, &control, Checkpoint::Expression).unwrap();
    let total = count.get();
    assert!(total >= 2);
    for at in 1..=total {
        let count = std::rc::Rc::new(std::cell::Cell::new(0));
        let visits = count.clone();
        let control = Control::new(move |_| {
            visits.set(visits.get() + 1);
            (visits.get() == at).then_some(Signal::Term)
        });
        assert!(matches!(
            evaluation_answer_fields(&nodes, 3, &proofs, &control, Checkpoint::Expression),
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

#[test]
fn compact_stops_discard_only_local_display_and_retry_keeps_native_and_saved_bytes() {
    let native = evaluation_nodes(Some(NodeRef(0)), Some(NodeRef(0)));
    let full_before = Json::Arr(
        native
            .iter()
            .enumerate()
            .map(|(i, node)| node.wire(i, &native[..i]))
            .collect(),
    )
    .canonical();
    let source = Json::obj([(
        "answers",
        Json::Arr(vec![Json::obj([(
            "outputs",
            Json::obj([
                ("evaluation", NodeRef(3).wire()),
                ("result", NodeRef(3).wire()),
            ]),
        )])]),
    )]);
    let count = std::rc::Rc::new(std::cell::Cell::new(0));
    let visits = count.clone();
    let control = Control::new(move |_| {
        visits.set(visits.get() + 1);
        None
    });
    let mut expected = source.clone();
    compact(&mut expected, &native, &control, Checkpoint::Expression).unwrap();
    let expected = expected.canonical();
    let total = count.get();
    assert!(
        total > 3,
        "include cleaning, projection, compression, references and renaming"
    );
    for at in 1..=total {
        let calls = std::rc::Rc::new(std::cell::Cell::new(0));
        let visits = calls.clone();
        let control = Control::new(move |_| {
            visits.set(visits.get() + 1);
            (visits.get() == at).then_some(Signal::Term)
        });
        let mut local = source.clone();
        assert_eq!(
            compact(&mut local, &native, &control, Checkpoint::Expression),
            Err(Signal::Term)
        );
        drop(local); // 途中の表示は成功成果物として使わない。
        let frozen = calls.get();
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(Signal::Term)
        );
        assert_eq!(calls.get(), frozen);
        let mut retry = source.clone();
        compact(&mut retry, &native, &quiet(), Checkpoint::Expression).unwrap();
        assert_eq!(retry.canonical(), expected);
        assert_eq!(
            Json::Arr(
                native
                    .iter()
                    .enumerate()
                    .map(|(i, node)| node.wire(i, &native[..i]))
                    .collect()
            )
            .canonical(),
            full_before
        );
    }
}

#[test]
fn proof_pruning_remains_before_reference_array_compaction_and_full_raw_stays_plain() {
    let native = evaluation_nodes(Some(NodeRef(2)), Some(NodeRef(2)));
    let (proofs, examples, completions) = classes(&native);
    let mut projected = project_node(
        &native,
        3,
        &proofs,
        &examples,
        &completions,
        &quiet(),
        Checkpoint::Expression,
    )
    .unwrap();
    let mut legacy = legacy_project_node(
        &native,
        3,
        &proofs,
        &examples,
        &completions,
        &quiet(),
        Checkpoint::Expression,
    )
    .unwrap();
    compact_reference_arrays(&mut projected, &quiet(), Checkpoint::Expression).unwrap();
    compact_reference_arrays(&mut legacy, &quiet(), Checkpoint::Expression).unwrap();
    assert_eq!(projected.canonical(), legacy.canonical());
    let mut references = BTreeSet::new();
    refs(
        &projected,
        &mut references,
        &quiet(),
        Checkpoint::Expression,
    )
    .unwrap();
    assert!(!references.contains("n2"));
    assert!(references.contains("n0"));
    let raw = public_raw_node(&native, 3, &proofs, &quiet(), Checkpoint::Expression).unwrap();
    let Json::Obj(fields) = &raw else { panic!() };
    assert!(
        matches!(&fields["arguments"], Json::Arr(_)),
        "raw proof pruning never receives bulk reference arrays"
    );
    let Json::Obj(value) = &fields["value"] else {
        panic!()
    };
    assert!(matches!(&value["parts"], Json::Arr(_)));
    assert!(value.contains_key("expression"));
    assert!(!value.contains_key("environment") && !value.contains_key("value"));
}
