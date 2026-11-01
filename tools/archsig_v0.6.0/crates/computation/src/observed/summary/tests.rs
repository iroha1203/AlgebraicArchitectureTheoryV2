use super::*;
use crate::observed::evaluate_observed_bytes;
use archsig_common::control::Control;
use archsig_common::types::Type;
use archsig_input::input::InputSources;

fn evaluated_counter() -> (ObservedEvaluation, NodeRef) {
    let sources = InputSources::from_bytes(
        vec![include_bytes!("../../../../../tests/fixtures/counter.atoms.json").to_vec()],
        include_bytes!("../../../../../tests/fixtures/counter.law").to_vec(),
        include_str!("../../../../../tests/fixtures/counter.archmap.json")
            .replace("\"value\": \"2\"", "\"value\": \"12\"")
            .into_bytes(),
    );
    let result = evaluate_observed_bytes(
        sources,
        &["c=check(CountAudit.bounded,s=@v/s)"],
        &Control::unlimited(),
    )
    .unwrap();
    let example = result.answers[0]
        .evidence
        .iter()
        .copied()
        .find(|r| {
            matches!(
                result.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )
        })
        .unwrap();
    (result, example)
}

fn expected_integer(value: &str) -> Json {
    Json::obj([("type", Json::str("Z")), ("value", Json::str(value))])
}

#[test]
fn typed_counterexample_variants_keep_values_and_optional_fact_fields() {
    let (result, reference) = evaluated_counter();
    let node = &result.nodes[reference.0];
    let Some(Payload::Counterexample { left, right, .. }) = &node.payload else {
        panic!()
    };
    let (left, right) = (*left, *right);
    let bindings = vec![Binding {
        name: "parameter".into(),
        value: left,
        ty: Type::Z,
    }];
    let facts = vec![
        Fact {
            snapshot: "v".into(),
            subject: "s".into(),
            field: None,
            atom: None,
        },
        Fact {
            snapshot: "v".into(),
            subject: "s".into(),
            field: Some("Counter.State.count".into()),
            atom: Some("count".into()),
        },
    ];
    let payloads = [
        Payload::Counterexample {
            bindings: bindings.clone(),
            left,
            right,
            facts: facts.clone(),
        },
        Payload::TermCounterexample {
            bindings: bindings.clone(),
            left,
            right,
            facts: facts.clone(),
        },
        Payload::PathCounterexample {
            bindings: bindings.clone(),
            left,
            right,
            facts: facts.clone(),
        },
        Payload::OwnedCallCounterexample {
            bindings,
            left,
            right,
            facts: facts.clone(),
        },
        Payload::ProjectionCounterexample { left, right, facts },
    ];
    for (index, payload) in payloads.iter().enumerate() {
        let expected_bindings = if index == 4 {
            vec![]
        } else {
            vec![Json::obj([
                ("name", Json::str("parameter")),
                ("value", expected_integer("12")),
            ])]
        };
        let expected = Json::obj([
            ("bindings_total", Json::Nat(expected_bindings.len() as u64)),
            ("bindings", Json::Arr(expected_bindings)),
            ("left", expected_integer("12")),
            ("right", expected_integer("10")),
            ("facts_total", Json::Nat(2)),
            (
                "facts",
                Json::Arr(vec![
                    Json::obj([("snapshot", Json::str("v")), ("subject", Json::str("s"))]),
                    Json::obj([
                        ("snapshot", Json::str("v")),
                        ("subject", Json::str("s")),
                        ("field", Json::str("Counter.State.count")),
                        ("atom", Json::str("count")),
                    ]),
                ]),
            ),
            ("operator", Json::str("<=")),
        ]);
        let actual =
            result.summary_counterexample(node, Counterexample::from_payload(payload).unwrap());
        assert_eq!(actual, expected, "variant {index}");
    }
}

#[test]
fn native_comparison_and_separating_pair_keep_their_distinct_shapes() {
    let (result, reference) = evaluated_counter();
    let node = &result.nodes[reference.0];
    let Some(Payload::Counterexample { left, right, .. }) = &node.payload else {
        panic!()
    };
    let comparison = Json::obj([
        ("kind", Json::str("counterexample")),
        (
            "data",
            Json::obj([
                ("bindings", Json::Arr(vec![])),
                ("left", right.wire()),
                ("right", left.wire()),
                ("facts", Json::Arr(vec![])),
            ]),
        ),
    ]);
    let actual =
        result.summary_counterexample(node, Counterexample::from_native(comparison).unwrap());
    assert_eq!(
        actual,
        Json::obj([
            ("bindings_total", Json::Nat(0)),
            ("bindings", Json::Arr(vec![])),
            ("left", expected_integer("10")),
            ("right", expected_integer("12")),
            ("facts_total", Json::Nat(0)),
            ("facts", Json::Arr(vec![])),
            ("operator", Json::str("<=")),
        ])
    );
    let separating = Json::obj([
        ("kind", Json::str("separating_pair")),
        (
            "data",
            Json::obj([
                ("first", left.wire()),
                ("second", right.wire()),
                ("law_values", Json::Arr(vec![right.wire(), left.wire()])),
            ]),
        ),
    ]);
    let actual =
        result.summary_counterexample(node, Counterexample::from_native(separating).unwrap());
    assert_eq!(
        actual,
        Json::obj([
            ("kind", Json::str("separating_pair")),
            ("first", expected_integer("12")),
            ("second", expected_integer("10")),
            ("left", expected_integer("10")),
            ("right", expected_integer("12")),
        ])
    );
    assert!(
        Counterexample::from_native(Json::obj([
            ("kind", Json::str("completion_pair")),
            ("data", Json::obj([])),
        ]))
        .is_none()
    );
}

#[test]
fn summary_keeps_counterexample_order_totals_and_utf8_byte_limits() {
    let (mut result, reference) = evaluated_counter();
    let mut template = result.nodes[reference.0].clone();
    let Some(Payload::Counterexample { left, right, .. }) = &template.payload else {
        panic!()
    };
    let (left, right) = (*left, *right);
    let long = "あ".repeat(100);
    template.arguments.clear(); // この表示テストは直接Law比較のoperatorを付けない。
    result.answers[0].evidence.clear();
    for index in 0..4 {
        let bindings = ["first", "second", long.as_str(), "omitted"]
            .into_iter()
            .map(|name| Binding {
                name: name.into(),
                value: if index % 2 == 0 { left } else { right },
                ty: Type::Z,
            })
            .collect();
        let facts = ["first", "second", long.as_str(), "omitted"]
            .into_iter()
            .map(|subject| Fact {
                snapshot: "v".into(),
                subject: subject.into(),
                field: None,
                atom: None,
            })
            .collect();
        template.payload = Some(Payload::Counterexample {
            bindings,
            left,
            right,
            facts,
        });
        result.answers[0].evidence.push(NodeRef(result.nodes.len()));
        result.nodes.push(template.clone());
    }
    let summary = result.summary_wire("complete", 1, &[]);
    let Json::Arr(answers) = &fields(&summary).unwrap()["answers"] else {
        panic!()
    };
    let answer = fields(&answers[0]).unwrap();
    assert_eq!(answer["counterexamples_total"], Json::Nat(4));
    let Json::Arr(examples) = &answer["counterexamples"] else {
        panic!()
    };
    assert_eq!(examples.len(), 3);
    for (example, value) in examples.iter().zip(["12", "10", "12"]) {
        assert_eq!(
            *example,
            Json::obj([
                ("bindings_total", Json::Nat(4)),
                (
                    "bindings",
                    Json::Arr(vec![
                        Json::obj([
                            ("name", Json::str("first")),
                            ("value", expected_integer(value))
                        ]),
                        Json::obj([
                            ("name", Json::str("second")),
                            ("value", expected_integer(value))
                        ]),
                        Json::obj([
                            ("name_bytes", Json::Nat(300)),
                            ("value", expected_integer(value))
                        ]),
                    ])
                ),
                ("left", expected_integer("12")),
                ("right", expected_integer("10")),
                ("facts_total", Json::Nat(4)),
                (
                    "facts",
                    Json::Arr(vec![
                        Json::obj([
                            ("snapshot", Json::str("v")),
                            ("subject", Json::str("first"))
                        ]),
                        Json::obj([
                            ("snapshot", Json::str("v")),
                            ("subject", Json::str("second"))
                        ]),
                        Json::obj([
                            ("snapshot", Json::str("v")),
                            ("subject_bytes", Json::Nat(300))
                        ]),
                    ])
                ),
            ])
        );
    }
}
