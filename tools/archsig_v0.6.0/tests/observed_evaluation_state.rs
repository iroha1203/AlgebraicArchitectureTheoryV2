//! AC14: 三入力 byte から混在状態・予算増加時の確定判断保持までを接続する。
use archsig::{
    archmap::{Slot, Value},
    canonical::{Json, sha256_digest},
    observed::{
        EvaluationFailure, PrepareFailure,
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{InputSources, check_inputs},
        request::{RequestIssueCode, ResolveFailure},
    },
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/counter.law");
const MAP: &[u8] = include_bytes!("fixtures/counter.archmap.json");
const ASKS: [&str; 4] = [
    "bad=check(CountAudit.bounded,s=@v/s)",
    "amount=evaluate(CountCheck.amount,s=@v/s)",
    "missing=check(CountAudit.bounded,s=@v/t)",
    "later=check(CountCheck.nonnegative,s=@v/s)",
];

fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn sources(definitions: &[u8], law: &[u8], map: &[u8]) -> InputSources {
    InputSources::from_bytes(vec![definitions.to_vec()], law.to_vec(), map.to_vec())
}
fn batch_map() -> Vec<u8> {
    let original = std::str::from_utf8(MAP).unwrap();
    let subject = r#"{"id": "s", "type": "Counter.State", "origin": "model"}"#;
    assert_eq!(original.matches(subject).count(), 1);
    assert_eq!(original.matches(r#""value": "2""#).count(), 1);
    original
        .replace(
            subject,
            &format!(
                "{subject}, {{\"id\": \"t\", \"type\": \"Counter.State\", \"origin\": \"model\"}}"
            ),
        )
        .replace(r#""value": "2""#, r#""value": "12""#)
        .into_bytes()
}
fn run(asks: &[&str]) -> Json {
    evaluate_observed_bytes(sources(DEFINITIONS, LAW, &batch_map()), asks, &mut quiet())
        .unwrap()
        .wire()
}
fn obj(json: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(value) = json else {
        panic!("object: {json:?}")
    };
    value
}
fn arr(json: &Json) -> &[Json] {
    let Json::Arr(value) = json else {
        panic!("array: {json:?}")
    };
    value
}
fn text(json: &Json) -> &str {
    let Json::Str(value) = json else {
        panic!("string: {json:?}")
    };
    value
}
fn field<'a>(json: &'a Json, key: &str) -> &'a Json {
    &obj(json)[key]
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    arr(field(wire, "answers"))
        .iter()
        .find(|a| field(a, "id") == &Json::str(id))
        .unwrap()
}
fn nodes(wire: &Json) -> BTreeMap<&str, &Json> {
    arr(field(wire, "nodes"))
        .iter()
        .map(|n| (text(field(n, "id")), n))
        .collect()
}
fn target<'a>(index: &BTreeMap<&str, &'a Json>, reference: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    index[text(field(reference, "node"))]
}
fn typed<'a>(index: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &str) -> &'a Json {
    let node = target(index, reference);
    assert_eq!(field(node, "type"), &Json::str(ty));
    node
}
fn value(node: &Json) -> &Json {
    assert_eq!(field(node, "state"), &Json::str("value"));
    field(node, "value")
}
fn law_slice(location: &Json) -> &[u8] {
    assert_eq!(field(location, "input"), &Json::str("law"));
    let [Json::Nat(start), Json::Nat(end)] = arr(field(location, "span")) else {
        panic!("元 byte の半開区間")
    };
    &LAW[*start as usize..*end as usize]
}
fn fact(subject: &str, known: bool) -> Json {
    let mut value = BTreeMap::from([
        ("snapshot".into(), Json::str("v")),
        ("subject".into(), Json::str(subject)),
        ("field".into(), Json::str("Counter.State.count")),
    ]);
    if known {
        value.insert("atom".into(), Json::str("count"));
    }
    Json::Obj(value)
}
fn refs(json: &Json, found: &mut Vec<String>) {
    match json {
        Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
            found.push(text(&fields["node"]).to_owned());
        }
        Json::Obj(fields) => fields.values().for_each(|v| refs(v, found)),
        Json::Arr(values) => values.iter().for_each(|v| refs(v, found)),
        _ => {}
    }
}
fn reachable(index: &BTreeMap<&str, &Json>, root: &Json) -> BTreeSet<String> {
    let mut pending = vec![];
    refs(root, &mut pending);
    let mut reached = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if reached.insert(id.clone()) {
            refs(index[id.as_str()], &mut pending);
        }
    }
    reached
}
fn scope(item: &Json, reading: &str, domain: &str) {
    let scope = field(item, "scope");
    assert_eq!(
        field(scope, "readings"),
        &Json::Arr(vec![Json::str(reading)])
    );
    assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
    assert_eq!(
        field(scope, "modes"),
        &Json::Arr(vec![Json::str("specification")])
    );
    assert_eq!(field(scope, "domain"), &Json::str(domain));
    for key in ["assumptions", "quantifiers"] {
        assert!(arr(field(scope, key)).is_empty());
    }
}

fn assert_known_answers(wire: &Json) {
    let index = nodes(wire);
    let bad = answer(wire, "bad");
    assert_eq!(field(bad, "status"), &Json::str("refuted"));
    scope(bad, "CountAudit", "finite_model");
    let proposition = typed(&index, field(bad, "claim"), "Proposition");
    assert_eq!(
        field(field(bad, "outputs"), "proposition"),
        field(bad, "claim")
    );
    assert_eq!(
        field(field(proposition, "judgment"), "status"),
        field(bad, "status")
    );
    assert_eq!(field(proposition, "evidence"), field(bad, "evidence"));
    assert_eq!(
        field(field(proposition, "judgment"), "evidence"),
        field(bad, "evidence")
    );
    let evaluation = typed(
        &index,
        field(field(bad, "outputs"), "evaluation"),
        "Evaluation",
    );
    let source = typed(&index, field(value(evaluation), "expression"), "Expression");
    assert_eq!(
        law_slice(field(value(source), "location")),
        b"s.count <= 10"
    );
    assert_eq!(
        value(typed(&index, field(value(evaluation), "value"), "Bool")),
        &Json::Bool(false)
    );
    assert!(arr(field(evaluation, "support")).contains(&fact("s", true)));
    let mut kinds = BTreeSet::new();
    for reference in arr(field(bad, "evidence")) {
        let evidence = typed(&index, reference, "Evidence");
        scope(evidence, "CountAudit", "finite_model");
        assert!(arr(field(evidence, "support")).contains(&fact("s", true)));
        let payload = value(evidence);
        let data = field(payload, "data");
        let kind = text(field(payload, "kind"));
        kinds.insert(kind.to_owned());
        let (left, right) = match kind {
            "evaluation" => {
                assert!(
                    !obj(data).contains_key("residual"),
                    "元の不等式に整数残差を作らない"
                );
                let instance = typed(&index, field(data, "instance"), "LawInstance");
                assert_eq!(
                    field(value(instance), "name"),
                    &Json::str("CountAudit.bounded")
                );
                ("lhs", "rhs")
            }
            "counterexample" => {
                assert!(arr(field(data, "facts")).contains(&fact("s", true)));
                let [binding] = arr(field(data, "bindings")) else {
                    panic!("元parameterの一束縛")
                };
                assert_eq!(field(binding, "name"), &Json::str("s"));
                let subject = target(&index, field(binding, "value"));
                assert_eq!(
                    field(subject, "type"),
                    &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
                );
                assert_eq!(
                    value(subject),
                    &Json::Arr(vec![Json::str("v"), Json::str("s")])
                );
                ("left", "right")
            }
            other => panic!("この不等式の未知Evidence: {other}"),
        };
        assert_eq!(
            value(typed(&index, field(data, left), "Z")),
            &Json::str("12")
        );
        assert_eq!(
            value(typed(&index, field(data, right), "Z")),
            &Json::str("10")
        );
    }
    assert_eq!(
        kinds,
        BTreeSet::from(["evaluation".to_owned(), "counterexample".to_owned()])
    );

    let amount = answer(wire, "amount");
    assert_eq!(field(amount, "status"), &Json::str("established"));
    assert!(!obj(amount).contains_key("claim"));
    assert!(arr(field(amount, "reasons")).is_empty());
    scope(amount, "CountCheck", "finite_model");
    let number = typed(&index, field(field(amount, "outputs"), "value"), "Z");
    assert_eq!(value(number), &Json::str("12"));
    assert!(arr(field(number, "support")).contains(&fact("s", true)));
    let evaluation = typed(
        &index,
        field(field(amount, "outputs"), "evaluation"),
        "Evaluation",
    );
    assert_eq!(
        field(value(evaluation), "value"),
        field(field(amount, "outputs"), "value")
    );
    let source = typed(&index, field(value(evaluation), "expression"), "Expression");
    assert_eq!(law_slice(field(value(source), "location")), b"s.count");

    // FactPointer を、同じ元 bytes の検査済み Atom とその JSON Pointer へ戻す。
    let map = batch_map();
    let checked = check_inputs(sources(DEFINITIONS, LAW, &map), &mut quiet()).unwrap();
    assert_eq!(checked.sources().archmap().bytes(), map);
    let snapshot = &checked.archmap().snapshots[0];
    assert_eq!(snapshot.id, "v");
    let subject = snapshot.subjects.iter().find(|s| s.id == "s").unwrap();
    let count = subject
        .fields
        .iter()
        .find(|f| f.name == "Counter.State.count")
        .unwrap();
    let Slot::Known {
        atom,
        origin,
        value: Value::Z(number),
        pointer,
    } = &count.slot
    else {
        panic!("反例の左辺は元の既知整数 Atom")
    };
    assert_eq!(atom, "count");
    assert_eq!(number.to_string(), "12");
    assert_eq!(pointer, "/snapshots/0/atoms/0/value");
    assert_eq!(origin, "model");
    assert!(std::str::from_utf8(&map).unwrap().contains(
        r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "12", "origin": "model"}"#
    ));
    let origin = checked
        .archmap()
        .origins
        .iter()
        .find(|o| &o.id == origin)
        .unwrap();
    assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
    let absent = snapshot.subjects.iter().find(|s| s.id == "t").unwrap();
    assert_eq!(absent.pointer, "/snapshots/0/subjects/1");
    assert!(matches!(&absent.fields[0].slot, Slot::Missing));
}

fn assert_missing_answer(wire: &Json) {
    let index = nodes(wire);
    let missing = answer(wire, "missing");
    assert_eq!(field(missing, "status"), &Json::str("undetermined"));
    scope(missing, "CountAudit", "all_completions");
    let claim = typed(&index, field(missing, "claim"), "Proposition");
    assert_eq!(
        field(field(claim, "judgment"), "status"),
        field(missing, "status")
    );
    assert_eq!(
        field(field(missing, "outputs"), "proposition"),
        field(missing, "claim")
    );
    let evaluation = typed(
        &index,
        field(field(missing, "outputs"), "evaluation"),
        "Evaluation",
    );
    assert!(!obj(value(evaluation)).contains_key("value"));
    assert!(!obj(field(missing, "outputs")).contains_key("value"));
    for item in [missing, evaluation, claim] {
        let reason = arr(field(item, "reasons"))
            .iter()
            .find(|r| field(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert_eq!(field(reason, "request"), &Json::str("missing"));
        assert_eq!(field(reason, "missing"), &Json::Arr(vec![fact("t", false)]));
        let dependencies = arr(field(reason, "dependencies"));
        assert!(
            !dependencies.is_empty(),
            "欠測元式への到達を空走査で済ませない"
        );
        for reference in dependencies {
            let expression = typed(&index, reference, "Expression");
            assert_eq!(law_slice(field(value(expression), "location")), b"s.count");
            let [binding] = arr(field(value(expression), "bindings")) else {
                panic!("欠測subjectの元束縛")
            };
            assert_eq!(field(binding, "name"), &Json::str("s"));
            assert_eq!(
                value(target(&index, field(binding, "value"))),
                &Json::Arr(vec![Json::str("v"), Json::str("t")])
            );
        }
    }
    for id in reachable(&index, missing) {
        let node = index[id.as_str()];
        assert!(!arr(field(node, "support")).contains(&fact("t", false)));
        assert!(
            !arr(field(node, "support")).contains(&fact("s", true)),
            "別subjectの既知countで欠測を埋めない"
        );
        if field(node, "type") == &Json::str("Evidence") {
            assert_ne!(field(value(node), "kind"), &Json::str("counterexample"));
        }
    }
}

#[test]
fn mixed_refutation_value_and_missing_preserve_typed_answers_and_source_facts() {
    let refutation = run(&ASKS[..1]);
    assert_eq!(field(&refutation, "status"), &Json::str("complete"));
    assert_eq!(arr(field(&refutation, "answers")).len(), 1);
    assert_eq!(
        field(answer(&refutation, "bad"), "status"),
        &Json::str("refuted")
    );
    let mixed = run(&ASKS);
    assert_eq!(field(&mixed, "status"), &Json::str("partial"));
    assert_eq!(
        arr(field(&mixed, "answers"))
            .iter()
            .map(|a| text(field(a, "id")))
            .collect::<Vec<_>>(),
        ["bad", "amount", "missing", "later"]
    );
    assert_known_answers(&mixed);
    assert_missing_answer(&mixed);
    assert_eq!(
        field(answer(&mixed, "later"), "status"),
        &Json::str("established")
    );
    assert_eq!(answer(&mixed, "bad"), answer(&refutation, "bad"));
}

type Trace = Rc<RefCell<Vec<(Checkpoint, Usage)>>>;

fn recorded_run(
    asks: &[&str],
    limits: Limits,
    stop_index: Option<usize>,
    memory: bool,
) -> (Json, Trace, Control) {
    let seen = Rc::new(RefCell::new(Vec::new()));
    let capture = seen.clone();
    let mut control = Control::new(limits, move |point| {
        let mut trace = capture.borrow_mut();
        // 同一checkpoint列に同一の小さい単調Usage列を適用する。実時計/RSSは読まない。
        let amount = if stop_index.is_some_and(|at| trace.len() >= at) {
            3
        } else {
            0
        };
        let usage = if memory {
            Usage {
                memory_mib: amount,
                ..Usage::default()
            }
        } else {
            Usage {
                elapsed_ms: amount,
                ..Usage::default()
            }
        };
        trace.push((point, usage));
        usage
    });
    let wire = evaluate_observed_bytes(sources(DEFINITIONS, LAW, &batch_map()), asks, &mut control)
        .unwrap()
        .wire();
    (wire, seen, control)
}

fn assert_budget_increase_preserves_completed_answers(memory: bool) {
    // source式が既知の二問を完了する正常対照から、その式境界数を求める。
    let (prefix, prefix_trace, _) = recorded_run(&ASKS[..2], Limits::default(), None, memory);
    assert_eq!(field(&prefix, "status"), &Json::str("complete"));
    assert_known_answers(&prefix);
    let complete_expressions = prefix_trace
        .borrow()
        .iter()
        .filter(|(p, _)| *p == Checkpoint::Expression)
        .count();
    assert!(complete_expressions > 0);
    let (normal, normal_trace, _) = recorded_run(&ASKS, Limits::default(), None, memory);
    assert_missing_answer(&normal);
    let stop_index = normal_trace
        .borrow()
        .iter()
        .enumerate()
        .filter(|(_, (p, _))| *p == Checkpoint::Expression)
        .nth(complete_expressions)
        .unwrap()
        .0;
    assert!(stop_index > 0 && stop_index + 1 < normal_trace.borrow().len());
    let limits = |amount| {
        if memory {
            Limits {
                time_ms: None,
                memory_mib: Some(amount),
            }
        } else {
            Limits {
                time_ms: Some(amount),
                memory_mib: None,
            }
        }
    };
    let (low, low_trace, mut low_control) =
        recorded_run(&ASKS, limits(3), Some(stop_index), memory);
    let (high, high_trace, high_control) = recorded_run(&ASKS, limits(4), Some(stop_index), memory);
    assert_eq!(field(&low, "status"), &Json::str("interrupted"));
    assert_eq!(field(&high, "status"), &Json::str("partial"));
    assert_eq!(
        high, normal,
        "高予算は正常対照の最終判断・証拠・元位置を再現する"
    );
    assert_eq!(
        high_trace
            .borrow()
            .iter()
            .map(|(p, _)| *p)
            .collect::<Vec<_>>(),
        normal_trace
            .borrow()
            .iter()
            .map(|(p, _)| *p)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        &**low_trace.borrow(),
        &high_trace.borrow()[..=stop_index],
        "同一checkpoint/Usage traceの第三問の式開始前で止まる"
    );
    assert_eq!(low_trace.borrow().len(), stop_index + 1);
    assert!(high_control.stop_reason().is_none());
    assert_known_answers(&low);
    assert_known_answers(&high);
    assert_missing_answer(&high);
    assert_eq!(
        field(answer(&high, "later"), "status"),
        &Json::str("established")
    );
    let (low_nodes, high_nodes) = (nodes(&low), nodes(&high));
    for id in ["bad", "amount"] {
        let previous = answer(&low, id);
        assert_eq!(
            previous,
            answer(&high, id),
            "完成済みAnswerのclaim/判断/Scopeを保持する"
        );
        let reached = reachable(&low_nodes, previous);
        assert!(!reached.is_empty());
        for node in reached {
            assert_eq!(
                low_nodes[node.as_str()],
                high_nodes[node.as_str()],
                "支持・元式・型付き値・証拠の導出を保持する"
            );
        }
    }
    let reason = low_control.stop_reason().unwrap().wire();
    let details = Json::obj([
        (
            "resource",
            Json::str(if memory { "memory_mib" } else { "time_ms" }),
        ),
        ("limit", Json::str("3")),
        ("observed", Json::str("3")),
    ]);
    assert_eq!(field(&reason, "details"), &details);
    for id in ["missing", "later"] {
        let pending = answer(&low, id);
        assert_eq!(field(pending, "status"), &Json::str("undetermined"));
        assert!(!obj(pending).contains_key("claim"));
        assert!(obj(field(pending, "outputs")).is_empty());
        assert!(arr(field(pending, "evidence")).is_empty());
        let [stopped] = arr(field(pending, "reasons")) else {
            panic!("同じ停止理由一件")
        };
        assert_eq!(field(stopped, "code"), &Json::str("budget_exhausted"));
        assert_eq!(field(stopped, "request"), &Json::str(id));
        assert_eq!(field(stopped, "details"), &details);
    }
    // 第三問には新しいsource Expressionがなく、第四問の原式も生成されていない。
    for node in low_nodes
        .values()
        .filter(|n| field(n, "type") == &Json::str("Expression"))
    {
        let payload = value(node);
        assert_ne!(law_slice(field(payload, "location")), b"s.count >= 0");
        for binding in arr(field(payload, "bindings")) {
            assert_ne!(
                value(target(&low_nodes, field(binding, "value"))),
                &Json::Arr(vec![Json::str("v"), Json::str("t")])
            );
        }
    }
    let before = low_control.usage();
    assert!(low_control.checkpoint(Checkpoint::Expression).is_err());
    assert!(low_control.checkpoint(Checkpoint::FiniteIteration).is_err());
    assert_eq!(low_control.usage(), before);
    assert_eq!(
        low_trace.borrow().len(),
        stop_index + 1,
        "同じ評価driverの停止後にprobeを再実行しない"
    );
}

#[test]
fn increasing_time_budget_preserves_established_value_and_refuted_counterexample() {
    assert_budget_increase_preserves_completed_answers(false);
}

#[test]
fn increasing_memory_budget_preserves_established_value_and_refuted_counterexample() {
    assert_budget_increase_preserves_completed_answers(true);
}

#[test]
fn byte_entry_rejections_keep_stage_metadata_and_original_input_identity() {
    let normal = evaluate_observed_bytes(sources(DEFINITIONS, LAW, MAP), &ASKS[..2], &mut quiet())
        .unwrap()
        .wire();
    assert_eq!(field(&normal, "status"), &Json::str("complete"));
    assert_eq!(
        field(answer(&normal, "bad"), "status"),
        &Json::str("established")
    );
    assert_eq!(
        value(typed(
            &nodes(&normal),
            field(field(answer(&normal, "amount"), "outputs"), "value"),
            "Z"
        )),
        &Json::str("2")
    );
    for key in ["declarations", "vocabularies"] {
        assert!(!arr(field(&normal, key)).is_empty());
    }
    // 各入力段階で構文不正と未知formatを一件ずつ通す。表の保持段階を横断する六件。
    for (stage, original, format) in [
        ("definition0", DEFINITIONS, "archsig.atom-definition/1"),
        ("law", LAW, "archsig.law/2"),
        ("archmap", MAP, "archsig.archmap/2"),
    ] {
        for unsupported in [false, true] {
            let mutated = if unsupported {
                std::str::from_utf8(original)
                    .unwrap()
                    .replace(format, "archsig.unknown/99")
                    .into_bytes()
            } else {
                b"?".to_vec()
            };
            let (definitions, law, map) = (
                if stage == "definition0" {
                    mutated.as_slice()
                } else {
                    DEFINITIONS
                },
                if stage == "law" {
                    mutated.as_slice()
                } else {
                    LAW
                },
                if stage == "archmap" {
                    mutated.as_slice()
                } else {
                    MAP
                },
            );
            let failure =
                evaluate_observed_bytes(sources(definitions, law, map), &ASKS[..2], &mut quiet())
                    .unwrap_err();
            assert!(matches!(
                &failure,
                EvaluationFailure::Prepare(PrepareFailure::Inputs(_))
            ));
            let wire = failure.wire().unwrap();
            assert_eq!(
                field(&wire, "status"),
                &Json::str(if unsupported {
                    "unsupported"
                } else {
                    "invalid"
                })
            );
            for key in ["declarations", "vocabularies"] {
                if stage == "archmap" {
                    assert_eq!(field(&wire, key), field(&normal, key));
                } else {
                    assert!(arr(field(&wire, key)).is_empty());
                }
            }
            for key in ["requests", "answers", "nodes"] {
                assert!(arr(field(&wire, key)).is_empty());
            }
            let identities = arr(field(&wire, "inputs"));
            assert_eq!(identities.len(), 3);
            for (id, bytes) in [("definition0", definitions), ("law", law), ("archmap", map)] {
                let input = identities
                    .iter()
                    .find(|i| field(i, "id") == &Json::str(id))
                    .unwrap();
                assert_eq!(field(input, "state"), &Json::str("read"));
                assert_eq!(
                    field(input, "bytes_digest"),
                    &Json::str(sha256_digest(bytes))
                );
                assert!(!obj(input).contains_key("path"));
            }
            let [issue] = arr(field(&wire, "issues")) else {
                panic!("元入力の拒否一件")
            };
            assert_eq!(
                field(issue, "code"),
                &Json::str(if unsupported {
                    "unsupported_version"
                } else {
                    "syntax"
                })
            );
            let location = field(issue, "location");
            assert_eq!(field(location, "input"), &Json::str(stage));
            if stage == "law" {
                let end = if unsupported {
                    mutated.iter().position(|&b| b == b';').unwrap() + 1
                } else {
                    1
                };
                assert_eq!(
                    field(location, "span"),
                    &Json::Arr(vec![Json::Nat(0), Json::Nat(end as u64)])
                );
            } else {
                assert_eq!(
                    field(location, "pointer"),
                    &Json::str(if unsupported { "/format" } else { "" })
                );
                if !unsupported {
                    assert_eq!(
                        field(location, "span"),
                        &Json::Arr(vec![Json::Nat(0), Json::Nat(1)])
                    );
                }
            }
            assert!(!text(field(issue, "message")).is_empty());
            if unsupported {
                assert_eq!(
                    field(field(issue, "details"), "found_format"),
                    &Json::str("archsig.unknown/99")
                );
                assert_eq!(
                    field(field(issue, "details"), "found_semantics"),
                    &Json::str("archsig/0.6.0")
                );
            }
        }
    }
    let failure = evaluate_observed_bytes(
        sources(DEFINITIONS, LAW, MAP),
        &["unbound=evaluate(CountCheck.amount)"],
        &mut quiet(),
    )
    .unwrap_err();
    let EvaluationFailure::Prepare(PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { issues, .. },
        ..
    }) = &failure
    else {
        panic!("要求解決の拒否")
    };
    let [issue] = issues.as_slice() else {
        panic!("不足束縛一件")
    };
    assert_eq!(issue.code, RequestIssueCode::MissingBinding);
    assert_eq!(issue.request, "unbound");
    assert_eq!(issue.argument, "s");
    let wire = failure.wire().unwrap();
    assert_eq!(field(&wire, "status"), &Json::str("invalid"));
    for key in ["inputs", "declarations", "vocabularies"] {
        assert_eq!(field(&wire, key), field(&normal, key));
    }
    for key in ["requests", "answers", "nodes"] {
        assert!(arr(field(&wire, key)).is_empty());
    }
    let [issue] = arr(field(&wire, "issues")) else {
        panic!("要求に帰属する理由")
    };
    assert_eq!(field(issue, "request"), &Json::str("unbound"));
    assert_eq!(field(issue, "code"), &Json::str("usage"));
    assert_eq!(field(field(issue, "details"), "argument"), &Json::str("s"));
    assert!(!obj(issue).contains_key("location"));
}
