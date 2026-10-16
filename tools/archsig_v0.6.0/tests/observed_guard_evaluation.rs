//! AC2: Bool値とLaw判断、guardの適用状態と全補完での成立を三入力から区別する。
use archsig::result::Signal;
use archsig::{
    canonical::Json,
    definition::check_definitions,
    law::model::Signature,
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{InputSources, check_inputs},
    },
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

fn control() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object: {j:?}")
    };
    v
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array: {j:?}")
    };
    v
}
fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string: {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    &obj(j)[key]
}
fn payload(j: &Json) -> &Json {
    assert_eq!(f(j, "state"), &Json::str("value"));
    f(j, "value")
}
fn index(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(nodes: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &str) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let node = nodes[text(f(reference, "node"))];
    assert_eq!(f(node, "type"), &Json::str(ty));
    node
}
fn answer<'a>(j: &'a Json, id: &str) -> &'a Json {
    arr(f(j, "answers"))
        .iter()
        .find(|a| text(f(a, "id")) == id)
        .unwrap()
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(v) if v.len() == 1 && v.contains_key("node") => out.push(text(&v["node"]).into()),
        Json::Obj(v) => {
            for item in v.values() {
                refs(item, out);
            }
        }
        Json::Arr(v) => {
            for item in v {
                refs(item, out);
            }
        }
        _ => {}
    }
}
fn reachable(nodes: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut todo = vec![];
    for root in roots {
        refs(root, &mut todo);
    }
    let mut found = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if found.insert(id.clone()) {
            refs(nodes[id.as_str()], &mut todo);
        }
    }
    found
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |j: &Json| {
        let Json::Nat(n) = j else { panic!("Nat") };
        *n as usize
    };
    (nat(&a[0]), nat(&a[1]))
}
fn fact(field: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str("current")),
        ("subject", Json::str("root")),
        ("field", Json::str(format!("Signal.Cell.{field}"))),
        ("atom", Json::str(field)),
    ])
}

fn fixture(gate: Option<bool>, body: Option<bool>) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Signal","version":"1",
      "dependencies":[],"declarations":[{"kind":"entity","name":"Signal.Cell","meaning":"二つのBool観測を持つ対象。",
      "parameters":[],"fields":[{"name":"gate","type":"Bool","meaning":"適用の条件。"},
      {"name":"payload","type":"Bool","meaning":"検査する値。"}],"alignments":[]}]}]}"#;
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Signal"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Inspect {{
  use vocabulary Signal version "1" digest "{digest}";
  view value(item: Cell): Bool = item.payload;
  law required raw(item: Cell): item.payload;
  law required guarded(item: Cell) when item.gate: item.payload;
}}
"#
    );
    let atoms=[("gate",gate,"permission"),("payload",body,"body")].into_iter().filter_map(|(field,value,origin)|
        value.map(|v|format!(r#"{{"id":"{field}","subject":"root","field":"Signal.Cell.{field}","value":{v},"origin":"{origin}"}}"#)))
        .collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Signal","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"source","uri":"urn:fixture:bool-reading","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[
        {{"id":"body","mode":"specification","method":"対象と値を提示する。","locations":[{{"source":"source","path":"payload.model","span":[0,4]}}]}},
        {{"id":"permission","mode":"specification","method":"適用条件を別の由来で提示する。","locations":[{{"source":"source","path":"gate.model","span":[5,9]}}]}}],
      "snapshots":[{{"id":"current","origin":"body","subjects":[{{"id":"root","type":"Signal.Cell","origin":"body"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn audit_dag(result: &Json) {
    let nodes = index(result);
    let mut earlier = BTreeSet::new();
    for node in arr(f(result, "nodes")) {
        let mut links = vec![];
        refs(node, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "全Refは既出nodeを指す");
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if let Some(value) = obj(node).get("value") {
            let mut links = vec![];
            refs(value, &mut links);
            for link in links {
                assert_ne!(f(nodes[link.as_str()], "state"), &Json::str("blocked"));
            }
            if f(node, "type") == &Json::str("Expression") {
                assert!(arr(f(value, "parameters")).is_empty());
                for binding in arr(f(value, "bindings")) {
                    assert_eq!(f(binding, "name"), &Json::str("item"));
                    let bound = nodes[text(f(f(binding, "value"), "node"))];
                    assert_eq!(
                        f(bound, "type"),
                        &Json::Arr(vec![Json::str("Ref"), Json::str("Signal.Cell")])
                    );
                    assert_eq!(
                        payload(bound),
                        &Json::Arr(vec![Json::str("current"), Json::str("root")])
                    );
                }
                if f(value, "kind") == &Json::str("transform") {
                    assert!(matches!(text(f(value, "operation")), "not" | "and"));
                    for operand in arr(f(value, "operands")) {
                        target(&nodes, operand, "Expression");
                    }
                }
            }
            if f(node, "type") == &Json::str("Evaluation") {
                target(&nodes, f(value, "expression"), "Expression");
                for part in arr(f(value, "parts")) {
                    assert!(
                        !obj(part).contains_key("residual"),
                        "一般Boolに整数残差を作らない"
                    );
                    for child in arr(f(part, "children")) {
                        target(&nodes, child, "Evaluation");
                    }
                }
            }
            if f(node, "type") == &Json::str("Evidence") {
                let data = f(value, "data");
                assert!(!obj(data).contains_key("residual"));
                if f(value, "kind") == &Json::str("counterexample") {
                    assert_eq!(
                        payload(target(&nodes, f(data, "left"), "Bool")),
                        &Json::Bool(false)
                    );
                    assert_eq!(
                        payload(target(&nodes, f(data, "right"), "Bool")),
                        &Json::Bool(true)
                    );
                }
            }
        }
        assert_ne!(
            f(node, "type"),
            &Json::str("Z"),
            "Boolの値や残差をZへ変換しない"
        );
    }
    for a in arr(f(result, "answers")) {
        if let Some(claim) = obj(a).get("claim") {
            let proposition = target(&nodes, claim, "Proposition");
            assert_eq!(f(f(proposition, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(f(a, "outputs"), "proposition"), claim);
        }
        let mut links = vec![];
        refs(a, &mut links);
        for link in links {
            assert!(nodes.contains_key(link.as_str()));
        }
    }
}

fn source_evaluation<'a>(
    nodes: &BTreeMap<&str, &'a Json>,
    application: &Json,
    position: (usize, usize),
) -> &'a Json {
    let parts: Vec<_> = arr(f(payload(application), "parts"))
        .iter()
        .filter(|part| span(f(part, "location")) == position)
        .collect();
    assert_eq!(parts.len(), 1, "元適用評価のAST位置は一意");
    let children = arr(f(parts[0], "children"));
    assert_eq!(children.len(), 1, "元観測guard/bodyの直接実評価を保持");
    let evaluation = target(nodes, &children[0], "Evaluation");
    let expression = payload(target(
        nodes,
        f(payload(evaluation), "expression"),
        "Expression",
    ));
    assert_eq!(f(expression, "kind"), &Json::str("source"));
    assert_eq!(span(f(expression, "location")), position);
    assert_eq!(
        f(payload(evaluation), "bindings"),
        f(payload(application), "bindings")
    );
    assert_eq!(
        f(expression, "bindings"),
        f(payload(evaluation), "bindings")
    );
    evaluation
}

fn completion_cases(
    nodes: &BTreeMap<&str, &Json>,
    answer: &Json,
    root: &Json,
    seed: &Json,
    observed: &Json,
    values: (Option<bool>, Option<bool>),
    positions: ((usize, usize), (usize, usize)),
) {
    let (gate, body) = values;
    let (guard_span, body_span) = positions;
    let root_args = arr(f(root, "arguments"));
    assert_eq!(f(&root_args[0], "node"), f(seed, "id"));
    let domain = target(nodes, &root_args[1], "Domain");
    let elements = arr(f(payload(domain), "elements"));
    let missing: Vec<_> = [("gate", gate), ("payload", body)]
        .into_iter()
        .filter(|(_, v)| v.is_none())
        .map(|(name, _)| name)
        .collect();
    assert_eq!(elements.len(), 1usize << missing.len());
    let parts = arr(f(payload(root), "parts"));
    assert_eq!(parts.len(), 1);
    assert_eq!(span(f(&parts[0], "location")), body_span);
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), elements.len());
    assert_eq!(&root_args[2..2 + cases.len()], cases);
    let propositions = &root_args[2 + cases.len()..];
    assert_eq!(propositions.len(), cases.len());
    assert_eq!(f(payload(root), "applicability"), &Json::str("applicable"));
    assert_eq!(f(payload(seed), "kind"), &Json::str("source"));
    assert_eq!(span(f(payload(seed), "location")), body_span);
    assert_eq!(
        f(payload(seed), "bindings"),
        f(payload(observed), "bindings")
    );
    let mut seen = BTreeSet::new();
    let mut case_values = Vec::new();
    for case_ref in cases {
        let case = target(nodes, case_ref, "Evaluation");
        let raw_guard = source_evaluation(nodes, case, guard_span);
        let source = target(nodes, f(payload(raw_guard), "expression"), "Expression");
        let anchors = arr(f(source, "arguments"));
        assert_eq!(anchors.len(), 4 + missing.len());
        assert_eq!(&anchors[1], &root_args[0]);
        assert_eq!(&anchors[2], &root_args[1]);
        let member = &anchors[3];
        assert!(elements.contains(member));
        assert!(seen.insert(text(f(member, "node"))));
        let member_node = nodes[text(f(member, "node"))];
        let assignment: Vec<_> = if missing.len() == 1 {
            vec![payload(member_node)]
        } else {
            arr(payload(member_node)).iter().collect()
        };
        let projections = &anchors[4..];
        for (i, projection) in projections.iter().enumerate() {
            let value = target(nodes, projection, "Bool");
            assert_eq!(payload(value), assignment[i]);
            for support in arr(f(value, "support")) {
                if obj(support).contains_key("field") {
                    assert!(
                        [("gate", gate), ("payload", body)]
                            .into_iter()
                            .any(|(name, known)| known.is_some() && *support == fact(name)),
                        "補完projectionへ欠測Atomを加えない"
                    );
                }
            }
            let args = arr(f(value, "arguments"));
            assert_eq!(args.len(), 4);
            assert_eq!(&args[..3], &anchors[1..4]);
            let field_source = target(nodes, &args[3], "Expression");
            assert_eq!(
                span(f(payload(field_source), "location")),
                if missing[i] == "gate" {
                    guard_span
                } else {
                    body_span
                }
            );
        }
        let assigned = |name: &str, known: Option<bool>| {
            known.unwrap_or_else(|| {
                let i = missing.iter().position(|field| *field == name).unwrap();
                let Json::Bool(value) = assignment[i] else {
                    panic!("Bool補完")
                };
                *value
            })
        };
        let actual_gate = assigned("gate", gate);
        bool_value(nodes, raw_guard, Some(actual_gate));
        let case_parts = arr(f(payload(case), "parts"));
        assert_eq!(case_parts.len(), 2);
        let body_part = case_parts
            .iter()
            .find(|part| span(f(part, "location")) == body_span)
            .unwrap();
        let expected = if actual_gate {
            assert_eq!(f(payload(case), "applicability"), &Json::str("applicable"));
            let actual_body = assigned("payload", body);
            bool_value(
                nodes,
                source_evaluation(nodes, case, body_span),
                Some(actual_body),
            );
            actual_body
        } else {
            assert_eq!(
                f(payload(case), "applicability"),
                &Json::str("not_applicable")
            );
            assert!(arr(f(body_part, "children")).is_empty());
            assert!(!obj(body_part).contains_key("value"));
            true
        };
        bool_value(nodes, case, Some(expected));
        case_values.push(expected);
        let matches: Vec<_> = propositions
            .iter()
            .map(|p| target(nodes, p, "Proposition"))
            .filter(|p| arr(f(p, "arguments")).get(1) == Some(case_ref))
            .collect();
        assert_eq!(matches.len(), 1);
        let proposition = matches[0];
        assert_eq!(
            f(f(proposition, "judgment"), "status"),
            &Json::str(if expected { "established" } else { "refuted" })
        );
        let instance = target(nodes, &arr(f(proposition, "arguments"))[0], "LawInstance");
        assert_eq!(
            f(payload(instance), "bindings"),
            f(payload(case), "bindings")
        );
        for (field, position) in [("guard", guard_span), ("body", body_span)] {
            let expression = target(nodes, f(payload(instance), field), "Expression");
            assert_eq!(span(f(payload(expression), "location")), position);
            assert_eq!(
                f(payload(expression), "bindings"),
                f(payload(case), "bindings")
            );
        }
        let counterexamples: Vec<_> = arr(f(proposition, "evidence"))
            .iter()
            .map(|e| target(nodes, e, "Evidence"))
            .filter(|e| f(payload(e), "kind") == &Json::str("counterexample"))
            .collect();
        assert_eq!(!counterexamples.is_empty(), !expected);
        for example in counterexamples {
            assert_eq!(&arr(f(example, "arguments"))[1], case_ref);
            assert_eq!(
                f(f(payload(example), "data"), "bindings"),
                f(payload(case), "bindings")
            );
        }
    }
    assert_eq!(seen.len(), elements.len());
    let all_same = case_values.iter().all(|value| *value == case_values[0]);
    let evidence = arr(f(answer, "evidence"));
    assert_eq!(evidence.len(), 1);
    assert_eq!(f(root, "evidence"), f(answer, "evidence"));
    let proof = target(nodes, &evidence[0], "Evidence");
    let data = f(payload(proof), "data");
    assert_ne!(
        f(payload(proof), "kind"),
        &Json::str("counterexample"),
        "補完外の単一観測反例を捏造しない"
    );
    if all_same {
        bool_value(nodes, root, Some(case_values[0]));
        assert_eq!(f(payload(proof), "kind"), &Json::str("finite_exhaustion"));
        assert_eq!(f(data, "domain"), &root_args[1]);
        assert_eq!(f(data, "checked"), &Json::Nat(cases.len() as u64));
        let covered = arr(f(data, "instances"));
        assert_eq!(covered.len(), cases.len());
        for case in cases {
            assert_eq!(covered.iter().filter(|r| *r == case).count(), 1);
        }
    } else {
        bool_value(nodes, root, None);
        assert_eq!(f(payload(proof), "kind"), &Json::str("completion_pair"));
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), missing.len());
        for (field, name) in fields.iter().zip(&missing) {
            assert_eq!(f(field, "snapshot"), &Json::str("current"));
            assert_eq!(f(field, "subject"), &Json::str("root"));
            assert_eq!(f(field, "field"), &Json::str(format!("Signal.Cell.{name}")));
            assert!(!obj(field).contains_key("atom"));
        }
        let mut results = Vec::new();
        for (side, result_field) in [("first", "first_result"), ("second", "second_result")] {
            let reference = f(data, result_field);
            assert!(cases.contains(reference));
            let result = target(nodes, reference, "Evaluation");
            let guard = source_evaluation(nodes, result, guard_span);
            let source = target(nodes, f(payload(guard), "expression"), "Expression");
            assert_eq!(arr(f(data, side)), &arr(f(source, "arguments"))[4..]);
            results.push(payload(target(nodes, f(payload(result), "value"), "Bool")));
        }
        assert_ne!(results[0], results[1]);
    }
}

fn bool_value(nodes: &BTreeMap<&str, &Json>, evaluation: &Json, expected: Option<bool>) {
    match expected {
        Some(b) => assert_eq!(
            payload(target(nodes, f(payload(evaluation), "value"), "Bool")),
            &Json::Bool(b)
        ),
        None => assert!(
            !obj(payload(evaluation)).contains_key("value"),
            "欠測のraw値をtrue/falseへ補わない"
        ),
    }
}

fn guarded_case(
    gate: Option<bool>,
    body: Option<bool>,
    decision: &str,
    applicability: &str,
    conditional: Option<bool>,
) {
    let inputs = fixture(gate, body);
    let checked = check_inputs(inputs.clone(), &mut control()).unwrap();
    let result = evaluate_observed_bytes(
        inputs,
        &["g=check(Inspect.guarded,item=@current/root)"],
        &mut control(),
    )
    .unwrap()
    .wire();
    assert_eq!(
        f(&result, "status"),
        &Json::str(if decision == "undetermined" {
            "partial"
        } else {
            "complete"
        })
    );
    let a = answer(&result, "g");
    assert_eq!(f(a, "status"), &Json::str(decision));
    let nodes = index(&result);
    let root_ref = f(f(a, "outputs"), "evaluation");
    let final_root = target(&nodes, root_ref, "Evaluation");
    let root_args = arr(f(final_root, "arguments"));
    let completion = root_args.get(1).is_some_and(|reference| {
        f(nodes[text(f(reference, "node"))], "type") == &Json::str("Domain")
    });
    let seed = completion.then(|| target(&nodes, &root_args[0], "Expression"));
    let root = if let Some(seed) = seed {
        assert_eq!(f(payload(final_root), "expression"), &root_args[0]);
        let originals: Vec<_> = arr(f(seed, "arguments"))
            .iter()
            .map(|r| nodes[text(f(r, "node"))])
            .filter(|node| f(node, "type") == &Json::str("Evaluation"))
            .collect();
        assert_eq!(originals.len(), 1, "CompletionSeed直下の元観測適用を選ぶ");
        originals[0]
    } else {
        final_root
    };
    assert_eq!(f(payload(root), "applicability"), &Json::str(applicability));
    bool_value(&nodes, root, conditional);
    bool_value(&nodes, final_root, conditional);
    let reached = reachable(&nodes, &[f(a, "outputs"), f(a, "claim"), f(a, "evidence")]);
    let from_evaluation = reachable(&nodes, &[root_ref]);
    let declaration = &checked.law().declarations["Inspect.guarded"];
    let Signature::Law {
        guard: Some(guard),
        body: body_id,
        ..
    } = &declaration.signature
    else {
        panic!("明示guardとbody")
    };
    let raw_guard = source_evaluation(&nodes, root, checked.law().exprs[*guard].span);
    let raw_body = source_evaluation(&nodes, root, checked.law().exprs[*body_id].span);
    for raw in [raw_guard, raw_body] {
        assert!(
            from_evaluation.contains(text(f(raw, "id"))),
            "返却適用評価も元guard/body双方へ戻る"
        );
    }
    bool_value(&nodes, raw_guard, gate);
    bool_value(&nodes, raw_body, body);
    if gate != Some(true) {
        let expression_ref = f(payload(root), "expression");
        let expression = payload(target(&nodes, expression_ref, "Expression"));
        assert_eq!(f(expression, "kind"), &Json::str("transform"));
        let expression_dependencies = reachable(&nodes, &[expression_ref]);
        for raw in [raw_guard, raw_body] {
            let source_ref = f(payload(raw), "expression");
            assert!(
                expression_dependencies.contains(text(f(source_ref, "node"))),
                "条件付きの原式変換自体から元guard/body双方へ戻れる"
            );
        }
    }
    for raw in [raw_guard, raw_body] {
        let bs = arr(f(payload(raw), "bindings"));
        assert_eq!(text(f(&bs[0], "name")), "item");
        let bound = nodes[text(f(f(&bs[0], "value"), "node"))];
        assert_eq!(
            f(bound, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Signal.Cell")])
        );
        assert_eq!(
            payload(bound),
            &Json::Arr(vec![Json::str("current"), Json::str("root")])
        );
    }
    let expected_missing: BTreeSet<_> = [("gate", gate), ("payload", body)]
        .into_iter()
        .filter(|(_, v)| v.is_none())
        .map(|(name, _)| format!("Signal.Cell.{name}"))
        .collect();
    let mut actual_missing = BTreeSet::new();
    for reason in arr(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
    {
        assert!(!arr(f(reason, "dependencies")).is_empty());
        for missing in arr(f(reason, "missing")) {
            assert_eq!(f(missing, "snapshot"), &Json::str("current"));
            assert_eq!(f(missing, "subject"), &Json::str("root"));
            assert!(!obj(missing).contains_key("atom"));
            actual_missing.insert(text(f(missing, "field")).to_owned());
        }
        for dependency in arr(f(reason, "dependencies")) {
            let source = target(&nodes, dependency, "Expression");
            let source = payload(source);
            assert_eq!(f(source, "kind"), &Json::str("source"));
            let position = span(f(source, "location"));
            assert!(
                position == checked.law().exprs[*guard].span
                    || position == checked.law().exprs[*body_id].span
            );
        }
    }
    assert_eq!(actual_missing, expected_missing);
    for item in [a, root, final_root] {
        let scope = f(item, "scope");
        assert_eq!(
            f(scope, "domain"),
            &Json::str(if expected_missing.is_empty() {
                "finite_model"
            } else {
                "all_completions"
            })
        );
        assert_eq!(
            f(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
        assert_eq!(
            f(scope, "snapshots"),
            &Json::Arr(vec![Json::str("current")])
        );
        assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Inspect")]));
        assert!(arr(f(scope, "quantifiers")).is_empty());
        assert!(arr(f(scope, "assumptions")).is_empty());
    }
    let expected_facts: Vec<_> = [("gate", gate), ("payload", body)]
        .into_iter()
        .filter(|(_, v)| v.is_some())
        .map(|(name, _)| fact(name))
        .collect();
    for expected in &expected_facts {
        assert!(arr(f(root, "support")).contains(expected));
        assert!(arr(f(final_root, "support")).contains(expected));
    }
    for support in arr(f(root, "support")) {
        if obj(support).contains_key("field") {
            assert!(expected_facts.contains(support));
            let subject = &checked.archmap().snapshots[0].subjects[0];
            let field = subject
                .fields
                .iter()
                .find(|field| field.name == text(f(support, "field")))
                .unwrap();
            let archsig::archmap::Slot::Known { atom, origin, .. } = &field.slot else {
                panic!("欠測をsupportへ加えない")
            };
            assert_eq!(atom, text(f(support, "atom")));
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == origin.locations[0].source)
                .unwrap();
            assert_eq!(source.uri, "urn:fixture:bool-reading");
            assert_eq!(
                origin.locations[0].path,
                if atom == "gate" {
                    "gate.model"
                } else {
                    "payload.model"
                }
            );
        }
    }
    let observed_reached = if let Some(seed) = seed {
        let original_roots: Vec<_> = arr(f(seed, "arguments"))
            .iter()
            .filter(|reference| {
                let ty = f(nodes[text(f(reference, "node"))], "type");
                ty == &Json::str("Evaluation") || ty == &Json::str("Proposition")
            })
            .collect();
        reachable(&nodes, &original_roots)
    } else {
        reached.clone()
    };
    let counterexamples: Vec<_> = observed_reached
        .iter()
        .map(|id| nodes[id.as_str()])
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(payload(n), "kind") == &Json::str("counterexample")
        })
        .collect();
    if let Some(seed) = seed {
        completion_cases(
            &nodes,
            a,
            final_root,
            seed,
            root,
            (gate, body),
            (
                checked.law().exprs[*guard].span,
                checked.law().exprs[*body_id].span,
            ),
        );
    }
    if decision == "refuted" {
        assert!(!counterexamples.is_empty());
        for e in counterexamples {
            for expected in &expected_facts {
                assert!(arr(f(f(payload(e), "data"), "facts")).contains(expected));
            }
        }
    } else {
        assert!(counterexamples.is_empty(), "未決や非適用へ反例を偽造しない");
    }
    audit_dag(&result);
}

#[test]
fn bool_false_view_is_established_while_the_same_field_law_is_refuted() {
    let result = evaluate_observed_bytes(
        fixture(Some(true), Some(false)),
        &[
            "v=evaluate(Inspect.value,item=@current/root)",
            "l=check(Inspect.raw,item=@current/root)",
        ],
        &mut control(),
    )
    .unwrap()
    .wire();
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    assert_eq!(
        arr(f(&result, "answers"))
            .iter()
            .map(|a| text(f(a, "id")))
            .collect::<Vec<_>>(),
        ["v", "l"]
    );
    let nodes = index(&result);
    let view = answer(&result, "v");
    let law = answer(&result, "l");
    assert_eq!(f(view, "status"), &Json::str("established"));
    assert!(!obj(view).contains_key("claim"));
    assert_eq!(
        payload(target(&nodes, f(f(view, "outputs"), "value"), "Bool")),
        &Json::Bool(false)
    );
    assert_eq!(f(law, "status"), &Json::str("refuted"));
    let reached = reachable(
        &nodes,
        &[f(law, "outputs"), f(law, "claim"), f(law, "evidence")],
    );
    assert!(
        reached
            .iter()
            .map(|id| nodes[id.as_str()])
            .any(|n| f(n, "type") == &Json::str("Evidence")
                && f(payload(n), "kind") == &Json::str("counterexample"))
    );
    audit_dag(&result);
}

#[test]
fn true_guard_preserves_true_false_and_missing_raw_body() {
    guarded_case(
        Some(true),
        Some(true),
        "established",
        "applicable",
        Some(true),
    );
    guarded_case(
        Some(true),
        Some(false),
        "refuted",
        "applicable",
        Some(false),
    );
    guarded_case(Some(true), None, "undetermined", "applicable", None);
}

#[test]
fn false_guard_is_not_applicable_and_keeps_raw_body_without_substitution() {
    for body in [Some(true), Some(false), None] {
        guarded_case(
            Some(false),
            body,
            "established",
            "not_applicable",
            Some(true),
        );
    }
}

#[test]
fn missing_guard_with_false_body_is_undetermined() {
    guarded_case(None, Some(false), "undetermined", "undetermined", None);
}

#[test]
fn missing_guard_with_true_body_is_established_for_all_completions() {
    guarded_case(None, Some(true), "established", "undetermined", Some(true));
}

#[test]
fn missing_guard_and_body_keep_both_slot_identities_and_source_dependencies() {
    guarded_case(None, None, "undetermined", "undetermined", None);
}

fn stop_between_guard_body_and_law_completion(
    expression_offset: usize,
    limits: Limits,
    stopped_usage: Usage,
) {
    let prefix = "seed=evaluate(Inspect.value,item=@current/root)";
    let prefix_count = Rc::new(Cell::new(0));
    let seen = prefix_count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(fixture(None, Some(true)), &[prefix], &mut baseline)
        .unwrap()
        .wire();
    assert_eq!(f(&prior, "status"), &Json::str("complete"));
    let stop_at = prefix_count.get() + expression_offset;
    let expressions = Rc::new(Cell::new(0));
    let calls = Rc::new(Cell::new(0));
    let stopped_calls = Rc::new(Cell::new(None));
    let (seen, probes, frozen) = (expressions.clone(), calls.clone(), stopped_calls.clone());
    let mut control = Control::new(limits, move |point| {
        probes.set(probes.get() + 1);
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
            if seen.get() == stop_at {
                frozen.set(Some(probes.get()));
                return stopped_usage;
            }
        }
        Usage::default()
    });
    let result = evaluate_observed_bytes(
        fixture(None, Some(true)),
        &[
            prefix,
            "g=check(Inspect.guarded,item=@current/root)",
            "later=check(Inspect.raw,item=@current/root)",
        ],
        &mut control,
    )
    .unwrap()
    .wire();
    assert_eq!(f(&result, "status"), &Json::str("interrupted"));
    assert_eq!(expressions.get(), stop_at);
    assert_eq!(Some(calls.get()), stopped_calls.get());
    let nodes = index(&result);
    let prior = answer(&result, "seed");
    assert_eq!(f(prior, "status"), &Json::str("established"));
    assert_eq!(
        payload(target(&nodes, f(f(prior, "outputs"), "value"), "Bool")),
        &Json::Bool(true)
    );
    let stop = control.stop_reason().unwrap().wire();
    for id in ["g", "later"] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert!(
            obj(f(a, "outputs")).is_empty(),
            "未完成の条件付きLawへraw bodyを回答として昇格しない"
        );
        assert!(!obj(a).contains_key("claim"));
        let reason = arr(f(a, "reasons"))
            .iter()
            .find(|r| f(r, "code") == f(&stop, "code"))
            .unwrap();
        assert_eq!(f(reason, "details"), f(&stop, "details"));
    }
    let g = answer(&result, "g");
    assert_eq!(f(f(g, "scope"), "domain"), &Json::str("all_completions"));
    let missing = arr(f(g, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    assert_eq!(
        f(missing, "missing"),
        &Json::Arr(vec![Json::obj([
            ("snapshot", Json::str("current")),
            ("subject", Json::str("root")),
            ("field", Json::str("Signal.Cell.gate")),
        ])])
    );
    assert!(!arr(f(missing, "dependencies")).is_empty());
    for dependency in arr(f(missing, "dependencies")) {
        target(&nodes, dependency, "Expression");
    }
    assert!(
        nodes
            .values()
            .all(|n| f(n, "type") != &Json::str("Proposition")
                && f(n, "type") != &Json::str("Evidence")),
        "Law判断の導出を停止後に追加しない"
    );
    let before = calls.get();
    assert!(control.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(calls.get(), before);
    audit_dag(&result);
}

#[test]
fn cancellation_after_guard_evaluation_preserves_prior_view_and_pending_law() {
    // guardの式処理前後を終え、bodyの式処理を始める前で停止する。
    stop_between_guard_body_and_law_completion(
        2,
        Limits::default(),
        Usage {
            signal: Some(Signal::Term),
            ..Usage::default()
        },
    );
}

#[test]
fn time_stop_after_raw_body_preserves_prior_view_without_promoting_raw_truth() {
    // guard/bodyの二つの原式を終え、条件付きの適用評価を構成する前で停止する。
    stop_between_guard_body_and_law_completion(
        4,
        Limits {
            time_ms: Some(7),
            memory_mib: None,
        },
        Usage {
            elapsed_ms: 7,
            ..Usage::default()
        },
    );
}
