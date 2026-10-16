//! AC4原始containerの小さい三入力fixture。型、原始encoding、全元子、支持と停止prefixを確認する。
mod common;
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::{ast::ExprKind, model::Signature},
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
fn quiet() -> Control {
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
fn val(j: &Json) -> &Json {
    assert_eq!(f(j, "state"), &Json::str("value"));
    f(j, "value")
}
fn index(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let node = ns[text(f(reference, "node"))];
    assert_eq!(f(node, "type"), ty);
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
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for value in m.values() {
                refs(value, out);
            }
        }
        Json::Arr(a) => {
            for value in a {
                refs(value, out);
            }
        }
        _ => {}
    }
}
fn reached(ns: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut todo = vec![];
    for root in roots {
        refs(root, &mut todo);
    }
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    seen
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
fn expression<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    target(
        ns,
        f(val(evaluation), "expression"),
        &Json::str("Expression"),
    )
}
fn evaluation_span(ns: &BTreeMap<&str, &Json>, evaluation: &Json) -> (usize, usize) {
    span(f(val(expression(ns, evaluation)), "location"))
}
// Law適用の集約は、通常の元式Evaluationと異なりLawInstanceを第一引数に持つ。
fn aggregate_instance<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Option<&'a Json> {
    let first = arr(f(evaluation, "arguments")).first()?;
    let node = ns[text(f(first, "node"))];
    (f(node, "type") == &Json::str("LawInstance")).then_some(node)
}
fn part(evaluation: &Json) -> &Json {
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    &parts[0]
}

fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("入力: {:?}", e.issues()));
    let wire = evaluate_observed_bytes(inputs, asks, &mut quiet())
        .unwrap_or_else(|e| panic!("評価: {e:?}"))
        .wire();
    audit(&wire, &checked);
    (wire, checked)
}
fn output<'a>(wire: &'a Json, id: &str, ty: &Json, expected: Json) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(
        f(a, "status"),
        &Json::str("established"),
        "{id}; issues: {:?}",
        f(wire, "issues")
    );
    assert!(
        !obj(a).contains_key("claim"),
        "Boolも値の問いはclaimを持たない"
    );
    assert_eq!(
        val(target(&index(wire), f(f(a, "outputs"), "value"), ty)),
        &expected,
        "{id}"
    );
    a
}
fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for n in arr(f(wire, "nodes")) {
        let mut links = vec![];
        refs(n, &mut links);
        for id in links {
            assert!(earlier.contains(id.as_str()), "既出Ref: {id}");
        }
        assert!(earlier.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut links = vec![];
            refs(v, &mut links);
            for id in links {
                assert_ne!(f(ns[id.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[id.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(n, "support")) {
            assert_eq!(f(fact, "snapshot"), &Json::str("v"));
            let subject = checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known {
                    atom,
                    origin,
                    pointer,
                    ..
                } = slot
                else {
                    panic!("欠測は支持Atomでない")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/0/atoms/"));
                origin
            } else {
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
            let at = &origin.locations[0];
            assert_eq!(
                at.path,
                if obj(fact).contains_key("field") {
                    "values.model"
                } else {
                    "subjects.model"
                }
            );
            assert_eq!(
                at.span,
                Some(if obj(fact).contains_key("field") {
                    (2, 5)
                } else {
                    (0, 1)
                })
            );
            assert_eq!(
                checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == at.source)
                    .unwrap()
                    .uri,
                "urn:fixture:containers"
            );
        }
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            assert!(arr(f(val(n), "parameters")).is_empty());
            let at = span(f(val(n), "location"));
            assert_eq!(span(f(f(n, "rule"), "location")), at);
            assert!(at.0 < at.1 && at.1 <= checked.sources().law().bytes().len());
        }
        if f(n, "type") == &Json::str("Evaluation") {
            if aggregate_instance(&ns, n).is_none() {
                assert_eq!(
                    f(val(expression(&ns, n)), "bindings"),
                    f(val(n), "bindings")
                );
                assert_eq!(span(f(part(n), "location")), evaluation_span(&ns, n));
            }
            for p in arr(f(val(n), "parts")) {
                for child in arr(f(p, "children")) {
                    for fact in arr(f(target(&ns, child, &Json::str("Evaluation")), "support")) {
                        assert!(arr(f(n, "support")).contains(fact));
                    }
                }
            }
        }
    }
    for a in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(a, &mut links);
        for id in links {
            assert!(ns.contains_key(id.as_str()));
        }
        assert!(arr(f(f(a, "scope"), "quantifiers")).is_empty());
    }
}
fn root<'a>(wire: &'a Json, id: &str) -> &'a Json {
    target(
        &index(wire),
        f(f(answer(wire, id), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    )
}
fn source<'a>(checked: &'a CheckedInputs, at: (usize, usize)) -> &'a [u8] {
    &checked.sources().law().bytes()[at.0..at.1]
}
fn declared_body(checked: &CheckedInputs, name: &str) -> usize {
    let Signature::View { body, .. } = &checked.law().declarations[name].signature else {
        panic!("view")
    };
    *body
}
fn assert_missing(wire: &Json, id: &str, field: &str, checked: &CheckedInputs) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(obj(f(a, "outputs")).get("value").is_none());
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
    let ns = index(wire);
    let reasons: Vec<_> = arr(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .collect();
    assert!(!reasons.is_empty());
    for r in reasons {
        assert_eq!(arr(f(r, "missing")).len(), 1);
        let m = &arr(f(r, "missing"))[0];
        assert_eq!(f(m, "snapshot"), &Json::str("v"));
        assert_eq!(f(m, "subject"), &Json::str("sample"));
        assert_eq!(
            f(m, "field"),
            &Json::str(format!("Containers.Sample.{field}"))
        );
        assert!(!obj(m).contains_key("atom"));
        assert!(!arr(f(r, "dependencies")).is_empty());
        for dep in arr(f(r, "dependencies")) {
            let at = span(f(
                val(target(&ns, dep, &Json::str("Expression"))),
                "location",
            ));
            assert_eq!(source(checked, at), format!("s.{field}").as_bytes());
        }
    }
}

fn ty(kind: &str, item: Json) -> Json {
    Json::Arr(vec![Json::str(kind), item])
}
fn fp() -> Json {
    ty("Fp", Json::str("5"))
}
fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}
fn numbers(values: &[&str]) -> Json {
    Json::Arr(values.iter().map(|v| Json::str(*v)).collect())
}
fn none() -> Json {
    Json::obj([("none", Json::Bool(true))])
}
fn some(v: Json) -> Json {
    Json::obj([("some", v)])
}
fn mixed_type() -> Json {
    Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Unit"),
        Json::str("Text"),
        Json::str("Bool"),
        ty("List", Json::str("Z")),
    ])
}
fn mixed() -> Json {
    Json::Arr(vec![
        Json::Arr(vec![]),
        Json::str("alpha"),
        Json::Bool(false),
        numbers(&["2", "1", "2"]),
    ])
}
fn nested_type() -> Json {
    ty("List", ty("Option", ty("Set", Json::str("Z"))))
}
fn nested() -> Json {
    Json::Arr(vec![none(), some(numbers(&["1", "2"]))])
}
fn data_type() -> Json {
    ty("Data", Json::str("Containers.Packet"))
}
fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}
fn packet() -> Json {
    data(
        "Full",
        vec![
            Json::Arr(vec![]),
            Json::str("alpha"),
            mixed(),
            nested(),
            some(numbers(&["2", "1", "2"])),
        ],
    )
}

fn fixture(script: &str) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let packet_definition = data_json(
        "Containers.Packet",
        &format!(
            "[{},{},{},{}]",
            constructor_json("Empty", "[]"),
            constructor_json(
                "Full",
                r#"["Unit","Text",["Tuple","Unit","Text","Bool",["List","Z"]],["List",["Option",["Set","Z"]]],["Option",["List","Z"]]]"#
            ),
            constructor_json("count", r#"[["List","Z"]]"#),
            constructor_json("sum", r#"[["Option","Unit"]]"#)
        ),
    );
    let fields = [
        ("u", r#""Unit""#),
        ("txt", r#""Text""#),
        ("mixed", r#"["Tuple","Unit","Text","Bool",["List","Z"]]"#),
        ("nested", r#"["List",["Option",["Set","Z"]]]"#),
        ("listnums", r#"["List","Z"]"#),
        ("setnums", r#"["Set","Z"]"#),
        ("maybe", r#"["Option",["List","Z"]]"#),
        ("no", r#"["Option","Z"]"#),
        ("empty", r#"["List","Q"]"#),
        ("zero", r#""Z""#),
        ("packet", r#"["Data","Containers.Packet"]"#),
        ("missing", r#""Z""#),
        ("missinglist", r#"["List","Z"]"#),
        ("missingoption", r#"["Option","Z"]"#),
    ]
    .into_iter()
    .map(|(n, t)| field_json(n, t))
    .collect::<Vec<_>>()
    .join(",");
    let entity = entity_json("Containers.Sample", "[]", &format!("[{fields}]"));
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "Containers",
            &format!("[{packet_definition},{entity}]"),
            "[]"
        )
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Containers"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{ use vocabulary Containers version "1" digest "{digest}"; {script} }}"#
    );
    // ArchMapは素値だけを観測する。問いの回答や生成containerは含めない。
    let fields = [
        ("u", Json::Arr(vec![])),
        ("txt", Json::str("alpha")),
        ("mixed", mixed()),
        ("nested", nested()),
        ("listnums", numbers(&["2", "1", "2"])),
        ("setnums", numbers(&["2", "1"])),
        ("maybe", some(numbers(&["2", "1", "2"]))),
        ("no", none()),
        ("empty", Json::Arr(vec![])),
        ("zero", Json::str("0")),
        ("packet", packet()),
    ];
    let atoms=fields.into_iter().map(|(name,value)|format!(r#"{{"id":"{name}","subject":"sample","field":"Containers.Sample.{name}","value":{},"origin":"values"}}"#,value.canonical())).collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Containers","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:containers","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"specification","method":"対象を提示する。","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
      {{"id":"values","mode":"specification","method":"fieldの観測。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Containers.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn children<'a>(wire: &'a Json, id: &str) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(part(root(wire, id)), "children"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evaluation")))
        .collect()
}
fn assert_scope(wire: &Json, id: &str) {
    let a = answer(wire, id);
    let scope = f(a, "scope");
    assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Calc")]));
    assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
    assert_eq!(
        f(scope, "modes"),
        &Json::Arr(vec![Json::str("specification")])
    );
    assert_eq!(f(scope, "domain"), &Json::str("finite_model"));
    assert!(arr(f(scope, "assumptions")).is_empty());
    let ns = index(wire);
    let value = ns[text(f(f(f(a, "outputs"), "value"), "node"))];
    assert_eq!(f(value, "scope"), scope);
}

#[test]
fn primitive_containers_preserve_wire_types_occurrences_and_origins() {
    let script = r#"
 view observed_unit(s: Sample): Unit = s.u;
 view observed_text(s: Sample): Text = s.txt;
 view literal_unit(): Unit = unit;
 view literal_text(): Text = "alpha";
 view observed_mixed(s: Sample): (Unit,Text,Bool,List<Z>) = s.mixed;
 view mixed(s: Sample): (Unit,Text,Bool,List<Z>) = (s.u,s.txt,false,list<Z>[2,1,2]);
 view text_part(s: Sample): Text = s.mixed.1;
 view list_part(s: Sample): List<Z> = (s.u,s.txt,false,s.listnums).3;
 view observed_nested(s: Sample): List<Option<Set<Z>>> = s.nested;
 view nested(): List<Option<Set<Z>>> = list<Option<Set<Z>>>[none<Set<Z>>,some(set<Z>{1,2})];
 view observed_packet(s: Sample): Packet = s.packet;
 view construct(s: Sample): Packet = Packet.Full(s.u,s.txt,s.mixed,s.nested,s.maybe);
 view echo(x: Packet): Packet = x;
 view connected(s: Sample): Packet = let held=Packet.Full(s.u,s.txt,s.mixed,s.nested,s.maybe) in if false then Packet.Empty else echo(held);
 view selected(s: Sample): List<Option<Set<Z>>> = match s.packet { Empty => list<Option<Set<Z>>>[]; Full(_,_,_,items,_) => items; count(_) => list<Option<Set<Z>>>[]; sum(_) => list<Option<Set<Z>>>[]; };
 view builtin_named_ctor(s: Sample): Packet = Containers.Packet.count(s.listnums);
 view other_builtin_named_ctor(): Packet = Packet.sum(some(unit));
 view short_ctor(): Packet = Empty;
 view unit_equal(s: Sample): Bool = s.u=unit;
 view text_unequal(s: Sample): Bool = s.txt!="beta";
 law required equality(s: Sample): s.mixed=(unit,"alpha",false,list<Z>[2,1,2]);
 law required false_equality(s: Sample): s.txt="beta";
"#;
    let asks = [
        "ou=evaluate(Calc.observed_unit,s=@v/sample)",
        "ot=evaluate(Calc.observed_text,s=@v/sample)",
        "lu=evaluate(Calc.literal_unit)",
        "lt=evaluate(Calc.literal_text)",
        "om=evaluate(Calc.observed_mixed,s=@v/sample)",
        "m=evaluate(Calc.mixed,s=@v/sample)",
        "tp=evaluate(Calc.text_part,s=@v/sample)",
        "lp=evaluate(Calc.list_part,s=@v/sample)",
        "on=evaluate(Calc.observed_nested,s=@v/sample)",
        "n=evaluate(Calc.nested)",
        "op=evaluate(Calc.observed_packet,s=@v/sample)",
        "c=evaluate(Calc.construct,s=@v/sample)",
        "v=evaluate(Calc.connected,s=@v/sample)",
        "selectedvalue=evaluate(Calc.selected,s=@v/sample)",
        "countctor=evaluate(Calc.builtin_named_ctor,s=@v/sample)",
        "sumctor=evaluate(Calc.other_builtin_named_ctor)",
        "short=evaluate(Calc.short_ctor)",
        "ue=evaluate(Calc.unit_equal,s=@v/sample)",
        "te=evaluate(Calc.text_unequal,s=@v/sample)",
        "validlaw=check(Calc.equality,s=@v/sample)",
        "falselaw=check(Calc.false_equality,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    for id in ["ou", "lu"] {
        output(&wire, id, &Json::str("Unit"), Json::Arr(vec![]));
    }
    for id in ["ot", "lt", "tp"] {
        output(&wire, id, &Json::str("Text"), Json::str("alpha"));
    }
    for id in ["om", "m"] {
        output(&wire, id, &mixed_type(), mixed());
    }
    output(
        &wire,
        "lp",
        &ty("List", Json::str("Z")),
        numbers(&["2", "1", "2"]),
    );
    for id in ["on", "n", "selectedvalue"] {
        output(&wire, id, &nested_type(), nested());
    }
    for id in ["op", "c", "v"] {
        output(&wire, id, &data_type(), packet());
    }
    output(
        &wire,
        "countctor",
        &data_type(),
        data("count", vec![numbers(&["2", "1", "2"])]),
    );
    output(
        &wire,
        "sumctor",
        &data_type(),
        data("sum", vec![some(Json::Arr(vec![]))]),
    );
    output(&wire, "short", &data_type(), data("Empty", vec![]));
    for id in ["ue", "te"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    let ns = index(&wire);
    for (id, status) in [("validlaw", "established"), ("falselaw", "refuted")] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str(status));
        let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
        assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
        for node in reached(&ns, &[f(a, "outputs"), f(a, "evidence")])
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        {
            for p in arr(f(val(node), "parts")) {
                assert!(
                    !obj(p).contains_key("residual"),
                    "混合Tuple/Textを数値残差にしない"
                );
            }
        }
        if status == "refuted" {
            assert!(!arr(f(claim, "evidence")).is_empty());
        }
    }
    // 同じ値でも元Atomと生成位置、viewの別callを保持する。
    let observed = target(
        &ns,
        f(f(answer(&wire, "op"), "outputs"), "value"),
        &data_type(),
    );
    let constructed = target(
        &ns,
        f(f(answer(&wire, "c"), "outputs"), "value"),
        &data_type(),
    );
    assert_eq!(f(f(observed, "rule"), "kind"), &Json::str("atom"));
    assert_eq!(f(f(constructed, "rule"), "kind"), &Json::str("law"));
    assert_ne!(f(observed, "id"), f(constructed, "id"));
    assert_eq!(
        span(f(f(constructed, "rule"), "location")),
        checked.law().exprs[declared_body(&checked, "Calc.construct")].span
    );
    for id in [
        "ou",
        "ot",
        "om",
        "m",
        "lp",
        "on",
        "op",
        "c",
        "v",
        "selectedvalue",
        "countctor",
    ] {
        assert_scope(&wire, id);
    }
    let body = declared_body(&checked, "Calc.construct");
    let ExprKind::Call { callee, args } = &checked.law().exprs[body].kind else {
        panic!("constructor call")
    };
    let ch = children(&wire, "c");
    assert_eq!(ch.len(), 5, "callee tokenへfake Evaluationを付けない");
    for (i, child) in ch.iter().enumerate() {
        assert_eq!(
            evaluation_span(&ns, child),
            checked.law().exprs[args[i]].span
        );
        assert!(
            arr(f(constructed, "support"))
                .iter()
                .any(|fact| obj(fact).get("field")
                    == Some(&Json::str(format!(
                        "Containers.Sample.{}",
                        ["u", "txt", "mixed", "nested", "maybe"][i]
                    ))))
        );
    }
    let callee_span = checked.law().exprs[*callee].span;
    assert!(
        !arr(f(&wire, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == callee_span)
    );
    let mixed_body = declared_body(&checked, "Calc.mixed");
    let ExprKind::Tuple(items) = &checked.law().exprs[mixed_body].kind else {
        panic!("mixed Tuple")
    };
    let ch = children(&wire, "m");
    assert_eq!(ch.len(), items.len());
    for (child, original) in ch.iter().zip(items) {
        assert_eq!(
            evaluation_span(&ns, child),
            checked.law().exprs[*original].span
        );
    }
    let archsig::definition::PrimitiveSignature::Data { constructors } =
        &checked.law().definitions.declarations["Containers.Packet"].signature
    else {
        panic!("Packet definition")
    };
    let archsig::issue::Location::Definition { input, pointer, .. } = &constructors[1].location
    else {
        panic!("constructor origin")
    };
    assert_eq!(input, "definition0");
    assert_eq!(pointer, "/vocabularies/0/declarations/0/constructors/1");
    let metadata = checked.metadata_wire();
    for key in ["inputs", "declarations", "vocabularies"] {
        assert_eq!(f(&wire, key), f(&metadata, key));
    }
}
fn output_set(wire: &Json, id: &str, item_type: Json, expected: &[Json]) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    let ns = index(wire);
    let value = val(target(
        &ns,
        f(f(a, "outputs"), "value"),
        &ty("Set", item_type),
    ));
    let mut actual = arr(value).iter().map(Json::canonical).collect::<Vec<_>>();
    let mut expected = expected.iter().map(Json::canonical).collect::<Vec<_>>();
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected, "Setの独立な表示順を固定しない");
}
#[test]
fn container_operations_keep_list_order_set_extensionality_and_typed_zero() {
    let script = r#"
 view list_value(): List<Z> = list<Z>[2,1,2];
 view set_value(): Set<Z> = set<Z>{2,1,2};
 view supported_set(s: Sample): Set<Z> = set<Z>{s.zero+2,1,count(s.setnums)};
 view list_count(): Z = count(list<Z>[2,1,2]);
 view list_sum(): Z = sum(list<Z>[2,1,2]);
 view set_count(): Z = count(set<Z>{2,1,2});
 view set_sum(): Z = sum(set<Z>{2,1,2});
 view extensional(): Bool = set<Z>{2,1,2}=set<Z>{1,2};
 view observed_extensional(s: Sample): Bool = s.setnums=set<Z>{1,2};
 view reordered_list(): Bool = list<Z>[2,1,2]=list<Z>[1,2,2];
 view unequal_list(): Bool = list<Z>[2,1,2]!=list<Z>[1,2,2];
 view list_member(): Bool = 1 in list<Z>[2,1,2];
 view set_member(): Bool = 2 in set<Z>{2,1,2};
 view absent_member(): Bool = 3 in set<Z>{2,1,2};
 view empty_member(): Bool = 0 in list<Z>[];
 view empty_count(): Z = count(set<Text>{});
 view option_tags(): Bool = none<Z>!=some(0);
 view some_equal(): Bool = some(list<Z>[2,1,2])=some(list<Z>[2,1,2]);
 view nested_set_count(): Z = count(set<Set<Z>>{set<Z>{2,1},set<Z>{1,2}});
 view q_sum(): Q = sum(list<Q>[rat(1,6),rat(1,3)]);
 view f_sum(): Fp(5) = sum(set<Fp(5)>{4,3});
 view tuple_sum(): (Z,Q,Fp(5)) = sum(list<(Z,Q,Fp(5))>[(1,rat(1,2),4),(2,rat(1,2),2)]);
 view z0(): Z = sum(list<Z>[]);
 view zs0(): Z = sum(set<Z>{});
 view q0(): Q = sum(list<Q>[]);
 view qs0(): Q = sum(set<Q>{});
 view f0(): Fp(5) = sum(list<Fp(5)>[]);
 view fs0(): Fp(5) = sum(set<Fp(5)>{});
 view t0(): (Z,Q,Fp(5)) = sum(list<(Z,Q,Fp(5))>[]);
 view ts0(): (Z,Q,Fp(5)) = sum(set<(Z,Q,Fp(5))>{});
"#;
    let names = [
        "list_value",
        "set_value",
        "list_count",
        "list_sum",
        "set_count",
        "set_sum",
        "extensional",
        "reordered_list",
        "unequal_list",
        "list_member",
        "set_member",
        "absent_member",
        "empty_member",
        "empty_count",
        "option_tags",
        "some_equal",
        "nested_set_count",
        "q_sum",
        "f_sum",
        "tuple_sum",
        "z0",
        "zs0",
        "q0",
        "qs0",
        "f0",
        "fs0",
        "t0",
        "ts0",
    ];
    let mut asks = names
        .iter()
        .map(|n| format!("{n}=evaluate(Calc.{n})"))
        .collect::<Vec<_>>();
    asks.push("supported=evaluate(Calc.supported_set,s=@v/sample)".into());
    asks.push("observed=evaluate(Calc.observed_extensional,s=@v/sample)".into());
    let (wire, checked) = run(
        fixture(script),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    output(
        &wire,
        "list_value",
        &ty("List", Json::str("Z")),
        numbers(&["2", "1", "2"]),
    );
    for id in ["set_value", "supported"] {
        output_set(&wire, id, Json::str("Z"), &[Json::str("1"), Json::str("2")]);
    }
    for (id, n) in [
        ("list_count", "3"),
        ("list_sum", "5"),
        ("set_count", "2"),
        ("set_sum", "3"),
        ("empty_count", "0"),
        ("nested_set_count", "1"),
        ("z0", "0"),
        ("zs0", "0"),
    ] {
        output(&wire, id, &Json::str("Z"), Json::str(n));
    }
    for id in [
        "extensional",
        "observed",
        "unequal_list",
        "list_member",
        "set_member",
        "option_tags",
        "some_equal",
    ] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    for id in ["reordered_list", "absent_member", "empty_member"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(false));
    }
    output(&wire, "q_sum", &Json::str("Q"), q("1", "2"));
    output(&wire, "f_sum", &fp(), Json::str("2"));
    let nt = Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Z"),
        Json::str("Q"),
        fp(),
    ]);
    output(
        &wire,
        "tuple_sum",
        &nt,
        Json::Arr(vec![Json::str("3"), q("1", "1"), Json::str("1")]),
    );
    for id in ["q0", "qs0"] {
        output(&wire, id, &Json::str("Q"), q("0", "1"));
    }
    for id in ["f0", "fs0"] {
        output(&wire, id, &fp(), Json::str("0"));
    }
    for id in ["t0", "ts0"] {
        output(
            &wire,
            id,
            &nt,
            Json::Arr(vec![Json::str("0"), q("0", "1"), Json::str("0")]),
        );
    }
    // Setの意味上の二要素と、元の三つの子Evaluationを別々に確認する。
    let ns = index(&wire);
    for (id, name) in [
        ("list_value", "Calc.list_value"),
        ("set_value", "Calc.set_value"),
        ("supported", "Calc.supported_set"),
    ] {
        let body = declared_body(&checked, name);
        let (ExprKind::ListLit { items, .. } | ExprKind::SetLit { items, .. }) =
            &checked.law().exprs[body].kind
        else {
            panic!("container literal")
        };
        let ch = children(&wire, id);
        assert_eq!(ch.len(), 3, "重複除去でも元子を落とさない");
        let mut ids = BTreeSet::new();
        for (i, (child, original)) in ch.iter().zip(items).enumerate() {
            assert!(ids.insert(text(f(child, "id"))));
            assert_eq!(
                evaluation_span(&ns, child),
                checked.law().exprs[*original].span
            );
            assert_eq!(
                val(target(&ns, f(val(child), "value"), &Json::str("Z"))),
                &Json::str(["2", "1", "2"][i])
            );
        }
    }
    let value = target(
        &ns,
        f(f(answer(&wire, "supported"), "outputs"), "value"),
        &ty("Set", Json::str("Z")),
    );
    for field in ["zero", "setnums"] {
        assert!(
            arr(f(value, "support"))
                .iter()
                .any(|fact| obj(fact).get("field")
                    == Some(&Json::str(format!("Containers.Sample.{field}"))))
        );
    }
    assert_scope(&wire, "supported");
}

#[test]
fn missing_container_slots_and_static_errors_keep_original_evidence() {
    let script = r#"
 view no(s: Sample): Option<Z> = s.no;
 view present(): Option<Z> = some(0);
 view empty(s: Sample): List<Q> = s.empty;
 view empty_set(): Set<Text> = set<Text>{};
 view zero(s: Sample): Z = s.zero;
 view absent(s: Sample): Z = s.missing;
 view absent_list(s: Sample): List<Z> = s.missinglist;
 view absent_option(s: Sample): Option<Z> = s.missingoption;
 view unknown_element(s: Sample): List<Z> = list<Z>[0,s.missing];
 view unknown_set_element(s: Sample): Set<Z> = set<Z>{0,s.missing};
 view unknown_some(s: Sample): Option<Z> = some(s.missing);
 view unknown_sum(s: Sample): Z = sum(s.missinglist);
 view unknown_count(s: Sample): Z = count(s.missinglist);
 view unknown_member(s: Sample): Bool = 0 in s.missinglist;
"#;
    let names = [
        "no",
        "empty",
        "zero",
        "absent",
        "absent_list",
        "absent_option",
        "unknown_element",
        "unknown_set_element",
        "unknown_some",
        "unknown_sum",
        "unknown_count",
        "unknown_member",
    ];
    let mut asks = names
        .iter()
        .map(|n| format!("{n}=evaluate(Calc.{n},s=@v/sample)"))
        .collect::<Vec<_>>();
    asks.push("presentvalue=evaluate(Calc.present)".into());
    asks.push("es=evaluate(Calc.empty_set)".into());
    let (wire, checked) = run(
        fixture(script),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    output(&wire, "no", &ty("Option", Json::str("Z")), none());
    output(
        &wire,
        "presentvalue",
        &ty("Option", Json::str("Z")),
        some(Json::str("0")),
    );
    output(
        &wire,
        "empty",
        &ty("List", Json::str("Q")),
        Json::Arr(vec![]),
    );
    output_set(&wire, "es", Json::str("Text"), &[]);
    output(&wire, "zero", &Json::str("Z"), Json::str("0"));
    for (id, field) in [
        ("absent", "missing"),
        ("absent_list", "missinglist"),
        ("absent_option", "missingoption"),
        ("unknown_element", "missing"),
        ("unknown_set_element", "missing"),
        ("unknown_some", "missing"),
        ("unknown_sum", "missinglist"),
        ("unknown_count", "missinglist"),
        ("unknown_member", "missinglist"),
    ] {
        assert_missing(&wire, id, field, &checked);
        let e = root(&wire, id);
        assert!(
            !obj(val(e)).contains_key("value"),
            "未知container/要素をnone/empty/zeroにしない"
        );
    }
    let ns = index(&wire);
    for id in ["unknown_element", "unknown_set_element"] {
        let ch = children(&wire, id);
        assert_eq!(ch.len(), 2);
        assert_eq!(
            val(target(&ns, f(val(ch[0]), "value"), &Json::str("Z"))),
            &Json::str("0")
        );
        assert!(!obj(val(ch[1])).contains_key("value"));
        assert_eq!(source(&checked, evaluation_span(&ns, ch[1])), b"s.missing");
    }
    // 未選択枝・未選択宣言も、要求解決前に全て静的検査する。
    for (bad, code) in [
        ("view bad(): Z = count(some(0));", "type"),
        ("view bad(): Z = sum(list<Text>[\"x\"]);", "type"),
        ("view bad(): Z = sum(list<(Z,Bool)>[(1,true)]);", "type"),
        ("view bad(): Bool = true in list<Z>[1];", "type"),
        ("view bad(): List<Z> = list<Z>[true];", "type"),
        ("view bad(): Z = if true then 0 else count(unit);", "type"),
        ("view bad(): (Z,Bool) = (1,true)+(2,false);", "type"),
        ("view bad(): Option<Z> = none<Text>;", "type"),
    ] {
        let input = fixture(&format!("view selected(): Z = 7; {bad}"));
        let law = input.law().bytes().to_vec();
        let failure = evaluate_observed_bytes(input, &["x=evaluate(Calc.selected)"], &mut quiet())
            .unwrap_err();
        let invalid = failure.wire().expect("静的不正はinvalid");
        assert_eq!(f(&invalid, "status"), &Json::str("invalid"), "{bad}");
        let issue = &arr(f(&invalid, "issues"))[0];
        assert_eq!(f(issue, "code"), &Json::str(code), "{bad}: {issue:?}");
        let at = span(f(issue, "location"));
        assert!(at.0 < at.1 && at.1 <= law.len());
        assert!(bad.contains(std::str::from_utf8(&law[at.0..at.1]).unwrap()));
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&invalid, key)).is_empty());
        }
    }
    // 観測Setの重複は構成のdedupとは別で、元ArchMap位置にて拒否する。
    let good = fixture("view known(s: Sample): Set<Z> = s.setnums;");
    let map = String::from_utf8(good.archmap().bytes().to_vec()).unwrap();
    let needle = r#""field":"Containers.Sample.setnums","value":["2","1"]"#;
    assert!(map.contains(needle));
    let duplicate = map.replace(
        needle,
        r#""field":"Containers.Sample.setnums","value":["2","1","2"]"#,
    );
    let bad = InputSources::from_bytes(
        good.definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        good.law().bytes().to_vec(),
        duplicate.into_bytes(),
    );
    let failure =
        evaluate_observed_bytes(bad, &["s=evaluate(Calc.known,s=@v/sample)"], &mut quiet())
            .unwrap_err();
    let invalid = failure.wire().unwrap();
    assert_eq!(f(&invalid, "status"), &Json::str("invalid"));
    let issue = &arr(f(&invalid, "issues"))[0];
    assert_eq!(f(f(issue, "location"), "input"), &Json::str("archmap"));
    assert!(text(f(f(issue, "location"), "pointer")).starts_with("/snapshots/0/atoms/"));
    for key in ["requests", "nodes", "answers"] {
        assert!(arr(f(&invalid, key)).is_empty());
    }
}
#[test]
fn container_expression_stops_keep_element_preconstruction_and_completed_sum_prefixes() {
    let script = r#"
 view seed(s: Sample): Z = s.zero;
 view missing(s: Sample): Z = s.missing;
 view elements(s: Sample): List<Z> = list<Z>[0,s.zero,2];
 view construct_set(s: Sample): Set<Z> = set<Z>{2,1,2};
 view total(s: Sample): Z = sum(list<Z>[2,1,2]);
 view later(s: Sample): Z = s.zero+9;
"#;
    let inputs = fixture(script);
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let prior_asks = [
        "seed=evaluate(Calc.seed,s=@v/sample)",
        "missing=evaluate(Calc.missing,s=@v/sample)",
    ];
    let count = Rc::new(Cell::new(0));
    let c = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(inputs.clone(), &prior_asks, &mut baseline)
        .unwrap()
        .wire();
    output(&prior, "seed", &Json::str("Z"), Json::str("0"));
    assert_missing(&prior, "missing", "missing", &checked);
    // Expressionの固定offsetだけを使う。Setループ/sumループ途中の実到達はprivate試験が担当する。
    // +4: 二つ目の要素開始、+7: Setの全literal完了後でSet構成前、+10: sum完成後。
    for (name, offset, kind, done_text) in [
        ("elements", 4, 0, b"0".as_slice()),
        ("construct_set", 7, 1, b"2".as_slice()),
        ("total", 10, 2, b"sum(list<Z>[2,1,2])".as_slice()),
    ] {
        let at = count.get() + offset;
        let expressions = Rc::new(Cell::new(0));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (e, p, s) = (expressions.clone(), probes.clone(), frozen.clone());
        let mut control = Control::new(
            Limits {
                time_ms: (kind == 1).then_some(1),
                memory_mib: (kind == 2).then_some(1),
            },
            move |point| {
                p.set(p.get() + 1);
                if point == Checkpoint::Expression {
                    e.set(e.get() + 1);
                    if e.get() == at {
                        s.set(Some(p.get()));
                        return Usage {
                            signal: (kind == 0).then_some(Signal::Term),
                            elapsed_ms: u128::from(kind == 1),
                            memory_mib: u128::from(kind == 2),
                        };
                    }
                }
                Usage::default()
            },
        );
        let current = format!("current=evaluate(Calc.{name},s=@v/sample)");
        let wire = evaluate_observed_bytes(
            inputs.clone(),
            &[
                prior_asks[0],
                prior_asks[1],
                &current,
                "later=evaluate(Calc.later,s=@v/sample)",
            ],
            &mut control,
        )
        .unwrap()
        .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        output(&wire, "seed", &Json::str("Z"), Json::str("0"));
        for key in ["status", "reasons", "scope", "outputs"] {
            assert_eq!(
                f(answer(&wire, "missing"), key),
                f(answer(&prior, "missing"), key)
            );
        }
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            if id == "later" || kind != 2 {
                assert!(obj(f(a, "outputs")).is_empty());
            }
            let reason = arr(f(a, "reasons"))
                .iter()
                .find(|r| {
                    f(r, "code")
                        == &Json::str(if kind == 0 {
                            "cancelled"
                        } else {
                            "budget_exhausted"
                        })
                })
                .unwrap();
            let details = if kind == 0 {
                Json::obj([("signal", Json::str("SIGTERM"))])
            } else {
                Json::obj([
                    (
                        "resource",
                        Json::str(if kind == 1 { "time_ms" } else { "memory_mib" }),
                    ),
                    ("limit", Json::str("1")),
                    ("observed", Json::str("1")),
                ])
            };
            assert_eq!(f(reason, "details"), &details);
        }
        audit(&wire, &checked);
        let ns = index(&wire);
        let original = declared_body(&checked, &format!("Calc.{name}"));
        let done_id = match &checked.law().exprs[original].kind {
            ExprKind::ListLit { items, .. } if kind == 0 => items[0],
            ExprKind::SetLit { items, .. } if kind == 1 => items[2],
            ExprKind::Call { .. } if kind == 2 => original,
            _ => panic!("固定した停止出現"),
        };
        let done_span = checked.law().exprs[done_id].span;
        assert_eq!(source(&checked, done_span), done_text);
        let done = arr(f(&wire, "nodes"))
            .iter()
            .find(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == done_span
            })
            .unwrap();
        assert_eq!(
            val(target(&ns, f(val(done), "value"), &Json::str("Z"))),
            &Json::str(if kind == 0 {
                "0"
            } else if kind == 1 {
                "2"
            } else {
                "5"
            })
        );
        if kind == 2 {
            assert_eq!(
                f(f(answer(&wire, "current"), "outputs"), "evaluation"),
                &Json::obj([("node", f(done, "id").clone())])
            );
            assert_eq!(
                val(target(
                    &ns,
                    f(f(answer(&wire, "current"), "outputs"), "value"),
                    &Json::str("Z")
                )),
                &Json::str("5")
            );
            let ch = arr(f(part(done), "children"));
            assert_eq!(ch.len(), 1, "sumは元containerだけを子として持つ");
            let list = target(&ns, &ch[0], &Json::str("Evaluation"));
            assert_eq!(
                val(target(
                    &ns,
                    f(val(list), "value"),
                    &ty("List", Json::str("Z"))
                )),
                &numbers(&["2", "1", "2"])
            );
        } else {
            let original_span = checked.law().exprs[original].span;
            assert!(
                !arr(f(&wire, "nodes"))
                    .iter()
                    .any(|n| f(n, "type") == &Json::str("Evaluation")
                        && aggregate_instance(&ns, n).is_none()
                        && evaluation_span(&ns, n) == original_span),
                "親Evaluation未完成prefixを通常値へ昇格しない"
            );
        }
        let later_span = checked.law().exprs[declared_body(&checked, "Calc.later")].span;
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == later_span)
        );
        assert_eq!(expressions.get(), at);
        assert_eq!(Some(probes.get()), frozen.get(), "停止後probeを再開しない");
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before);
    }
}
