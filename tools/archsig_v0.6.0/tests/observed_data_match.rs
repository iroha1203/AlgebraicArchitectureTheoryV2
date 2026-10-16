//! AC4の非再帰Dataと既知値match。独立した三入力から元式・型・支持・停止prefixを読む。
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

fn data_type(name: &str) -> Json {
    Json::Arr(vec![Json::str("Data"), Json::str(format!("Cases.{name}"))])
}
fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}
fn q() -> Json {
    Json::Arr(vec![Json::str("-2"), Json::str("3")])
}
fn numeric_tuple() -> Json {
    Json::Arr(vec![Json::str("3"), q(), Json::str("4")])
}
fn full() -> Json {
    data(
        "Full",
        vec![
            Json::str("3"),
            q(),
            Json::str("4"),
            numeric_tuple(),
            Json::Bool(false),
            Json::Arr(vec![Json::str("v"), Json::str("sample")]),
        ],
    )
}
fn fixture(omitted: &[&str], script: &str) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let packet = data_json(
        "Cases.Packet",
        &format!(
            "[{},{}]",
            constructor_json("Empty", "[]"),
            constructor_json(
                "Full",
                r#"["Z","Q",["Fp","5"],["Tuple","Z","Q",["Fp","5"]],"Bool",["Ref","Cases.Sample"]]"#
            )
        ),
    );
    let boxed = data_json(
        "Cases.Boxed",
        &format!(
            "[{}]",
            constructor_json("Wrap", r#"[["Data","Cases.Packet"]]"#)
        ),
    );
    let other = data_json(
        "Cases.Other",
        &format!("[{}]", constructor_json("Empty", "[]")),
    );
    let fields = [
        ("z", r#""Z""#),
        ("q", r#""Q""#),
        ("f", r#"["Fp","5"]"#),
        ("t", r#"["Tuple","Z","Q",["Fp","5"]]"#),
        ("p", r#""Bool""#),
        ("packet", r#"["Data","Cases.Packet"]"#),
        ("missing", r#""Z""#),
    ]
    .into_iter()
    .map(|(n, t)| field_json(n, t))
    .collect::<Vec<_>>()
    .join(",");
    let entity = entity_json("Cases.Sample", "[]", &format!("[{fields}]"));
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "Cases",
            &format!("[{packet},{boxed},{other},{entity}]"),
            "[]"
        )
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Cases"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Cases {{ use vocabulary Cases version "1" digest "{digest}"; }}
reading Calc {{ use vocabulary Cases version "1" digest "{digest}"; use Cases as C; {script} }}"#
    );
    // ArchMapは計算の回答を含めず、独立したfieldの観測だけを持つ。
    let packet_wire =
        r#"{"tag":"Full","args":["3",["-2","3"],"4",["3",["-2","3"],"4"],false,["v","sample"]]}"#;
    let mut atoms = [("z", r#""3""#), ("q", r#"["-2","3"]"#), ("f", r#""4""#),
        ("t", r#"["3",["-2","3"],"4"]"#), ("p", "false"), ("packet", packet_wire)]
        .into_iter().filter(|(n,_)| !omitted.contains(n)).map(|(n,v)| format!(r#"{{"id":"{n}","subject":"sample","field":"Cases.Sample.{n}","value":{v},"origin":"values"}}"#)).collect::<Vec<_>>();
    atoms.push(r#"{"id":"empty","subject":"empty","field":"Cases.Sample.packet","value":{"tag":"Empty","args":[]},"origin":"values"}"#.into());
    let atoms = atoms.join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Cases","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:data-match","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"specification","method":"対象の提示","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
      {{"id":"values","mode":"specification","method":"fieldの観測","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Cases.Sample","origin":"base"}},{{"id":"empty","type":"Cases.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
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
                "urn:fixture:data-match"
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
        assert_eq!(f(m, "field"), &Json::str(format!("Cases.Sample.{field}")));
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

#[test]
fn nonrecursive_data_constructors_preserve_payload_types_and_origins() {
    let script = r#"
 view observed(s: Sample): Packet = s.packet;
 view short(): Packet = Empty;
 view qualified(): Packet = Cases.Packet.Empty;
 view zero(): Packet = Packet.Empty();
 view alias(): Packet = C.Packet.Empty;
 view construct(s: Sample): Packet = Full(s.z,s.q,s.f,s.t,s.p,s);
 view nested(s: Sample): Boxed = Boxed.Wrap(Full(s.z,s.q,s.f,s.t,s.p,s));
 view echo(x: Packet): Packet = x;
 view connected(s: Sample): Packet = let held=Packet.Full(s.z,s.q,s.f,s.t,s.p,s) in if s.p then Empty else echo(held);
 view other(): Other = Other.Empty;
"#;
    let (wire, checked) = run(
        fixture(&[], script),
        &[
            "o=evaluate(Calc.observed,s=@v/sample)",
            "s=evaluate(Calc.short)",
            "q=evaluate(Calc.qualified)",
            "zero=evaluate(Calc.zero)",
            "a=evaluate(Calc.alias)",
            "c=evaluate(Calc.construct,s=@v/sample)",
            "n=evaluate(Calc.nested,s=@v/sample)",
            "v=evaluate(Calc.connected,s=@v/sample)",
            "t=evaluate(Calc.other)",
        ],
    );
    assert_eq!(
        f(&wire, "status"),
        &Json::str("complete"),
        "issues: {:?}",
        f(&wire, "issues")
    );
    for id in ["o", "c", "v"] {
        output(&wire, id, &data_type("Packet"), full());
    }
    for id in ["s", "q", "a", "zero"] {
        output(&wire, id, &data_type("Packet"), data("Empty", vec![]));
    }
    output(&wire, "n", &data_type("Boxed"), data("Wrap", vec![full()]));
    output(&wire, "t", &data_type("Other"), data("Empty", vec![]));
    let ns = index(&wire);
    let c = root(&wire, "c");
    let body = declared_body(&checked, "Calc.construct");
    let ExprKind::Call { args, .. } = &checked.law().exprs[body].kind else {
        panic!("constructor")
    };
    let children = arr(f(part(c), "children"));
    assert_eq!(children.len(), 6);
    let types = [
        Json::str("Z"),
        Json::str("Q"),
        Json::Arr(vec![Json::str("Fp"), Json::str("5")]),
        Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Z"),
            Json::str("Q"),
            Json::Arr(vec![Json::str("Fp"), Json::str("5")]),
        ]),
        Json::str("Bool"),
        Json::Arr(vec![Json::str("Ref"), Json::str("Cases.Sample")]),
    ];
    for (i, child) in children.iter().enumerate() {
        let e = target(&ns, child, &Json::str("Evaluation"));
        assert_eq!(evaluation_span(&ns, e), checked.law().exprs[args[i]].span);
        assert_eq!(
            val(target(&ns, f(val(e), "value"), &types[i])),
            &arr(f(&full(), "args"))[i]
        );
    }
    let observed = target(
        &ns,
        f(f(answer(&wire, "o"), "outputs"), "value"),
        &data_type("Packet"),
    );
    assert_eq!(f(f(observed, "rule"), "kind"), &Json::str("atom"));
    assert!(
        arr(f(observed, "support"))
            .iter()
            .any(|fact| obj(fact).get("field") == Some(&Json::str("Cases.Sample.packet")))
    );
    let cvalue = target(&ns, f(val(c), "value"), &data_type("Packet"));
    assert_eq!(f(f(cvalue, "rule"), "kind"), &Json::str("law"));
    assert_eq!(
        span(f(f(cvalue, "rule"), "location")),
        checked.law().exprs[body].span
    );
    let scope = f(answer(&wire, "c"), "scope");
    assert_eq!(f(cvalue, "scope"), scope);
    assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Calc")]));
    assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
    assert_eq!(
        f(scope, "modes"),
        &Json::Arr(vec![Json::str("specification")])
    );
    assert_eq!(f(scope, "domain"), &Json::str("finite_model"));
    assert!(arr(f(scope, "assumptions")).is_empty());
    let bindings = arr(f(val(c), "bindings"));
    assert_eq!(bindings.len(), 1);
    assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
    assert_eq!(
        val(target(&ns, f(&bindings[0], "value"), &types[5])),
        &Json::Arr(vec![Json::str("v"), Json::str("sample")])
    );

    assert_ne!(
        f(cvalue, "id"),
        f(observed, "id"),
        "同じ値でも観測と別producerを共有しない"
    );
    let declaration = &checked.law().definitions.declarations["Cases.Packet"];
    let archsig::definition::PrimitiveSignature::Data { constructors } = &declaration.signature
    else {
        panic!("data定義")
    };
    assert_eq!(constructors[1].name, "Full");
    for (location, suffix) in [
        (&declaration.location, "/declarations/0"),
        (&constructors[1].location, "/declarations/0/constructors/1"),
    ] {
        let archsig::issue::Location::Definition { input, pointer, .. } = location else {
            panic!("定義元Location")
        };
        assert_eq!(input, "definition0");
        assert_eq!(pointer, &format!("/vocabularies/0{suffix}"));
    }
    let metadata = checked.metadata_wire();
    for key in ["inputs", "declarations", "vocabularies"] {
        assert_eq!(f(&wire, key), f(&metadata, key));
    }
}

#[test]
fn known_data_patterns_preserve_lexical_bindings_and_selected_children() {
    let script = r#"
 view read(s: Sample): Z = match s.packet { Empty => 0; Packet.Full(n,_,_,_,_,_) => n+1; };
 view nested(s: Sample): Z = match Boxed.Wrap(s.packet) { Wrap(Full(n,_,_,_,_,_)) => n; _ => 19; };
 view wildcard(s: Sample): Z = match s.packet { _ => s.z; };
 view named(s: Sample): Packet = match s.packet { whole => whole; };
 view plain(s: Sample): Z = match s.z { number => number+1; };
 view boolean(s: Sample): Z = match s.p { _ => s.z; };
 view repeated(s: Sample): Z = read(s)+read(s);
 view rational(s: Sample): Q = match s.packet { Full(_,r,_,_,_,_) => r; _ => rat(0,1); };
 view residue(s: Sample): Fp(5) = match s.packet { Full(_,_,r,_,_,_) => r; _ => 0; };
 view tupled(s: Sample): (Z,Q,Fp(5)) = match s.packet { Full(_,_,_,r,_,_) => r; _ => (0,rat(0,1),0); };
 view flagged(s: Sample): Bool = match s.packet { Full(_,_,_,_,r,_) => r; _ => true; };
 view referenced(s: Sample): Sample = match s.packet { Full(_,_,_,_,_,r) => r; _ => s; };
"#;
    let (wire, checked) = run(
        fixture(&[], script),
        &[
            "f=evaluate(Calc.read,s=@v/sample)",
            "e=evaluate(Calc.read,s=@v/empty)",
            "n=evaluate(Calc.nested,s=@v/sample)",
            "w=evaluate(Calc.wildcard,s=@v/sample)",
            "b=evaluate(Calc.named,s=@v/sample)",
            "p=evaluate(Calc.plain,s=@v/sample)",
            "t=evaluate(Calc.boolean,s=@v/sample)",
            "r=evaluate(Calc.repeated,s=@v/sample)",
            "q=evaluate(Calc.rational,s=@v/sample)",
            "a=evaluate(Calc.residue,s=@v/sample)",
            "c=evaluate(Calc.tupled,s=@v/sample)",
            "d=evaluate(Calc.flagged,s=@v/sample)",
            "h=evaluate(Calc.referenced,s=@v/sample)",
        ],
    );
    for (id, n) in [
        ("f", "4"),
        ("e", "0"),
        ("n", "3"),
        ("w", "3"),
        ("p", "4"),
        ("t", "3"),
        ("r", "8"),
    ] {
        output(&wire, id, &Json::str("Z"), Json::str(n));
    }
    output(&wire, "b", &data_type("Packet"), full());
    let payload_types = [
        Json::str("Q"),
        Json::Arr(vec![Json::str("Fp"), Json::str("5")]),
        Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Z"),
            Json::str("Q"),
            Json::Arr(vec![Json::str("Fp"), Json::str("5")]),
        ]),
        Json::str("Bool"),
        Json::Arr(vec![Json::str("Ref"), Json::str("Cases.Sample")]),
    ];
    for ((id, ty), expected) in ["q", "a", "c", "d", "h"]
        .into_iter()
        .zip(&payload_types)
        .zip([
            q(),
            Json::str("4"),
            numeric_tuple(),
            Json::Bool(false),
            Json::Arr(vec![Json::str("v"), Json::str("sample")]),
        ])
    {
        output(&wire, id, ty, expected);
        let ns = index(&wire);
        let e = root(&wire, id);
        let cs = arr(f(part(e), "children"));
        let binding = target(&ns, &cs[1], &Json::str("Evaluation"));
        assert_eq!(source(&checked, evaluation_span(&ns, binding)), b"r");
        assert_eq!(
            f(part(binding), "children"),
            &Json::Arr(vec![cs[0].clone()])
        );
        let bound = arr(f(val(binding), "bindings"));
        assert!(
            bound.iter().all(|b| f(b, "name") != &Json::str("r")),
            "pattern由来は元scrutineeへ接続し外部Bindingに捏造しない"
        );
    }

    let ns = index(&wire);
    let body = declared_body(&checked, "Calc.read");
    let ExprKind::Match { scrutinee, arms } = &checked.law().exprs[body].kind else {
        panic!("match")
    };
    let mut match_ids = BTreeSet::new();
    for (id, selected) in [("f", 1), ("e", 0)] {
        let e = root(&wire, id);
        let cs = arr(f(part(e), "children"));
        assert_eq!(cs.len(), 2);
        assert!(match_ids.insert(text(f(&cs[0], "node"))));
        assert_eq!(
            evaluation_span(&ns, target(&ns, &cs[0], &Json::str("Evaluation"))),
            checked.law().exprs[*scrutinee].span
        );
        assert_eq!(
            evaluation_span(&ns, target(&ns, &cs[1], &Json::str("Evaluation"))),
            checked.law().exprs[arms[selected].body].span
        );
        let reach = reached(&ns, &[&cs[1]]);
        let other = checked.law().exprs[arms[1 - selected].body].span;
        assert!(
            !reach
                .iter()
                .map(|id| ns[id.as_str()])
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == other)
        );
        for n in reach
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        {
            if source(&checked, evaluation_span(&ns, n)) == b"n" {
                assert_eq!(f(part(n), "children"), &Json::Arr(vec![cs[0].clone()]));
                let projected = target(&ns, f(val(n), "value"), &Json::str("Z"));
                assert_eq!(val(projected), &Json::str("3"));
                assert_eq!(
                    span(f(f(projected, "rule"), "location")),
                    evaluation_span(&ns, n)
                );
            }
        }
    }
    // whole matchの元Sourceは未選択pattern/bodyも含む。値を与えないarmを実評価しない。
    for (arm, (pattern_bytes, body_bytes)) in arms.iter().zip([
        (b"Empty".as_slice(), b"0".as_slice()),
        (b"Packet.Full(n,_,_,_,_,_)".as_slice(), b"n+1".as_slice()),
    ]) {
        let whole = evaluation_span(&ns, root(&wire, "f"));
        let at = checked.law().exprs[arm.body].span;
        let pattern = arm.pattern.span();
        assert!(whole.0 <= pattern.0 && pattern.1 <= at.0 && at.1 <= whole.1);
        assert_eq!(source(&checked, pattern), pattern_bytes);
        assert_eq!(source(&checked, at), body_bytes);
    }
    let repeated = root(&wire, "r");
    let reach = reached(&ns, &[f(part(repeated), "children")]);
    let selected: Vec<_> = reach
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == checked.law().exprs[body].span
        })
        .collect();
    assert_eq!(selected.len(), 2, "同じ元ASTでも別callのmatchを共有しない");
    assert_ne!(
        f(part(selected[0]), "children"),
        f(part(selected[1]), "children")
    );
}

#[test]
fn unknown_data_and_selected_missing_remain_original_slots() {
    let script = r#"
 view direct(s: Sample): Packet = s.packet;
 view unknown(s: Sample): Z = match s.packet { Empty => 0; Full(n,_,_,_,_,_) => n; };
 view selected(s: Sample): Z = match s.packet { Empty => 7; Full(_,_,_,_,_,_) => s.missing; };
 view unselected(s: Sample): Z = match s.packet { Empty => s.missing; Full(n,_,_,_,_,_) => n; };
"#;
    let (wire, checked) = run(
        fixture(&["packet"], script),
        &[
            "d=evaluate(Calc.direct,s=@v/sample)",
            "u=evaluate(Calc.unknown,s=@v/sample)",
        ],
    );
    for id in ["d", "u"] {
        assert_missing(&wire, id, "packet", &checked);
    }
    let ns = index(&wire);
    let u = root(&wire, "u");
    assert_eq!(
        arr(f(part(u), "children")).len(),
        1,
        "未知tagからarmを選ばない"
    );
    let reach = reached(&ns, &[f(val(u), "expression"), f(part(u), "children")]);
    for n in reach
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| f(n, "type") == &Json::str("Expression"))
    {
        assert!(
            arr(f(val(n), "bindings"))
                .iter()
                .all(|b| f(b, "name") != &Json::str("n")),
            "未知payloadからbinderを捏造しない"
        );
    }
    let (known, checked) = run(
        fixture(&[], script),
        &[
            "s=evaluate(Calc.selected,s=@v/sample)",
            "u=evaluate(Calc.unselected,s=@v/sample)",
        ],
    );
    assert_missing(&known, "s", "missing", &checked);
    let a = output(&known, "u", &Json::str("Z"), Json::str("3"));
    assert!(
        arr(f(a, "reasons")).is_empty(),
        "未選択armのmissingを通常値の依存にしない"
    );
    let ns = index(&known);
    let u = root(&known, "u");
    let body = declared_body(&checked, "Calc.unselected");
    let ExprKind::Match { arms, .. } = &checked.law().exprs[body].kind else {
        panic!("match")
    };
    let reach = reached(&ns, &[f(part(u), "children")]);
    assert!(
        !reach
            .iter()
            .map(|id| ns[id.as_str()])
            .any(|n| f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == checked.law().exprs[arms[0].body].span)
    );
}

#[test]
fn data_structural_equality_and_law_guards_keep_bool_judgments() {
    let script = r#"
 view equal(s: Sample): Bool = s.packet=Full(s.z,s.q,s.f,s.t,s.p,s);
 view tagdiff(s: Sample): Bool = s.packet!=Empty;
 view order(s: Sample): Bool = s.packet!=Full(s.z+1,s.q,s.f,s.t,s.p,s);
 view same(): Bool = Packet.Empty=Packet.Empty;
 view equal_false(s: Sample): Bool = s.packet=Empty;
 view unequal_false(s: Sample): Bool = s.packet!=Full(s.z,s.q,s.f,s.t,s.p,s);
 law required valid(s: Sample) when match s.packet { Empty => false; Full(_,_,_,_,_,_) => true; }: s.packet=Full(s.z,s.q,s.f,s.t,s.p,s);
 law required false_case(s: Sample): s.packet=Empty;
"#;
    let (wire, _) = run(
        fixture(&[], script),
        &[
            "e=evaluate(Calc.equal,s=@v/sample)",
            "t=evaluate(Calc.tagdiff,s=@v/sample)",
            "o=evaluate(Calc.order,s=@v/sample)",
            "s=evaluate(Calc.same)",
            "ef=evaluate(Calc.equal_false,s=@v/sample)",
            "uf=evaluate(Calc.unequal_false,s=@v/sample)",
            "v=check(Calc.valid,s=@v/sample)",
            "f=check(Calc.false_case,s=@v/sample)",
        ],
    );
    for id in ["e", "t", "o", "s"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    for id in ["ef", "uf"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(false));
    }
    let ns = index(&wire);
    for (id, status) in [("v", "established"), ("f", "refuted")] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str(status));
        let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
        assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
        let reach = reached(&ns, &[f(a, "outputs"), f(a, "evidence")]);
        for n in reach
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        {
            for p in arr(f(val(n), "parts")) {
                assert!(
                    !obj(p).contains_key("residual"),
                    "Dataの等値は数値残差でない"
                );
            }
        }
    }
}

#[test]
fn invalid_data_and_patterns_are_rejected_from_original_bytes() {
    let good = "view v(s: Sample): Z = match s.packet { Empty => 0; Full(n,_,_,_,_,_) => n; };";
    let (wire, _) = run(fixture(&[], good), &["x=evaluate(Calc.v,s=@v/sample)"]);
    output(&wire, "x", &Json::str("Z"), Json::str("3"));
    for (script, code) in [
        ("view v(s: Sample): Packet = Packet.Unknown;", "reference"),
        (
            "view v(s: Sample): Bool = Packet.Empty=Other.Empty;",
            "type",
        ),
        ("view v(s: Sample): Packet = Full(s.z);", "syntax"),
        (
            "view v(s: Sample): Packet = Full(s.p,s.q,s.f,s.t,s.p,s);",
            "type",
        ),
        (
            "view v(s: Sample): Z = match s.packet { Empty => 0; Empty => 1; _ => 2; };",
            "syntax",
        ),
        (
            "view v(s: Sample): Z = match s.packet { Empty => 0; };",
            "syntax",
        ),
        (
            "view v(s: Sample): Z = match s.packet { _ => 0; Empty => 1; };",
            "syntax",
        ),
        (
            "view v(s: Sample): Z = match s.packet { Empty => false; Full(_,_,_,_,_,_) => s.z; };",
            "type",
        ),
    ] {
        let inputs = fixture(&[], script);
        let law = inputs.law().bytes().to_vec();
        let err =
            evaluate_observed_bytes(inputs, &["x=evaluate(Calc.v,s=@v/sample)"], &mut quiet())
                .unwrap_err();
        let wire = err.wire().expect("静的不正はinvalid");
        assert_eq!(f(&wire, "status"), &Json::str("invalid"), "{script}");
        let issue = &arr(f(&wire, "issues"))[0];
        assert_eq!(f(issue, "code"), &Json::str(code), "{script}: {issue:?}");
        let at = span(f(issue, "location"));
        assert!(at.0 < at.1 && at.1 <= law.len());
        assert!(script.contains(std::str::from_utf8(&law[at.0..at.1]).unwrap()));
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&wire, key)).is_empty());
        }
    }
}

#[test]
fn injected_stops_keep_constructor_and_match_prefixes() {
    let script = r#"
 view seed(s: Sample): Z = s.z;
 view missing(s: Sample): Z = s.missing;
 view ctor(s: Sample): Packet = Full(s.z,s.q,s.f,s.t,s.p,s);
 view selected(s: Sample): Z = match s.packet { Empty => 0; Full(n,_,_,_,_,_) => n+1; };
 view later(s: Sample): Z = s.z+9;
"#;
    let inputs = fixture(&[], script);
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let prior_asks = [
        "seed=evaluate(Calc.seed,s=@v/sample)",
        "missing=evaluate(Calc.missing,s=@v/sample)",
    ];
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(inputs.clone(), &prior_asks, &mut baseline)
        .unwrap()
        .wire();
    output(&prior, "seed", &Json::str("Z"), Json::str("3"));
    assert_missing(&prior, "missing", "missing", &checked);
    // eval前後のExpression checkpointだけを数える。4は最初のconstructor引数完了後、
    // matchの4は選択body開始前、7は選択bodyのbinder完了後・literal開始前。
    for (ask, offset, kind, done_text) in [
        (
            "current=evaluate(Calc.ctor,s=@v/sample)",
            4,
            0,
            b"s.z".as_slice(),
        ),
        (
            "current=evaluate(Calc.selected,s=@v/sample)",
            4,
            1,
            b"s.packet".as_slice(),
        ),
        (
            "current=evaluate(Calc.selected,s=@v/sample)",
            7,
            2,
            b"n".as_slice(),
        ),
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
        let asks = [
            prior_asks[0],
            prior_asks[1],
            ask,
            "later=evaluate(Calc.later,s=@v/sample)",
        ];
        let wire = evaluate_observed_bytes(inputs.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        output(&wire, "seed", &Json::str("Z"), Json::str("3"));
        for key in ["status", "reasons", "scope", "outputs"] {
            assert_eq!(
                f(answer(&wire, "missing"), key),
                f(answer(&prior, "missing"), key)
            );
        }
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(obj(f(a, "outputs")).is_empty());
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
        let name = if kind == 0 {
            "Calc.ctor"
        } else {
            "Calc.selected"
        };
        let original = declared_body(&checked, name);
        let done_id = match &checked.law().exprs[original].kind {
            ExprKind::Call { args, .. } if kind == 0 => args[0],
            ExprKind::Match { scrutinee, .. } if kind == 1 => *scrutinee,
            ExprKind::Match { arms, .. } if kind == 2 => {
                let ExprKind::Binary { lhs, .. } = &checked.law().exprs[arms[1].body].kind else {
                    panic!("選択arm加算")
                };
                *lhs
            }
            _ => panic!("元停止箇所"),
        };
        let done_span = checked.law().exprs[done_id].span;
        assert_eq!(source(&checked, done_span), done_text);
        let complete = arr(f(&wire, "nodes"))
            .iter()
            .find(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == done_span
            })
            .unwrap();
        let expected_type = if kind == 1 {
            data_type("Packet")
        } else {
            Json::str("Z")
        };
        let expected_value = if kind == 1 { full() } else { Json::str("3") };
        assert_eq!(
            val(target(&ns, f(val(complete), "value"), &expected_type)),
            &expected_value
        );
        let original_span = checked.law().exprs[original].span;
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == original_span),
            "未完成親を完成Evaluationへ昇格しない"
        );
        let later_span = checked.law().exprs[declared_body(&checked, "Calc.later")].span;
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && evaluation_span(&ns, n) == later_span),
            "未着手の問いを評価しない"
        );
        assert_eq!(expressions.get(), at);
        assert_eq!(
            Some(probes.get()),
            frozen.get(),
            "停止後にprobeを再開しない"
        );
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before);
    }
}
