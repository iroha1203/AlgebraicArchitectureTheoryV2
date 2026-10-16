//! 既知List/Set上の内包を独立三入力から評価し、元式・依存・支持・停止prefixを確認する。
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
                "urn:fixture:comprehensions"
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
            &Json::str(format!("Comprehensions.Sample.{field}"))
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
fn numbers(values: &[&str]) -> Json {
    Json::Arr(values.iter().map(|v| Json::str(*v)).collect())
}
fn reference(subject: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(subject)])
}
fn fixture(script: &str) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let fields = [
        ("nums", r#"["List","Z"]"#),
        ("setnums", r#"["Set","Z"]"#),
        ("empty", r#"["List","Q"]"#),
        ("refs", r#"["List",["Ref","Comprehensions.Sample"]]"#),
        ("zero", r#""Z""#),
        ("prime", r#"["Fp","5"]"#),
        ("missing", r#""Z""#),
        ("missinglist", r#"["List","Z"]"#),
        ("flag", r#""Bool""#),
    ]
    .into_iter()
    .map(|(n, t)| field_json(n, t))
    .collect::<Vec<_>>()
    .join(",");
    let entity = entity_json("Comprehensions.Sample", "[]", &format!("[{fields}]"));
    let packet = data_json(
        "Comprehensions.Packet",
        &format!("[{}]", constructor_json("Full", r#"["Z"]"#)),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Comprehensions", &format!("[{entity},{packet}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Comprehensions"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{ use vocabulary Comprehensions version "1" digest "{digest}"; {script} }}"#
    );
    // 独立した観測は原始fieldだけを持ち、内包の結果や判定を持たない。
    let values = [
        ("nums", numbers(&["2", "1", "2"])),
        ("setnums", numbers(&["2", "1"])),
        ("empty", Json::Arr(vec![])),
        (
            "refs",
            Json::Arr(vec![reference("sample"), reference("peer")]),
        ),
        ("zero", Json::str("0")),
        ("prime", Json::str("4")),
    ];
    let mut atoms = values.into_iter().map(|(name,value)| format!(r#"{{"id":"{name}","subject":"sample","field":"Comprehensions.Sample.{name}","value":{},"origin":"values"}}"#,value.canonical())).collect::<Vec<_>>();
    atoms.push(r#"{"id":"peerzero","subject":"peer","field":"Comprehensions.Sample.zero","value":"4","origin":"values"}"#.into());
    let atoms = atoms.join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
"vocabularies":[{{"namespace":"Comprehensions","version":"1","digest":"{digest}"}}],
"sources":[{{"id":"scan","uri":"urn:fixture:comprehensions","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
"origins":[{{"id":"base","mode":"specification","method":"対象を提示する。","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
{{"id":"values","mode":"specification","method":"fieldの観測。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Comprehensions.Sample","origin":"base"}},{{"id":"peer","type":"Comprehensions.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn output_set(wire: &Json, id: &str, item_type: Json, expected: &[Json]) {
    let a = answer(wire, id);
    assert_eq!(
        f(a, "status"),
        &Json::str("established"),
        "{id}: {:?}",
        f(a, "reasons")
    );
    assert!(!obj(a).contains_key("claim"));
    let ns = index(wire);
    let value = val(target(
        &ns,
        f(f(a, "outputs"), "value"),
        &ty("Set", item_type.clone()),
    ));
    let key = |v: &Json| {
        if let Json::Arr(t) = &item_type
            && t.first() == Some(&Json::str("Set"))
        {
            let mut members = arr(v).iter().map(Json::canonical).collect::<Vec<_>>();
            members.sort();
            format!("{members:?}")
        } else {
            v.canonical()
        }
    };
    let mut actual = arr(value).iter().map(key).collect::<Vec<_>>();
    let mut wanted = expected.iter().map(key).collect::<Vec<_>>();
    actual.sort();
    wanted.sort();
    assert_eq!(actual, wanted, "Setの表示順を意味上の差にしない: {id}");
}

#[test]
fn set_comprehension_lexical_calls_nested_and_ref_fields() {
    let script = r#"
view step(x: Z): Z = let held=x+1 in if x>1 then held else 0;
view called(s: Sample): (Set<Z>,Z) = (set { step(x) | x in s.nums where if x>0 then true else false },step(9));
view nested(): Set<Set<Z>> = set { set { x+y | y in list<Z>[1,2] } | x in list<Z>[1,2] };
view restore(x: Sample): (Set<Z>,Sample) = (set { step(y) | y in list<Z>[1,2] },x);
view ref_read(s: Sample): Set<Z> = set { r.zero | r in s.refs };
view ref_keep(s: Sample): Set<Sample> = set { r | r in s.refs };
"#;
    let asks = [
        "a=evaluate(Calc.called,s=@v/sample)",
        "b=evaluate(Calc.nested)",
        "c=evaluate(Calc.restore,x=@v/sample)",
        "d=evaluate(Calc.restore,x=@v/peer)",
        "e=evaluate(Calc.ref_read,s=@v/sample)",
        "f=evaluate(Calc.ref_keep,s=@v/sample)",
        "g=evaluate(Calc.called,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let ns = index(&wire);
    let pair_type = Json::Arr(vec![
        Json::str("Tuple"),
        ty("Set", Json::str("Z")),
        Json::str("Z"),
    ]);
    for id in ["a", "g", "c", "d"] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str("established"));
        assert!(!obj(a).contains_key("claim"));
        let expected_type = if id == "a" || id == "g" {
            pair_type.clone()
        } else {
            Json::Arr(vec![
                Json::str("Tuple"),
                ty("Set", Json::str("Z")),
                ty("Ref", Json::str("Comprehensions.Sample")),
            ])
        };
        let pair = arr(val(target(
            &ns,
            f(f(a, "outputs"), "value"),
            &expected_type,
        )));
        let mut members = arr(&pair[0]).iter().map(|n| text(n)).collect::<Vec<_>>();
        members.sort();
        assert_eq!(members, vec!["0", "3"]);
        let last = match id {
            "a" | "g" => Json::str("10"),
            "c" => reference("sample"),
            _ => reference("peer"),
        };
        assert_eq!(pair[1], last, "終了後に元parameter/call環境へ戻る");
    }
    output_set(
        &wire,
        "b",
        ty("Set", Json::str("Z")),
        &[numbers(&["2", "3"]), numbers(&["3", "4"])],
    );
    output_set(
        &wire,
        "e",
        Json::str("Z"),
        &[Json::str("0"), Json::str("4")],
    );
    output_set(
        &wire,
        "f",
        ty("Ref", Json::str("Comprehensions.Sample")),
        &[reference("sample"), reference("peer")],
    );
    assert_ne!(
        f(root(&wire, "a"), "id"),
        f(root(&wire, "g"), "id"),
        "別Requestの元式評価を保つ"
    );
    for (id, n) in [("c", "sample"), ("d", "peer")] {
        let bs = arr(f(val(root(&wire, id)), "bindings"));
        assert_eq!(bs.len(), 1);
        assert_eq!(f(&bs[0], "name"), &Json::str("x"));
        assert_eq!(
            val(target(
                &ns,
                f(&bs[0], "value"),
                &ty("Ref", Json::str("Comprehensions.Sample"))
            )),
            &reference(n)
        );
    }
    let called = declared_body(&checked, "Calc.called");
    let ExprKind::Tuple(parts) = &checked.law().exprs[called].kind else {
        panic!("tuple")
    };
    let tail = evaluations_at(&wire, checked.law().exprs[parts[1]].span);
    assert_eq!(tail.len(), 2);
    for e in tail {
        assert_eq!(source(&checked, evaluation_span(&ns, e)), b"step(9)");
        assert_eq!(
            val(target(&ns, f(val(e), "value"), &Json::str("Z"))),
            &Json::str("10")
        );
        assert_eq!(
            arr(f(val(e), "bindings"))
                .iter()
                .map(|b| text(f(b, "name")))
                .collect::<Vec<_>>(),
            vec!["s"]
        );
    }
    let body = declared_body(&checked, "Calc.ref_read");
    let ExprKind::SetComp { elem, domain, .. } = &checked.law().exprs[body].kind else {
        panic!("内包")
    };
    let ch = children(&ns, root(&wire, "e"));
    assert_eq!(ch.len(), 3);
    assert_eq!(
        evaluation_span(&ns, ch[0]),
        checked.law().exprs[*domain].span
    );
    for e in &ch[1..] {
        assert_eq!(evaluation_span(&ns, e), checked.law().exprs[*elem].span);
    }
    let fields = arr(f(root(&wire, "e"), "support"))
        .iter()
        .filter(|p| obj(p).get("field") == Some(&Json::str("Comprehensions.Sample.zero")))
        .map(|p| text(f(p, "subject")))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        fields,
        BTreeSet::from(["sample", "peer"]),
        "各Refの既存fieldと支持を読む"
    );
    for id in ["e", "f"] {
        assert_scope(&wire, id);
    }
}

#[test]
fn set_comprehension_missing_and_static_rejection_keep_original_slots() {
    let script = r#"
view excluded(s: Sample): Set<Z> = set { s.missing | x in list<Z>[1] where false };
view adopted(s: Sample): Set<Z> = set { s.missing | x in list<Z>[1] where true };
view unknown_domain(s: Sample): Set<Z> = set { x+1 | x in s.missinglist };
view unknown_filter(s: Sample): Set<Z> = set { x+1 | x in list<Z>[1] where s.flag };
view unknown_element(s: Sample): Set<Z> = set { x+s.missing | x in list<Z>[1] };
view prior(s: Sample): Z = s.zero;
"#;
    let asks = [
        "a=evaluate(Calc.excluded,s=@v/sample)",
        "b=evaluate(Calc.adopted,s=@v/sample)",
        "c=evaluate(Calc.unknown_domain,s=@v/sample)",
        "d=evaluate(Calc.unknown_filter,s=@v/sample)",
        "e=evaluate(Calc.unknown_element,s=@v/sample)",
        "f=evaluate(Calc.prior,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    output_set(&wire, "a", Json::str("Z"), &[]);
    output(&wire, "f", &Json::str("Z"), Json::str("0"));
    for (id, field) in [
        ("b", "missing"),
        ("c", "missinglist"),
        ("d", "flag"),
        ("e", "missing"),
    ] {
        assert_missing(&wire, id, field, &checked);
        assert!(!obj(val(root(&wire, id))).contains_key("value"));
        assert!(!obj(answer(&wire, id)).contains_key("claim"));
    }
    let ns = index(&wire);
    for (id, name, count) in [
        ("a", "Calc.excluded", 2),
        ("c", "Calc.unknown_domain", 1),
        ("d", "Calc.unknown_filter", 2),
    ] {
        let body = declared_body(&checked, name);
        let ExprKind::SetComp { elem, .. } = &checked.law().exprs[body].kind else {
            panic!("内包")
        };
        assert_eq!(children(&ns, root(&wire, id)).len(), count);
        assert!(
            evaluations_at(&wire, checked.law().exprs[*elem].span).is_empty(),
            "不要/未確定要素を値や欠測へ昇格しない: {id}"
        );
    }
    for bad in [
        "view bad(): Set<Z> = set { x | x in 1 };",
        "view bad(): Set<Z> = set { x | x in list<Z>[] where 1 };",
        "view bad(): Set<Z> = set { absent_name | x in list<Z>[] };",
        "view bad(): Set<Z> = set { true | x in list<Z>[] };",
        "view bad(): Set<Z> = if true then set<Z>{} else set { x | x in false };",
    ] {
        let input = fixture(&format!("view selected(): Z = 7; {bad}"));
        let law = input.law().bytes().to_vec();
        let failure = evaluate_observed_bytes(input, &["a=evaluate(Calc.selected)"], &mut quiet())
            .unwrap_err();
        let invalid = failure.wire().unwrap();
        assert_eq!(f(&invalid, "status"), &Json::str("invalid"), "{bad}");
        let issue = &arr(f(&invalid, "issues"))[0];
        assert!(
            ["type", "reference"].contains(&text(f(issue, "code"))),
            "{bad}: {issue:?}"
        );
        let at = span(f(issue, "location"));
        assert!(at.0 < at.1 && at.1 <= law.len());
        assert!(bad.contains(std::str::from_utf8(&law[at.0..at.1]).unwrap()));
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&invalid, key)).is_empty());
        }
    }
}
fn children<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Vec<&'a Json> {
    arr(f(part(evaluation), "children"))
        .iter()
        .map(|r| target(ns, r, &Json::str("Evaluation")))
        .collect()
}
fn evaluations_at<'a>(wire: &'a Json, at: (usize, usize)) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == at
        })
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
    assert!(arr(f(scope, "quantifiers")).is_empty());
    assert!(arr(f(scope, "assumptions")).is_empty());
    let ns = index(wire);
    assert_eq!(
        f(ns[text(f(f(f(a, "outputs"), "value"), "node"))], "scope"),
        scope
    );
}

#[test]
fn set_comprehension_types_occurrences_and_support() {
    let script = r#"
view filtered(s: Sample): Set<Z> = set { x+1 | x in s.nums where x>1 };
view plain(s: Sample): Set<Z> = set { x | x in s.nums };
view set_domain(s: Sample): Set<Z> = set { x+1 | x in s.setnums };
view empty_domain(s: Sample): Set<Q> = set { x+rat(1,2) | x in s.empty };
view kinds(s: Sample): Set<(Unit,Text,Bool,Z,Q,Fp(5),(Z,Bool),Option<Z>,List<Z>,Set<Z>,Packet,Sample)> = set { (unit,"alpha",false,x,rat(1,2),s.prime,(x,true),some(x),list<Z>[x,x],set<Z>{x},Packet.Full(x),s) | x in list<Z>[2] };
law required check_set(s: Sample): set { x+1 | x in s.nums where x>1 }=set<Z>{3};
"#;
    let asks = [
        "a=evaluate(Calc.filtered,s=@v/sample)",
        "b=evaluate(Calc.plain,s=@v/sample)",
        "c=evaluate(Calc.set_domain,s=@v/sample)",
        "d=evaluate(Calc.empty_domain,s=@v/sample)",
        "e=evaluate(Calc.kinds,s=@v/sample)",
        "f=check(Calc.check_set,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    output_set(&wire, "a", Json::str("Z"), &[Json::str("3")]);
    output_set(
        &wire,
        "b",
        Json::str("Z"),
        &[Json::str("1"), Json::str("2")],
    );
    output_set(
        &wire,
        "c",
        Json::str("Z"),
        &[Json::str("2"), Json::str("3")],
    );
    output_set(&wire, "d", Json::str("Q"), &[]);
    let tuple_type = Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Unit"),
        Json::str("Text"),
        Json::str("Bool"),
        Json::str("Z"),
        Json::str("Q"),
        ty("Fp", Json::str("5")),
        Json::Arr(vec![Json::str("Tuple"), Json::str("Z"), Json::str("Bool")]),
        ty("Option", Json::str("Z")),
        ty("List", Json::str("Z")),
        ty("Set", Json::str("Z")),
        ty("Data", Json::str("Comprehensions.Packet")),
        ty("Ref", Json::str("Comprehensions.Sample")),
    ]);
    let tuple = Json::Arr(vec![
        Json::Arr(vec![]),
        Json::str("alpha"),
        Json::Bool(false),
        Json::str("2"),
        numbers(&["1", "2"]),
        Json::str("4"),
        Json::Arr(vec![Json::str("2"), Json::Bool(true)]),
        Json::obj([("some", Json::str("2"))]),
        numbers(&["2", "2"]),
        numbers(&["2"]),
        Json::obj([("tag", Json::str("Full")), ("args", numbers(&["2"]))]),
        reference("sample"),
    ]);
    output_set(&wire, "e", tuple_type, &[tuple]);
    for id in ["a", "b", "c", "d", "e"] {
        assert_scope(&wire, id);
    }
    let ns = index(&wire);
    let claim = target(
        &ns,
        f(answer(&wire, "f"), "claim"),
        &Json::str("Proposition"),
    );
    assert_eq!(f(answer(&wire, "f"), "status"), &Json::str("established"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str("established"));
    let body = declared_body(&checked, "Calc.filtered");
    let ExprKind::SetComp {
        elem,
        domain,
        filter: Some(filter),
        ..
    } = &checked.law().exprs[body].kind
    else {
        panic!("内包")
    };
    let ch = children(&ns, root(&wire, "a"));
    assert_eq!(ch.len(), 6, "元domain + 全3filter + 採用2elem");
    assert_eq!(
        evaluation_span(&ns, ch[0]),
        checked.law().exprs[*domain].span
    );
    assert_eq!(
        val(target(
            &ns,
            f(val(ch[0]), "value"),
            &ty("List", Json::str("Z"))
        )),
        &numbers(&["2", "1", "2"])
    );
    let domain_ref = Json::obj([("node", f(ch[0], "id").clone())]);
    let filter_span = checked.law().exprs[*filter].span;
    let elem_span = checked.law().exprs[*elem].span;
    assert_eq!(
        ch.iter()
            .map(|e| evaluation_span(&ns, e))
            .collect::<Vec<_>>(),
        vec![
            checked.law().exprs[*domain].span,
            filter_span,
            elem_span,
            filter_span,
            filter_span,
            elem_span
        ]
    );
    for (e, truth) in [(ch[1], true), (ch[3], false), (ch[4], true)] {
        assert_eq!(
            val(target(&ns, f(val(e), "value"), &Json::str("Bool"))),
            &Json::Bool(truth)
        );
        assert!(
            reached(&ns, &[e]).contains(text(f(ch[0], "id"))),
            "各反復から元domainへ戻る"
        );
    }
    let reachable = reached(&ns, &[root(&wire, "a")]);
    let x_evals = arr(f(&wire, "nodes"))
        .iter()
        .filter(|e| {
            f(e, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, e).is_none()
                && reachable.contains(text(f(e, "id")))
                && source(&checked, evaluation_span(&ns, e)) == b"x"
        })
        .collect::<Vec<_>>();
    assert!(!x_evals.is_empty());
    for e in x_evals {
        assert!(
            arr(f(val(e), "bindings"))
                .iter()
                .all(|b| f(b, "name") != &Json::str("x")),
            "binderを自由parameterへ追加しない"
        );
        assert_eq!(arr(f(part(e), "children")), &[domain_ref.clone()]);
        let scalar = target(&ns, f(val(e), "value"), &Json::str("Z"));
        assert_eq!(arr(f(scalar, "arguments")), &[domain_ref.clone()]);
    }
    let result = target(
        &ns,
        f(f(answer(&wire, "a"), "outputs"), "value"),
        &ty("Set", Json::str("Z")),
    );
    assert!(
        arr(f(result, "support"))
            .iter()
            .any(|p| obj(p).get("field") == Some(&Json::str("Comprehensions.Sample.nums")))
    );
    let empty = declared_body(&checked, "Calc.empty_domain");
    let ExprKind::SetComp { elem, .. } = &checked.law().exprs[empty].kind else {
        panic!("内包")
    };
    assert!(
        evaluations_at(&wire, checked.law().exprs[*elem].span).is_empty(),
        "空域で要素を捏造しない"
    );
}

#[test]
fn set_comprehension_expression_stops_preserve_completed_prefixes() {
    let inputs = fixture(
        r#"
view seed(s: Sample): Z = s.zero;
view absent(s: Sample): Z = s.missing;
view current(s: Sample): Set<Z> = set { x | x in list<Z>[2,1] where x>1 };
view later(s: Sample): Z = s.zero+9;
"#,
    );
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/sample)",
        "absent=evaluate(Calc.absent,s=@v/sample)",
        "current=evaluate(Calc.current,s=@v/sample)",
        "later=evaluate(Calc.later,s=@v/sample)",
    ];
    let prior_count = Rc::new(Cell::new(0));
    let c = prior_count.clone();
    let mut prior_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(inputs.clone(), &asks[..2], &mut prior_control)
        .unwrap()
        .wire();
    output(&prior, "seed", &Json::str("Z"), Json::str("0"));
    assert_missing(&prior, "absent", "missing", &checked);
    let total_count = Rc::new(Cell::new(0));
    let c = total_count.clone();
    let mut baseline_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let baseline = evaluate_observed_bytes(inputs.clone(), &asks[..3], &mut baseline_control)
        .unwrap()
        .wire();
    audit(&baseline, &checked);
    output_set(&baseline, "current", Json::str("Z"), &[Json::str("2")]);
    assert_eq!(
        total_count.get() - prior_count.get(),
        22,
        "固定した元ASTのExpression pre/post"
    );
    let original = declared_body(&checked, "Calc.current");
    let ExprKind::SetComp {
        elem,
        domain,
        filter: Some(filter),
        ..
    } = &checked.law().exprs[original].kind
    else {
        panic!("内包")
    };
    let domain_span = checked.law().exprs[*domain].span;
    let filter_span = checked.law().exprs[*filter].span;
    let elem_span = checked.law().exprs[*elem].span;
    let ns = index(&baseline);
    let full = children(&ns, root(&baseline, "current"));
    assert_eq!(
        full.iter()
            .map(|e| evaluation_span(&ns, e))
            .collect::<Vec<_>>(),
        vec![domain_span, filter_span, elem_span, filter_span]
    );
    assert_eq!(source(&checked, domain_span), b"list<Z>[2,1]");
    assert_eq!(source(&checked, filter_span), b"x>1");
    assert_eq!(source(&checked, elem_span), b"x");
    // 公開Expressionの固定3箇所。実反復/Set構成loop内部への注入はprivate試験が担う。
    // +8: domain post後のfilter pre、+14: true filter post後のelem pre、+21: false filter post。
    for (offset, kind, filters, elements) in [(8, 0, 0, 0), (14, 1, 1, 0), (21, 2, 2, 1)] {
        let at = prior_count.get() + offset;
        let expressions = Rc::new(Cell::new(0));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (e, p, frozen_at) = (expressions.clone(), probes.clone(), frozen.clone());
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
                        frozen_at.set(Some(p.get()));
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
        let wire = evaluate_observed_bytes(inputs.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        audit(&wire, &checked);
        output(&wire, "seed", &Json::str("Z"), Json::str("0"));
        for key in ["status", "reasons", "scope", "outputs"] {
            assert_eq!(
                f(answer(&wire, "absent"), key),
                f(answer(&prior, "absent"), key)
            );
        }
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(obj(f(a, "outputs")).is_empty());
            let code = if kind == 0 {
                "cancelled"
            } else {
                "budget_exhausted"
            };
            let reason = arr(f(a, "reasons"))
                .iter()
                .find(|r| f(r, "code") == &Json::str(code))
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
        assert!(
            evaluations_at(&wire, checked.law().exprs[original].span).is_empty(),
            "未完成親を通常値へ昇格しない"
        );
        let domains = evaluations_at(&wire, domain_span);
        assert_eq!(domains.len(), 1);
        let ns = index(&wire);
        assert_eq!(
            val(target(
                &ns,
                f(val(domains[0]), "value"),
                &ty("List", Json::str("Z"))
            )),
            &numbers(&["2", "1"])
        );
        let fs = evaluations_at(&wire, filter_span);
        assert_eq!(fs.len(), filters);
        for (i, e) in fs.iter().enumerate() {
            assert_eq!(
                val(target(&ns, f(val(e), "value"), &Json::str("Bool"))),
                &Json::Bool(i == 0)
            );
        }
        let es = evaluations_at(&wire, elem_span);
        assert_eq!(es.len(), elements);
        for e in es {
            assert_eq!(
                val(target(&ns, f(val(e), "value"), &Json::str("Z"))),
                &Json::str("2")
            );
        }
        let later_span = checked.law().exprs[declared_body(&checked, "Calc.later")].span;
        assert!(
            evaluations_at(&wire, later_span).is_empty(),
            "未着手の問いを評価しない"
        );
        assert_eq!(expressions.get(), at);
        assert_eq!(Some(probes.get()), frozen.get());
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before, "停止後probeを再開しない");
    }
}
