#[path = "common/identity_paths.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::check_inputs,
    },
};
use std::collections::BTreeMap;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn object(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(fields) = j else {
        panic!("object {j:?}")
    };
    fields
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(items) = j else {
        panic!("array {j:?}")
    };
    items
}
fn text(j: &Json) -> &str {
    let Json::Str(s) = j else {
        panic!("text {j:?}")
    };
    s
}
fn f<'a>(j: &'a Json, field: &str) -> &'a Json {
    &object(j)[field]
}
fn node<'a>(j: &'a Json, r: &Json, ty: &Json) -> &'a Json {
    assert_eq!(object(r).len(), 1);
    let id = text(f(r, "node"));
    let n = array(f(j, "nodes"))
        .iter()
        .find(|n| f(n, "id") == &Json::str(id))
        .unwrap();
    assert_eq!(f(n, "state"), &Json::str("value"));
    assert_eq!(f(n, "type"), ty);
    n
}
fn output<'a>(j: &'a Json, id: &str, ty: &Json) -> &'a Json {
    let answer = array(f(j, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap();
    assert_eq!(f(answer, "status"), &Json::str("established"));
    node(j, f(f(answer, "outputs"), "value"), ty)
}
fn path() -> Json {
    Json::Arr(vec![
        Json::str("Path"),
        Json::str("Paths.Node"),
        Json::str("Paths.Node"),
    ])
}
fn unary(kind: &str, ty: Json) -> Json {
    Json::Arr(vec![Json::str(kind), ty])
}
fn reference() -> Json {
    unary("Ref", Json::str("Paths.Node"))
}
fn assert_identity(j: &Json, n: &Json, snapshot: &str, subject: &str) {
    let payload = f(n, "value");
    assert_eq!(object(payload).len(), 4);
    assert_eq!(f(payload, "reading"), &Json::str("Walk"));
    assert_eq!(f(payload, "generators"), &Json::Arr(vec![]));
    for endpoint in ["source", "target"] {
        assert_eq!(
            f(node(j, f(payload, endpoint), &reference()), "value"),
            &Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
        );
    }
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
            out.push(text(&fields["node"]).into())
        }
        Json::Obj(fields) => {
            for value in fields.values() {
                refs(value, out)
            }
        }
        Json::Arr(items) => {
            for value in items {
                refs(value, out)
            }
        }
        _ => {}
    }
}
fn run(moved: bool, asks: &[&str]) -> Json {
    let inputs = fixture::input(moved);
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("input {:?}", e.issues()));
    let result = evaluate_observed_bytes(inputs.clone(), asks, &mut quiet()).unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.wire());
    assert_eq!(result.prepared().inputs().sources(), &inputs);
    assert_eq!(
        result.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots
    );
    let source = &result.prepared().inputs().archmap().sources[0];
    assert_eq!(
        source.uri,
        if moved {
            "urn:fixture:paths-moved"
        } else {
            "urn:fixture:paths"
        }
    );
    assert_eq!(source.revision, if moved { "r2" } else { "r1" });
    let origin = &result.prepared().inputs().archmap().origins[0];
    assert_eq!(origin.locations[0].source, source.id);
    assert_eq!(
        origin.locations[0].span,
        Some(if moved { (10, 11) } else { (0, 1) })
    );
    let wire = result.wire();
    for (index, n) in array(f(&wire, "nodes")).iter().enumerate() {
        assert_eq!(f(n, "id"), &Json::str(format!("n{index}")));
        let mut found = Vec::new();
        refs(n, &mut found);
        for r in found {
            assert!(
                r.strip_prefix('n').unwrap().parse::<usize>().unwrap() < index,
                "forward {r}"
            );
        }
        assert!(!matches!(f(n,"type"),Json::Str(name) if name=="Operation" || name=="Atom"));
    }
    wire
}

#[test]
fn identity_path_retains_reading_empty_word_and_snapshot_endpoints() {
    let j = run(
        false,
        &[
            "a=evaluate(Walk.id,x=@v/a)",
            "b=evaluate(Walk.id,x=@v/b)",
            "w=evaluate(Walk.id,x=@w/a)",
            "s=evaluate(Walk.start,x=@v/a)",
            "t=evaluate(Walk.end,x=@w/a)",
        ],
    );
    for (id, snapshot, subject) in [("a", "v", "a"), ("b", "v", "b"), ("w", "w", "a")] {
        let n = output(&j, id, &path());
        assert_identity(&j, n, snapshot, subject);
        assert!(
            array(f(n, "support"))
                .iter()
                .any(|fact| f(fact, "snapshot") == &Json::str(snapshot)
                    && f(fact, "subject") == &Json::str(subject))
        );
    }
    for (id, snapshot) in [("s", "v"), ("t", "w")] {
        assert_eq!(
            f(output(&j, id, &reference()), "value"),
            &Json::Arr(vec![Json::str(snapshot), Json::str("a")])
        );
    }
}

#[test]
fn nonprimitive_nested_containers_use_prior_typed_refs_and_preserve_primitives() {
    let j = run(
        false,
        &[
            "o=evaluate(Walk.maybe_value,x=@v/a)",
            "n=evaluate(Walk.nested,x=@v/b)",
            "a=evaluate(Walk.absent)",
            "e=evaluate(Walk.empty)",
            "p=evaluate(Walk.primitive)",
        ],
    );
    let o = output(&j, "o", &unary("Option", path()));
    assert_identity(&j, node(&j, f(f(o, "value"), "some"), &path()), "v", "a");
    let option = unary("Option", path());
    let tuple = Json::Arr(vec![Json::str("Tuple"), Json::str("Bool"), option.clone()]);
    let list = unary("List", tuple.clone());
    let n = output(&j, "n", &unary("Option", list.clone()));
    let l = node(&j, f(f(n, "value"), "some"), &list);
    let rows = array(f(l, "value"));
    assert_eq!(rows.len(), 2);
    for (index, row) in rows.iter().enumerate() {
        let t = node(&j, row, &tuple);
        let parts = array(f(t, "value"));
        assert_eq!(parts.len(), 2);
        assert_eq!(
            f(node(&j, &parts[0], &Json::str("Bool")), "value"),
            &Json::Bool(index == 0)
        );
        let o = node(&j, &parts[1], &option);
        if index == 0 {
            assert_identity(&j, node(&j, f(f(o, "value"), "some"), &path()), "v", "b")
        } else {
            assert_eq!(f(o, "value"), &Json::obj([("none", Json::Bool(true))]))
        }
    }
    assert_eq!(
        f(output(&j, "a", &option), "value"),
        &Json::obj([("none", Json::Bool(true))])
    );
    assert_eq!(
        f(output(&j, "e", &unary("List", path())), "value"),
        &Json::Arr(vec![])
    );
    let ptype = unary(
        "Option",
        unary(
            "List",
            Json::Arr(vec![Json::str("Tuple"), Json::str("Bool"), Json::str("Z")]),
        ),
    );
    assert_eq!(
        f(output(&j, "p", &ptype), "value"),
        &Json::obj([(
            "some",
            Json::Arr(vec![
                Json::Arr(vec![Json::Bool(false), Json::str("2")]),
                Json::Arr(vec![Json::Bool(true), Json::str("1")])
            ])
        )])
    );
}

#[test]
fn lexical_identity_and_current_provenance_preserve_the_same_math() {
    let asks = ["value=evaluate(Walk.lexical,x=@v/a)"];
    let a = run(false, &asks);
    let b = run(true, &asks);
    let inputs = fixture::input(false);
    for j in [&a, &b] {
        let n = output(j, "value", &path());
        assert_identity(j, n, "v", "a");
        assert_eq!(array(f(n, "support")).len(), 1);
        let expressions: Vec<_> = array(f(j, "nodes"))
            .iter()
            .filter(|n| f(n, "type") == &Json::str("Expression"))
            .collect();
        assert!(expressions.len() >= 5);
        assert!(expressions.iter().any(|n| {
            let payload = f(n, "value");
            if f(payload, "kind") != &Json::str("source") {
                return false;
            }
            let span = array(f(f(payload, "location"), "span"));
            let (Json::Nat(start), Json::Nat(end)) = (&span[0], &span[1]) else {
                panic!()
            };
            &inputs.law().bytes()[*start as usize..*end as usize] == b"p"
                && array(f(payload, "bindings"))
                    .iter()
                    .any(|binding| f(binding, "name") == &Json::str("x"))
        }));
    }
    assert_ne!(f(&a, "inputs"), f(&b, "inputs"));
    assert_eq!(
        f(output(&a, "value", &path()), "scope"),
        f(output(&b, "value", &path()), "scope")
    );
}

#[test]
fn identity_math_equality_uses_endpoints_and_identity_action_across_readings() {
    let inputs = fixture::cross_reading();
    let r = evaluate_observed_bytes(
        inputs.clone(),
        &[
            "same=evaluate(Other.mixed,x=@v/a,y=@v/a)",
            "subject=evaluate(Other.mixed,x=@v/a,y=@v/b)",
            "snapshot=evaluate(Other.mixed,x=@v/a,y=@w/a)",
            "nested=evaluate(Other.nested,x=@v/a,y=@v/a)",
            "different=evaluate(Other.different_term,x=@v/a)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(r.prepared().inputs().sources(), &inputs);
    let j = r.wire();
    for (id, expected) in [
        ("same", true),
        ("subject", false),
        ("snapshot", false),
        ("nested", true),
        ("different", false),
    ] {
        let n = output(&j, id, &Json::str("Bool"));
        assert_eq!(f(n, "value"), &Json::Bool(expected), "{id}");
        let readings = array(f(f(n, "scope"), "readings"));
        for reading in ["Walk", "Other"] {
            assert!(readings.contains(&Json::str(reading)), "{id} {reading}");
        }
    }
    let readings: std::collections::BTreeSet<_> = array(f(&j, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &path())
        .map(|n| text(f(f(n, "value"), "reading")))
        .collect();
    assert_eq!(
        readings,
        std::collections::BTreeSet::from(["Other", "Walk"])
    );
}

#[test]
fn direct_identity_comparisons_and_membership_keep_result_types_and_law_judgments() {
    let inputs = fixture::cross_reading();
    let mut asks = Vec::new();
    let mut expected = Vec::new();
    for view in [
        "equal_path",
        "unequal_path",
        "equal_option",
        "equal_list",
        "equal_tuple",
        "member_path",
    ] {
        for (suffix, target, same) in [
            ("same", "v/a", true),
            ("subject", "v/b", false),
            ("snapshot", "w/a", false),
        ] {
            let id = format!("{view}_{suffix}");
            asks.push(format!("{id}=evaluate(Other.{view},x=@v/a,y=@{target})"));
            expected.push((id, if view == "unequal_path" { !same } else { same }));
        }
    }
    asks.extend([
        "empty=evaluate(Other.equal_absent)".into(),
        "lawgood=check(Other.direct_law,x=@v/a,y=@v/a)".into(),
        "lawbad=check(Other.direct_law,x=@v/a,y=@v/b)".into(),
    ]);
    expected.push(("empty".into(), true));
    let request_text = asks.iter().map(String::as_str).collect::<Vec<_>>();
    let r = evaluate_observed_bytes(inputs.clone(), &request_text, &mut quiet()).unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(r.prepared().inputs().sources(), &inputs);
    let j = r.wire();
    assert_eq!(array(f(&j, "answers")).len(), asks.len());
    for (id, value) in expected {
        let n = output(&j, &id, &Json::str("Bool"));
        assert_eq!(f(n, "value"), &Json::Bool(value), "{id}");
    }
    for (id, status) in [("lawgood", "established"), ("lawbad", "refuted")] {
        let a = array(f(&j, "answers"))
            .iter()
            .find(|a| f(a, "id") == &Json::str(id))
            .unwrap();
        assert_eq!(f(a, "status"), &Json::str(status));
        let claim = node(&j, f(a, "claim"), &Json::str("Proposition"));
        assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
        if status == "refuted" {
            let proof = array(f(f(claim, "judgment"), "evidence"))
                .iter()
                .map(|r| node(&j, r, &Json::str("Evidence")))
                .find(|p| object(f(p, "value")).get("kind") == Some(&Json::str("counterexample")))
                .unwrap();
            let data = f(f(proof, "value"), "data");
            assert!(!array(f(data, "facts")).is_empty());
            for (side, reading, subject) in [("left", "Walk", "a"), ("right", "Other", "b")] {
                let p = node(&j, f(data, side), &path());
                let value = f(p, "value");
                assert_eq!(f(value, "reading"), &Json::str(reading));
                assert!(array(f(value, "generators")).is_empty());
                for endpoint in ["source", "target"] {
                    assert_eq!(
                        f(node(&j, f(value, endpoint), &reference()), "value"),
                        &Json::Arr(vec![Json::str("v"), Json::str(subject)])
                    );
                }
            }
        }
    }
    for (index, n) in array(f(&j, "nodes")).iter().enumerate() {
        let mut found = Vec::new();
        refs(n, &mut found);
        assert!(
            found
                .iter()
                .all(|r| r.strip_prefix('n').unwrap().parse::<usize>().unwrap() < index)
        );
    }
}
