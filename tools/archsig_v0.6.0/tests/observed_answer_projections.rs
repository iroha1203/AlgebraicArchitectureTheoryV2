#[path = "common/answer_projections.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!() };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else { panic!() };
    v
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn output<'a>(w: &'a Json, id: &str) -> &'a Json {
    node(w, f(f(answer(w, id), "outputs"), "value"))
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
#[test]
fn answer_projection_nested_components_keep_original_typed_roots_and_full_paths() {
    let asks = [
        "n=evaluate(Applications.abIdentity,x=$nested.evaluation.value[0].some[1][1])",
        "double=evaluate(Applications.abDouble,x=$packed.value[6][0])",
        "option=evaluate(Applications.abIdentity,x=$packed.value[8].some)",
        "reference=evaluate(Applications.abFree,p=$packed.evaluation.value[9])",
        "map=evaluate(Applications.apMap,f=$packed.value[10],p=@v/p)",
        "term=evaluate(Applications.apTerm,f=$packed.evaluation.value[11])",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
        "nested=evaluate(Applications.apNested)",
    ];
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    for (id, value) in [
        ("n", "4"),
        ("double", "4"),
        ("option", "0"),
        ("reference", "2"),
        ("term", "3"),
    ] {
        assert_eq!(f(output(&w, id), "value"), &Json::str(value));
    }
    assert_eq!(
        f(output(&w, "map"), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("r")])
    );
    let evaluation = node(&w, f(f(answer(&w, "n"), "outputs"), "evaluation"));
    let binding = &arr(f(f(evaluation, "value"), "bindings"))[0];
    let projected = node(&w, f(binding, "value"));
    assert_eq!(f(f(projected, "rule"), "name"), &Json::str("projection"));
    assert_eq!(
        f(f(projected, "rule"), "path"),
        &Json::Arr(vec![
            Json::str("value"),
            Json::Nat(0),
            Json::str("some"),
            Json::Nat(1),
            Json::Nat(1)
        ])
    );
    let root = f(f(answer(&w, "nested"), "outputs"), "evaluation");
    assert_eq!(f(projected, "arguments"), &Json::Arr(vec![root.clone()]));
    assert_eq!(f(projected, "scope"), f(node(&w, root), "scope"));
    assert_eq!(f(projected, "support"), f(node(&w, root), "support"));
}

#[test]
fn answer_projection_data_constructor_paths_feed_recursion_and_original_z_universal() {
    let asks = [
        "sub=evaluate(Trees.total,t=$tree.value[1])",
        "number=evaluate(Trees.integer,x=$tree.evaluation.value[0][0])",
        "nested=evaluate(Trees.integer,x=$wrapped.value[0][1].some[0][0])",
        "universal=check(Trees.two,x=$tree.value[0][0])",
        "tree=evaluate(Trees.raw,s=@v/sample)",
        "wrapped=evaluate(Trees.wrapped,s=@v/sample)",
    ];
    let r = evaluate_observed_bytes(fixture::tree_input(false, "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    for (id, value) in [("sub", "2"), ("number", "3"), ("nested", "3")] {
        assert_eq!(f(output(&w, id), "value"), &Json::str(value));
    }
    assert_eq!(
        f(answer(&w, "universal"), "status"),
        &Json::str("established")
    );
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|s| Json::str(s.split('=').next().unwrap()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn answer_projection_keeps_all_component_types_and_reuses_whole_output_ref() {
    let asks = [
        "q=evaluate(Applications.apQ,x=$packed.value[1])",
        "fp=evaluate(Applications.apFp,x=$packed.value[2])",
        "boolean=evaluate(Applications.abBool,x=$packed.value[3])",
        "text=evaluate(Applications.apText,x=$packed.value[4])",
        "unitValue=evaluate(Applications.apUnit,x=$packed.value[5])",
        "listValue=evaluate(Applications.apList,x=$packed.value[6])",
        "setValue=evaluate(Applications.apSet,x=$packed.value[7])",
        "optionValue=evaluate(Applications.apOption,x=$packed.value[8])",
        "whole=evaluate(Applications.abCopy,x=$packed.evaluation.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ];
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    let values = arr(f(output(&w, "packed"), "value"));
    let types = arr(f(output(&w, "packed"), "type"));
    for (id, index) in [
        ("q", 1),
        ("fp", 2),
        ("boolean", 3),
        ("text", 4),
        ("unitValue", 5),
        ("listValue", 6),
        ("setValue", 7),
        ("optionValue", 8),
    ] {
        assert_eq!(f(output(&w, id), "value"), &values[index]);
        assert_eq!(f(output(&w, id), "type"), &types[index + 1]);
    }
    assert_eq!(
        f(f(answer(&w, "whole"), "outputs"), "value"),
        f(f(answer(&w, "packed"), "outputs"), "value")
    );
    let root = f(f(answer(&w, "packed"), "outputs"), "value");
    for n in arr(f(&w, "nodes")).iter().filter(
        |n| matches!(f(n,"rule"),Json::Obj(m)if m.get("name")==Some(&Json::str("projection"))),
    ) {
        assert_eq!(f(n, "arguments"), &Json::Arr(vec![root.clone()]));
        assert_eq!(f(n, "scope"), f(node(&w, root), "scope"));
        assert_eq!(f(n, "support"), f(node(&w, root), "support"));
        assert!(matches!(
            arr(f(f(n, "rule"), "path")).first(),
            Some(Json::Nat(_))
        ));
    }
}

#[test]
fn answer_projection_missing_roots_keep_original_reasons_through_component_paths() {
    let asks = [
        "last=evaluate(Applications.abDouble,x=$first.value)",
        "first=evaluate(Applications.abIdentity,x=$missing.evaluation.value[0])",
        "missing=evaluate(Applications.apMissing,p=@v/p)",
        "opaque=evaluate(Applications.apUnsupported)",
        "copied=evaluate(Applications.abBool,x=$opaque.value[0])",
        "known=evaluate(Applications.abSeed)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "partial", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    for (consumer, producer) in [
        ("first", "missing"),
        ("last", "first"),
        ("copied", "opaque"),
    ] {
        let a = answer(&w, consumer);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert_eq!(f(a, "outputs"), &Json::obj([]));
        assert!(arr(f(a, "reasons")).iter().any(|reason| f(reason, "code")
            == &Json::str("dependency_blocked")
            && f(f(reason, "details"), "request") == &Json::str(producer)));
        for reason in arr(f(answer(&w, producer), "reasons")) {
            assert!(arr(f(a, "reasons")).contains(reason));
        }
    }
    assert!(
        arr(f(answer(&w, "missing"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
    );
    assert!(
        arr(f(answer(&w, "opaque"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
    assert_eq!(f(answer(&w, "known"), "status"), &Json::str("established"));
    let tree = evaluate_observed_bytes(
        fixture::tree_input(true, "r1"),
        &[
            "take=evaluate(Trees.integer,x=$raw.value[0][0])",
            "raw=evaluate(Trees.raw,s=@v/sample)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(tree.status(), "partial");
    let w = tree.wire();
    for reason in arr(f(answer(&w, "raw"), "reasons")) {
        assert!(arr(f(answer(&w, "take"), "reasons")).contains(reason));
    }
}

#[test]
fn answer_projection_static_invalid_and_unprovided_dynamic_cases_stay_distinct() {
    // 同じ動的射影でも、別の不適合parameterが先に記載されたことで内部失敗にしない。
    let mixed = evaluate_observed_bytes(
        fixture::tree_input(false, "r1"),
        &[
            "take=evaluate(Trees.acceptsPair,x=$raw.value[0],t=$raw.value[0])",
            "raw=evaluate(Trees.raw,s=@v/sample)",
        ],
        &mut quiet(),
    );
    match mixed {
        Err(archsig::observed::EvaluationFailure::NotImplemented { .. }) => {}
        Err(other) => panic!(
            "unexpected failure {:?}",
            other.wire().as_ref().map(|w| f(w, "issues"))
        ),
        Ok(result) => panic!(
            "dynamic boundary became {}: {:?}",
            result.status(),
            f(&result.wire(), "issues")
        ),
    }
    for path in [
        "[6][0][0]",
        "[7][0]",
        "[10][0]",
        "[9].snapshot",
        "[11].body",
        "[99]",
    ] {
        let ask = format!("take=evaluate(Applications.abIdentity,x=$packed.value{path})");
        let e = evaluate_observed_bytes(
            fixture::input("known", "r1"),
            &[&ask, "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)"],
            &mut quiet(),
        )
        .unwrap_err();
        let w = e.wire().unwrap();
        assert_eq!(f(&w, "status"), &Json::str("invalid"));
        assert!(arr(f(&w, "nodes")).is_empty());
        assert!(arr(f(&w, "answers")).is_empty());
    }
    for asks in [
        vec![
            "take=evaluate(Applications.abIdentity,x=$opt.value.some)",
            "opt=evaluate(Applications.apNone)",
        ],
        vec![
            "take=evaluate(Applications.abIdentity,x=$empty.value[0])",
            "empty=evaluate(Applications.apEmpty)",
        ],
    ] {
        let e = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
            .unwrap_err();
        assert!(matches!(
            e,
            archsig::observed::EvaluationFailure::NotImplemented { .. }
        ));
        assert!(e.wire().is_none());
    }
    for asks in [
        vec![
            "take=evaluate(Trees.integer,x=$empty.value[0])",
            "empty=evaluate(Trees.empty)",
        ],
        vec![
            "take=evaluate(Trees.integer,x=$raw.value[0])",
            "raw=evaluate(Trees.raw,s=@v/sample)",
        ],
    ] {
        let e = evaluate_observed_bytes(fixture::tree_input(false, "r1"), &asks, &mut quiet())
            .unwrap_err();
        assert!(matches!(
            e,
            archsig::observed::EvaluationFailure::NotImplemented { .. }
        ));
        assert!(e.wire().is_none());
    }
}

#[test]
fn answer_projection_keeps_original_inputs_producer_nodes_and_current_provenance() {
    let asks = [
        "take=evaluate(Applications.abIdentity,x=$packed.evaluation.value[6][0])",
        "reference=evaluate(Applications.abFree,p=$packed.value[9])",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ];
    let mut runs = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("known", revision);
        let original = input.clone();
        let mut c = quiet();
        let checked = archsig::observed::input::check_inputs(input.clone(), &mut c).unwrap();
        let r = evaluate_observed_bytes(input, &asks, &mut c).unwrap();
        assert_eq!(r.status(), "complete");
        assert_eq!(r.prepared().inputs().sources(), &original);
        assert_eq!(r.prepared().inputs().definitions(), checked.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", checked.law())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", checked.archmap())
        );
        let w = r.wire();
        let mut facts = 0;
        let mut projections = 0;
        let producer =
            evaluate_observed_bytes(fixture::input("known", revision), &[asks[2]], &mut quiet())
                .unwrap();
        assert_eq!(output(&w, "packed"), output(&producer.wire(), "packed"));
        for (at, n) in arr(f(&w, "nodes")).iter().enumerate() {
            fn references(j: &Json, refs: &mut Vec<Json>) {
                match j {
                    Json::Obj(m) if m.len() == 1 && m.contains_key("node") => refs.push(j.clone()),
                    Json::Obj(m) => {
                        for v in m.values() {
                            references(v, refs)
                        }
                    }
                    Json::Arr(xs) => {
                        for x in xs {
                            references(x, refs)
                        }
                    }
                    _ => {}
                }
            }
            let mut refs = vec![];
            references(n, &mut refs);
            for reference in refs {
                assert!(arr(f(&w, "nodes"))[..at].contains(node(&w, &reference)));
            }
            if matches!(f(n,"rule"),Json::Obj(m)if m.get("name")==Some(&Json::str("projection"))) {
                projections += 1;
                assert!(!arr(f(f(n, "rule"), "path")).is_empty());
                let roots = arr(f(n, "arguments"));
                assert_eq!(roots.len(), 1);
                assert_eq!(f(n, "scope"), f(node(&w, &roots[0]), "scope"));
                assert_eq!(f(n, "support"), f(node(&w, &roots[0]), "support"));
            }
            for fact in arr(f(n, "support")) {
                let Json::Obj(fact) = fact else { panic!() };
                let Some(atom) = fact.get("atom") else {
                    continue;
                };
                facts += 1;
                let map = r.prepared().inputs().archmap();
                let snapshot = map
                    .snapshots
                    .iter()
                    .find(|s| Json::str(&s.id) == fact["snapshot"])
                    .unwrap();
                let subject = snapshot
                    .subjects
                    .iter()
                    .find(|s| Json::str(&s.id) == fact["subject"])
                    .unwrap();
                let field = subject
                    .fields
                    .iter()
                    .find(|p| Json::str(&p.name) == fact["field"])
                    .unwrap();
                let archsig::archmap::Slot::Known {
                    atom: actual,
                    origin,
                    ..
                } = &field.slot
                else {
                    panic!()
                };
                assert_eq!(&Json::str(actual), atom);
                let origin = map.origins.iter().find(|o| o.id == *origin).unwrap();
                assert!(!origin.locations.is_empty());
                for at in &origin.locations {
                    assert_eq!(
                        map.sources
                            .iter()
                            .find(|s| s.id == at.source)
                            .unwrap()
                            .revision,
                        revision
                    );
                }
            }
        }
        assert!(facts > 0);
        assert_eq!(projections, 2);
        runs.push(w);
    }
    assert_eq!(f(&runs[0], "nodes"), f(&runs[1], "nodes"));
    assert_eq!(f(&runs[0], "answers"), f(&runs[1], "answers"));
    assert_ne!(f(&runs[0], "inputs"), f(&runs[1], "inputs"));
}
