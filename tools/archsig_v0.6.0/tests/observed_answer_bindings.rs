//! 同一batchの既知出力を元Requestと既出Refへ接続する。
#[path = "common/answer_bindings.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("object") };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(get(w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn output<'a>(w: &'a Json, id: &str) -> &'a Json {
    node(w, get(get(answer(w, id), "outputs"), "value"))
}
fn run(asks: &[&str]) -> Json {
    let r = evaluate_observed_bytes(
        fixture::input("r1"),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_or_else(|e| panic!("{e:?}: {:?}", e.wire()));
    assert_eq!(r.status(), "complete", "{:?}", r.wire());
    r.wire()
}
#[test]
fn answer_known_values_follow_forward_dependencies_and_keep_requested_order() {
    let asks = [
        "last=check(Applications.abFour,x=$middle.evaluation.value)",
        "middle=evaluate(Applications.abDouble,x=$bridge.value)",
        "bridge=evaluate(Applications.abIdentity,x=$first.evaluation.value)",
        "first=evaluate(Applications.abSeed)",
    ];
    let w = run(&asks);
    assert_eq!(
        arr(get(&w, "answers"))
            .iter()
            .map(|a| get(a, "id"))
            .collect::<Vec<_>>(),
        vec![
            &Json::str("last"),
            &Json::str("middle"),
            &Json::str("bridge"),
            &Json::str("first")
        ]
    );
    assert_eq!(get(output(&w, "first"), "value"), &Json::str("2"));
    assert_eq!(get(output(&w, "middle"), "value"), &Json::str("4"));
    assert_eq!(get(answer(&w, "last"), "status"), &Json::str("established"));
    let requests = arr(get(&w, "requests"));
    assert_eq!(
        get(&requests[0], "dependencies"),
        &Json::Arr(vec![Json::str("middle")])
    );
    assert_eq!(
        get(&requests[1], "dependencies"),
        &Json::Arr(vec![Json::str("bridge")])
    );
    for request in requests {
        assert!(
            arr(get(request, "defaults"))
                .iter()
                .any(|d| get(d, "rule") == &Json::str("observed_environment"))
        );
        for argument in arr(get(request, "arguments")) {
            assert_eq!(get(argument, "origin"), &Json::str("explicit"));
        }
    }
    for (request, text) in requests.iter().zip(asks) {
        assert_eq!(get(request, "text"), &Json::str(text));
    }
    for (consumer, producer) in [
        ("middle", "bridge"),
        ("last", "middle"),
        ("bridge", "first"),
    ] {
        let e = node(&w, get(get(answer(&w, consumer), "outputs"), "evaluation"));
        let binding = &arr(get(get(e, "value"), "bindings"))[0];
        assert_eq!(
            get(binding, "value"),
            get(get(answer(&w, producer), "outputs"), "value")
        );
    }
    let universal = run(&[
        "universal=check(Applications.abUniversal,x=$seed.value)",
        "seed=evaluate(Applications.abSeed)",
    ]);
    assert_eq!(
        get(answer(&universal, "universal"), "status"),
        &Json::str("established")
    );
}
#[test]
fn answer_known_composite_values_keep_all_types_and_original_output_refs() {
    let w = run(&[
        "used=evaluate(Applications.abUse,x=$copied.value)",
        "copied=evaluate(Applications.abCopy,x=$packed.evaluation.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ]);
    assert_eq!(
        get(get(answer(&w, "copied"), "outputs"), "value"),
        get(get(answer(&w, "packed"), "outputs"), "value")
    );
    let v = output(&w, "used");
    assert_eq!(
        get(v, "type"),
        &Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Z"),
            Json::str("Q"),
            Json::Arr(vec![Json::str("Fp"), Json::str("5")]),
            Json::str("Bool"),
            Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]),
            Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]),
            Json::str("Z")
        ])
    );
    assert_eq!(
        get(v, "value"),
        &Json::Arr(vec![
            Json::str("3"),
            Json::Arr(vec![Json::str("1"), Json::str("1")]),
            Json::str("1"),
            Json::Bool(true),
            Json::Arr(vec![Json::str("v"), Json::str("p")]),
            Json::Arr(vec![Json::str("v"), Json::str("r")]),
            Json::str("3")
        ])
    );
    let packed = output(&w, "packed");
    let values = arr(get(packed, "value"));
    assert_eq!(values.len(), 12);
    assert_eq!(
        values[6],
        Json::Arr(vec![Json::str("2"), Json::str("1"), Json::str("2")])
    );
    assert_eq!(arr(&values[7]).len(), 2);
    assert_eq!(get(&values[8], "some"), &Json::str("0"));
}
#[test]
fn answer_references_keep_snapshot_fields_and_false_values_separate_from_law_refutation() {
    let w = run(&[
        "sv=evaluate(Applications.abFree,p=$rv.value)",
        "sw=evaluate(Applications.abFree,p=$rw.evaluation.value)",
        "rv=evaluate(Applications.abReference,p=@v/p)",
        "rw=evaluate(Applications.abReference,p=@w/r)",
        "falseCopy=evaluate(Applications.abBool,x=$falseView.value)",
        "falseLaw=check(Applications.abRequire,x=$falseCopy.evaluation.value)",
        "falseFromLaw=evaluate(Applications.abBool,x=$falseLaw.evaluation.value)",
        "falseView=evaluate(Applications.abFalse)",
    ]);
    for id in ["falseView", "falseCopy", "falseFromLaw"] {
        assert_eq!(get(answer(&w, id), "status"), &Json::str("established"));
        assert_eq!(get(output(&w, id), "value"), &Json::Bool(false));
    }
    assert_eq!(get(answer(&w, "falseLaw"), "status"), &Json::str("refuted"));
    assert_eq!(get(output(&w, "sv"), "value"), &Json::str("2"));
    assert_eq!(get(output(&w, "sw"), "value"), &Json::str("4"));
    assert_eq!(
        get(output(&w, "rv"), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("p")])
    );
    assert_eq!(
        get(output(&w, "rw"), "value"),
        &Json::Arr(vec![Json::str("w"), Json::str("r")])
    );
    for (id, snapshot) in [("sv", "v"), ("sw", "w")] {
        assert!(arr(get(get(output(&w, id), "scope"), "snapshots")).contains(&Json::str(snapshot)));
        assert!(
            arr(get(output(&w, id), "support"))
                .iter()
                .any(|f| get(f, "snapshot") == &Json::str(snapshot)
                    && get(f, "field") == &Json::str("Reservations.State.free"))
        );
    }
}
#[test]
fn answer_finite_data_output_remains_original_tree_for_structural_recursion() {
    let asks = [
        "n=evaluate(Trees.total,t=$tree.value)",
        "copy=evaluate(Trees.copy,t=$tree.evaluation.value)",
        "tree=evaluate(Trees.raw,s=@v/sample)",
    ];
    let r = evaluate_observed_bytes(
        fixture::tree_input("r1"),
        &asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.wire());
    let w = r.wire();
    assert_eq!(get(output(&w, "n"), "type"), &Json::str("Z"));
    assert_eq!(get(output(&w, "n"), "value"), &Json::str("4"));
    assert_eq!(
        get(output(&w, "copy"), "value"),
        get(output(&w, "tree"), "value")
    );
    assert_eq!(
        get(output(&w, "copy"), "type"),
        &Json::Arr(vec![Json::str("Data"), Json::str("Trees.Tree")])
    );
    let e = node(&w, get(get(answer(&w, "n"), "outputs"), "evaluation"));
    let binding = &arr(get(get(e, "value"), "bindings"))[0];
    assert_eq!(
        get(binding, "value"),
        get(get(answer(&w, "tree"), "outputs"), "value")
    );
}
#[test]
fn answer_binding_static_errors_and_unprovided_outputs_do_not_become_values() {
    for asks in [
        vec![
            "first=evaluate(Applications.abSeed)",
            "bad=evaluate(Applications.abDouble)",
        ],
        vec![
            "first=evaluate(Applications.abSeed)",
            "first=evaluate(Applications.abSeed)",
        ],
        vec!["bad=evaluate(Applications.abDouble,x=$absent.value)"],
        vec![
            "first=evaluate(Applications.abFalse)",
            "bad=evaluate(Applications.abDouble,x=$first.value)",
        ],
        vec![
            "first=evaluate(Applications.abSeed)",
            "bad=evaluate(Applications.abDouble,x=$first.value,x=$first.value)",
        ],
        vec![
            "first=evaluate(Applications.abSeed)",
            "bad=evaluate(Applications.abDouble,x=$first.value[0])",
        ],
        vec![
            "first=evaluate(Applications.abSeed)",
            "bad=evaluate(Applications.abDouble,x=$first.evaluation.parts)",
        ],
    ] {
        let e = evaluate_observed_bytes(
            fixture::input("r1"),
            &asks,
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap_err();
        assert!(
            matches!(e, archsig::observed::EvaluationFailure::Prepare(_)),
            "{e:?}"
        );
        let w = e.wire().unwrap();
        assert_eq!(get(&w, "status"), &Json::str("invalid"));
        assert!(arr(get(&w, "nodes")).is_empty());
        assert!(arr(get(&w, "answers")).is_empty());
    }
    for asks in [
        vec![
            "raw=evaluate(Applications.abFree,p=@v/p)",
            "consumer=evaluate(Applications.abDouble,x=$raw.value)",
        ],
        vec![
            "raw=evaluate(Applications.abFree,p=@v/p)",
            "consumer=evaluate(Applications.abDouble,x=$raw.evaluation.value)",
        ],
    ] {
        let r = evaluate_observed_bytes(
            fixture::input_mode("stop", "r1"),
            &asks,
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        assert_eq!(
            get(answer(&w, "consumer"), "status"),
            &Json::str("undetermined")
        );
        assert_eq!(get(answer(&w, "consumer"), "outputs"), &Json::obj([]));
        assert!(
            arr(get(answer(&w, "consumer"), "reasons"))
                .iter()
                .any(|reason| get(reason, "code") == &Json::str("dependency_blocked"))
        );
    }
}
#[test]
fn answer_known_binding_keeps_input_tables_and_current_provenance() {
    let asks = [
        "used=evaluate(Applications.abUse,x=$copied.value)",
        "copied=evaluate(Applications.abCopy,x=$packed.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ];
    let mut runs = Vec::new();
    for revision in ["r1", "r2"] {
        let i = fixture::input(revision);
        let original = i.clone();
        let mut c = Control::new(Limits::default(), |_| Usage::default());
        let checked = archsig::observed::input::check_inputs(i.clone(), &mut c).unwrap();
        let r = evaluate_observed_bytes(i, &asks, &mut c).unwrap();
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
        for (at, n) in arr(get(&w, "nodes")).iter().enumerate() {
            fn refs(j: &Json, rs: &mut Vec<Json>) {
                match j {
                    Json::Obj(m) if m.len() == 1 && m.contains_key("node") => rs.push(j.clone()),
                    Json::Obj(m) => {
                        for v in m.values() {
                            refs(v, rs)
                        }
                    }
                    Json::Arr(a) => {
                        for v in a {
                            refs(v, rs)
                        }
                    }
                    _ => {}
                }
            }
            let mut rs = Vec::new();
            refs(n, &mut rs);
            for reference in rs {
                assert!(arr(get(&w, "nodes"))[..at].contains(node(&w, &reference)));
            }
            for f in arr(get(n, "support")) {
                let Json::Obj(f) = f else { panic!() };
                let Some(atom) = f.get("atom") else { continue };
                facts += 1;
                let map = r.prepared().inputs().archmap();
                let s = map
                    .snapshots
                    .iter()
                    .find(|s| Json::str(&s.id) == f["snapshot"])
                    .unwrap()
                    .subjects
                    .iter()
                    .find(|s| Json::str(&s.id) == f["subject"])
                    .unwrap();
                let field = s
                    .fields
                    .iter()
                    .find(|p| Json::str(&p.name) == f["field"])
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
                let o = map.origins.iter().find(|o| o.id == *origin).unwrap();
                assert!(!o.locations.is_empty());
                for at in &o.locations {
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
        runs.push(w);
    }
    assert_eq!(get(&runs[0], "answers"), get(&runs[1], "answers"));
    assert_eq!(get(&runs[0], "nodes"), get(&runs[1], "nodes"));
    assert_ne!(get(&runs[0], "inputs"), get(&runs[1], "inputs"));
}
