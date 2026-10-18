//! Mapのkey/image所属と完全なOwned始域を元三入力から計算する。
#[path = "common/owned_map_calls.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
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
fn run_input(i: InputSources, asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let r = evaluate_observed_bytes(
        i,
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", get(&r.wire(), "issues"));
    r
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    run_input(fixture::input("known", "r1"), asks)
}
fn codes(a: &Json) -> Vec<&Json> {
    arr(get(a, "reasons"))
        .iter()
        .map(|r| get(r, "code"))
        .collect()
}
fn assert_failed(w: &Json, id: &str) {
    let a = answer(w, id);
    assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
    let Json::Obj(o) = get(a, "outputs") else {
        panic!()
    };
    assert!(!o.contains_key("value"));
    let reason = arr(get(a, "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .expect(id);
    let c = node(w, get(get(reason, "details"), "condition"));
    assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
    assert!(!arr(get(c, "support")).is_empty());
}
#[test]
fn owned_map_calls_check_actual_keys_images_returns_nested_values_and_z_binders() {
    let r = run(&[
        "parameter=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)",
        "returned=evaluate(Applications.mcReturned,a=@v/A,b=@v/B,m=@v/m)",
        "image=evaluate(Applications.mcRead,a=@v/A,b=@v/B,m=@v/m,x=@v/p)",
        "domainOnly=evaluate(Applications.mcDomainUse,a=@v/A,m=@v/m)",
        "imageOnly=evaluate(Applications.mcImageUse,b=@v/B,m=@v/m)",
        "nested=evaluate(Applications.mcNestedUse,a=@v/A,b=@v/B,m=@v/m)",
        "affine=check(Applications.mcAffine,a=@v/A,b=@v/B,m=@v/m)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for id in [
        "parameter",
        "returned",
        "image",
        "domainOnly",
        "imageOnly",
        "nested",
        "affine",
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert!(codes(a).is_empty());
    }
    for id in ["parameter", "returned", "domainOnly", "imageOnly", "nested"] {
        let a = answer(&w, id);
        assert_eq!(
            get(node(&w, get(get(a, "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
    }
    let n = node(&w, get(get(answer(&w, "image"), "outputs"), "value"));
    assert_eq!(
        get(n, "type"),
        &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")])
    );
    assert_eq!(
        get(n, "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("r")])
    );
    for id in ["parameter", "returned", "nested", "affine"] {
        let a = answer(&w, id);
        let target = if id == "affine" {
            get(a, "claim")
        } else {
            get(get(a, "outputs"), "evaluation")
        };
        let n = node(&w, target);
        for atom in ["p-owner", "q-owner", "r-owner", "s-owner", "m-states"] {
            assert!(
                arr(get(n, "support"))
                    .iter()
                    .any(|f| matches!(f,Json::Obj(m)if m.get("atom")==Some(&Json::str(atom)))),
                "{id}:{atom}"
            );
        }
        assert!(arr(get(get(n, "scope"), "snapshots")).contains(&Json::str("v")));
    }
}
#[test]
fn owned_map_known_key_image_snapshot_and_return_failures_keep_original_conditions() {
    let r = run(&[
        "keys=evaluate(Applications.mcParameter,a=@v/B,b=@v/B,m=@v/m)",
        "images=evaluate(Applications.mcParameter,a=@v/A,b=@v/A,m=@v/m)",
        "returned=evaluate(Applications.mcReturned,a=@v/A,b=@v/A,m=@v/m)",
        "nested=evaluate(Applications.mcNestedUse,a=@v/A,b=@v/A,m=@v/m)",
        "snapshot=evaluate(Applications.mcParameter,a=@v/A,b=@w/B,m=@v/m)",
        "ignored=evaluate(Applications.mcIgnored,a=@v/A,b=@v/A,m=@v/m)",
        "affine=check(Applications.mcAffine,a=@v/A,b=@v/A,m=@v/m)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in [
        "keys", "images", "returned", "nested", "snapshot", "ignored", "affine",
    ] {
        assert_failed(&w, id);
        assert!(!codes(answer(&w, id)).contains(&&Json::str("unsupported_algorithm")));
    }
    let reason = arr(get(answer(&w, "images"), "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let c = node(&w, get(get(reason, "details"), "condition"));
    let operands = arr(get(get(c, "value"), "operands"));
    assert_eq!(operands.len(), 2);
    for (v, id) in operands.iter().zip(["B", "A"]) {
        let n = node(&w, v);
        assert_eq!(
            get(n, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
        );
        assert_eq!(
            get(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(id)])
        );
    }
}
#[test]
fn owned_map_empty_domain_is_typed_and_nonempty_expected_domain_is_refuted() {
    let r = run_input(
        fixture::input("empty", "r1"),
        &[
            "emptyDomain=evaluate(Applications.mcParameter,a=@v/Z,b=@v/B,m=@v/m)",
            "emptyBoth=evaluate(Applications.mcParameter,a=@v/Z,b=@v/Z,m=@v/m)",
            "missingKeys=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)",
            "returned=evaluate(Applications.mcReturned,a=@v/A,b=@v/B,m=@v/m)",
        ],
    );
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in ["emptyDomain", "emptyBoth"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert_eq!(
            get(node(&w, get(get(a, "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
    }
    for id in ["missingKeys", "returned"] {
        assert_failed(&w, id);
        let a = answer(&w, id);
        let reason = arr(get(a, "reasons"))
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        let c = node(&w, get(get(reason, "details"), "condition"));
        let ops = arr(get(get(c, "value"), "operands"));
        assert_eq!(ops.len(), 2);
        for v in ops {
            assert_eq!(
                get(node(&w, v), "type"),
                &Json::Arr(vec![
                    Json::str("Set"),
                    Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")])
                ])
            );
        }
        assert_eq!(get(node(&w, &ops[0]), "value"), &Json::Arr(vec![]));
        assert_eq!(
            arr(get(node(&w, &ops[1]), "value"))
                .iter()
                .map(Json::canonical)
                .collect::<std::collections::BTreeSet<_>>(),
            ["p", "q"]
                .map(|x| Json::Arr(vec![Json::str("v"), Json::str(x)]).canonical())
                .into_iter()
                .collect()
        );
        for atom in ["p-owner", "q-owner", "r-owner", "s-owner", "m-states"] {
            assert!(
                arr(get(c, "support"))
                    .iter()
                    .any(|f| matches!(f,Json::Obj(m)if m.get("atom")==Some(&Json::str(atom))))
            );
        }
    }
}
#[test]
fn owned_map_finite_parameter_enumeration_keeps_all_four_original_maps() {
    let r = run(&["x=check(Applications.mcFamily,a=@v/A,b=@v/B)"]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(get(answer(&w, "x"), "status"), &Json::str("established"));
    let concrete = arr(get(&w, "nodes"))
        .iter()
        .filter(|n| {
            get(n, "type") == &Json::str("LawInstance")
                && arr(get(get(n, "value"), "bindings")).len() == 3
        })
        .collect::<Vec<_>>();
    assert_eq!(concrete.len(), 4);
    let mut maps = std::collections::BTreeSet::new();
    for row in concrete {
        let bs = arr(get(get(row, "value"), "bindings"));
        let m = node(&w, get(&bs[2], "value"));
        let pairs = arr(get(m, "value"));
        assert_eq!(pairs.len(), 2);
        assert_eq!(
            pairs
                .iter()
                .map(|p| arr(p)[0].canonical())
                .collect::<std::collections::BTreeSet<_>>(),
            ["p", "q"]
                .map(|x| Json::Arr(vec![Json::str("v"), Json::str(x)]).canonical())
                .into_iter()
                .collect()
        );
        assert!(pairs.iter().all(|p| {
            ["r", "s"]
                .iter()
                .any(|x| arr(p)[1] == Json::Arr(vec![Json::str("v"), Json::str(*x)]))
        }));
        assert!(maps.insert(get(m, "value").canonical()));
    }
    assert_eq!(maps.len(), 4);
}
#[test]
fn owned_map_missing_table_and_unknown_owner_keep_distinct_boundaries() {
    let r = run_input(
        fixture::input("missing", "r1"),
        &["x=evaluate(Applications.mcParameter,a=@v/B,b=@v/B,m=@v/m)"],
    );
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(codes(a).contains(&&Json::str("missing_observation")));
    let Json::Obj(o) = get(a, "outputs") else {
        panic!()
    };
    assert!(!o.contains_key("value"));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "field") == &Json::str("Reservations.Migration.states"))
    );
}

#[test]
fn owned_map_unknown_owner_uses_known_input_constraints() {
    let r = run_input(
        fixture::input("unknown_owner", "r1"),
        &["x=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)"],
    );
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("established"));
    assert_eq!(
        get(node(&w, get(get(a, "outputs"), "value")), "value"),
        &Json::Bool(true)
    );
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "subject") == &Json::str("p")
                && get(f, "field") == &Json::str("Reservations.State.owner"))
    );
    assert!(!codes(a).contains(&&Json::str("condition_failed")));
}

#[test]
fn owned_map_calls_keep_original_inputs_facts_and_current_provenance() {
    let asks = [
        "ok=evaluate(Applications.mcParameter,a=@v/A,b=@v/B,m=@v/m)",
        "bad=evaluate(Applications.mcParameter,a=@v/A,b=@v/A,m=@v/m)",
    ];
    let mut results = Vec::new();
    for revision in ["r1", "r2"] {
        let input = fixture::input("known", revision);
        let original = input.clone();
        let before = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
        let r = evaluate_observed_bytes(input, &asks, &mut quiet()).unwrap();
        assert_eq!(r.prepared().inputs().sources(), &original);
        assert_eq!(r.prepared().inputs().definitions(), before.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", before.law())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", before.archmap())
        );
        let w = r.wire();
        assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
        for a in arr(get(&w, "answers")) {
            assert_eq!(
                get(a, "status"),
                &Json::str(if get(a, "id") == &Json::str("ok") {
                    "established"
                } else {
                    "undetermined"
                })
            );
        }
        let mut counterexamples = 0;
        for (i, n) in arr(get(&w, "nodes")).iter().enumerate() {
            fn refs(j: &Json, out: &mut Vec<Json>) {
                match j {
                    Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(j.clone()),
                    Json::Obj(m) => {
                        for v in m.values() {
                            refs(v, out)
                        }
                    }
                    Json::Arr(a) => {
                        for v in a {
                            refs(v, out)
                        }
                    }
                    _ => {}
                }
            }
            let mut rs = Vec::new();
            refs(n, &mut rs);
            for reference in rs {
                let target = node(&w, &reference);
                assert!(arr(get(&w, "nodes"))[..i].contains(target));
            }
            if get(n, "type") == &Json::str("Evidence")
                && get(get(n, "value"), "kind") == &Json::str("counterexample")
            {
                counterexamples += 1;
                let Json::Obj(data) = get(get(n, "value"), "data") else {
                    panic!("data")
                };
                assert_eq!(
                    data.keys().map(String::as_str).collect::<Vec<_>>(),
                    vec!["bindings", "facts", "left", "paths", "right"]
                );
                assert_eq!(
                    get(node(&w, &data["left"]), "type"),
                    &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
                );
            }
            for fact in arr(get(n, "support")) {
                if let Json::Obj(f) = fact
                    && f.contains_key("atom")
                {
                    let atom = r
                        .prepared()
                        .inputs()
                        .archmap()
                        .snapshots
                        .iter()
                        .find(|s| Json::str(&s.id) == f["snapshot"])
                        .unwrap()
                        .subjects
                        .iter()
                        .find(|s| Json::str(&s.id) == f["subject"])
                        .unwrap()
                        .fields
                        .iter()
                        .find(|field| Json::str(&field.name) == f["field"])
                        .unwrap();
                    let archsig::archmap::Slot::Known { atom, origin, .. } = &atom.slot else {
                        panic!("known")
                    };
                    assert_eq!(&Json::str(atom), &f["atom"]);
                    let origin = r
                        .prepared()
                        .inputs()
                        .archmap()
                        .origins
                        .iter()
                        .find(|o| o.id == *origin)
                        .unwrap();
                    for at in &origin.locations {
                        assert_eq!(
                            r.prepared()
                                .inputs()
                                .archmap()
                                .sources
                                .iter()
                                .find(|s| s.id == at.source)
                                .unwrap()
                                .revision,
                            revision
                        );
                    }
                }
            }
        }
        assert!(counterexamples > 0);
        results.push(w);
    }
    assert_eq!(get(&results[0], "answers"), get(&results[1], "answers"));
    assert_eq!(get(&results[0], "nodes"), get(&results[1], "nodes"));
    assert_ne!(get(&results[0], "inputs"), get(&results[1], "inputs"));
}
