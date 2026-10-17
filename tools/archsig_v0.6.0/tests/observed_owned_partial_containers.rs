//! 部分Option/Setの所属を元三入力から計算する。
#[path = "common/owned_partial_containers.rs"]
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
    run_input(fixture::input(false, "r1"), asks)
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
fn partial_option_set_calls_keep_z_q_nested_members_and_return_boundaries() {
    let r = run(&[
        "optionCase=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)",
        "collectionCase=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/q)",
        "nested=check(Reservations.ocNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/r)",
        "returned=check(Reservations.ocReturned,a=@v/A,p=@v/p)",
        "returnset=check(Reservations.ocReturnedSet,a=@v/A,p=@v/p)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for a in arr(get(&w, "answers")) {
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert!(codes(a).is_empty());
    }
    let law = r.prepared().inputs().law();
    let mut seen = std::collections::BTreeSet::new();
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") != &Json::str("Evaluation") {
            continue;
        }
        let ev = get(n, "value");
        let src = get(node(&w, get(ev, "expression")), "value");
        let Json::Obj(sm) = src else { panic!() };
        let Some(location) = sm.get("location") else {
            continue;
        };
        let span = arr(get(location, "span"));
        let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
            panic!()
        };
        let id = law
            .exprs
            .iter()
            .position(|e| e.span == (*a as usize, *b as usize))
            .unwrap();
        if matches!(
            law.expr_type(id),
            Some(archsig::types::Type::Set(_) | archsig::types::Type::Option(_))
        ) {
            let Json::Obj(m) = ev else { panic!() };
            assert!(!m.contains_key("value"));
            seen.insert(get(n, "id").canonical());
        }
    }
    assert!(seen.len() >= 5);
    let mut axes = std::collections::BTreeSet::new();
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") == &Json::str("Expression") {
            if let Json::Obj(v) = get(n, "value") {
                if let Some(Json::Arr(ps)) = v.get("parameters") {
                    for p in ps {
                        axes.insert(get(p, "type").canonical());
                    }
                }
            }
        }
    }
    assert_eq!(
        axes,
        std::collections::BTreeSet::from([Json::str("Z").canonical(), Json::str("Q").canonical()])
    );

    for id in [
        "optionCase",
        "collectionCase",
        "nested",
        "returned",
        "returnset",
    ] {
        let claim = node(&w, get(answer(&w, id), "claim"));
        assert!(
            arr(get(claim, "support"))
                .iter()
                .any(|f| matches!(f,Json::Obj(m) if m.get("atom")==Some(&Json::str("p-owner"))))
        );
        assert!(arr(get(get(claim, "scope"), "snapshots")).contains(&Json::str("v")));
    }
}
#[test]
fn partial_option_set_known_owner_and_snapshot_failures_keep_typed_conditions() {
    let r = run(&[
        "optionCase=check(Reservations.ocSomeGood,a=@v/B,p=@v/p)",
        "collectionCase=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/r)",
        "nested=check(Reservations.ocNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/q)",
        "returned=check(Reservations.ocReturned,a=@v/B,p=@v/p)",
        "returnset=check(Reservations.ocReturnedSet,a=@v/B,p=@v/p)",
        "snapshot=check(Reservations.ocSomeGood,a=@v/A,p=@w/p)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in [
        "optionCase",
        "collectionCase",
        "nested",
        "returned",
        "returnset",
        "snapshot",
    ] {
        assert_failed(&w, id);
        assert!(!codes(answer(&w, id)).contains(&&Json::str("unsupported_algorithm")));
    }
    let a = answer(&w, "optionCase");
    let reason = arr(get(a, "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let c = node(&w, get(get(reason, "details"), "condition"));
    for (v, id) in arr(get(get(c, "value"), "operands")).iter().zip(["A", "B"]) {
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
fn partial_option_set_numeric_missing_keeps_known_members_without_fake_set_cardinality() {
    let r = run(&[
        "optionCase=evaluate(Reservations.ocMissing,a=@v/A,p=@v/p,q=@v/q)",
        "collectionCase=evaluate(Reservations.ocMissingSet,a=@v/A,p=@v/p,q=@v/q)",
        "bad=evaluate(Reservations.ocMissingSet,a=@v/B,p=@v/p,q=@v/q)",
        "counted=evaluate(Reservations.ocCount,a=@v/A,p=@v/p,q=@v/q)",
        "empty=evaluate(Reservations.ocEmpty,a=@v/B)",
        "emptyvalues=evaluate(Reservations.ocEmptyValuesUse,a=@v/B)",
        "extensional=evaluate(Reservations.ocKnownSet,a=@v/A,p=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "partial");
    for id in ["optionCase", "collectionCase", "empty", "extensional"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert_eq!(
            get(node(&w, get(get(a, "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
    }
    for id in ["optionCase", "collectionCase", "counted"] {
        assert!(codes(answer(&w, id)).contains(&&Json::str("missing_observation")));
    }
    assert_failed(&w, "bad");
    let a = answer(&w, "counted");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(o) = get(a, "outputs") else {
        panic!()
    };
    assert!(!o.contains_key("value"));
    assert!(codes(answer(&w, "empty")).is_empty());
    let a = answer(&w, "emptyvalues");
    assert_eq!(get(a, "status"), &Json::str("established"));
    assert_eq!(
        get(node(&w, get(get(a, "outputs"), "value")), "value"),
        &Json::Arr(vec![
            Json::obj([("none", Json::Bool(true))]),
            Json::Arr(vec![]),
            Json::str("0")
        ])
    );
    assert!(codes(a).is_empty());
}
#[test]
fn partial_option_set_pending_and_missing_members_keep_independent_known_mismatch() {
    let mut asks = Vec::new();
    for (id, v) in [
        ("optionCase", "ocPending"),
        ("collectionCase", "ocPendingSet"),
        ("returnedPending", "ocPendingReturnUse"),
        ("returnsetPending", "ocPendingReturnSetUse"),
        ("first", "ocMixed"),
        ("last", "ocMixedReverse"),
    ] {
        for (s, p) in [("good", "r"), ("bad", "p")] {
            asks.push(format!(
                "{id}{s}=evaluate(Reservations.{v},a=@v/B,e=@v/e,p=@v/{p}{} )",
                if v.starts_with("ocMixed") {
                    ",q=@v/q"
                } else {
                    ""
                }
            ));
        }
    }
    let refs = asks.iter().map(String::as_str).collect::<Vec<_>>();
    let r = run_input(fixture::missing_reference_input(), &refs);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in [
        "optionCase",
        "collectionCase",
        "returnedPending",
        "returnsetPending",
        "first",
        "last",
    ] {
        for s in ["good", "bad"] {
            let name = format!("{id}{s}");
            let a = answer(&w, &name);
            assert_eq!(get(a, "status"), &Json::str("undetermined"));
            let cs = codes(a);
            assert!(cs.contains(&&Json::str("missing_observation")));
            assert_eq!(cs.contains(&&Json::str("condition_failed")), s == "bad");
            if s == "bad" {
                assert_failed(&w, &name);
            }
        }
    }
}
#[test]
fn partial_option_missing_reference_and_unknown_owner_keep_their_boundary() {
    let r = run_input(
        fixture::missing_reference_input(),
        &["x=evaluate(Reservations.ocUnknown,a=@v/A,e=@v/e,q=@v/q)"],
    );
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(codes(a).contains(&&Json::str("missing_observation")));
    assert!(!codes(a).contains(&&Json::str("condition_failed")));
    let e = evaluate_observed_bytes(
        fixture::input(true, "r1"),
        &["x=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)"],
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_err();
    assert!(matches!(
        e,
        archsig::observed::EvaluationFailure::NotImplemented { .. }
    ));
    assert!(e.wire().is_none());
}

#[test]
fn partial_option_set_calls_preserve_original_inputs_and_current_provenance() {
    let asks = [
        "ok=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/q)",
        "bad=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/r)",
    ];
    let mut results = Vec::new();
    for revision in ["r1", "r2"] {
        let input = fixture::input(false, revision);
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
