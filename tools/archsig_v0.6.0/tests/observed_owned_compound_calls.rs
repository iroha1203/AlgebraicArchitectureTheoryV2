//! 複合署名の各実memberを、元ownerと観測された所属事実へ接続する。
#[path = "common/owned_compound_calls.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn get<'a>(j: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("object") };
    &m[key]
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
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input(false, "r1"), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("input/evaluation: {:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", get(&r.wire(), "issues"));
    r
}
fn reference(s: &str, id: &str) -> Json {
    Json::Arr(vec![Json::str(s), Json::str(id)])
}

#[test]
fn compound_owned_parameters_and_returns_keep_each_owner_list_order_and_set_extensionality() {
    let r = run(&[
        "p=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/s,e=@v/e)",
        "v=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,e=@v/e)",
        "sets=evaluate(Reservations.ccSetEqual,a=@v/A,p=@v/p,q=@v/q)",
        "universal=check(Reservations.ccAffine,a=@v/A,p=@v/p)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for id in ["p", "v", "sets", "universal"] {
        assert_eq!(get(answer(&w, id), "status"), &Json::str("established"));
    }
    for id in ["p", "sets"] {
        assert_eq!(
            get(
                node(&w, get(get(answer(&w, id), "outputs"), "value")),
                "value"
            ),
            &Json::Bool(true)
        );
    }
    let n = node(&w, get(get(answer(&w, "v"), "outputs"), "value"));
    assert_eq!(
        get(n, "value"),
        &Json::Arr(vec![
            Json::Arr(vec![
                reference("v", "q"),
                reference("v", "p"),
                reference("v", "q")
            ]),
            Json::obj([("some", reference("v", "e"))]),
            Json::Arr(vec![reference("v", "r")])
        ])
    );
    for atom in ["p-owner", "q-owner", "r-owner", "e-owner"] {
        assert!(
            arr(get(n, "support"))
                .iter()
                .any(|f| matches!(f,Json::Obj(m) if m.get("atom")==Some(&Json::str(atom)))),
            "{atom}"
        );
    }
}

#[test]
fn compound_owned_wrong_members_preserve_failed_condition_and_skip_unused_body() {
    let r = run(&[
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "p=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/p,e=@v/e)",
        "r=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@v/p,q=@v/r,r=@v/r,e=@v/e)",
        "edge=evaluate(Reservations.ccParameter,a=@v/B,b=@v/B,p=@v/r,q=@v/s,r=@v/r,s=@v/s,e=@v/e)",
        "skip=evaluate(Reservations.ccSkipped,a=@v/B,p=@v/p,s=@v/q)",
        "snapshot=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@w/p,q=@v/q,r=@v/r,e=@v/e)",
        "ignored=evaluate(Reservations.ccIgnored,a=@v/A,b=@v/B,p=@v/p,q=@v/r,r=@v/r,e=@v/e)",
        "missing=evaluate(Reservations.ccMissing,a=@v/B,p=@v/p)",
        "affine=check(Reservations.ccAffine,a=@v/B,p=@v/p)",
        "later=evaluate(Reservations.seed)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in ["seed", "later"] {
        assert_eq!(get(answer(&w, id), "status"), &Json::str("established"));
    }
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    for id in [
        "p", "r", "edge", "skip", "snapshot", "ignored", "missing", "affine",
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let reasons = arr(get(a, "reasons"));
        let reason = reasons
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        assert!(
            !reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("missing_observation")),
            "{id}"
        );
        let condition = node(&w, get(get(reason, "details"), "condition"));
        assert_eq!(
            get(get(condition, "judgment"), "status"),
            &Json::str("refuted")
        );
        assert!(!arr(get(condition, "support")).is_empty());
    }
}

#[test]
fn compound_owned_none_and_empty_values_keep_explicit_shape_and_no_fabricated_member() {
    let r = run(&[
        "a=evaluate(Reservations.ccEmpty,a=@v/A)",
        "z=evaluate(Reservations.ccEmptyReturned,a=@v/Z)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    let a = answer(&w, "a");
    assert_eq!(
        get(node(&w, get(get(a, "outputs"), "value")), "value"),
        &Json::str("0")
    );
    let z = answer(&w, "z");
    let n = node(&w, get(get(z, "outputs"), "value"));
    assert_eq!(
        get(n, "value"),
        &Json::Arr(vec![
            Json::obj([("none", Json::Bool(true))]),
            Json::Arr(vec![]),
            Json::Arr(vec![])
        ])
    );
    assert!(arr(get(n,"support")).iter().all(|f|!matches!(f,Json::Obj(m) if m.get("field")==Some(&Json::str("Reservations.State.owner")))));
    assert!(arr(get(z, "reasons")).is_empty());
}

#[test]
fn compound_owned_unknown_actual_owner_remains_unprovided() {
    let r = evaluate_observed_bytes(
        fixture::input(true, "r1"),
        &["p=evaluate(Reservations.ccSetEqual,a=@v/A,p=@v/p,q=@v/q)"],
        &mut quiet(),
    )
    .unwrap_err();
    assert!(matches!(
        r,
        archsig::observed::EvaluationFailure::NotImplemented { .. }
    ));
    assert!(r.wire().is_none());
}

#[test]
fn compound_owned_provenance_and_original_inputs_preserve_values_facts_and_current_sources() {
    let asks = [
        "ok=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,e=@v/e)",
        "bad=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/p,e=@v/e)",
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
        results.push(w);
    }
    assert_eq!(get(&results[0], "answers"), get(&results[1], "answers"));
    assert_eq!(get(&results[0], "nodes"), get(&results[1], "nodes"));
    assert_ne!(get(&results[0], "inputs"), get(&results[1], "inputs"));
}

#[test]
fn compound_owned_missing_member_is_not_an_explicit_none_or_empty_value() {
    let r = evaluate_observed_bytes(
        fixture::missing_member_input(),
        &[
            "unknown=evaluate(Reservations.ccUnknown,a=@v/A,e=@v/e)",
            "empty=evaluate(Reservations.ccEmpty,a=@v/A)",
        ],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = answer(&w, "unknown");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
    let rs = arr(get(a, "reasons"));
    assert!(
        !rs.iter()
            .any(|r| get(r, "code") == &Json::str("condition_failed"))
    );
    assert!(
        rs.iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "snapshot") == &Json::str("v")
                && get(f, "subject") == &Json::str("e")
                && get(f, "field") == &Json::str("Reservations.Reserve.to"))
    );
    let empty = answer(&w, "empty");
    assert_eq!(get(empty, "status"), &Json::str("established"));
    assert_eq!(
        get(node(&w, get(get(empty, "outputs"), "value")), "value"),
        &Json::str("0")
    );
}
