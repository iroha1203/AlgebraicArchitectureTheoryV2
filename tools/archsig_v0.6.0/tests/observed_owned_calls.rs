//! 元署名の単一Owned参照を実callと原始owner事実へ接続する。
#[path = "common/owned_calls.rs"]
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
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else {
        panic!("object {j:?}")
    };
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
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    evaluate_observed_bytes(fixture::input(false, true, "r1"), asks, &mut quiet()).unwrap()
}
#[test]
fn owned_view_call_parameters_and_returns_preserve_original_owner_facts() {
    let r = run(&[
        "p=evaluate(Reservations.parameter,a=@v/A,s=@v/p)",
        "r=evaluate(Reservations.returned,a=@v/A,s=@v/p)",
        "n=evaluate(Reservations.nested,a=@v/A,s=@v/q)",
        "a=evaluate(Reservations.arrowParameter,a=@v/A,e=@v/e)",
        "ar=evaluate(Reservations.arrowReturned,a=@v/A,e=@v/e)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete", "{:?}", get(&w, "issues"));
    for (id, value) in [
        ("p", Json::Bool(true)),
        ("r", Json::Arr(vec![Json::str("v"), Json::str("p")])),
        ("n", Json::Arr(vec![Json::str("v"), Json::str("q")])),
        ("a", Json::Bool(true)),
        ("ar", Json::Arr(vec![Json::str("v"), Json::str("e")])),
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        let v = node(&w, get(get(a, "outputs"), "value"));
        assert_eq!(get(v, "value"), &value);
        assert!(arr(get(v,"support")).iter().any(|f|matches!(f,Json::Obj(m) if m.get("field").is_some_and(|x|matches!(x,Json::Str(x) if x.ends_with(".owner"))))));
    }
}
#[test]
fn wrong_owner_and_snapshot_calls_keep_refuted_conditions_without_a_value() {
    let r = run(&[
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "p=evaluate(Reservations.parameter,a=@v/B,s=@v/p)",
        "r=evaluate(Reservations.returned,a=@v/B,s=@v/p)",
        "cross=evaluate(Reservations.parameter,a=@v/A,s=@w/p)",
        "skip=evaluate(Reservations.skipped,a=@v/B,s=@v/p)",
        "a=evaluate(Reservations.arrowParameter,a=@v/B,e=@v/e)",
        "ar=evaluate(Reservations.arrowReturned,a=@v/B,e=@v/e)",
        "nested=evaluate(Reservations.nested,a=@v/B,s=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    assert_eq!(get(answer(&w, "seed"), "status"), &Json::str("established"));
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    for id in ["p", "r", "cross", "skip", "a", "ar", "nested"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let reason = arr(get(a, "reasons"))
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        let condition = node(&w, get(get(reason, "details"), "condition"));
        assert_eq!(
            get(get(condition, "judgment"), "status"),
            &Json::str("refuted")
        );
        let operands = arr(get(get(condition, "value"), "operands"));
        assert_eq!(operands.len(), 2);
        assert_ne!(
            get(node(&w, &operands[0]), "value"),
            get(node(&w, &operands[1]), "value")
        );
        assert!(arr(get(condition,"support")).iter().any(|f|matches!(f,Json::Obj(m) if m.get("field").is_some_and(|x|matches!(x,Json::Str(x) if x.ends_with(".owner"))))));
        assert!(
            !arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("missing_observation")),
            "不適合引数ではfree欠測を読むbodyに入らない"
        );
    }
}
#[test]
fn unknown_owner_is_not_silently_accepted_at_a_view_call_boundary() {
    let r = evaluate_observed_bytes(
        fixture::input(true, false, "r1"),
        &["x=evaluate(Reservations.parameter,a=@v/A,s=@v/p)"],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(r.status(), "partial");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
    assert!(arr(get(a, "reasons")).iter().any(|r| {
        get(r, "code") == &Json::str("missing_observation")
            && arr(get(r, "missing")).iter().any(|f| {
                get(f, "subject") == &Json::str("p")
                    && get(f, "field") == &Json::str("Reservations.State.owner")
            })
    }));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("condition_failed"))
    );
    assert_eq!(
        get(get(a, "scope"), "domain"),
        &Json::str("all_completions")
    );
}
#[test]
fn owned_calls_keep_finite_binders_fields_and_universal_affine_constraints() {
    let r = run(&[
        "all=evaluate(Reservations.quantified,a=@v/A)",
        "empty=evaluate(Reservations.quantified,a=@v/Z)",
        "field=evaluate(Reservations.fieldOwner,s=@v/p)",
        "good=check(Reservations.affineCall,a=@v/A,s=@v/p)",
        "bad=check(Reservations.affineCall,a=@v/B,s=@v/p)",
        "goodReturn=check(Reservations.affineReturn,a=@v/A,s=@v/p)",
        "badReturn=check(Reservations.affineReturn,a=@v/B,s=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    for id in ["all", "empty", "field", "good", "goodReturn"] {
        assert_eq!(
            get(answer(&w, id), "status"),
            &Json::str("established"),
            "{id}"
        );
    }
    for id in ["bad", "badReturn"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed"))
        );
    }
}
#[test]
fn owned_call_provenance_pair_and_fixed_evidence_keys_preserve_current_sources() {
    let asks = [
        "ok=evaluate(Reservations.returned,a=@v/A,s=@v/p)",
        "bad=evaluate(Reservations.parameter,a=@v/B,s=@v/p)",
    ];
    let mut results = Vec::new();
    for revision in ["r1", "r2"] {
        let input = fixture::input(false, true, revision);
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
fn equal_owner_cross_snapshot_calls_keep_the_actual_failed_snapshot_condition() {
    let r = evaluate_observed_bytes(
        fixture::cross_snapshot_input(),
        &[
            "seed=evaluate(Reservations.seed)",
            "p=evaluate(Reservations.parameter,a=@w/A,s=@v/p)",
            "r=evaluate(Reservations.returned,a=@w/A,s=@v/p)",
            "skip=evaluate(Reservations.skipped,a=@w/A,s=@v/p)",
            "affine=check(Reservations.affineCall,a=@w/A,s=@v/p)",
            "affineReturn=check(Reservations.affineReturn,a=@w/A,s=@v/p)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{w:?}");
    assert_eq!(get(answer(&w, "seed"), "status"), &Json::str("established"));
    for id in ["p", "r", "skip", "affine", "affineReturn"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed"))
        );
        assert!(
            !arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("missing_observation")),
            "invalid parameter must skip missing free body"
        );
    }
}
#[test]
fn failed_inner_call_cannot_be_ignored_by_plain_or_other_owned_outer_parameters() {
    let r = run(&[
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "plain=evaluate(Reservations.invalidIgnored,a=@v/B,s=@v/p)",
        "owned=evaluate(Reservations.invalidIgnoredOwned,a=@v/B,b=@v/A,s=@v/p,t=@v/q)",
        "binding=evaluate(Reservations.invalidLet,a=@v/B,s=@v/p)",
        "boolean=evaluate(Reservations.invalidBoolean,a=@v/B,s=@v/p)",
        "discarded=evaluate(Reservations.invalidDiscardedLet,a=@v/B,s=@v/p)",
        "conditional=evaluate(Reservations.invalidConditional,a=@v/B,s=@v/p)",
        "projection=evaluate(Reservations.invalidProjection,a=@v/B,s=@v/p)",
        "quantified=evaluate(Reservations.invalidForall,a=@v/A)",
        "existential=evaluate(Reservations.invalidExists,a=@v/A)",
        "affine=check(Reservations.ignoredAffine,a=@v/B,s=@v/p)",
        "good=evaluate(Reservations.invalidIgnored,a=@v/A,s=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{w:?}");
    assert_eq!(get(answer(&w, "seed"), "status"), &Json::str("established"));
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    assert_eq!(get(answer(&w, "good"), "status"), &Json::str("established"));
    for id in [
        "plain",
        "owned",
        "binding",
        "boolean",
        "discarded",
        "conditional",
        "projection",
        "quantified",
        "existential",
        "affine",
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed"))
        );
        if id == "quantified" {
            let evaluation = node(&w, &outputs["evaluation"]);
            let proofs = arr(get(evaluation, "evidence"));
            assert!(
                !proofs.is_empty(),
                "既に得た正常false-instance反例を保持する"
            );
            assert!(proofs.iter().all(|r|get(get(node(&w,r),"value"),"kind")==&Json::str("counterexample")));
        }
    }
}

#[test]
fn failed_call_field_projection_preserves_original_condition_and_batch_answers() {
    let result = evaluate_observed_bytes(
        fixture::input(false, true, "r1"),
        &[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
            "direct=evaluate(Reservations.fieldDirect,a=@v/B,s=@v/p)",
            "lexical=evaluate(Reservations.fieldLexical,a=@v/B,s=@v/p)",
            "owner=evaluate(Reservations.failedFieldOwner,a=@v/B,s=@v/p)",
            "ignored=evaluate(Reservations.fieldIgnored,a=@v/B,s=@v/p)",
            "affine=check(Reservations.fieldAffine,a=@v/B,s=@v/p)",
            "ordinary=evaluate(Reservations.fieldDirect,a=@v/A,s=@v/p)",
            "later=evaluate(Reservations.seed)",
        ],
        &mut quiet(),
    );
    let r = match result {
        Ok(r) => r,
        Err(archsig::observed::EvaluationFailure::NotImplemented { feature, .. }) => {
            panic!("field projection lost a known failed condition: {feature}")
        }
        Err(_) => panic!("unexpected input/evaluation failure"),
    };
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    for id in ["seed", "later"] {
        assert_eq!(get(answer(&w, id), "status"), &Json::str("established"));
    }
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    for id in ["direct", "lexical", "owner", "ignored", "affine"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let reasons = arr(get(a, "reasons"));
        assert!(
            reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed"))
        );
        assert!(
            !reasons.iter().any(|r| [
                Json::str("missing_observation"),
                Json::str("unsupported_algorithm")
            ]
            .contains(get(r, "code"))),
            "{id}: {reasons:?}"
        );
    }
    let ordinary = answer(&w, "ordinary");
    assert_eq!(get(ordinary, "status"), &Json::str("undetermined"));
    assert!(
        arr(get(ordinary, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("missing_observation"))
    );
    assert!(
        !arr(get(ordinary, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("condition_failed"))
    );
}
