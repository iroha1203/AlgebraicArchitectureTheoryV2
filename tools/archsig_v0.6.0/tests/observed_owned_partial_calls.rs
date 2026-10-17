//! 数値が通常値でない部分Tupleの所属条件を元入力で確かめる。
#[path = "common/owned_partial_calls.rs"]
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
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
#[test]
fn partial_owned_tuple_checks_members_beside_unbound_numbers() {
    let r = evaluate_observed_bytes(
        fixture::input(false, "r1"),
        &[
            "good=check(Reservations.pcGood,a=@v/A,p=@v/p)",
            "bad=check(Reservations.pcGood,a=@v/B,p=@v/p)",
        ],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_ne!(r.status(), "error", "{:?}", get(&w, "issues"));
    assert_eq!(get(answer(&w, "good"), "status"), &Json::str("established"));
    let bad = answer(&w, "bad");
    assert_eq!(get(bad, "status"), &Json::str("undetermined"));
    assert!(
        arr(get(bad, "reasons"))
            .iter()
            .any(|x| get(x, "code") == &Json::str("condition_failed"))
    );
}

fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input(false, "r1"), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", get(&r.wire(), "issues"));
    r
}
#[test]
fn partial_owned_calls_keep_nested_list_return_and_z_q_binders() {
    let r = run(&[
        "tuple=check(Reservations.pcGood,a=@v/A,p=@v/p)",
        "returned=check(Reservations.pcReturned,a=@v/A,p=@v/p)",
        "returnlist=check(Reservations.pcReturnedList,a=@v/A,p=@v/p)",
        "affine=check(Reservations.pcAffine,a=@v/A,p=@v/p)",
        "qaffine=check(Reservations.pcQAffine,a=@v/A,p=@v/p)",
        "collection=check(Reservations.pcListGood,a=@v/A,p=@v/p,q=@v/q)",
        "nested=check(Reservations.pcNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/r)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for a in arr(get(&w, "answers")) {
        assert_eq!(get(a, "status"), &Json::str("established"));
    }
    // 数値binderを架空のScalar/固定Bindingにしない。
    let mut symbolic_tuple = 0;
    let mut numeric_parameters = std::collections::BTreeSet::new();
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") == &Json::str("Expression") {
            let v = get(n, "value");
            if let Json::Obj(m) = v {
                if let Some(Json::Arr(ps)) = m.get("parameters") {
                    for p in ps {
                        assert!([Json::str("Z"), Json::str("Q")].contains(get(p, "type")));
                        numeric_parameters.insert(get(p, "type").canonical());
                    }
                }
            }
        }
        if get(n, "type") == &Json::str("Evaluation") {
            let v = get(n, "value");
            let source = node(&w, get(v, "expression"));
            let Json::Obj(payload) = get(source, "value") else {
                panic!("source")
            };
            let Some(location) = payload.get("location") else {
                continue;
            };
            let spans = arr(get(location, "span"));
            let (Json::Nat(start), Json::Nat(end)) = (&spans[0], &spans[1]) else {
                panic!("span")
            };
            let law = r.prepared().inputs().law();
            let id = law
                .exprs
                .iter()
                .position(|e| e.span == (*start as usize, *end as usize))
                .unwrap();
            if matches!(law.expr_type(id), Some(archsig::types::Type::Tuple(_))) {
                let Json::Obj(v) = v else {
                    panic!("evaluation")
                };
                assert!(!v.contains_key("value"));
                symbolic_tuple += 1;
            }
        }
    }
    for (id, atoms) in [
        ("collection", vec!["p-owner", "q-owner"]),
        ("nested", vec!["p-owner", "r-owner"]),
        ("returnlist", vec!["p-owner"]),
    ] {
        let claim = node(&w, get(answer(&w, id), "claim"));
        for atom in atoms {
            assert!(
                arr(get(claim, "support"))
                    .iter()
                    .any(|f| matches!(f,Json::Obj(m) if m.get("atom")==Some(&Json::str(atom)))),
                "{id}:{atom}"
            );
        }
        assert!(arr(get(get(claim, "scope"), "snapshots")).contains(&Json::str("v")));
    }
    assert!(symbolic_tuple >= 5);
    assert_eq!(
        numeric_parameters,
        std::collections::BTreeSet::from([Json::str("Z").canonical(), Json::str("Q").canonical()])
    );
    for id in [
        "tuple",
        "qaffine",
        "returned",
        "returnlist",
        "affine",
        "collection",
        "nested",
    ] {
        let a = answer(&w, id);
        assert!(arr(get(a, "reasons")).is_empty());
    }
}
#[test]
fn partial_owned_known_failures_keep_condition_through_returns_and_ignored_calls() {
    let r = run(&[
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "tuple=check(Reservations.pcGood,a=@v/B,p=@v/p)",
        "qaffine=check(Reservations.pcQAffine,a=@v/B,p=@v/p)",
        "returned=check(Reservations.pcReturned,a=@v/B,p=@v/p)",
        "returnlist=check(Reservations.pcReturnedList,a=@v/B,p=@v/p)",
        "collection=check(Reservations.pcListGood,a=@v/A,p=@v/p,q=@v/r)",
        "nested=check(Reservations.pcNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/q)",
        "snapshot=check(Reservations.pcGood,a=@v/A,p=@w/p)",
        "ignored=check(Reservations.pcIgnored,a=@v/B,p=@v/p)",
        "later=evaluate(Reservations.seed)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in [
        "tuple",
        "qaffine",
        "returned",
        "returnlist",
        "collection",
        "nested",
        "snapshot",
        "ignored",
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let rs = arr(get(a, "reasons"));
        let reason = rs
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        assert!(
            !rs.iter()
                .any(|r| get(r, "code") == &Json::str("unsupported_algorithm")),
            "{id}"
        );
        let c = node(&w, get(get(reason, "details"), "condition"));
        assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
        assert!(!arr(get(c, "support")).is_empty());
    }
    assert_eq!(get(answer(&w, "seed"), "status"), &Json::str("established"));
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    assert_eq!(
        get(answer(&w, "later"), "status"),
        &Json::str("established")
    );
}
#[test]
fn partial_owned_numeric_missing_keeps_same_slot_correlation_and_known_members() {
    let r = run(&[
        "unused=evaluate(Reservations.pcMissing,a=@v/A,p=@v/p,q=@v/q)",
        "zero=evaluate(Reservations.pcMissingAffine,a=@v/A,p=@v/p,q=@v/q)",
        "bad=evaluate(Reservations.pcMissing,a=@v/B,p=@v/p,q=@v/q)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for (id, t, v) in [
        ("unused", "Bool", Json::Bool(true)),
        ("zero", "Z", Json::str("0")),
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        let n = node(&w, get(get(a, "outputs"), "value"));
        assert_eq!(get(n, "type"), &Json::str(t));
        assert_eq!(get(n, "value"), &v);
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .filter(|r| get(r, "code") == &Json::str("missing_observation"))
                .flat_map(|r| arr(get(r, "missing")))
                .any(|f| get(f, "snapshot") == &Json::str("v")
                    && get(f, "subject") == &Json::str("q")
                    && get(f, "field") == &Json::str("Reservations.State.free"))
        );
    }
    let bad = answer(&w, "bad");
    assert_eq!(get(bad, "status"), &Json::str("undetermined"));
    assert!(
        arr(get(bad, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("condition_failed"))
    );
    let absent = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &["absent=evaluate(Reservations.pcUnknown,a=@v/A,e=@v/e,q=@v/q)"],
        &mut quiet(),
    )
    .unwrap();
    let absent_wire = absent.wire();
    let a = answer(&absent_wire, "absent");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to"))
    );
    assert!(
        !arr(get(a, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("condition_failed"))
    );
    let u = evaluate_observed_bytes(
        fixture::input(true, "r1"),
        &["unknown=check(Reservations.pcGood,a=@v/A,p=@v/p)"],
        &mut quiet(),
    )
    .unwrap_err();
    assert!(matches!(
        u,
        archsig::observed::EvaluationFailure::NotImplemented { .. }
    ));
    assert!(u.wire().is_none());
}
#[test]
fn partial_owned_calls_preserve_original_inputs_and_current_provenance() {
    let asks = [
        "ok=check(Reservations.pcListGood,a=@v/A,p=@v/p,q=@v/q)",
        "bad=check(Reservations.pcListGood,a=@v/A,p=@v/p,q=@v/r)",
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
fn partial_owned_known_mismatch_after_or_before_unknown_member_keeps_the_same_condition() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &[
            "after=evaluate(Reservations.pcMixed,a=@v/B,e=@v/e,p=@v/p,q=@v/q)",
            "before=evaluate(Reservations.pcMixedReverse,a=@v/B,e=@v/e,p=@v/p,q=@v/q)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in ["after", "before"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        let reasons = arr(get(a, "reasons"));
        let failed = reasons
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        let c = node(&w, get(get(failed, "details"), "condition"));
        assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
        let operands = arr(get(get(c, "value"), "operands"));
        assert_eq!(operands.len(), 2);
        for (operand, id) in operands.iter().zip(["A", "B"]) {
            let n = node(&w, operand);
            assert_eq!(
                get(n, "type"),
                &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
            );
            assert_eq!(
                get(n, "value"),
                &Json::Arr(vec![Json::str("v"), Json::str(id)])
            );
        }
        assert!(
            reasons
                .iter()
                .filter(|r| get(r, "code") == &Json::str("missing_observation"))
                .flat_map(|r| arr(get(r, "missing")))
                .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to"))
        );
    }
}

#[test]
fn partial_owned_blocked_inner_numeric_call_cannot_be_discarded_by_tuple_boundary() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &["wrapped=evaluate(Reservations.pcUnknownNumeric,a=@v/B,e=@v/e,p=@v/r)"],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_ne!(r.status(), "error", "{:?}", get(&w, "issues"));
    let a = answer(&w, "wrapped");
    assert_eq!(
        get(a, "status"),
        &Json::str("undetermined"),
        "未確定の内側所属条件を数値欠測として捨てない: {:?}",
        get(a, "outputs")
    );
    let Json::Obj(o) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!o.contains_key("value"));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to"))
    );
}

#[test]
fn partial_owned_pending_conditions_survive_plain_calls_lexical_forms_and_quantification() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &[
            "plain=evaluate(Reservations.pcPendingPlain,a=@v/B,e=@v/e,p=@v/r)",
            "binding=evaluate(Reservations.pcPendingLet,a=@v/B,e=@v/e)",
            "branch=evaluate(Reservations.pcPendingIf,a=@v/B,e=@v/e)",
            "projection=evaluate(Reservations.pcPendingProjection,a=@v/B,e=@v/e)",
            "field=evaluate(Reservations.pcPendingField,a=@v/B,e=@v/e)",
            "boolean=evaluate(Reservations.pcPendingBool,a=@v/B,e=@v/e)",
            "quantified=evaluate(Reservations.pcPendingQuant,a=@v/B,e=@v/e)",
            "affine=check(Reservations.pcPendingAffine,a=@v/B,e=@v/e)",
            "universal=check(Reservations.pcPendingUniversal,a=@v/B,e=@v/e,p=@v/r)",
            "later=evaluate(Reservations.seed)",
        ],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    for id in [
        "plain",
        "binding",
        "branch",
        "projection",
        "field",
        "boolean",
        "quantified",
        "affine",
        "universal",
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(o) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!o.contains_key("value"), "{id}");
        let reasons = arr(get(a, "reasons"));
        assert!(
            !reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed")),
            "未確定条件を反証済みにしない: {id}"
        );
        assert!(
            reasons
                .iter()
                .filter(|r| get(r, "code") == &Json::str("missing_observation"))
                .flat_map(|r| arr(get(r, "missing")))
                .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to")),
            "元の欠測を残す: {id}"
        );
        assert!(
            !reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("not_implemented")),
            "{id}"
        );
    }
    assert_eq!(
        get(answer(&w, "later"), "status"),
        &Json::str("established")
    );
}

#[test]
fn partial_owned_pending_conditions_in_unselected_branches_allow_the_selected_result() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &[
            "branch=evaluate(Reservations.pcSkipIf,a=@v/B,e=@v/e)",
            "boolean=evaluate(Reservations.pcSkipOr,a=@v/B,e=@v/e)",
        ],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_eq!(r.status(), "complete", "{:?}", get(&w, "issues"));
    for id in ["branch", "boolean"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert_eq!(
            get(node(&w, get(get(a, "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("missing_observation"))
        );
        assert!(
            !arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("condition_failed"))
        );
    }
}

#[test]
fn partial_owned_pending_numeric_condition_keeps_independent_known_mismatch() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &["bad=evaluate(Reservations.pcUnknownNumeric,a=@v/B,e=@v/e,p=@v/p)"],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    let a = answer(&w, "bad");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let failed = arr(get(a, "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .expect("pendingな数値子とは独立に既知owner不等を保持する");
    let c = node(&w, get(get(failed, "details"), "condition"));
    assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
    for (operand, id) in arr(get(get(c, "value"), "operands")).iter().zip(["A", "B"]) {
        let n = node(&w, operand);
        assert_eq!(
            get(n, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
        );
        assert_eq!(
            get(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(id)])
        );
    }
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .filter(|r| get(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(get(r, "missing")))
            .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to"))
    );
}

#[test]
fn partial_owned_false_implies_pending_right_keeps_true_value_and_missing() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &[
            "implication=evaluate(Reservations.pcSkipImplies,a=@v/B,e=@v/e)",
            "universal=check(Reservations.pcSkipImpliesLaw,a=@v/B,e=@v/e)",
            "conjunction=evaluate(Reservations.pcSkipAnd,a=@v/B,e=@v/e)",
            "needed=evaluate(Reservations.pcTrueImplies,a=@v/B,e=@v/e)",
        ],
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    for (id, value) in [
        ("implication", true),
        ("universal", true),
        ("conjunction", false),
    ] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"), "{id}");
        let value_ref = if id == "universal" {
            get(
                get(node(&w, get(get(a, "outputs"), "evaluation")), "value"),
                "value",
            )
        } else {
            get(get(a, "outputs"), "value")
        };
        assert_eq!(get(node(&w, value_ref), "value"), &Json::Bool(value));
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("missing_observation"))
        );
    }
    let a = answer(&w, "needed");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
}

#[test]
fn partial_owned_pending_components_keep_mismatch_across_order_list_returns_and_universal_calls() {
    let mut asks = Vec::new();
    for (id, view) in [
        ("reverse", "pcPendingReverse"),
        ("list", "pcPendingList"),
        ("returned", "pcPendingReturnUse"),
        ("returnlist", "pcPendingReturnListUse"),
        ("separate", "pcPendingTwo"),
        ("universal", "pcPendingUniversal"),
    ] {
        for (suffix, p) in [("good", "r"), ("bad", "p")] {
            asks.push(format!(
                "{id}{suffix}={}(Reservations.{view},a=@v/B,e=@v/e,p=@v/{p})",
                if id == "universal" {
                    "check"
                } else {
                    "evaluate"
                }
            ));
        }
    }
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    let w = r.wire();
    assert_eq!(r.status(), "partial", "{:?}", get(&w, "issues"));
    for a in arr(get(&w, "answers")) {
        let Json::Str(id) = get(a, "id") else {
            panic!("id")
        };
        assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
        let Json::Obj(o) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!o.contains_key("value"), "{id}");
        let reasons = arr(get(a, "reasons"));
        let failed = reasons
            .iter()
            .find(|r| get(r, "code") == &Json::str("condition_failed"));
        assert_eq!(failed.is_some(), id.ends_with("bad"), "{id}");
        if let Some(failed) = failed {
            let c = node(&w, get(get(failed, "details"), "condition"));
            assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
            let operands = arr(get(get(c, "value"), "operands"));
            assert_eq!(operands.len(), 2);
            for (operand, owner) in operands.iter().zip(["A", "B"]) {
                let n = node(&w, operand);
                assert_eq!(
                    get(n, "type"),
                    &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
                );
                assert_eq!(
                    get(n, "value"),
                    &Json::Arr(vec![Json::str("v"), Json::str(owner)])
                );
            }
            assert!(
                arr(get(c, "support"))
                    .iter()
                    .any(|f| matches!(f,Json::Obj(m)if m.get("atom")==Some(&Json::str("p-owner"))))
            );
        }
        assert!(
            reasons
                .iter()
                .filter(|r| get(r, "code") == &Json::str("missing_observation"))
                .flat_map(|r| arr(get(r, "missing")))
                .any(|f| get(f, "field") == &Json::str("Reservations.Reserve.to")),
            "{id}"
        );
    }
}
