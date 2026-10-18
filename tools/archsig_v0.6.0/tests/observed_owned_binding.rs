//! 固定ownerと原始Owned参照の同batch束縛。
#[path = "common/owned_binding.rs"]
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
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("object") };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn a<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    match evaluate_observed_bytes(fixture::input(false, false, "r1"), asks, &mut quiet()) {
        Ok(r) => r,
        Err(e) => panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))),
    }
}
#[test]
fn fixed_owned_binding_consumes_matching_values_and_blocks_nonmembers() {
    for child in ["p", "r"] {
        let producer = format!("child=evaluate(Reservations.obChild,p=@v/{child})");
        let r = run(&[
            "take=evaluate(Reservations.obUse,a=@v/A,p=$child.value)",
            &producer,
        ]);
        let w = r.wire();
        assert_eq!(
            f(a(&w, "take"), "status"),
            &Json::str(if child == "p" {
                "established"
            } else {
                "undetermined"
            }),
            "{:?}",
            f(a(&w, "take"), "reasons")
        );
        assert_eq!(
            r.status(),
            if child == "p" { "complete" } else { "partial" }
        );
    }
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
#[test]
fn fixed_owned_binding_preserves_original_refs_paths_order_and_finite_free_axes() {
    for (owner, child, producer) in [
        (
            "@v/A",
            "$child.value",
            "child=evaluate(Reservations.obChild,p=@v/p)",
        ),
        (
            "@v/A",
            "$child.evaluation.value",
            "child=evaluate(Reservations.obChild,p=@v/p)",
        ),
        (
            "$child.value[0]",
            "$child.value[1]",
            "child=evaluate(Reservations.obPair,a=@v/A,p=@v/p)",
        ),
        (
            "$child.evaluation.value[0]",
            "$child.evaluation.value[1]",
            "child=evaluate(Reservations.obPair,a=@v/A,p=@v/p)",
        ),
        (
            "$child.value",
            "@v/p",
            "child=evaluate(Reservations.adOwner,a=@v/A)",
        ),
    ] {
        let value = format!("take=evaluate(Reservations.obUse,bind.a={owner},p={child})");
        let yes = format!("yes=check(Reservations.obEq,a={owner},p={child})");
        let no = format!("no=check(Reservations.obFalse,a={owner},p={child})");
        let family = format!("family=check(Reservations.obFamily,a={owner},p={child})");
        let r = run(&[&value, &no, &family, &yes, producer]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        assert_eq!(
            arr(f(&w, "answers"))
                .iter()
                .map(|a| f(a, "id").clone())
                .collect::<Vec<_>>(),
            ["take", "no", "family", "yes", "child"].map(Json::str)
        );
        for id in ["take", "yes", "family", "child"] {
            assert_eq!(f(a(&w, id), "status"), &Json::str("established"));
        }
        assert_eq!(f(a(&w, "no"), "status"), &Json::str("refuted"));
        let take = a(&w, "take");
        assert_eq!(
            f(node(&w, f(f(take, "outputs"), "value")), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str("p")])
        );
        let evaluation = node(&w, f(f(take, "outputs"), "evaluation"));
        let binding = arr(f(f(evaluation, "value"), "bindings"))
            .iter()
            .find(|b| f(b, "name") == &Json::str("p"))
            .unwrap();
        let checked = node(&w, f(binding, "value"));
        assert_eq!(f(f(checked, "rule"), "name"), &Json::str("binding"));
        assert!(!arr(f(checked, "arguments")).is_empty());
        let original = node(&w, &arr(f(checked, "arguments"))[0]);
        assert_eq!(f(original, "value"), f(checked, "value"));
        assert!(arr(f(checked,"support")).iter().any(|fact| matches!(fact,Json::Obj(m) if m.get("field")==Some(&Json::str("Reservations.State.owner")))));
        assert!(arr(f(a(&w,"family"),"evidence")).iter().any(|r| {
            let n=node(&w,r); matches!(f(n,"value"),Json::Obj(m) if m.get("data").is_some_and(|d| matches!(d,Json::Obj(d) if d.get("checked")==Some(&Json::Nat(3)))))
        }));
    }
}
fn blocked(w: &Json, id: &str, producer: &str) {
    let answer = a(w, id);
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    assert_eq!(f(answer, "outputs"), &Json::obj([] as [(&str, Json); 0]));
    let reasons = arr(f(answer, "reasons"));
    let reason = reasons
        .iter()
        .find(|r| {
            f(r, "code") == &Json::str("condition_failed") && f(r, "request") == &Json::str(id)
        })
        .unwrap();
    assert_eq!(
        f(f(reason, "details"), "construction"),
        &Json::str("projection")
    );
    let condition = node(w, f(f(reason, "details"), "condition"));
    assert_eq!(f(condition, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(condition, "judgment"), "status"), &Json::str("refuted"));
    assert_eq!(arr(f(condition, "evidence")).len(), 1);
    let evidence = node(w, &arr(f(condition, "evidence"))[0]);
    assert_eq!(f(evidence, "type"), &Json::str("Evidence"));
    assert_eq!(f(evidence, "support"), f(condition, "support"));
    assert!(
        reasons
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                && f(f(r, "details"), "request") == &Json::str(producer))
    );
}
#[test]
fn fixed_owned_mismatch_builds_typed_conditions_preserves_reasons_and_independent_results() {
    for (owner, child, producer, extra, direct) in [
        (
            "@v/A",
            "$child.value",
            "child=evaluate(Reservations.obChild,p=@v/r)",
            "owner=evaluate(Reservations.adOwner,a=@v/A)",
            "child",
        ),
        (
            "$owner.value",
            "@v/r",
            "child=evaluate(Reservations.obChild,p=@v/r)",
            "owner=evaluate(Reservations.adOwner,a=@v/A)",
            "owner",
        ),
        (
            "$owner.value",
            "$child.evaluation.value",
            "child=evaluate(Reservations.obChild,p=@v/r)",
            "owner=evaluate(Reservations.adOwner,a=@v/A)",
            "child",
        ),
        (
            "$child.value[0]",
            "$child.evaluation.value[1]",
            "child=evaluate(Reservations.obPair,a=@v/A,p=@v/r)",
            "owner=evaluate(Reservations.adOwner,a=@v/A)",
            "child",
        ),
    ] {
        let take = format!("take=check(Reservations.obFinite,a={owner},p={child})");
        let r = run(&[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
            &take,
            "later=check(Reservations.adBool,a=@v/A,flag=$take.evaluation.value)",
            producer,
            extra,
        ]);
        let w = r.wire();
        assert_eq!(
            r.status(),
            "partial",
            "{owner}/{child}: {:?}",
            f(&w, "issues")
        );
        blocked(&w, "take", direct);
        assert!(arr(f(&w,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Evidence")).any(|n|
            arr(f(n,"support")).iter().any(|fact|matches!(fact,Json::Obj(m)if m.get("field")==Some(&Json::str("Reservations.State.owner"))))));
        assert_eq!(f(a(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(a(&w, "prior"), "status"), &Json::str("refuted"));
        assert_eq!(f(a(&w, "later"), "status"), &Json::str("undetermined"));
        for reason in arr(f(a(&w, "take"), "reasons")) {
            assert!(arr(f(a(&w, "later"), "reasons")).contains(reason));
        }
    }
}
#[test]
fn fixed_owned_binding_rejects_cross_snapshot_and_preserves_producer_quantifiers() {
    let r = evaluate_observed_bytes(
        fixture::input(false, true, "r1"),
        &[
            "take=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)",
            "owner=evaluate(Reservations.adOwner,a=@w/A)",
            "child=evaluate(Reservations.obChild,p=@v/p)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    blocked(&r.wire(), "take", "child");
    for producer in [
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        "owner=evaluate(Reservations.adCompletionOwner,a=@v/A,p=@v/p)",
    ] {
        let r = run(&[
            "take=check(Reservations.obFamily,a=$owner.value,p=$child.value)",
            producer,
            "child=evaluate(Reservations.obChild,p=@v/p)",
        ]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        let ps = f(a(&w, "owner"), "scope");
        let cs = f(a(&w, "take"), "scope");
        assert_eq!(
            f(ps, "domain"),
            &Json::str(if producer.contains("Universal") {
                "all_assignments"
            } else {
                "all_completions"
            })
        );
        assert_eq!(f(cs, "domain"), f(ps, "domain"));
        for q in arr(f(ps, "quantifiers")) {
            assert!(arr(f(cs, "quantifiers")).contains(q));
        }
        assert!(arr(f(cs, "quantifiers")).len() > arr(f(ps, "quantifiers")).len());
    }
}
#[test]
fn fixed_owned_unprovided_and_inapplicable_values_keep_original_reasons() {
    for (owner, child, source, direct) in [
        (
            "$unknown.value",
            "$child.value",
            "unknown=evaluate(Reservations.adUnknownOwner,p=@v/p)",
            "unknown",
        ),
        (
            "$unknown.value",
            "$child.value",
            "unknown=evaluate(Reservations.obOpaqueOwner,a=@v/A,b=@v/B)",
            "unknown",
        ),
        (
            "@v/A",
            "$empty.value[0]",
            "unknown=evaluate(Reservations.adOwner,a=@v/A)",
            "empty",
        ),
        (
            "$child.evaluation.environment.root",
            "@v/p",
            "unknown=evaluate(Reservations.adOwner,a=@v/A)",
            "child",
        ),
    ] {
        // environment.rootはowner型のproducerを選ぶ。
        let child_producer = if owner.contains("environment") {
            "child=evaluate(Reservations.adOwner,a=@v/A)"
        } else {
            "child=evaluate(Reservations.obChild,p=@v/p)"
        };
        let ask = format!("take=evaluate(Reservations.obUse,a={owner},p={child})");
        let r = evaluate_observed_bytes(
            fixture::input(true, false, "r1"),
            &[
                "seed=evaluate(Reservations.seed)",
                &ask,
                "later=evaluate(Reservations.obChild,p=$take.value)",
                source,
                child_producer,
                "empty=evaluate(Reservations.obEmpty)",
            ],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        for id in ["take", "later"] {
            assert_eq!(f(a(&w, id), "status"), &Json::str("undetermined"));
            assert_eq!(f(a(&w, id), "outputs"), &Json::obj([] as [(&str, Json); 0]));
        }
        assert_eq!(f(a(&w, "seed"), "status"), &Json::str("established"));
        assert!(
            arr(f(a(&w, "take"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str(direct))
        );
        for reason in arr(f(a(&w, direct), "reasons")) {
            assert!(arr(f(a(&w, "take"), "reasons")).contains(reason));
        }
        for reason in arr(f(a(&w, "take"), "reasons")) {
            assert!(arr(f(a(&w, "later"), "reasons")).contains(reason));
        }
        if direct == "unknown" {
            assert!(!arr(f(a(&w, direct), "reasons")).is_empty());
        } else {
            blocked(&w, "take", direct);
        }
    }
}
#[test]
fn fixed_owned_binding_keeps_static_invalidity_and_unknown_membership_distinct() {
    for ask in [
        "take=evaluate(Reservations.obUse,a=@v/A,p=$flag.value)",
        "take=evaluate(Reservations.obUse,a=@v/A,p=$pair.value[2])",
        "take=evaluate(Reservations.obUse,a=@v/A,p=$typed.value)",
        "take=evaluate(Reservations.obUse,a=@v/A,p=$child.value,bind.p=$child.value)",
        "take=evaluate(Reservations.obUse,a=@v/A,p=$child.private.value)",
    ] {
        let r = evaluate_observed_bytes(
            fixture::input(false, false, "r1"),
            &[
                ask,
                "flag=evaluate(Reservations.adFlag)",
                "pair=evaluate(Reservations.obPair,a=@v/A,p=@v/p)",
                "typed=evaluate(Reservations.obTyped,a=@v/B,p=@v/r)",
                "child=evaluate(Reservations.obChild,p=@v/p)",
            ],
            &mut quiet(),
        );
        let w = match r {
            Ok(r) => r.wire(),
            Err(e) => e.wire().unwrap(),
        };
        assert_eq!(f(&w, "status"), &Json::str("invalid"));
        assert!(arr(f(&w, "nodes")).is_empty());
        assert!(arr(f(&w, "answers")).is_empty());
    }
    // 未観測の原始所属は「違う」と判断せず、未実装の全補完へ残す。
    assert!(matches!(
        evaluate_observed_bytes(
            fixture::input(true, false, "r1"),
            &[
                "take=check(Reservations.obFalse,a=@v/A,p=$child.value)",
                "child=evaluate(Reservations.obChild,p=@v/p)"
            ],
            &mut quiet()
        ),
        Err(archsig::observed::EvaluationFailure::NotImplemented { .. })
    ));
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
            let Json::Str(s) = &m["node"] else { panic!() };
            out.push(s.clone());
        }
        Json::Obj(m) => m.values().for_each(|j| refs(j, out)),
        Json::Arr(a) => a.iter().for_each(|j| refs(j, out)),
        _ => {}
    }
}
#[test]
fn fixed_owned_binding_preserves_three_inputs_dag_owner_atoms_and_current_provenance() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    let asks = [
        "take=check(Reservations.obFamily,a=$owner.value,p=$child.value)",
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        "child=evaluate(Reservations.obChild,p=@v/p)",
    ];
    let input = fixture::input(false, false, "r1");
    let original = input.clone();
    let before = check_inputs(input.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(input, &asks, &mut quiet()).unwrap();
    assert_eq!(r.status(), "complete");
    let checked = r.prepared().inputs();
    assert_eq!(checked.sources(), &original);
    assert_eq!(checked.inputs(), before.inputs());
    assert_eq!(checked.definitions(), before.definitions());
    assert_eq!(checked.law().declarations, before.law().declarations);
    assert_eq!(checked.law().exprs, before.law().exprs);
    assert_eq!(checked.archmap().snapshots, before.archmap().snapshots);
    let w = r.wire();
    let mut seen = BTreeSet::new();
    let mut owner_atoms = 0;
    for n in arr(f(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        let Json::Str(id) = f(n, "id") else { panic!() };
        assert!(seen.insert(id.clone()));
        for fact in arr(f(n, "support")) {
            let Json::Str(snapshot) = f(fact, "snapshot") else {
                panic!()
            };
            let Json::Str(subject) = f(fact, "subject") else {
                panic!()
            };
            let s = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| &s.id == snapshot)
                .unwrap()
                .subjects
                .iter()
                .find(|s| &s.id == subject)
                .unwrap();
            let origin = if let Json::Obj(m) = fact
                && let Some(Json::Str(field)) = m.get("field")
            {
                let slot = &s.fields.iter().find(|f| &f.name == field).unwrap().slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!()
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                if field == "Reservations.State.owner" {
                    owner_atoms += 1;
                }
                origin
            } else {
                &s.origin
            };
            let o = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            for loc in &o.locations {
                assert_eq!(
                    checked
                        .archmap()
                        .sources
                        .iter()
                        .find(|s| s.id == loc.source)
                        .unwrap()
                        .revision,
                    "r1"
                );
            }
        }
    }
    assert!(owner_atoms > 0);
    let moved =
        evaluate_observed_bytes(fixture::input(false, false, "r2"), &asks, &mut quiet()).unwrap();
    let mw = moved.wire();
    assert_eq!(f(&w, "nodes"), f(&mw, "nodes"));
    assert_eq!(f(&w, "answers"), f(&mw, "answers"));
    assert_ne!(f(&w, "inputs"), f(&mw, "inputs"));
    assert!(
        moved
            .prepared()
            .inputs()
            .archmap()
            .sources
            .iter()
            .all(|s| s.revision == "r2")
    );
}
#[test]
fn fixed_owned_bindings_flow_through_nested_view_calls_and_successive_producers() {
    let r = run(&[
        "last=evaluate(Reservations.obUse,a=@v/A,p=$next.value)",
        "raw=evaluate(Reservations.obChild,p=$first.value)",
        "finite=check(Reservations.obFinite,a=@v/A,p=$next.value)",
        "next=evaluate(Reservations.obCall,a=@v/A,p=$first.value)",
        "first=evaluate(Reservations.obUse,a=@v/A,p=$child.value)",
        "child=evaluate(Reservations.obChild,p=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete", "{:?}", f(&w, "issues"));
    for id in ["first", "next", "last", "raw"] {
        let answer = a(&w, id);
        assert_eq!(f(answer, "status"), &Json::str("established"));
        assert_eq!(
            f(node(&w, f(f(answer, "outputs"), "value")), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str("p")])
        );
    }
    assert_eq!(f(a(&w, "finite"), "status"), &Json::str("refuted"));
    assert!(!arr(f(a(&w, "finite"), "evidence")).is_empty());
}
