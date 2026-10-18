//! 固定Answer ownerから元snapshotの実依存fiberを構成する。
#[path = "common/answer_dependent_family.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
use std::collections::BTreeMap;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(m) = j else { panic!("object") };
    m
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input(false, false, "r1"), asks, &mut quiet());
    match r {
        Ok(r) => r,
        Err(e) => {
            if let Some(w) = e.wire() {
                panic!("{:?}", f(&w, "issues"))
            } else {
                panic!("{e:?}")
            }
        }
    }
}
#[test]
fn answer_owner_builds_the_original_dependent_option_fiber() {
    let r = run(&[
        "take=check(Reservations.option_values,a=$owner.value)",
        "owner=evaluate(Reservations.adOwner,a=@v/A)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "owner"), "status"), &Json::str("established"));
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        vec![Json::str("take"), Json::str("owner")]
    );
    let option = Json::Arr(vec![
        Json::str("Option"),
        Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]),
    ]);
    let ds: Vec<_> = arr(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && obj(n)
                    .get("value")
                    .is_some_and(|v| obj(v).get("type") == Some(&option))
        })
        .collect();
    assert_eq!(ds.len(), 2);
    for d in ds {
        assert_eq!(arr(f(f(d, "value"), "elements")).len(), 3);
    }
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn owner_script(a: &str, b: &str) -> String {
    format!("owners=evaluate(Reservations.adOwners,a={a},b={b})")
}
#[test]
fn answer_owner_projections_keep_all_compound_fibers_and_original_fixed_refs() {
    for (law, count) in [
        ("tupled", 2),
        ("subset", 4),
        ("maps", 4),
        ("map_option", 5),
        ("map_tuple", 4),
        ("map_set", 16),
    ] {
        let ask = if law == "tupled" || law == "subset" {
            format!("take=check(Reservations.{law},a=$owners.value[0])")
        } else {
            format!(
                "take=check(Reservations.{law},a=$owners.evaluation.value[0],b=$owners.value[1])"
            )
        };
        let owners = owner_script("@v/A", "@v/B");
        let r = run(&[&ask, &owners]);
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        let a = answer(&w, "take");
        assert_eq!(f(a, "status"), &Json::str("established"));
        let e = node(&w, f(f(a, "outputs"), "evaluation"));
        let source = node(&w, f(f(e, "value"), "expression"));
        let bs = arr(f(f(source, "value"), "bindings"));
        assert_eq!(
            bs.len(),
            if law == "tupled" || law == "subset" {
                1
            } else {
                2
            }
        );
        for b in bs {
            let n = node(&w, f(b, "value"));
            assert_eq!(
                f(n, "type"),
                &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
            );
            assert_eq!(
                f(n, "value"),
                &Json::Arr(vec![
                    Json::str("v"),
                    Json::str(if f(b, "name") == &Json::str("a") {
                        "A"
                    } else {
                        "B"
                    })
                ])
            );
        }
        let proofs: Vec<_> = arr(f(a, "evidence"))
            .iter()
            .map(|r| node(&w, r))
            .filter(|n| {
                obj(n).get("value").is_some_and(|v| {
                    obj(v)
                        .get("data")
                        .is_some_and(|d| obj(d).get("checked") == Some(&Json::Nat(count)))
                })
            })
            .collect();
        assert_eq!(proofs.len(), 1);
        assert_eq!(
            arr(f(f(f(proofs[0], "value"), "data"), "instances")).len(),
            count as usize
        );
        let req = &arr(f(&w, "requests"))[0];
        assert_eq!(arr(f(req, "arguments")).len(), bs.len());
        assert!(
            arr(f(req, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("universal_parameters"))
        );
    }
}
#[test]
fn answer_owner_families_accept_independent_fixed_bool_and_numeric_values() {
    for (law, binding, producer, status) in [
        (
            "adFixed",
            "flag",
            "flag=evaluate(Reservations.adFlag)",
            "established",
        ),
        (
            "adScalar",
            "n",
            "flag=evaluate(Reservations.adZero)",
            "established",
        ),
    ] {
        let ask = format!("take=check(Reservations.{law},a=$owner.value,{binding}=$flag.value)");
        let r = run(&[
            &ask,
            producer,
            "owner=evaluate(Reservations.adOwner,a=@v/A)",
        ]);
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str(status));
        let e = node(&w, f(f(answer(&w, "take"), "outputs"), "evaluation"));
        let bs = arr(f(f(e, "value"), "bindings"));
        assert_eq!(bs.len(), 2);
        assert_eq!(
            f(&bs[1], "value"),
            f(f(answer(&w, "flag"), "outputs"), "value")
        );
    }
    let r = run(&[
        "take=check(Reservations.impossible,a=$owner.value,b=$owner.value)",
        "owner=evaluate(Reservations.adOwner,a=@v/A)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("refuted"));
    assert!(!arr(f(answer(&w, "take"), "evidence")).is_empty());
}
#[test]
fn answer_owner_empty_and_multiple_snapshot_fibers_preserve_declared_domains() {
    let owners = owner_script("@v/Z", "@v/B");
    let r = run(&[
        "cOption=check(Reservations.option_values,a=$owners.value[0])",
        "empty=check(Reservations.tupled,a=$owners.value[0])",
        "empty_map=check(Reservations.maps,a=$owners.value[0],b=$owners.value[1])",
        &owners,
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    for (id, count) in [("cOption", 1), ("empty", 0), ("empty_map", 1)] {
        let a = answer(&w, id);
        assert_eq!(f(a, "status"), &Json::str("established"));
        assert!(arr(f(a, "evidence")).iter().map(|r| node(&w, r)).any(|n| {
            obj(n).get("value").is_some_and(|v| {
                obj(v)
                    .get("data")
                    .is_some_and(|d| obj(d).get("checked") == Some(&Json::Nat(count)))
            })
        }));
    }
    let r = evaluate_observed_bytes(
        fixture::input(false, true, "r1"),
        &[
            "take=check(Reservations.adOwned,a=$owner.value)",
            "owner=evaluate(Reservations.adOwner,a=@w/A)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    let state = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]);
    let values: Vec<_> = arr(f(&w, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &state)
        .collect();
    assert!(!values.is_empty());
    for n in values {
        assert_eq!(arr(f(n, "value"))[0], Json::str("w"));
    }
}
#[test]
fn answer_owner_families_keep_producer_all_completion_and_assignment_scope() {
    for producer in [
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        "owner=evaluate(Reservations.adCompletionOwner,a=@v/A,p=@v/p)",
    ] {
        let r = run(&[
            "take=check(Reservations.option_values,a=$owner.value)",
            producer,
        ]);
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        let producer_scope = f(answer(&w, "owner"), "scope");
        assert_eq!(
            f(producer_scope, "domain"),
            &Json::str(if producer.contains("Universal") {
                "all_assignments"
            } else {
                "all_completions"
            })
        );
        let consumer_scope = f(answer(&w, "take"), "scope");
        assert_eq!(f(consumer_scope, "domain"), f(producer_scope, "domain"));
        for q in arr(f(producer_scope, "quantifiers")) {
            assert!(arr(f(consumer_scope, "quantifiers")).contains(q));
        }
        assert!(
            arr(f(consumer_scope, "quantifiers")).len()
                > arr(f(producer_scope, "quantifiers")).len()
        );
    }
}
#[test]
fn answer_owner_failed_and_unprovided_bindings_keep_conditions_original_reasons_and_order() {
    let input = fixture::input(true, false, "r1");
    for (binding, extra) in [
        ("a=$missing.value", ""),
        ("a=$emptyOwners.value[0]", ""),
        ("a=$owner.evaluation.environment.root", ""),
        ("a=$owner.value,flag=$opaque.value", ",flag"),
    ] {
        let law = if extra.is_empty() {
            "option_values"
        } else {
            "adBool"
        };
        let take = format!("take=check(Reservations.{law},{binding})");
        let r = evaluate_observed_bytes(
            input.clone(),
            &[
                "seed=evaluate(Reservations.seed)",
                "prior=check(Reservations.prior)",
                &take,
                "last=check(Reservations.adBool,a=$owner.value,flag=$take.evaluation.value)",
                "owner=evaluate(Reservations.adOwner,a=@v/A)",
                "missing=evaluate(Reservations.adUnknownOwner,p=@v/p)",
                "opaque=evaluate(Reservations.adOpaque)",
                "emptyOwners=evaluate(Reservations.adEmpty)",
            ],
            &mut quiet(),
        )
        .unwrap();
        let w = r.wire();
        assert_eq!(r.status(), "partial");
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        for id in ["take", "last"] {
            let a = answer(&w, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(obj(f(a, "outputs")).is_empty());
        }
        let take = answer(&w, "take");
        let direct = if binding.contains("missing") {
            "missing"
        } else if binding.contains("opaque") {
            "opaque"
        } else if binding.contains("emptyOwners") {
            "emptyOwners"
        } else {
            "owner"
        };
        assert!(
            arr(f(take, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str(direct))
        );
        if direct == "missing" || direct == "opaque" {
            let a = answer(&w, direct);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(!arr(f(a, "reasons")).is_empty());
        }
        if direct == "emptyOwners" || binding.contains("environment") {
            assert!(
                arr(f(take, "reasons"))
                    .iter()
                    .any(|r| f(r, "request") == &Json::str("take")
                        && f(r, "code") == &Json::str("condition_failed"))
            );
        }
        let source = if binding.contains("emptyOwners") {
            answer(&w, "emptyOwners")
        } else if binding.contains("missing") {
            answer(&w, "missing")
        } else if binding.contains("opaque") {
            answer(&w, "opaque")
        } else {
            answer(&w, "owner")
        };
        for reason in arr(f(source, "reasons")) {
            assert!(arr(f(take, "reasons")).contains(reason));
        }
        for reason in arr(f(take, "reasons")) {
            assert!(arr(f(answer(&w, "last"), "reasons")).contains(reason));
        }
    }
}
fn text(j: &Json) -> &str {
    let Json::Str(s) = j else { panic!("string") };
    s
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
#[test]
fn answer_owner_families_keep_inputs_original_dag_support_and_current_provenance() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    let asks = [
        "take=check(Reservations.option_values,a=$owner.value)",
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
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
    let mut known = 0;
    for n in arr(f(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        assert!(seen.insert(text(f(n, "id")).to_string()));
        for fact in arr(f(n, "support")) {
            let subject = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap()
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|ff| ff.name == text(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!("known fact")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                known += 1;
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
            for location in &origin.locations {
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == location.source)
                    .unwrap();
                assert_eq!(source.revision, "r1");
            }
        }
    }
    assert!(known > 0);
    let producer = run(&[asks[1]]);
    let a = answer(&w, "owner");
    assert_eq!(f(a, "status"), &Json::str("established"));
    // 依存順はownerが先であり、consumerの追加で元producerの導出を変更しない。
    let pw = producer.wire();
    let producer_nodes = arr(f(&pw, "nodes"));
    assert_eq!(&arr(f(&w, "nodes"))[..producer_nodes.len()], producer_nodes);
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
fn answer_owner_families_still_reject_static_invalid_bindings_before_nodes() {
    for take in [
        "take=check(Reservations.option_values,a=$flag.value)",
        "take=check(Reservations.option_values,a=$owners.value[2])",
        "take=check(Reservations.option_values,a=$owners.value[0],bind.a=$owners.value[0])",
        "take=check(Reservations.option_values,unknown=$owners.value[0])",
        "take=check(Reservations.option_values,a=$owners.private.snapshot)",
    ] {
        let outcome = evaluate_observed_bytes(
            fixture::input(false, false, "r1"),
            &[
                take,
                "flag=evaluate(Reservations.adFlag)",
                "owners=evaluate(Reservations.adOwners,a=@v/A,b=@v/B)",
            ],
            &mut quiet(),
        );
        let wire = match outcome {
            Ok(r) => r.wire(),
            Err(e) => e.wire().unwrap(),
        };
        assert_eq!(f(&wire, "status"), &Json::str("invalid"));
        assert!(arr(f(&wire, "nodes")).is_empty());
        assert!(arr(f(&wire, "answers")).is_empty());
    }
}

#[test]
fn answer_owner_fixed_owned_constraints_are_checked_before_finite_family_evaluation() {
    use archsig::observed::prepare_observed;
    for selector in [
        "$owner.value",
        "$owner.evaluation.value",
        "$owners.value[0]",
        "$owners.evaluation.value[0]",
    ] {
        for child in ["r", "p"] {
            let take = format!("take=check(Reservations.adFixedMember,a={selector},p=@v/{child})");
            let asks = [
                take.as_str(),
                "owner=evaluate(Reservations.adOwner,a=@v/A)",
                "owners=evaluate(Reservations.adOwners,a=@v/A,b=@v/B)",
            ];
            let prepared =
                prepare_observed(fixture::input(false, false, "r1"), &asks, &mut quiet()).unwrap();
            assert!(
                prepared.requests().requests()[0]
                    .constraints
                    .iter()
                    .any(|c| c.parameter == "p" && c.dynamic)
            );
            let r = run(&asks);
            let w = r.wire();
            let answer = answer(&w, "take");
            assert_eq!(
                r.status(),
                if child == "p" { "complete" } else { "partial" }
            );
            assert_eq!(
                f(answer, "status"),
                &Json::str(if child == "p" {
                    "refuted"
                } else {
                    "undetermined"
                })
            );
            if child == "r" {
                assert!(obj(f(answer, "outputs")).is_empty());
                assert!(
                    arr(f(answer, "reasons"))
                        .iter()
                        .any(|r| f(r, "code") == &Json::str("condition_failed"))
                );
                assert!(
                    arr(f(answer, "reasons"))
                        .iter()
                        .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
                );
            } else {
                assert!(!arr(f(answer, "evidence")).is_empty());
            }
        }
    }
}
