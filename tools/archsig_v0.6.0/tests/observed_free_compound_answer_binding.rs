//! 自由ownerの実prefixと固定複合Answer値を元三入力から検査する。
#[path = "common/completion_evidence.rs"]
mod completion_evidence;
#[path = "common/free_compound_answer_binding.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        ObservedEvaluation,
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
fn run(input: archsig::observed::input::InputSources, asks: &[&str]) -> ObservedEvaluation {
    evaluate_observed_bytes(input, asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().map(|w| f(&w, "issues").clone())))
}
fn checked(w: &Json, id: &str) -> u64 {
    arr(f(answer(w, id), "evidence"))
        .iter()
        .find_map(|r| {
            let Json::Obj(m) = f(node(w, r), "value") else {
                return None;
            };
            let Json::Obj(d) = m.get("data")? else {
                return None;
            };
            let Json::Nat(n) = d.get("checked")? else {
                return None;
            };
            Some(*n)
        })
        .unwrap()
}
fn rows(w: &Json) -> Vec<&Json> {
    arr(f(w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("LawInstance")
                && arr(f(f(n, "value"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("a"))
        })
        .collect()
}
#[test]
fn free_compound_answer_members_paths_multiple_owners_and_finite_axes_keep_actual_fibers() {
    for (law, producer, path, owners) in [
        ("fcOption", "cbOption,p=@v/p", "$v.value", vec!["A"]),
        ("fcList", "cbList,p=@w/p,q=@w/q", "$v.value", vec!["A"]),
        ("fcSet", "cbSet,p=@v/p,q=@v/q", "$v.value", vec!["A"]),
        (
            "fcList",
            "cbWrapped,p=@v/p,q=@v/q",
            "$v.evaluation.value[1]",
            vec!["A"],
        ),
        (
            "fcTuple",
            "cbTuple,p=@v/p,q=@v/r",
            "$v.value",
            vec!["A", "B"],
        ),
        (
            "fcNested",
            "cbNested,p=@w/p,q=@w/r",
            "$v.value",
            vec!["A", "B"],
        ),
        ("fcMap", "cbMap,m=@v/m", "$v.value", vec!["A", "B"]),
        (
            "fcMapWrapped",
            "cbMapWrapped,m=@w/m",
            "$v.value",
            vec!["A", "B"],
        ),
    ] {
        let take = format!("take=check(Applications.{law},x={path})");
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(fixture::input("known", "r1"), &[&take, &make]);
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        assert_eq!(checked(&w, "take"), 2);
        let rr = rows(&w);
        assert_eq!(rr.len(), 2);
        let snapshot = if producer.contains("@w/") { "w" } else { "v" };
        let mut flags = std::collections::BTreeSet::new();
        for row in rr {
            let bs = arr(f(f(row, "value"), "bindings"));
            assert_eq!(bs.len(), owners.len() + 2);
            for (i, owner) in owners.iter().enumerate() {
                assert_eq!(
                    f(node(&w, f(&bs[i], "value")), "value"),
                    &Json::Arr(vec![Json::str(snapshot), Json::str(*owner)])
                );
            }
            let Json::Bool(flag) = f(node(&w, f(bs.last().unwrap(), "value")), "value") else {
                panic!()
            };
            flags.insert(*flag);
        }
        assert_eq!(flags, [false, true].into());
        assert_eq!(f(&arr(f(&w, "answers"))[0], "id"), &Json::str("take"));
        let evaluation = node(&w, f(f(answer(&w, "take"), "outputs"), "evaluation"));
        let bs = arr(f(f(evaluation, "value"), "bindings"));
        assert_eq!(bs.len(), 1);
        assert_eq!(f(&bs[0], "name"), &Json::str("x"));
        let original = f(&bs[0], "value");
        if path == "$v.value" {
            assert_eq!(original, f(f(answer(&w, "v"), "outputs"), "value"));
        } else {
            assert_eq!(
                f(f(node(&w, original), "rule"), "path"),
                &Json::Arr(vec![Json::str("value"), Json::Nat(1)])
            );
        }
        let request = &arr(f(&w, "requests"))[0];
        assert_eq!(
            f(&arr(f(request, "arguments"))[0], "origin"),
            &Json::str("explicit")
        );
        assert!(
            arr(f(request, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("universal_parameters"))
        );
    }
}
#[test]
fn free_compound_answer_empty_members_map_total_domain_and_counterexample_are_distinct() {
    let r = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcEmpty,x=$v.value[0],xs=$v.value[1],ys=$v.value[2])",
            "v=evaluate(Applications.cbEmpty)",
        ],
    );
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(checked(&w, "take"), 4);
    assert_eq!(rows(&w).len(), 4);
    let r = run(
        fixture::input("empty", "r1"),
        &[
            "take=check(Applications.fcDomain,x=$v.value)",
            "v=evaluate(Applications.cbMap,m=@v/m)",
        ],
    );
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(checked(&w, "take"), 2);
    for row in rows(&w) {
        let bs = arr(f(f(row, "value"), "bindings"));
        let Json::Arr(owner) = f(node(&w, f(&bs[0], "value")), "value") else {
            panic!()
        };
        assert_eq!(owner[1], Json::str("Z"));
    }
    let r = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcFalse,x=$v.value)",
            "v=evaluate(Applications.cbList,p=@v/p,q=@v/r)",
        ],
    );
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(checked(&w, "take"), 0);
    assert!(rows(&w).is_empty());
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
    let r = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcFalse,x=$v.value)",
            "v=evaluate(Applications.cbList,p=@w/p,q=@w/q)",
        ],
    );
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(rows(&w).len(), 1);
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("refuted"));
    assert!(!arr(f(answer(&w, "take"), "evidence")).is_empty());
}
#[test]
fn free_compound_answer_unknown_unprovided_fixed_failures_and_mixed_fibers_are_preserved() {
    for (producer, code) in [
        ("cbMissing,p=@v/p", "missing_observation"),
        ("cbOpaque,p=@v/p,q=@v/q", "unsupported_algorithm"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(
            fixture::input("stop", "r1"),
            &[
                "take=check(Applications.fcList,x=$v.value)",
                &make,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
            ],
        );
        let w = r.wire();
        assert_eq!(r.status(), "partial");
        assert_eq!(f(answer(&w, "v"), "status"), &Json::str("undetermined"));
        assert!(
            arr(f(answer(&w, "v"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str(code))
        );
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        for id in ["take", "later"] {
            for reason in arr(f(answer(&w, "v"), "reasons")) {
                assert!(arr(f(answer(&w, id), "reasons")).contains(reason));
            }
        }
    }
    for (law, producer) in [
        ("fcList", "cbList,p=@v/p,q=@v/q"),
        ("fcDomain", "cbMap,m=@v/m"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let take = format!("take=check(Applications.{law},x=$v.value)");
        let r = run(fixture::input("unknown_owner", "r1"), &[&take, &make]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        let (domain, _) = completion_evidence::established_cases(&w, "take", 1);
        completion_evidence::original_owner_is_missing(&r, "v");
        completion_evidence::original_owner_is_missing(&r, "w");
        assert!(
            arr(f(domain, "support"))
                .iter()
                .any(|fact| matches!(fact, Json::Obj(fields) if fields.get("atom") == Some(&Json::str("m-states"))))
        );
        assert_eq!(
            f(f(answer(&w, "take"), "scope"), "domain"),
            &Json::str("all_completions")
        );
        assert!(
            !arr(f(answer(&w, "take"), "reasons"))
                .iter()
                .any(|reason| f(reason, "code") == &Json::str("unsupported_algorithm"))
        );
        let producer = f(f(answer(&w, "v"), "outputs"), "value");
        let instances = rows(&w);
        assert_eq!(instances.len(), if law == "fcList" { 2 } else { 1 });
        for instance in instances {
            let bindings = arr(f(f(instance, "value"), "bindings"));
            assert_eq!(
                f(
                    node(
                        &w,
                        f(
                            bindings
                                .iter()
                                .find(|b| f(b, "name") == &Json::str("a"))
                                .unwrap(),
                            "value"
                        )
                    ),
                    "value"
                ),
                &Json::Arr(vec![Json::str("v"), Json::str("A")])
            );
            assert_eq!(
                f(
                    bindings
                        .iter()
                        .find(|b| f(b, "name") == &Json::str("x"))
                        .unwrap(),
                    "value"
                ),
                producer
            );
        }
    }
    let r = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcList,a=@v/B,x=$v.value)",
            "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)",
        ],
    );
    let w = r.wire();
    assert_eq!(r.status(), "partial");
    assert!(
        arr(f(answer(&w, "take"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    let mixed = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcTuple,a=@v/A,x=$v.value)",
            "v=evaluate(Applications.cbTuple,p=@v/p,q=@v/r)",
        ],
    );
    assert_eq!(mixed.status(), "complete");
    assert_eq!(checked(&mixed.wire(), "take"), 2);
    let Err(error) = evaluate_observed_bytes(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.fcList,x=$v.value)",
            "v=evaluate(Applications.seed)",
        ],
        &mut quiet(),
    ) else {
        panic!("invalid binding accepted")
    };
    let w = error.wire().unwrap();
    assert_eq!(f(&w, "status"), &Json::str("invalid"));
    assert!(arr(f(&w, "nodes")).is_empty());
    assert!(arr(f(&w, "answers")).is_empty());
}
#[test]
fn free_compound_answer_inherits_producer_completion_and_universal_scope() {
    for (producer, domain) in [
        ("fcMapAll,m=@v/m", "all_assignments"),
        ("fcMapCompletion,m=@v/m,p=@v/p", "all_completions"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(
            fixture::input("stop", "r1"),
            &["take=check(Applications.fcMap,x=$v.value)", &make],
        );
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        let original = f(answer(&w, "v"), "scope");
        let actual = f(answer(&w, "take"), "scope");
        assert_eq!(f(actual, "domain"), f(original, "domain"));
        assert_eq!(f(original, "domain"), &Json::str(domain));
        for q in arr(f(original, "quantifiers")) {
            assert!(arr(f(actual, "quantifiers")).contains(q));
        }
        assert!(arr(f(actual, "quantifiers")).len() > arr(f(original, "quantifiers")).len());
        assert_eq!(checked(&w, "take"), 2);
    }
}

fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
            let Json::Str(s) = &m["node"] else { panic!() };
            out.push(s.clone());
        }
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
#[test]
fn free_compound_answer_keeps_three_inputs_dag_map_owner_facts_and_current_sources() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    let asks = [
        "take=check(Applications.fcMap,x=$v.value)",
        "v=evaluate(Applications.cbMap,m=@v/m)",
    ];
    let i = fixture::input("known", "r1");
    let original = i.clone();
    let before = check_inputs(i.clone(), &mut quiet()).unwrap();
    let r = run(i, &asks);
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
    let mut atoms = BTreeSet::new();
    for n in arr(f(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        let Json::Str(id) = f(n, "id") else { panic!() };
        assert!(seen.insert(id.clone()));
        for fact in arr(f(n, "support")) {
            let Json::Str(snap) = f(fact, "snapshot") else {
                panic!()
            };
            let Json::Str(subject) = f(fact, "subject") else {
                panic!()
            };
            let s = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| &s.id == snap)
                .unwrap()
                .subjects
                .iter()
                .find(|s| &s.id == subject)
                .unwrap();
            let origin = if let Json::Obj(m) = fact
                && let Some(Json::Str(field)) = m.get("field")
            {
                let archsig::archmap::Slot::Known { atom, origin, .. } =
                    &s.fields.iter().find(|f| &f.name == field).unwrap().slot
                else {
                    panic!()
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                atoms.insert(atom.clone());
                origin
            } else {
                &s.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            for loc in &origin.locations {
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
    assert!(atoms.contains("p-owner"));
    let relocated = run(fixture::input("known", "r2"), &asks);
    assert!(
        relocated
            .prepared()
            .inputs()
            .archmap()
            .sources
            .iter()
            .all(|s| s.revision == "r2")
    );
    let moved = relocated.wire();
    assert_eq!(f(&w, "nodes"), f(&moved, "nodes"));
    assert_eq!(f(&w, "answers"), f(&moved, "answers"));
    assert_ne!(f(&w, "inputs"), f(&moved, "inputs"));
}

#[test]
fn free_compound_answer_dynamic_public_projection_failure_keeps_conditions_and_batch_results() {
    for (law, binding, path, producer) in [
        ("fcMap", "x", "$v.value.some[99]", "cbMapWrapped,m=@v/m"),
        ("fcMap", "x", "$v.value.some", "fcMapNone"),
        ("fcPrimitive", "p", "$v.value.some", "cbNone"),
    ] {
        let take = format!("take=check(Applications.{law},{binding}={path})");
        let make = format!("v=evaluate(Applications.{producer})");
        let r = match evaluate_observed_bytes(
            fixture::input("known", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
                &take,
                &make,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
                "last=evaluate(Applications.seed)",
            ],
            &mut quiet(),
        ) {
            Ok(r) => r,
            Err(archsig::observed::EvaluationFailure::NotImplemented { feature, .. }) => {
                panic!("dynamic projection escaped typed condition: {feature}")
            }
            Err(e) => panic!("{:?}", e.wire().map(|w| f(&w, "issues").clone())),
        };
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        for id in ["seed", "v", "last"] {
            assert_eq!(f(answer(&w, id), "status"), &Json::str("established"));
        }
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(!arr(f(answer(&w, "prior"), "evidence")).is_empty());
        for id in ["take", "later"] {
            assert_eq!(f(answer(&w, id), "status"), &Json::str("undetermined"));
            assert_eq!(
                f(answer(&w, id), "outputs"),
                &Json::obj([] as [(&str, Json); 0])
            );
        }
        let reasons = arr(f(answer(&w, "take"), "reasons"));
        let reason = reasons
            .iter()
            .find(|r| f(r, "code") == &Json::str("condition_failed"))
            .unwrap();
        assert_eq!(
            f(f(reason, "details"), "construction"),
            &Json::str("projection")
        );
        let condition = node(&w, f(f(reason, "details"), "condition"));
        assert_eq!(f(condition, "type"), &Json::str("Proposition"));
        assert_eq!(f(f(condition, "judgment"), "status"), &Json::str("refuted"));
        assert!(!arr(f(condition, "evidence")).is_empty());
        assert!(arr(f(condition, "arguments")).contains(f(f(answer(&w, "v"), "outputs"), "value")));
        assert!(
            reasons
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str("v"))
        );
        for reason in reasons {
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
        assert!(
            arr(f(answer(&w, "later"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str("take"))
        );
        let request = &arr(f(&w, "requests"))[2];
        assert_eq!(arr(f(request, "arguments")).len(), 1);
        assert!(
            arr(f(request, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("universal_parameters"))
        );
    }
}
