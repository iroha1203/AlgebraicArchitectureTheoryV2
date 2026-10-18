//! 自由ownerの実prefixと固定Answer原始参照を元三入力から検査する。
#[path = "common/free_owner_answer_binding.rs"]
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
#[test]
fn free_owner_fixed_answer_refs_match_subject_fibers_keep_paths_order_and_finite_axes() {
    for path in ["$v.value", "$pair.evaluation.value[1]"] {
        let ask = format!("take=check(Reservations.foMixed,p={path})");
        let r = run(
            fixture::input(false, true, "r1"),
            &[
                &ask,
                "v=evaluate(Reservations.foChild,p=@v/p)",
                "pair=evaluate(Reservations.foPair,p=@v/p)",
                "subject=check(Reservations.foMixed,p=@v/p)",
            ],
        );
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        assert_eq!(
            f(answer(&w, "take"), "status"),
            f(answer(&w, "subject"), "status")
        );
        assert_eq!(checked(&w, "take"), 4);
        assert_eq!(checked(&w, "subject"), 4);
        let rows: Vec<_> = arr(f(&w, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("LawInstance")
                    && arr(f(f(n, "value"), "bindings")).len() == 4
            })
            .collect();
        assert_eq!(rows.len(), 8);
        for row in rows {
            let bs = arr(f(f(row, "value"), "bindings"));
            assert_eq!(
                f(node(&w, f(&bs[0], "value")), "value"),
                &Json::Arr(vec![Json::str("v"), Json::str("A")])
            );
            assert_eq!(
                f(node(&w, f(&bs[1], "value")), "value"),
                &Json::Arr(vec![Json::str("v"), Json::str("p")])
            );
        }

        assert_eq!(f(&arr(f(&w, "answers"))[0], "id"), &Json::str("take"));
        let e = node(&w, f(f(answer(&w, "take"), "outputs"), "evaluation"));
        let bindings = arr(f(f(e, "value"), "bindings"));
        assert_eq!(bindings.len(), 1);
        assert_eq!(f(&bindings[0], "name"), &Json::str("p"));
        let original = f(&bindings[0], "value");
        if path == "$v.value" {
            assert_eq!(original, f(f(answer(&w, "v"), "outputs"), "value"));
        } else {
            assert_eq!(
                f(f(node(&w, original), "rule"), "path"),
                &Json::Arr(vec![Json::str("value"), Json::Nat(1)])
            );
        }
        let request = &arr(f(&w, "requests"))[0];
        assert_eq!(arr(f(request, "arguments")).len(), 1);
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
fn free_owner_fixed_answer_empty_fibers_and_known_counterexample_keep_admissible_domains() {
    let r = run(
        fixture::input(false, true, "r1"),
        &[
            "empty=check(Reservations.foEmpty,p=$v.value)",
            "no=check(Reservations.foFalse,p=$v.value)",
            "v=evaluate(Reservations.foChild,p=@w/r)",
        ],
    );
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(f(answer(&w, "empty"), "status"), &Json::str("established"));
    assert_eq!(checked(&w, "empty"), 0);
    assert_eq!(f(answer(&w, "no"), "status"), &Json::str("refuted"));
    assert!(!arr(f(answer(&w, "no"), "evidence")).is_empty());
    let rows: Vec<_> = arr(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("LawInstance")
                && arr(f(f(n, "value"), "bindings")).len() == 2
        })
        .collect();
    assert_eq!(rows.len(), 1);
    let bs = arr(f(f(rows[0], "value"), "bindings"));
    assert_eq!(
        f(node(&w, f(&bs[0], "value")), "value"),
        &Json::Arr(vec![Json::str("w"), Json::str("B")])
    );
}
#[test]
fn free_owner_fixed_answer_preserves_unknown_unprovided_static_invalid_and_fixed_owner_failure() {
    for (producer, code) in [
        (
            "v=evaluate(Reservations.foMissing,p=@v/p,q=@v/r)",
            "missing_observation",
        ),
        (
            "v=evaluate(Reservations.foOpaque,p=@v/p,q=@v/r)",
            "unsupported_algorithm",
        ),
    ] {
        let r = run(
            fixture::input(false, false, "r1"),
            &[
                "seed=evaluate(Reservations.seed)",
                "prior=check(Reservations.prior)",
                "take=check(Reservations.foEq,p=$v.value)",
                "later=check(Reservations.adBool,a=@v/A,flag=$take.evaluation.value)",
                producer,
            ],
        );
        let w = r.wire();
        assert_eq!(r.status(), "partial");
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(
            arr(f(answer(&w, "v"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str(code))
        );
        for id in ["take", "later"] {
            assert_eq!(f(answer(&w, id), "status"), &Json::str("undetermined"));
            for reason in arr(f(answer(&w, "v"), "reasons")) {
                assert!(arr(f(answer(&w, id), "reasons")).contains(reason));
            }
        }
    }
    let unknown = run(
        fixture::input(true, false, "r1"),
        &[
            "take=check(Reservations.foEq,p=$v.value)",
            "v=evaluate(Reservations.foChild,p=@v/p)",
        ],
    );
    let w = unknown.wire();
    assert_eq!(unknown.status(), "partial");
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("undetermined"));
    assert!(
        arr(f(answer(&w, "take"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
    );
    let fixed = run(
        fixture::input(false, false, "r1"),
        &[
            "take=check(Reservations.foEq,a=@v/B,p=$v.value)",
            "v=evaluate(Reservations.foChild,p=@v/p)",
        ],
    );
    let w = fixed.wire();
    assert_eq!(fixed.status(), "partial");
    assert!(
        arr(f(answer(&w, "take"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    for ask in [
        "take=check(Reservations.foEq,p=$v.value)",
        "take=check(Reservations.foEq,p=$v.private.value)",
        "take=check(Reservations.foEq,p=$v.value,p=$v.value)",
    ] {
        let r = evaluate_observed_bytes(
            fixture::input(false, false, "r1"),
            &[ask, "v=evaluate(Reservations.adFlag)"],
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
}
#[test]
fn free_owner_fixed_answer_keeps_producer_completion_and_assignment_scope() {
    for (producer, domain) in [
        (
            "v=evaluate(Reservations.foUniversal,p=@v/p)",
            "all_assignments",
        ),
        (
            "v=evaluate(Reservations.foCompletion,p=@v/p)",
            "all_completions",
        ),
    ] {
        let r = run(
            fixture::input(false, false, "r1"),
            &["take=check(Reservations.foEq,p=$v.value)", producer],
        );
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        let base = f(answer(&w, "v"), "scope");
        let scope = f(answer(&w, "take"), "scope");
        assert_eq!(f(base, "domain"), &Json::str(domain));
        assert_eq!(f(scope, "domain"), f(base, "domain"));
        for q in arr(f(base, "quantifiers")) {
            assert!(arr(f(scope, "quantifiers")).contains(q));
        }
        assert!(arr(f(scope, "quantifiers")).len() > arr(f(base, "quantifiers")).len());
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
fn free_owner_fixed_answer_keeps_input_tables_dag_owner_facts_and_current_sources() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    let asks = [
        "take=check(Reservations.foMixed,p=$v.value)",
        "v=evaluate(Reservations.foChild,p=@v/p)",
    ];
    let i = fixture::input(false, true, "r1");
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
    let relocated = run(fixture::input(false, true, "r2"), &asks);
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
