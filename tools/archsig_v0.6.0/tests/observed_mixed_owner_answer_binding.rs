//! 固定/自由ownerの実prefixと固定複合Answer値を元三入力から検査する。
#[path = "common/mixed_owner_answer_binding.rs"]
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
    evaluate_observed_bytes(input, asks, &mut quiet()).unwrap_or_else(|e| match e {
        archsig::observed::EvaluationFailure::NotImplemented { feature, .. } => {
            panic!("unimplemented: {feature}")
        }
        e => panic!("{:?}", e.wire().map(|w| f(&w, "issues").clone())),
    })
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
                && arr(f(f(n, "value"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("x"))
                && arr(f(f(n, "value"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("b"))
        })
        .collect()
}
#[test]
fn mixed_owner_compounds_keep_fixed_conditions_actual_free_fibers_and_original_values() {
    for (law, producer, path, fixed, snap, owner, other) in [
        (
            "mxOptionLaw",
            "mxOption,p=@v/p,q=@v/r",
            "$v.value",
            "a",
            "v",
            "A",
            "B",
        ),
        (
            "mxListLaw",
            "mxList,p=@w/p,q=@w/r",
            "$v.value",
            "a",
            "w",
            "A",
            "B",
        ),
        (
            "mxSetLaw",
            "mxSet,p=@v/p,q=@v/r",
            "$v.value",
            "b",
            "v",
            "B",
            "A",
        ),
        (
            "mxTuple",
            "mxAll,p=@v/p,q=@v/r",
            "$v.value",
            "a",
            "v",
            "A",
            "B",
        ),
        (
            "fcNested",
            "cbNested,p=@w/p,q=@w/r",
            "$v.value",
            "b",
            "w",
            "B",
            "A",
        ),
        ("fcMap", "cbMap,m=@v/m", "$v.value", "a", "v", "A", "B"),
        (
            "fcMapWrapped",
            "cbMapWrapped,m=@w/m",
            "$v.value",
            "b",
            "w",
            "B",
            "A",
        ),
        (
            "mxListLaw",
            "mxWrapped,p=@v/p,q=@v/r",
            "$v.evaluation.value[1].some",
            "a",
            "v",
            "A",
            "B",
        ),
    ] {
        let explicit = format!("@{snap}/{owner}");
        let selected = if fixed == "a" { "$a.value" } else { &explicit };
        let take = format!("take=check(Applications.{law},{fixed}={selected},x={path})");
        let make = format!("v=evaluate(Applications.{producer})");
        let a = format!("a=evaluate(Applications.cbOwner,a=@{snap}/{owner})");
        let r = run(fixture::input("known", "r1"), &[&take, &make, &a]);
        assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        assert_eq!(checked(&w, "take"), 2);
        let rr = rows(&w);
        assert_eq!(rr.len(), 2);
        let mut flags = std::collections::BTreeSet::new();
        for row in rr {
            let bs = arr(f(f(row, "value"), "bindings"));
            assert_eq!(bs.len(), 4);
            let free = if fixed == "a" { "b" } else { "a" };
            let i = if fixed == "a" { 1 } else { 0 };
            assert_eq!(f(&bs[i], "name"), &Json::str(free));
            assert_eq!(
                f(node(&w, f(&bs[i], "value")), "value"),
                &Json::Arr(vec![Json::str(snap), Json::str(other)])
            );
            assert_eq!(f(&bs[2], "name"), &Json::str("x"));
            let Json::Bool(flag) = f(node(&w, f(&bs[3], "value")), "value") else {
                panic!()
            };
            flags.insert(*flag);
        }
        assert_eq!(flags, [false, true].into());
        assert_eq!(f(&arr(f(&w, "answers"))[0], "id"), &Json::str("take"));
        let e = node(&w, f(f(answer(&w, "take"), "outputs"), "evaluation"));
        let bs = arr(f(f(e, "value"), "bindings"));
        assert_eq!(bs.len(), 2);
        let x = bs.iter().find(|b| f(b, "name") == &Json::str("x")).unwrap();
        if path == "$v.value" {
            assert_eq!(f(x, "value"), f(f(answer(&w, "v"), "outputs"), "value"));
        } else {
            assert_eq!(
                f(f(node(&w, f(x, "value")), "rule"), "path"),
                &Json::Arr(vec![Json::str("value"), Json::Nat(1), Json::str("some")])
            );
        }
        if fixed == "a" {
            let b = bs.iter().find(|b| f(b, "name") == &Json::str("a")).unwrap();
            assert_eq!(f(b, "value"), f(f(answer(&w, "a"), "outputs"), "value"));
        }
        let req = &arr(f(&w, "requests"))[0];
        assert_eq!(arr(f(req, "arguments")).len(), 2);
        assert!(
            arr(f(req, "arguments"))
                .iter()
                .all(|a| f(a, "origin") == &Json::str("explicit"))
        );
        assert!(
            arr(f(req, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("universal_parameters"))
        );
    }
}
fn condition<'a>(w: &'a Json, id: &str) -> &'a Json {
    let a = answer(w, id);
    let reason = arr(f(a, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let c = node(w, f(f(reason, "details"), "condition"));
    assert_eq!(f(c, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(c, "judgment"), "status"), &Json::str("refuted"));
    assert!(!arr(f(c, "evidence")).is_empty());
    c
}
#[test]
fn mixed_fixed_owner_failures_keep_original_operands_and_never_become_empty_success() {
    for (law, producer, fixed, bad) in [
        ("mxOptionLaw", "mxOption,p=@v/p,q=@v/r", "a", "@v/B"),
        ("mxListLaw", "mxList,p=@v/p,q=@v/r", "b", "@v/A"),
        ("mxSetLaw", "mxSet,p=@v/p,q=@v/r", "a", "@w/A"),
        ("fcNested", "cbNested,p=@v/p,q=@v/r", "a", "@v/B"),
        ("fcMap", "cbMap,m=@v/m", "a", "@v/B"),
        ("fcMapWrapped", "cbMapWrapped,m=@v/m", "b", "@v/A"),
        (
            "mxConflictLaw",
            "mxConflict,p=@v/p,q=@v/r,r=@v/p",
            "a",
            "@v/B",
        ),
    ] {
        let take = format!("take=check(Applications.{law},{fixed}=$a.value,x=$v.value)");
        let a = format!("a=evaluate(Applications.cbOwner,a={bad})");
        let v = format!("v=evaluate(Applications.{producer})");
        let r = run(
            fixture::input("known", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
                &take,
                &v,
                &a,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
            ],
        );
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let c = condition(&w, "take");
        let inputs = arr(f(f(c, "value"), "operands"));
        assert!(inputs.contains(f(f(answer(&w, "v"), "outputs"), "value")));
        assert!(inputs.contains(f(f(answer(&w, "a"), "outputs"), "value")));
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str("undetermined"));
        assert_eq!(
            f(answer(&w, "take"), "outputs"),
            &Json::obj([] as [(&str, Json); 0])
        );
        assert!(rows(&w).is_empty());
        for reason in arr(f(answer(&w, "take"), "reasons")) {
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
        assert!(
            arr(f(answer(&w, "later"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str("take"))
        );
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(!arr(f(answer(&w, "prior"), "evidence")).is_empty());
    }
}
#[test]
fn mixed_empty_values_map_total_domain_no_admissible_fiber_and_counterexample_are_distinct() {
    for (mode, take, make, count) in [
        (
            "known",
            "take=check(Applications.mxEmptyLaw,a=@v/A,x=$v.value[0],xs=$v.value[1],ys=$v.value[2])",
            "v=evaluate(Applications.mxEmpty)",
            4,
        ),
        (
            "empty",
            "take=check(Applications.fcMap,a=@v/Z,x=$v.value)",
            "v=evaluate(Applications.cbMap,m=@v/m)",
            12,
        ),
        (
            "empty",
            "take=check(Applications.fcMap,b=@v/B,x=$v.value)",
            "v=evaluate(Applications.cbMap,m=@v/m)",
            4,
        ),
        (
            "known",
            "take=check(Applications.mxConflictLaw,a=@v/A,x=$v.value)",
            "v=evaluate(Applications.mxConflict,p=@v/p,q=@v/r,r=@v/p)",
            0,
        ),
    ] {
        let r = run(fixture::input(mode, "r1"), &[take, make]);
        assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        assert_eq!(checked(&w, "take"), count);
        assert_eq!(rows(&w).len() as u64, count);
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
        if mode == "empty" && take.contains("b=@") {
            for row in rows(&w) {
                let bs = arr(f(f(row, "value"), "bindings"));
                let Json::Arr(a) = f(node(&w, f(&bs[0], "value")), "value") else {
                    panic!()
                };
                assert_eq!(a[1], Json::str("Z"));
            }
        }
    }
    let r = run(
        fixture::input("known", "r1"),
        &[
            "take=check(Applications.mxFalse,a=@v/A,x=$v.value)",
            "v=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
        ],
    );
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(rows(&w).len(), 1);
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("refuted"));
    assert!(!arr(f(answer(&w, "take"), "evidence")).is_empty());
}
#[test]
fn mixed_completed_owners_keep_fixed_producer_scope_and_actual_fibers() {
    for (law, producer, fixed, mode) in [
        (
            "mxTuple",
            "mxAll,p=@v/p,q=@v/r",
            "a=@v/A",
            "unknown_free_owner",
        ),
        ("fcMap", "cbMap,m=@v/m", "b=@v/B", "unknown_owner"),
        ("fcMap", "fcMapAll,m=@v/m", "a=@v/A", "unknown_owner"),
    ] {
        let take = format!("take=check(Applications.{law},{fixed},x=$v.value)");
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(fixture::input(mode, "r1"), &[&take, &make]);
        assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        let a = answer(&w, "take");
        assert_eq!(f(a, "status"), &Json::str("established"));
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        let rr = rows(&w);
        assert_eq!(rr.len(), 2);
        let mut flags = std::collections::BTreeSet::new();
        for row in rr {
            let bs = arr(f(f(row, "value"), "bindings"));
            assert_eq!(bs.len(), 4);
            let free = if fixed.starts_with("a=") { "b" } else { "a" };
            let expected = if free == "b" { "B" } else { "A" };
            let owner = bs
                .iter()
                .find(|b| f(b, "name") == &Json::str(free))
                .unwrap();
            assert_eq!(
                f(node(&w, f(owner, "value")), "value"),
                &Json::Arr(vec![Json::str("v"), Json::str(expected)])
            );
            let x = bs.iter().find(|b| f(b, "name") == &Json::str("x")).unwrap();
            assert_eq!(f(x, "value"), f(f(answer(&w, "v"), "outputs"), "value"));
            let flag = bs
                .iter()
                .find(|b| f(b, "name") == &Json::str("flag"))
                .unwrap();
            let Json::Bool(value) = f(node(&w, f(flag, "value")), "value") else {
                panic!()
            };
            flags.insert(*value);
        }
        assert_eq!(flags, [false, true].into());
        assert!(
            arr(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("missing_observation"))
        );
        assert!(
            !arr(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        );
        let producer_quantifiers = arr(f(f(answer(&w, "v"), "scope"), "quantifiers"));
        for q in producer_quantifiers {
            assert!(arr(f(f(a, "scope"), "quantifiers")).contains(q));
        }
    }
}
#[test]
fn mixed_ambiguous_free_owner_keeps_actual_fibers_and_completion_pair() {
    for (law, state, status) in [
        ("mxTuple", "complete", "established"),
        ("mxFalse", "partial", "undetermined"),
    ] {
        let take = format!("take=check(Applications.{law},a=@v/A,x=$v.value)");
        let r = run(
            fixture::input("ambiguous_free_owner", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                &take,
                "v=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
            ],
        );
        assert_eq!(r.status(), state, "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        let a = answer(&w, "take");
        assert_eq!(f(a, "status"), &Json::str(status));
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        let rr = rows(&w);
        assert_eq!(rr.len(), if law == "mxTuple" { 4 } else { 2 });
        let mut owners = std::collections::BTreeSet::new();
        for row in rr {
            let bs = arr(f(f(row, "value"), "bindings"));
            let b = bs.iter().find(|b| f(b, "name") == &Json::str("b")).unwrap();
            let Json::Arr(owner) = f(node(&w, f(b, "value")), "value") else {
                panic!()
            };
            assert_eq!(owner[0], Json::str("v"));
            let Json::Str(owner) = &owner[1] else {
                panic!()
            };
            owners.insert(owner.clone());
            let x = bs.iter().find(|b| f(b, "name") == &Json::str("x")).unwrap();
            assert_eq!(f(x, "value"), f(f(answer(&w, "v"), "outputs"), "value"));
        }
        if law == "mxFalse" {
            assert!(arr(f(a, "evidence")).iter().any(|r| {
                let evidence = node(&w, r);
                f(f(evidence, "value"), "kind") == &Json::str("completion_pair")
            }));
        }
        assert_eq!(owners, ["A".to_owned(), "B".to_owned()].into());
        assert!(arr(f(a, "reasons")).iter().any(|r| {
            f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing"))
                    .iter()
                    .any(|m| f(m, "subject") == &Json::str("r"))
                && !arr(f(r, "dependencies")).is_empty()
        }));
    }
}
#[test]
fn mixed_unknown_unprovided_projection_failures_keep_scope_reasons_and_independent_answers() {
    for (producer, code) in [
        ("mxMissing", "missing_observation"),
        ("mxOpaque", "unsupported_algorithm"),
    ] {
        let make = format!("v=evaluate(Applications.{producer},p=@v/p,q=@v/r)");
        let r = run(
            fixture::input("stop", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
                "take=check(Applications.mxFalse,a=@v/A,x=$v.value)",
                &make,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
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
        for id in ["take", "later"] {
            for reason in arr(f(answer(&w, "v"), "reasons")) {
                assert!(arr(f(answer(&w, id), "reasons")).contains(reason));
            }
        }
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
    }
    for (law, path, producer) in [
        ("fcMap", "$v.value.some[99]", "cbMapWrapped,m=@v/m"),
        ("fcMap", "$v.value.some", "fcMapNone"),
        ("mxFalse", "$v.value[0].some", "mxEmpty"),
    ] {
        let take = format!("take=check(Applications.{law},a=@v/A,x={path})");
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(
            fixture::input("known", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
                &take,
                &make,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
                "last=evaluate(Applications.seed)",
            ],
        );
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let c = condition(&w, "take");
        assert!(arr(f(c, "arguments")).contains(f(f(answer(&w, "v"), "outputs"), "value")));
        for id in ["seed", "v", "last"] {
            assert_eq!(f(answer(&w, id), "status"), &Json::str("established"));
        }
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        for id in ["take", "later"] {
            assert_eq!(
                f(answer(&w, id), "outputs"),
                &Json::obj([] as [(&str, Json); 0])
            );
        }
        for reason in arr(f(answer(&w, "take"), "reasons")) {
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
    }
}
#[test]
fn mixed_inherits_fixed_owner_and_value_producer_completion_and_universal_scope() {
    for (a, v, domain, mode) in [
        ("cbUniversalOwner", "mxAll", "all_assignments", "known"),
        (
            "cbCompletionOwner",
            "mxCompletion",
            "all_completions",
            "stop",
        ),
    ] {
        let owner = format!(
            "a=evaluate(Applications.{a},a=@v/A{})",
            if a == "cbCompletionOwner" {
                ",p=@v/p"
            } else {
                ""
            }
        );
        let value = format!("v=evaluate(Applications.{v},p=@v/p,q=@v/r)");
        let r = run(
            fixture::input(mode, "r1"),
            &[
                "take=check(Applications.mxTuple,a=$a.value,x=$v.value)",
                &owner,
                &value,
            ],
        );
        assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        let actual = f(answer(&w, "take"), "scope");
        assert_eq!(f(actual, "domain"), &Json::str(domain));
        for id in ["a", "v"] {
            let original = f(answer(&w, id), "scope");
            assert_eq!(f(original, "domain"), &Json::str(domain));
            for q in arr(f(original, "quantifiers")) {
                assert!(arr(f(actual, "quantifiers")).contains(q));
            }
        }
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
fn mixed_keeps_three_inputs_dag_fixed_and_free_owner_facts_and_current_sources() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    for mode in ["known", "unknown_owner"] {
        let asks = [
            "take=check(Applications.fcMap,a=$a.value,x=$v.value)",
            "v=evaluate(Applications.cbMap,m=@v/m)",
            "a=evaluate(Applications.cbOwner,a=@v/A)",
        ];
        let i = fixture::input(mode, "r1");
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
        assert_eq!(atoms.contains("p-owner"), mode == "known");
        assert!(atoms.contains("r-owner"));
        let relocated = run(fixture::input(mode, "r2"), &asks);
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
}

#[test]
fn mixed_direct_subject_fixed_owner_failure_keeps_typed_operands_and_later_reasons() {
    for (law, producer, fixed, snapshot, owner) in [
        ("mxTuple", "mxAll,p=@v/p,q=@v/r", "a", "v", "B"),
        ("mxOptionLaw", "mxOption,p=@v/p,q=@v/r", "a", "v", "B"),
        ("mxListLaw", "mxList,p=@v/p,q=@v/r", "b", "v", "A"),
        ("mxSetLaw", "mxSet,p=@v/p,q=@v/r", "a", "w", "A"),
        ("fcNested", "cbNested,p=@v/p,q=@v/r", "a", "v", "B"),
        ("fcMap", "cbMap,m=@v/m", "a", "v", "B"),
        ("fcMapWrapped", "cbMapWrapped,m=@v/m", "b", "v", "A"),
        (
            "mxConflictLaw",
            "mxConflict,p=@v/p,q=@v/r,r=@v/p",
            "a",
            "v",
            "B",
        ),
    ] {
        let take = format!("take=check(Applications.{law},{fixed}=@{snapshot}/{owner},x=$v.value)");
        let v = format!("v=evaluate(Applications.{producer})");
        let a = format!("a=evaluate(Applications.cbOwner,a=@{snapshot}/{owner})");
        let r = run(
            fixture::input("known", "r1"),
            &[
                "seed=evaluate(Applications.seed)",
                "prior=check(Applications.prior)",
                &a,
                &v,
                &take,
                "later=check(Applications.fcBool,x=$take.evaluation.value)",
            ],
        );
        assert_eq!(r.status(), "partial", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        let c = condition(&w, "take");
        let inputs = arr(f(f(c, "value"), "operands"));
        assert_eq!(
            inputs.len(),
            3,
            "direct subject fixed owner operand is required"
        );
        assert_eq!(&inputs[1], f(f(answer(&w, "v"), "outputs"), "value"));
        let direct = node(&w, &inputs[2]);
        assert_eq!(
            f(direct, "value"),
            &Json::Arr(vec![Json::str(snapshot), Json::str(owner)])
        );
        let foreign = f(f(answer(&w, "a"), "outputs"), "value");
        assert_ne!(&inputs[2], foreign);
        assert_eq!(f(direct, "type"), f(node(&w, foreign), "type"));
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str("undetermined"));
        assert_eq!(
            f(answer(&w, "take"), "outputs"),
            &Json::obj([] as [(&str, Json); 0])
        );
        assert!(rows(&w).is_empty());
        for reason in arr(f(answer(&w, "take"), "reasons")) {
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
        assert!(
            arr(f(answer(&w, "later"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str("take"))
        );
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(!arr(f(answer(&w, "prior"), "evidence")).is_empty());
    }
    // 全固定の逆順署名でも、Answer/直接subjectを署名のowner順へ戻す。
    let r = run(
        fixture::input("known", "r1"),
        &[
            "b=evaluate(Applications.cbOwner,a=@v/B)",
            "v=evaluate(Applications.cbTuple,p=@v/p,q=@v/r)",
            "take=evaluate(Applications.cbReverseUse,b=$b.value,a=@v/B,x=$v.value)",
            "later=evaluate(Applications.cbTupleUse,a=@v/A,b=@v/B,x=$take.value)",
        ],
    );
    assert_eq!(r.status(), "partial", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    let c = condition(&w, "take");
    let inputs = arr(f(f(c, "value"), "operands"));
    assert_eq!(inputs.len(), 4);
    assert_eq!(&inputs[1], f(f(answer(&w, "v"), "outputs"), "value"));
    assert_eq!(&inputs[2], f(f(answer(&w, "b"), "outputs"), "value"));
    assert_ne!(inputs[2], inputs[3]);
    assert_eq!(
        f(node(&w, &inputs[3]), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("B")])
    );
    for reason in arr(f(answer(&w, "take"), "reasons")) {
        assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
    }
}

#[test]
fn mixed_completed_public_projections_keep_seed_refs_for_all_cases() {
    for (law, producer, path, fixed, mode, output, steps) in [
        (
            "mxListLaw",
            "mxWrapped,p=@v/p,q=@v/r",
            "$v.value[1].some",
            "a=@v/A",
            "unknown_free_owner",
            "value",
            vec![Json::Nat(1), Json::str("some")],
        ),
        (
            "mxListLaw",
            "mxWrapped,p=@v/p,q=@v/r",
            "$v.value[1].some",
            "",
            "unknown_free_owner",
            "value",
            vec![Json::Nat(1), Json::str("some")],
        ),
        (
            "mxTuple",
            "mxWrapped,p=@v/p,q=@v/r",
            "$v.evaluation.value[1].some[0]",
            "a=@v/A",
            "unknown_free_owner",
            "evaluation",
            vec![
                Json::str("value"),
                Json::Nat(1),
                Json::str("some"),
                Json::Nat(0),
            ],
        ),
        (
            "fcMap",
            "cbMapWrapped,m=@v/m",
            "$v.value.some[1]",
            "b=@v/B",
            "unknown_owner",
            "value",
            vec![Json::str("some"), Json::Nat(1)],
        ),
    ] {
        let bound = if fixed.is_empty() {
            String::new()
        } else {
            format!("{fixed},")
        };
        let take = format!("take=check(Applications.{law},{bound}x={path})");
        let make = format!("v=evaluate(Applications.{producer})");
        let r = run(
            fixture::input(mode, "r1"),
            &[&take, &make, "later=evaluate(Applications.seed)"],
        );
        assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
        assert_eq!(
            f(f(answer(&w, "take"), "scope"), "domain"),
            &Json::str("all_completions")
        );
        assert_eq!(f(answer(&w, "later"), "status"), &Json::str("established"));
        assert!(
            !arr(f(answer(&w, "take"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        );
        let evaluation = node(&w, f(f(answer(&w, "take"), "outputs"), "evaluation"));
        let bs = arr(f(f(evaluation, "value"), "bindings"));
        let x = f(
            bs.iter().find(|b| f(b, "name") == &Json::str("x")).unwrap(),
            "value",
        );
        let projected = node(&w, x);
        assert_eq!(f(f(projected, "rule"), "path"), &Json::Arr(steps));
        assert_eq!(
            arr(f(projected, "arguments")),
            &[f(f(answer(&w, "v"), "outputs"), output).clone()]
        );
        let rr = rows(&w);
        assert_eq!(rr.len(), 2);
        let mut flags = std::collections::BTreeSet::new();
        for row in rr {
            let bindings = arr(f(f(row, "value"), "bindings"));
            assert_eq!(
                f(
                    bindings
                        .iter()
                        .find(|b| f(b, "name") == &Json::str("x"))
                        .unwrap(),
                    "value"
                ),
                x
            );
            let free = if fixed.starts_with("a=") { "b" } else { "a" };
            let owner = bindings
                .iter()
                .find(|b| f(b, "name") == &Json::str(free))
                .unwrap();
            assert_eq!(
                f(node(&w, f(owner, "value")), "value"),
                &Json::Arr(vec![
                    Json::str("v"),
                    Json::str(if free == "b" { "B" } else { "A" })
                ])
            );
            let flag = bindings
                .iter()
                .find(|b| f(b, "name") == &Json::str("flag"))
                .unwrap();
            let Json::Bool(flag) = f(node(&w, f(flag, "value")), "value") else {
                panic!()
            };
            flags.insert(*flag);
        }
        assert_eq!(flags, [false, true].into());
    }
}
