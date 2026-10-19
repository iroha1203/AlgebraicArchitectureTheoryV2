//! 全ownerを固定した複合値の元Refと動的所属を同batchで検査する。
#[path = "common/compound_owned_binding.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
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
fn run_input(i: InputSources, asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let r = evaluate_observed_bytes(i, asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().map(|w| f(&w, "issues").clone())));
    assert_ne!(r.status(), "error", "{:?}", f(&r.wire(), "issues"));
    r
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    run_input(fixture::input("known", "r1"), asks)
}
fn binding<'a>(w: &'a Json, id: &str, name: &str) -> &'a Json {
    let evaluation = node(w, f(f(answer(w, id), "outputs"), "evaluation"));
    f(
        arr(f(f(evaluation, "value"), "bindings"))
            .iter()
            .find(|b| f(b, "name") == &Json::str(name))
            .unwrap(),
        "value",
    )
}
fn failed<'a>(w: &'a Json, id: &str, direct: &str) -> &'a Json {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(f(a, "outputs"), &Json::obj([] as [(&str, Json); 0]));
    let reasons = arr(f(a, "reasons"));
    let reason = reasons
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let c = node(w, f(f(reason, "details"), "condition"));
    assert_eq!(f(c, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(c, "value"), "predicate"), &Json::str("constructible"));
    assert_eq!(f(f(c, "judgment"), "status"), &Json::str("refuted"));
    let args = arr(f(c, "arguments"));
    let operands = arr(f(f(c, "value"), "operands"));
    assert_eq!(&operands[1..], &args[..args.len() - 2]);
    assert_eq!(&operands[0], &args[args.len() - 2]);
    assert!(
        reasons
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                && f(f(r, "details"), "request") == &Json::str(direct))
    );
    let evidence = node(w, &arr(f(c, "evidence"))[0]);
    assert_eq!(f(evidence, "type"), &Json::str("Evidence"));
    assert_eq!(f(evidence, "support"), f(c, "support"));
    c
}
#[test]
fn fixed_compound_owned_containers_preserve_original_refs_paths_order_and_members() {
    for (consumer, producer, value) in [
        (
            "cbOptionUse",
            "v=evaluate(Applications.cbOption,p=@v/p)",
            "$v.value",
        ),
        (
            "cbListUse",
            "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)",
            "$v.value",
        ),
        (
            "cbSetUse",
            "v=evaluate(Applications.cbSet,p=@v/p,q=@v/q)",
            "$v.value",
        ),
        (
            "cbListUse",
            "v=evaluate(Applications.cbWrapped,p=@v/p,q=@v/q)",
            "$v.evaluation.value[1]",
        ),
    ] {
        let take = format!("take=evaluate(Applications.{consumer},bind.a=$owner.value,x={value})");
        let r = run(&[
            &take,
            producer,
            "owner=evaluate(Applications.cbOwner,a=@v/A)",
        ]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
        assert_eq!(
            arr(f(&w, "answers"))
                .iter()
                .map(|a| f(a, "id").clone())
                .collect::<Vec<_>>(),
            ["take", "v", "owner"].map(Json::str)
        );
        let original = binding(&w, "take", "x");
        assert_eq!(original, f(f(answer(&w, "take"), "outputs"), "value"));
        if value == "$v.value" {
            assert_eq!(original, f(f(answer(&w, "v"), "outputs"), "value"));
        } else {
            let p = node(&w, original);
            assert_eq!(
                f(f(p, "rule"), "path"),
                &Json::Arr(vec![Json::str("value"), Json::Nat(1)])
            );
            assert_eq!(
                &arr(f(p, "arguments"))[0],
                f(f(answer(&w, "v"), "outputs"), "evaluation")
            );
        }
        let check = arr(f(&w, "nodes"))
            .iter()
            .find(|n| {
                matches!(f(n,"rule"),Json::Obj(m)if m.get("name")==Some(&Json::str("binding")))
                    && arr(f(n, "arguments")).first() == Some(original)
            })
            .unwrap();
        assert_eq!(f(check, "type"), &Json::str("Bool"));
        assert_eq!(f(check, "value"), &Json::Bool(true));
        assert_ne!(f(check, "id"), f(node(&w, original), "id"));
        if consumer == "cbListUse" {
            assert_eq!(
                f(node(&w, original), "value"),
                &Json::Arr(vec![
                    Json::Arr(vec![Json::str("v"), Json::str("q")]),
                    Json::Arr(vec![Json::str("v"), Json::str("p")]),
                    Json::Arr(vec![Json::str("v"), Json::str("q")])
                ])
            );
        }
        if consumer == "cbSetUse" {
            assert_eq!(arr(f(node(&w, original), "value")).len(), 2);
        }
    }
}
#[test]
fn fixed_compound_owned_multi_owner_nested_values_and_finite_free_axes_are_computed() {
    for (use_name, make) in [("cbTupleUse", "cbTuple"), ("cbNestedUse", "cbNested")] {
        let asks = [
            format!("take=evaluate(Applications.{use_name},a=$a.value,b=$b.value,x=$v.value)"),
            format!("v=evaluate(Applications.{make},p=@v/p,q=@v/r)"),
        ];
        let r = run(&[
            &asks[0],
            &asks[1],
            "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
            "b=evaluate(Applications.cbOwner,a=@v/B)",
        ]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        assert_eq!(
            binding(&w, "take", "x"),
            f(f(answer(&w, "v"), "outputs"), "value")
        );
        assert_eq!(
            f(f(answer(&w, "take"), "scope"), "domain"),
            &Json::str("all_assignments")
        );
        for q in arr(f(f(answer(&w, "a"), "scope"), "quantifiers")) {
            assert!(arr(f(f(answer(&w, "take"), "scope"), "quantifiers")).contains(q));
        }
    }
    let r = run(&[
        "family=check(Applications.cbFamily,a=@v/A,x=$v.value)",
        "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)",
        "no=check(Applications.cbFalse,a=@v/A,b=@v/B,x=$tuple.value)",
        "tuple=evaluate(Applications.cbTuple,p=@v/p,q=@v/r)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(f(answer(&w, "family"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "no"), "status"), &Json::str("refuted"));
    assert!(!arr(f(answer(&w, "no"), "evidence")).is_empty());
    assert!(arr(f(answer(&w,"family"),"evidence")).iter().any(|r|matches!(f(node(&w,r),"value"),Json::Obj(m)if m.get("data").is_some_and(|d|matches!(d,Json::Obj(d)if d.get("checked")==Some(&Json::Nat(3)))))));
}
#[test]
fn fixed_compound_owned_nonmembers_preserve_all_owner_operands_conditions_and_later_reasons() {
    for (consumer, producer, a, b) in [
        (
            "cbOptionUse",
            "v=evaluate(Applications.cbOption,p=@v/r)",
            "A",
            None,
        ),
        (
            "cbListUse",
            "v=evaluate(Applications.cbList,p=@v/p,q=@v/r)",
            "A",
            None,
        ),
        (
            "cbSetUse",
            "v=evaluate(Applications.cbSet,p=@v/p,q=@v/r)",
            "A",
            None,
        ),
        (
            "cbTupleUse",
            "v=evaluate(Applications.cbTuple,p=@v/p,q=@v/r)",
            "A",
            Some("A"),
        ),
        (
            "cbNestedUse",
            "v=evaluate(Applications.cbNested,p=@v/r,q=@v/p)",
            "A",
            Some("B"),
        ),
        (
            "cbReverseUse",
            "v=evaluate(Applications.cbTuple,p=@v/p,q=@v/r)",
            "A",
            Some("A"),
        ),
    ] {
        let take = format!(
            "take=evaluate(Applications.{consumer},a=$a.value,{}x=$v.value)",
            if b.is_some() { "b=$b.value," } else { "" }
        );
        let oa = format!("a=evaluate(Applications.cbOwner,a=@v/{a})");
        let ob = format!("b=evaluate(Applications.cbOwner,a=@v/{})", b.unwrap_or("B"));
        let later = format!(
            "later=evaluate(Applications.{consumer},a=$a.value,{}x=$take.value)",
            if b.is_some() { "b=$b.value," } else { "" }
        );
        let r = run(&[
            "seed=evaluate(Applications.seed)",
            "prior=check(Applications.prior)",
            &take,
            &later,
            producer,
            &oa,
            &ob,
        ]);
        let w = r.wire();
        assert_eq!(r.status(), "partial");
        let c = failed(&w, "take", "v");
        let mut expected = vec![
            f(f(answer(&w, "v"), "outputs"), "value").clone(),
            f(f(answer(&w, "a"), "outputs"), "value").clone(),
        ];
        if b.is_some() {
            expected.push(f(f(answer(&w, "b"), "outputs"), "value").clone());
        }
        if consumer == "cbReverseUse" {
            expected.swap(1, 2);
        }
        assert_eq!(&arr(f(f(c, "value"), "operands"))[1..], expected.as_slice());
        for reason in arr(f(answer(&w, "take"), "reasons")) {
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
    }
}
#[test]
fn fixed_compound_owned_none_empty_and_map_full_domain_are_distinct() {
    let r = run(&[
        "empty=evaluate(Applications.cbEmptyUse,a=$a.value,x=$v.value[0],xs=$v.value[1],ys=$v.value[2])",
        "v=evaluate(Applications.cbEmpty)",
        "a=evaluate(Applications.cbOwner,a=@v/A)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(
        f(
            node(&w, f(f(answer(&w, "empty"), "outputs"), "value")),
            "value"
        ),
        &Json::str("0")
    );
    for (consumer, producer) in [("cbMapUse", "cbMap"), ("cbMapWrappedUse", "cbMapWrapped")] {
        let source = format!("v=evaluate(Applications.{producer},m=@v/m)");
        let take =
            format!("take=evaluate(Applications.{consumer},a=$a.value,b=$b.value,x=$v.value)");
        let r = run(&[
            &take,
            &source,
            "a=evaluate(Applications.cbOwner,a=@v/A)",
            "b=evaluate(Applications.cbOwner,a=@v/B)",
        ]);
        let w = r.wire();
        assert_eq!(r.status(), "complete");
        assert_eq!(
            binding(&w, "take", "x"),
            f(f(answer(&w, "v"), "outputs"), "value")
        );
        for (owner, mode) in [("A", "empty"), ("B", "known")] {
            let a = format!("a=evaluate(Applications.cbOwner,a=@v/{owner})");
            let r = run_input(
                fixture::input(mode, "r1"),
                &[
                    &take,
                    &source,
                    &a,
                    "b=evaluate(Applications.cbOwner,a=@v/B)",
                ],
            );
            assert_eq!(r.status(), "partial");
            failed(&r.wire(), "take", "v");
        }
        let empty = run_input(
            fixture::input("empty", "r1"),
            &[
                &take,
                &source,
                "a=evaluate(Applications.cbOwner,a=@v/Z)",
                "b=evaluate(Applications.cbOwner,a=@v/B)",
            ],
        );
        assert_eq!(empty.status(), "complete");
    }
    // 全domain Aの表でも、imageをAへ要求すれば実r/sの所属で不適合。
    let r = run(&[
        "take=evaluate(Applications.cbMapUse,a=@v/A,b=@v/A,x=$v.value)",
        "v=evaluate(Applications.cbMap,m=@v/m)",
    ]);
    assert_eq!(r.status(), "partial");
    failed(&r.wire(), "take", "v");
}
#[test]
fn fixed_compound_owned_static_invalid_unprovided_unknown_and_cross_snapshot_remain_distinct() {
    for ask in [
        "take=evaluate(Applications.cbListUse,a=@v/A,x=$typed.value)",
        "take=evaluate(Applications.cbListUse,a=@v/A,x=$option.value)",
        "take=evaluate(Applications.cbListUse,a=@v/A,x=$list.private.value)",
        "take=evaluate(Applications.cbListUse,a=@v/A,x=$list.value,bind.x=$list.value)",
    ] {
        let r = evaluate_observed_bytes(
            fixture::input("known", "r1"),
            &[
                ask,
                "typed=evaluate(Applications.cbTypedList,a=@v/B,p=@v/r)",
                "option=evaluate(Applications.cbOption,p=@v/p)",
                "list=evaluate(Applications.cbList,p=@v/p,q=@v/q)",
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
    for (mode, producer, code) in [
        (
            "stop",
            "v=evaluate(Applications.cbMissing,p=@v/p)",
            "missing_observation",
        ),
        (
            "known",
            "v=evaluate(Applications.cbOpaque,p=@v/p,q=@v/q)",
            "unsupported_algorithm",
        ),
    ] {
        let r = run_input(
            fixture::input(mode, "r1"),
            &[
                "take=evaluate(Applications.cbListUse,a=@v/A,x=$v.value)",
                "later=evaluate(Applications.cbListUse,a=@v/A,x=$take.value)",
                producer,
            ],
        );
        let w = r.wire();
        assert_eq!(r.status(), "partial");
        assert!(
            arr(f(answer(&w, "v"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str(code))
        );
        for id in ["take", "later"] {
            assert_eq!(
                f(answer(&w, id), "outputs"),
                &Json::obj([] as [(&str, Json); 0])
            );
            for reason in arr(f(answer(&w, "v"), "reasons")) {
                assert!(arr(f(answer(&w, id), "reasons")).contains(reason));
            }
        }
    }
    // 既知Migration.statesの全域制約は、未観測p.ownerをAへ絞る。
    let completed = run_input(
        fixture::input("unknown_owner", "r1"),
        &[
            "take=evaluate(Applications.cbOptionUse,a=@v/A,x=$v.value)",
            "v=evaluate(Applications.cbOption,p=@v/p)",
        ],
    );
    assert_eq!(completed.status(), "complete");
    let w = completed.wire();
    assert_eq!(f(answer(&w, "take"), "status"), &Json::str("established"));
    assert_eq!(
        f(f(answer(&w, "take"), "outputs"), "value"),
        f(f(answer(&w, "v"), "outputs"), "value")
    );
    assert_eq!(
        f(f(answer(&w, "take"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    let p = completed.prepared().inputs().archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "p")
        .unwrap();
    assert!(matches!(
        p.fields
            .iter()
            .find(|f| f.name == "Reservations.State.owner")
            .unwrap()
            .slot,
        archsig::archmap::Slot::Missing
    ));
    let r = run(&[
        "take=evaluate(Applications.cbOptionUse,a=$a.value,x=$v.value)",
        "a=evaluate(Applications.cbOwner,a=@w/A)",
        "v=evaluate(Applications.cbOption,p=@v/p)",
    ]);
    assert_eq!(r.status(), "partial");
    failed(&r.wire(), "take", "v");
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
fn fixed_compound_owned_map_keeps_three_inputs_dag_roster_support_and_current_provenance() {
    use archsig::observed::input::check_inputs;
    use std::collections::BTreeSet;
    let asks = [
        "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)",
        "v=evaluate(Applications.cbMap,m=@v/m)",
        "a=evaluate(Applications.cbCompletionOwner,a=@v/A,p=@v/p)",
        "b=evaluate(Applications.cbOwner,a=@v/B)",
    ];
    // p.freeを欠測にして補完Scopeを実際に発生させる。
    let i = fixture::input("stop", "r1");
    let original = i.clone();
    let before = check_inputs(i.clone(), &mut quiet()).unwrap();
    let r = run_input(i, &asks);
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    let checked = r.prepared().inputs();
    assert_eq!(checked.sources(), &original);
    assert_eq!(checked.inputs(), before.inputs());
    assert_eq!(checked.definitions(), before.definitions());
    assert_eq!(checked.law().declarations, before.law().declarations);
    assert_eq!(checked.law().exprs, before.law().exprs);
    assert_eq!(checked.archmap().snapshots, before.archmap().snapshots);
    let mut seen = BTreeSet::new();
    let mut owner_atoms = BTreeSet::new();
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
                    owner_atoms.insert(atom.clone());
                }
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
    assert!(
        owner_atoms.contains("p-owner")
            && owner_atoms.contains("q-owner")
            && owner_atoms.contains("r-owner")
            && owner_atoms.contains("s-owner")
    );
    assert_eq!(
        f(f(answer(&w, "take"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    for q in arr(f(f(answer(&w, "a"), "scope"), "quantifiers")) {
        assert!(arr(f(f(answer(&w, "take"), "scope"), "quantifiers")).contains(q));
    }
    let moved = run_input(fixture::input("stop", "r2"), &asks);
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
fn fixed_compound_owned_nested_calls_and_successive_producers_keep_selected_bindings() {
    let r = run(&[
        "last=evaluate(Applications.cbListUse,a=@v/A,x=$next.value)",
        "next=evaluate(Applications.cbCall,a=@v/A,x=$first.value)",
        "first=evaluate(Applications.cbListUse,a=@v/A,x=$v.value)",
        "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    for (id, producer) in [("first", "v"), ("next", "first"), ("last", "next")] {
        assert_eq!(
            binding(&w, id, "x"),
            f(f(answer(&w, producer), "outputs"), "value")
        );
        assert_eq!(
            f(node(&w, f(f(answer(&w, id), "outputs"), "value")), "value"),
            f(node(&w, f(f(answer(&w, "v"), "outputs"), "value")), "value")
        );
    }
}
