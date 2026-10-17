#[path = "common/answer_dependencies.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!() };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!() };
    a
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn run(asks: &[&str]) -> Json {
    let r = evaluate_observed_bytes(
        fixture::input("stop", "r1"),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_eq!(r.status(), "partial", "{:?}", r.wire());
    r.wire()
}
#[test]
fn unavailable_answer_chain_retains_missing_and_unsupported_reasons() {
    let asks = [
        "last=check(Applications.abFour,x=$middle.evaluation.value)",
        "middle=evaluate(Applications.abDouble,x=$first.value)",
        "first=evaluate(Applications.abIdentity,x=$raw.evaluation.value)",
        "raw=evaluate(Applications.adMissing,p=@v/p)",
        "opaque=evaluate(Applications.adOpaque)",
        "copied=evaluate(Applications.abBool,x=$opaque.value)",
        "known=evaluate(Applications.abSeed)",
        "falseLaw=check(Applications.abPrior)",
    ];
    let w = run(&asks);
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id"))
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|t| Json::str(t.split('=').next().unwrap()))
            .collect::<Vec<_>>()
            .iter()
            .collect::<Vec<_>>()
    );
    for id in ["first", "middle", "last", "copied"] {
        let a = answer(&w, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert_eq!(f(a, "outputs"), &Json::obj([]));
        let Json::Obj(fields) = a else { panic!() };
        assert!(!fields.contains_key("claim"));
        assert!(arr(f(a, "evidence")).is_empty());
        assert!(
            arr(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
        );
    }

    for (consumer, producer) in [
        ("first", "raw"),
        ("middle", "first"),
        ("last", "middle"),
        ("copied", "opaque"),
    ] {
        assert!(
            arr(f(answer(&w, consumer), "reasons"))
                .iter()
                .any(
                    |reason| f(reason, "code") == &Json::str("dependency_blocked")
                        && f(reason, "request") == &Json::str(consumer)
                        && f(f(reason, "details"), "request") == &Json::str(producer)
                )
        );
    }
    let original = arr(f(answer(&w, "raw"), "reasons"));
    assert!(!original.is_empty());
    for id in ["first", "middle", "last"] {
        for reason in original {
            assert!(arr(f(answer(&w, id), "reasons")).contains(reason));
        }
    }
    let original = arr(f(answer(&w, "opaque"), "reasons"));
    assert!(
        original
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm")),
        "{:?}",
        answer(&w, "opaque")
    );
    for reason in original {
        assert!(arr(f(answer(&w, "copied"), "reasons")).contains(reason));
    }
    assert_eq!(f(answer(&w, "known"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "falseLaw"), "status"), &Json::str("refuted"));
}

#[test]
fn unavailable_multiple_inputs_keep_each_direct_dependency_and_original_details() {
    let asks = [
        "both=evaluate(Applications.adBoth,x=$raw.value,b=$opaque.evaluation.value)",
        "raw=evaluate(Applications.adMissing,p=@w/p)",
        "opaque=evaluate(Applications.adOpaque)",
        "other=evaluate(Applications.adMissing,p=@v/p)",
        "later=check(Applications.abRequire,x=$both.value)",
    ];
    // 最後のZ→Bool束縛は、graph生成前の静的不正として拒否する。
    let error = evaluate_observed_bytes(
        fixture::input("stop", "r1"),
        &asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap_err();
    let invalid = error.wire().unwrap();
    assert_eq!(f(&invalid, "status"), &Json::str("invalid"));
    assert!(arr(f(&invalid, "nodes")).is_empty());
    let w = run(&[
        "both=evaluate(Applications.adBoth,x=$raw.value,b=$opaque.evaluation.value)",
        "raw=evaluate(Applications.adMissing,p=@v/p)",
        "opaque=evaluate(Applications.adOpaque)",
        "later=check(Applications.abFour,x=$both.value)",
        "known=evaluate(Applications.abSeed)",
    ]);
    let both = answer(&w, "both");
    let dependencies: Vec<_> = arr(f(both, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("dependency_blocked"))
        .map(|r| f(f(r, "details"), "request").clone())
        .collect();
    assert_eq!(dependencies.len(), 2);
    assert!(dependencies.contains(&Json::str("opaque")));
    assert!(dependencies.contains(&Json::str("raw")));
    for id in ["raw", "opaque"] {
        for reason in arr(f(answer(&w, id), "reasons")) {
            assert!(arr(f(both, "reasons")).contains(reason));
            assert!(arr(f(answer(&w, "later"), "reasons")).contains(reason));
        }
    }
    for reason in arr(f(both, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("dependency_blocked"))
    {
        assert!(!arr(f(reason, "dependencies")).is_empty());
        for reference in arr(f(reason, "dependencies")) {
            assert!(
                arr(f(&w, "nodes"))
                    .iter()
                    .any(|n| f(n, "id") == f(reference, "node"))
            );
        }
    }
    assert_eq!(f(both, "outputs"), &Json::obj([]));
    assert!(
        arr(f(answer(&w, "later"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                && f(f(r, "details"), "request") == &Json::str("both"))
    );
}

#[test]
fn unavailable_values_do_not_change_known_bindings_false_values_or_requested_metadata() {
    let asks = [
        "blocked=evaluate(Applications.abDouble,x=$missing.value)",
        "known=evaluate(Applications.abDouble,x=$seed.evaluation.value)",
        "seed=evaluate(Applications.abSeed)",
        "copied=evaluate(Applications.abBool,x=$falseView.value)",
        "refuted=check(Applications.abRequire,x=$copied.evaluation.value)",
        "falseView=evaluate(Applications.abFalse)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
    ];
    let w = run(&asks);
    for (request, text) in arr(f(&w, "requests")).iter().zip(asks) {
        assert_eq!(f(request, "text"), &Json::str(text));
        assert!(
            arr(f(request, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("observed_environment"))
        );
        for arg in arr(f(request, "arguments")) {
            assert_eq!(f(arg, "origin"), &Json::str("explicit"));
        }
    }
    fn out<'a>(w: &'a Json, id: &str) -> &'a Json {
        let r = f(f(answer(w, id), "outputs"), "value");
        arr(f(w, "nodes"))
            .iter()
            .find(|n| f(n, "id") == f(r, "node"))
            .unwrap()
    }
    assert_eq!(f(out(&w, "known"), "value"), &Json::str("4"));
    assert_eq!(f(out(&w, "copied"), "value"), &Json::Bool(false));
    assert_eq!(f(answer(&w, "copied"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "refuted"), "status"), &Json::str("refuted"));
    assert_eq!(f(answer(&w, "blocked"), "outputs"), &Json::obj([]));
    assert!(!format!("{:?}", f(&w, "issues")).contains("internal"));
}

#[test]
fn unavailable_answers_keep_inputs_and_current_provenance_without_changing_judgments() {
    let asks = [
        "raw=evaluate(Applications.adMissing,p=@v/p)",
        "take=evaluate(Applications.abDouble,x=$raw.value)",
        "known=evaluate(Applications.abFree,p=@w/r)",
    ];
    let mut runs = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("stop", revision);
        let original = input.clone();
        let mut c = Control::new(Limits::default(), |_| Usage::default());
        let checked = archsig::observed::input::check_inputs(input.clone(), &mut c).unwrap();
        let r = evaluate_observed_bytes(input, &asks, &mut c).unwrap();
        assert_eq!(r.status(), "partial");
        assert_eq!(r.prepared().inputs().sources(), &original);
        assert_eq!(r.prepared().inputs().definitions(), checked.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", checked.law())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", checked.archmap())
        );
        let w = r.wire();
        let mut found = 0;
        for n in arr(f(&w, "nodes")) {
            for fact in arr(f(n, "support")) {
                let Json::Obj(fact) = fact else { panic!() };
                let Some(atom) = fact.get("atom") else {
                    continue;
                };
                found += 1;
                let map = r.prepared().inputs().archmap();
                let snapshot = map
                    .snapshots
                    .iter()
                    .find(|s| Json::str(&s.id) == fact["snapshot"])
                    .unwrap();
                let subject = snapshot
                    .subjects
                    .iter()
                    .find(|s| Json::str(&s.id) == fact["subject"])
                    .unwrap();
                let field = subject
                    .fields
                    .iter()
                    .find(|p| Json::str(&p.name) == fact["field"])
                    .unwrap();
                let archsig::archmap::Slot::Known {
                    atom: actual,
                    origin,
                    ..
                } = &field.slot
                else {
                    panic!()
                };
                assert_eq!(&Json::str(actual), atom);
                let origin = map.origins.iter().find(|o| o.id == *origin).unwrap();
                assert!(!origin.locations.is_empty());
                for at in &origin.locations {
                    assert_eq!(
                        map.sources
                            .iter()
                            .find(|s| s.id == at.source)
                            .unwrap()
                            .revision,
                        revision
                    );
                }
            }
        }
        assert!(found > 0);
        let missing = arr(f(answer(&w, "raw"), "reasons"))
            .iter()
            .find(|r| f(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert!(arr(f(answer(&w, "take"), "reasons")).contains(missing));
        runs.push(w);
    }
    assert_eq!(f(&runs[0], "answers"), f(&runs[1], "answers"));
    assert_eq!(f(&runs[0], "nodes"), f(&runs[1], "nodes"));
    assert_ne!(f(&runs[0], "inputs"), f(&runs[1], "inputs"));
}
