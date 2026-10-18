#[path = "common/answer_family_conditions.rs"]
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
    let Json::Arr(xs) = j else { panic!() };
    xs
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
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn blocked(w: &Json, id: &str, producer: &str) -> Json {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(f(a, "outputs"), &Json::obj([]));
    assert!(
        arr(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                && f(f(r, "details"), "request") == &Json::str(producer))
    );
    let reason = arr(f(a, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    assert_eq!(
        f(f(reason, "details"), "construction"),
        &Json::str("projection")
    );
    let condition = node(w, f(f(reason, "details"), "condition"));
    assert_eq!(f(condition, "type"), &Json::str("Proposition"));
    assert_eq!(
        f(f(condition, "value"), "predicate"),
        &Json::str("constructible")
    );
    assert_eq!(f(f(condition, "judgment"), "status"), &Json::str("refuted"));
    assert!(!arr(f(condition, "evidence")).is_empty());
    condition.clone()
}
#[test]
fn answer_family_projection_failure_keeps_condition_refutation_without_filling_free_parameters() {
    for (declaration, path) in [
        ("afFinite", "$empty.value[0]"),
        ("afNumeric", "$empty.evaluation.value[9007199254740991]"),
        ("afMixed", "$opt.value.some"),
        ("afFinite", "$nested.value[0].some[0]"),
    ] {
        let take = format!("take=check(Applications.{declaration},x={path})");
        let asks = [
            take.as_str(),
            "empty=evaluate(Applications.apEmpty)",
            "opt=evaluate(Applications.apNone)",
            "nested=evaluate(Applications.acNestedNone)",
            "seed=evaluate(Applications.abSeed)",
            "prior=check(Applications.abPrior)",
        ];
        let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
            .unwrap_or_else(|e| match e {
                archsig::observed::EvaluationFailure::NotImplemented { feature, .. } => {
                    panic!("NotImplemented: {feature}")
                }
                e => panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))),
            });
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let producer = path.trim_start_matches('$').split('.').next().unwrap();
        blocked(&w, "take", producer);
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(!arr(f(answer(&w, "prior"), "evidence")).is_empty());
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
fn answer_family_known_fixed_values_keep_finite_numeric_mixed_quantifiers_and_original_arguments() {
    let asks = [
        "finite=check(Applications.afFinite,x=$seed.value)",
        "numeric=check(Applications.afNumeric,x=$seed.evaluation.value)",
        "rational=check(Applications.afRational,x=$packed.value[1])",
        "mixed=check(Applications.afMixed,x=$seed.value)",
        "reference=check(Applications.afRef,p=$packed.value[9])",
        "bad=check(Applications.afFinite,x=$double.value)",
        "seed=evaluate(Applications.abSeed)",
        "double=evaluate(Applications.abDouble,x=$seed.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ];
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    for (id, names) in [
        ("finite", vec!["b"]),
        ("numeric", vec!["z"]),
        ("rational", vec!["q"]),
        ("mixed", vec!["b", "z"]),
        ("reference", vec!["b"]),
        ("bad", vec!["b"]),
    ] {
        let a = answer(&w, id);
        assert_eq!(
            f(a, "status"),
            &Json::str(if id == "bad" {
                "refuted"
            } else {
                "established"
            })
        );
        assert_eq!(
            f(f(node(&w, f(a, "claim")), "judgment"), "status"),
            f(a, "status")
        );
        if id == "bad" {
            assert!(!arr(f(a, "evidence")).is_empty());
        }
        let request = arr(f(&w, "requests"))
            .iter()
            .find(|r| f(r, "id") == &Json::str(id))
            .unwrap();
        assert_eq!(arr(f(request, "arguments")).len(), 1);
        assert_eq!(
            f(&arr(f(request, "arguments"))[0], "origin"),
            &Json::str("explicit")
        );
        let default = arr(f(request, "defaults"))
            .iter()
            .find(|d| f(d, "rule") == &Json::str("universal_parameters"))
            .unwrap();
        assert_eq!(
            f(default, "parameters"),
            &Json::Arr(names.iter().map(|n| Json::str(*n)).collect())
        );
        for name in names {
            assert!(
                arr(f(f(a, "scope"), "quantifiers"))
                    .iter()
                    .any(|q| f(q, "name") == &Json::str(name))
            );
        }
    }
    let seed = f(f(answer(&w, "seed"), "outputs"), "value");
    assert!(arr(f(&w,"nodes")).iter().any(|n|matches!(f(n,"value"),Json::Obj(v)if v.get("bindings").is_some_and(|bs|arr(bs).iter().any(|b|f(b,"name")==&Json::str("x")&&f(b,"value")==seed)))));
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|a| Json::str(a.split('=').next().unwrap()))
            .collect::<Vec<_>>()
    );
}
#[test]
fn answer_family_missing_unsupported_and_omitted_environment_keep_original_reasons_through_free_laws()
 {
    for (source, call, own_condition) in [
        (
            "source=evaluate(Applications.adMissing,p=@v/p)",
            "afFinite,x=$source.value",
            false,
        ),
        (
            "source=evaluate(Applications.adMissing,p=@v/p)",
            "afNumeric,x=$source.evaluation.value",
            false,
        ),
        (
            "source=evaluate(Applications.adOpaque)",
            "afBool,c=$source.value",
            false,
        ),
        (
            "source=evaluate(Applications.adMissing,p=@v/p)",
            "afRoot,a=$source.evaluation.environment.root",
            true,
        ),
        (
            "source=evaluate(Applications.adOpaque)",
            "afRoot,a=$source.evaluation.environment.root",
            true,
        ),
        (
            "source=evaluate(Applications.abIdentity,x=$empty.value[0])",
            "afRoot,a=$source.evaluation.environment.root",
            false,
        ),
    ] {
        let take = format!("take=check(Applications.{call})");
        let asks = [
            take.as_str(),
            source,
            "empty=evaluate(Applications.apEmpty)",
            "later=check(Applications.afBool,c=$take.evaluation.value)",
            "last=evaluate(Applications.abBool,x=$later.evaluation.value)",
            "seed=evaluate(Applications.abSeed)",
            "prior=check(Applications.abPrior)",
        ];
        let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet())
            .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        for (consumer, producer) in [("take", "source"), ("later", "take"), ("last", "later")] {
            let a = answer(&w, consumer);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert_eq!(f(a, "outputs"), &Json::obj([]));
            assert!(
                arr(f(a, "reasons"))
                    .iter()
                    .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                        && f(f(r, "details"), "request") == &Json::str(producer))
            );
            for reason in arr(f(answer(&w, producer), "reasons")) {
                assert!(arr(f(a, "reasons")).contains(reason));
            }
        }
        assert_eq!(
            arr(f(answer(&w, "take"), "reasons"))
                .iter()
                .filter(|r| f(r, "request") == &Json::str("take")
                    && f(r, "code") == &Json::str("condition_failed"))
                .count(),
            usize::from(own_condition)
        );
        if own_condition {
            blocked(&w, "take", "source");
        }
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
    }
}
#[test]
fn answer_family_fixed_producers_keep_existing_completion_and_universal_scope() {
    let asks = [
        "numeric=check(Applications.afNumeric,x=$zero.value)",
        "finite=check(Applications.afFinite,x=$zero.value)",
        "boolean=check(Applications.afBool,c=$universal.evaluation.value)",
        "zero=evaluate(Applications.mcMissingZero,p=@v/p)",
        "universal=check(Applications.abUniversal,x=$seed.value)",
        "seed=evaluate(Applications.abSeed)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    for (id, status) in [
        ("numeric", "established"),
        ("finite", "refuted"),
        ("boolean", "established"),
        ("zero", "established"),
        ("universal", "established"),
    ] {
        assert_eq!(f(answer(&w, id), "status"), &Json::str(status));
    }
    assert_eq!(
        f(f(answer(&w, "zero"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    for id in ["numeric", "finite"] {
        assert_eq!(
            f(f(answer(&w, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
    assert_eq!(
        f(f(answer(&w, "universal"), "scope"), "domain"),
        &Json::str("all_assignments")
    );
    assert_eq!(
        f(f(answer(&w, "boolean"), "scope"), "domain"),
        &Json::str("all_assignments")
    );
    for q in arr(f(f(answer(&w, "universal"), "scope"), "quantifiers")) {
        assert!(arr(f(f(answer(&w, "boolean"), "scope"), "quantifiers")).contains(q));
    }
}

#[test]
fn answer_family_mixed_fixed_failures_keep_each_direct_reason_and_requested_order() {
    let asks = [
        "mixed=check(Applications.afMany,a=$missing.evaluation.environment.root,x=$empty.value[0],y=$missing.value,c=$opaque.value)",
        "later=check(Applications.afBool,c=$mixed.evaluation.value)",
        "last=evaluate(Applications.abBool,x=$later.evaluation.value)",
        "empty=evaluate(Applications.apEmpty)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "opaque=evaluate(Applications.adOpaque)",
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet()).unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for producer in ["empty", "missing", "opaque"] {
        assert!(
            arr(f(answer(&w, "mixed"), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("dependency_blocked")
                    && f(f(r, "details"), "request") == &Json::str(producer))
        );
        for reason in arr(f(answer(&w, producer), "reasons")) {
            assert!(arr(f(answer(&w, "mixed"), "reasons")).contains(reason));
        }
    }
    assert_eq!(
        arr(f(answer(&w, "mixed"), "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("condition_failed"))
            .count(),
        2
    );
    for (consumer, producer) in [("later", "mixed"), ("last", "later")] {
        blocked(&w, consumer, producer);
        for reason in arr(f(answer(&w, producer), "reasons")) {
            assert!(arr(f(answer(&w, consumer), "reasons")).contains(reason));
        }
    }
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|a| Json::str(a.split('=').next().unwrap()))
            .collect::<Vec<_>>()
    );
    assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
}
#[test]
fn answer_family_static_bad_bindings_remain_invalid_before_evaluation() {
    for call in [
        "take=check(Applications.afFinite,x=$packed.value[99])",
        "take=check(Applications.afFinite,x=$packed.value[3])",
        "take=check(Applications.afFinite,x=$packed.value[9].snapshot)",
        "take=check(Applications.afFinite,x=$packed.value[0],bind.x=$packed.value[0])",
        "take=check(Applications.afFinite,unknown=$packed.value[0])",
        "take=evaluate(Applications.abDouble)",
    ] {
        let e = evaluate_observed_bytes(
            fixture::input("known", "r1"),
            &[call, "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)"],
            &mut quiet(),
        )
        .unwrap_err();
        let w = e.wire().unwrap();
        assert_eq!(f(&w, "status"), &Json::str("invalid"));
        assert!(arr(f(&w, "answers")).is_empty());
        assert!(arr(f(&w, "nodes")).is_empty());
    }
}

#[test]
fn answer_family_conditions_keep_inputs_original_root_dag_support_and_current_provenance() {
    let asks = [
        "take=check(Applications.afFinite,x=$packed.evaluation.value[6][99])",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
        "prior=check(Applications.abPrior)",
    ];
    let mut runs = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("known", revision);
        let original = input.clone();
        let checked = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
        let r = evaluate_observed_bytes(input, &asks, &mut quiet()).unwrap();
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
        let condition = blocked(&w, "take", "packed");
        let root = f(f(answer(&w, "packed"), "outputs"), "evaluation");
        assert_eq!(&arr(f(&condition, "arguments"))[0], root);
        assert_eq!(f(&condition, "support"), f(node(&w, root), "support"));
        assert_eq!(f(&condition, "scope"), f(node(&w, root), "scope"));
        assert!(!arr(f(&condition, "support")).is_empty());
        let producer =
            evaluate_observed_bytes(fixture::input("known", revision), &[asks[1]], &mut quiet())
                .unwrap();
        assert_eq!(
            node(&w, root),
            node(
                &producer.wire(),
                f(
                    f(answer(&producer.wire(), "packed"), "outputs"),
                    "evaluation"
                )
            )
        );
        fn refs(j: &Json, out: &mut Vec<Json>) {
            match j {
                Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(j.clone()),
                Json::Obj(m) => {
                    for v in m.values() {
                        refs(v, out);
                    }
                }
                Json::Arr(xs) => {
                    for x in xs {
                        refs(x, out);
                    }
                }
                _ => {}
            }
        }
        for (index, n) in arr(f(&w, "nodes")).iter().enumerate() {
            let mut rs = vec![];
            refs(n, &mut rs);
            for reference in rs {
                assert!(arr(f(&w, "nodes"))[..index].contains(node(&w, &reference)));
            }
        }
        let map = r.prepared().inputs().archmap();
        let mut facts = 0;
        for fact in arr(f(&condition, "support")) {
            let Json::Obj(fact) = fact else { panic!() };
            let Some(atom) = fact.get("atom") else {
                continue;
            };
            facts += 1;
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
                .find(|s| Json::str(&s.name) == fact["field"])
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
        assert!(facts > 0);
        runs.push(w);
    }
    assert_eq!(f(&runs[0], "nodes"), f(&runs[1], "nodes"));
    assert_eq!(f(&runs[0], "answers"), f(&runs[1], "answers"));
    assert_ne!(f(&runs[0], "inputs"), f(&runs[1], "inputs"));
}
