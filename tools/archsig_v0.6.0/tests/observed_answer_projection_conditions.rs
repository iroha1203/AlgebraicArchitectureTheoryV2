#[path = "common/answer_projection_conditions.rs"]
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
fn projection_conditions_keep_dynamic_failures_as_typed_refutations_and_continue_batch() {
    for path in ["[0]", "[9007199254740991]"] {
        let take = format!("take=evaluate(Applications.abIdentity,x=$empty.value{path})");
        let asks = [
            take.as_str(),
            "empty=evaluate(Applications.apEmpty)",
            "seed=evaluate(Applications.abSeed)",
            "prior=check(Applications.abPrior)",
        ];
        let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
            .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
        assert_eq!(r.status(), "partial", "{:?}", f(&r.wire(), "issues"));
        let w = r.wire();
        blocked(&w, "take", "empty");
        assert_eq!(f(answer(&w, "empty"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
        assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
        assert!(!arr(f(answer(&w, "prior"), "evidence")).is_empty());
    }
    for asks in [
        vec![
            "take=check(Applications.abFour,x=$opt.evaluation.value.some)",
            "opt=evaluate(Applications.apNone)",
        ],
        vec![
            "take=evaluate(Applications.abIdentity,x=$nested.value[0].some[0])",
            "nested=evaluate(Applications.acNestedNone)",
        ],
        vec![
            "take=evaluate(Applications.acRoot,a=$seed.evaluation.environment.root)",
            "seed=evaluate(Applications.abSeed)",
        ],
    ] {
        let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
            .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        let producer = asks[1].split('=').next().unwrap();
        blocked(&w, "take", producer);
        assert_eq!(f(answer(&w, producer), "status"), &Json::str("established"));
    }
    for asks in [
        vec![
            "take=evaluate(Trees.integer,x=$empty.value[0])",
            "empty=evaluate(Trees.empty)",
        ],
        vec![
            "take=evaluate(Trees.integer,x=$raw.value[0])",
            "raw=evaluate(Trees.raw,s=@v/sample)",
        ],
        vec![
            "take=evaluate(Trees.acceptsPair,x=$raw.value[0],t=$raw.value[0])",
            "raw=evaluate(Trees.raw,s=@v/sample)",
        ],
    ] {
        let r = evaluate_observed_bytes(fixture::tree_input(false, "r1"), &asks, &mut quiet())
            .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
        assert_eq!(r.status(), "partial");
        let w = r.wire();
        blocked(&w, "take", asks[1].split('=').next().unwrap());
    }
}
#[test]
fn projection_conditions_propagate_direct_ids_original_reasons_and_evidence_through_mixed_bindings()
{
    let asks = [
        "last=evaluate(Applications.abDouble,x=$middle.value)",
        "middle=evaluate(Applications.abIdentity,x=$mixed.value)",
        "mixed=evaluate(Applications.acMix,x=$empty.value[0],y=$missing.value,b=$opaque.value)",
        "empty=evaluate(Applications.apEmpty)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "opaque=evaluate(Applications.adOpaque)",
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "partial", "{:?}", f(&r.wire(), "issues"));
    let w = r.wire();
    blocked(&w, "mixed", "empty");
    blocked(&w, "middle", "mixed");
    blocked(&w, "last", "middle");
    for (consumer, producer) in [
        ("mixed", "missing"),
        ("mixed", "opaque"),
        ("middle", "mixed"),
        ("last", "middle"),
    ] {
        for reason in arr(f(answer(&w, producer), "reasons")) {
            assert!(arr(f(answer(&w, consumer), "reasons")).contains(reason));
        }
    }
    let reasons = arr(f(answer(&w, "mixed"), "reasons"));
    for code in [
        "missing_observation",
        "unsupported_algorithm",
        "condition_failed",
        "dependency_blocked",
    ] {
        assert!(reasons.iter().any(|r| f(r, "code") == &Json::str(code)));
    }
    assert_eq!(f(answer(&w, "seed"), "status"), &Json::str("established"));
    assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
    assert_eq!(
        arr(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|s| Json::str(s.split('=').next().unwrap()))
            .collect::<Vec<_>>()
    );
}
#[test]
fn projection_conditions_preserve_valid_none_empty_zero_false_and_original_producers() {
    let asks = [
        "opt=evaluate(Applications.apNone)",
        "listValue=evaluate(Applications.apEmpty)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
        "noneCopy=evaluate(Applications.apOption,x=$opt.value)",
        "emptyCopy=evaluate(Applications.apList,x=$listValue.evaluation.value)",
        "zero=evaluate(Applications.abIdentity,x=$packed.value[8].some)",
        "boolean=evaluate(Applications.abBool,x=$packed.value[3])",
    ];
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), &asks, &mut quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire().as_ref().map(|w| f(w, "issues"))));
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for (consumer, producer) in [("noneCopy", "opt"), ("emptyCopy", "listValue")] {
        assert_eq!(
            f(f(answer(&w, consumer), "outputs"), "value"),
            f(f(answer(&w, producer), "outputs"), "value")
        );
    }
    for (id, value) in [("zero", Json::str("0")), ("boolean", Json::Bool(false))] {
        let n = node(&w, f(f(answer(&w, id), "outputs"), "value"));
        assert_eq!(f(n, "value"), &value);
    }
    assert!(!arr(f(&w,"nodes")).iter().any(|n|matches!(f(n,"value"),Json::Obj(m)if m.get("predicate")==Some(&Json::str("constructible")))));
}
#[test]
fn projection_conditions_keep_root_support_scope_original_inputs_dag_and_current_provenance() {
    let asks = [
        "take=evaluate(Applications.abIdentity,x=$packed.evaluation.value[6][99])",
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
