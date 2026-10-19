use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
#[path = "common/composed_paths.rs"]
#[allow(dead_code)]
mod fixture;
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(o) = j else { panic!() };
    &o[k]
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!() };
    a
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    array(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    array(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(w: &'a Json, id: &str) -> &'a Json {
    f(node(w, f(f(answer(w, id), "outputs"), "value")), "value")
}
fn run(missing: bool, asks: &[&str]) -> Json {
    let input = fixture::input(missing, "r1");
    let r = evaluate_observed_bytes(
        input.clone(),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    assert_eq!(r.prepared().inputs().sources(), &input);
    assert!(
        matches!(r.status(), "complete" | "partial"),
        "{:?}",
        f(&r.wire(), "issues")
    );
    r.wire()
}
#[test]
fn then_keeps_two_named_generators_in_order_and_actual_distinct_endpoints() {
    let w = run(false, &["x=evaluate(Walk.join,e=@v/e,f=@v/next)"]);
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("established"));
    let p = value(&w, "x");
    let word = array(f(p, "generators"));
    assert_eq!(word.len(), 2);
    for (r, name) in word.iter().zip(["e", "next"]) {
        assert_eq!(
            f(node(&w, r), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
    for (k, name) in [("source", "p"), ("target", "r")] {
        assert_eq!(
            f(node(&w, f(p, k)), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
}

#[test]
fn then_units_association_and_different_words_compare_full_action() {
    let w = run(
        false,
        &[
            "left=evaluate(Walk.left_unit,e=@v/e)",
            "right=evaluate(Walk.right_unit,e=@v/e)",
            "associate=evaluate(Walk.associative,s=@v/self,e=@v/e,f=@v/next)",
            "self=evaluate(Walk.same_self,s=@v/self,e=@v/e)",
            "outside=evaluate(Walk.no_reextend,e=@v/e,f=@v/next,g=@v/different)",
            "word=evaluate(Walk.triple,s=@v/self,e=@v/e,f=@v/next)",
            "empty=evaluate(Walk.empty,x=@v/p)",
        ],
    );
    for (id, v) in [
        ("left", true),
        ("right", true),
        ("associate", true),
        ("self", true),
        ("outside", false),
    ] {
        assert_eq!(f(answer(&w, id), "status"), &Json::str("established"));
        assert_eq!(value(&w, id), &Json::Bool(v));
    }
    let word = array(f(value(&w, "word"), "generators"));
    assert_eq!(word.len(), 3);
    for (r, name) in word.iter().zip(["self", "e", "next"]) {
        assert_eq!(
            f(node(&w, r), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
    assert!(array(f(value(&w, "empty"), "generators")).is_empty());
}
#[test]
fn then_invalid_actual_endpoint_keeps_typed_counterexample_prior_values_and_dependency_blocked() {
    let w = run(
        false,
        &[
            "seed=evaluate(Walk.seed)",
            "prior=check(Walk.prior)",
            "bad=evaluate(Walk.join,e=@v/e,f=@v/self)",
            "used=evaluate(Walk.keep,p=$bad.value)",
            "later=evaluate(Walk.seed)",
        ],
    );
    let a = answer(&w, "bad");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    let reason = array(f(a, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let condition = node(&w, f(f(reason, "details"), "condition"));
    let operands = array(f(f(condition, "value"), "operands"));
    assert_eq!(operands.len(), 2);
    for (r, name) in operands.iter().zip(["q", "p"]) {
        let n = node(&w, r);
        assert_eq!(
            f(n, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Paths.Node")])
        );
        assert_eq!(
            f(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
    assert!(
        array(f(answer(&w, "used"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
    );
    assert_eq!(value(&w, "seed"), &Json::str("1"));
    assert_eq!(value(&w, "later"), &Json::str("1"));
    assert_eq!(f(answer(&w, "prior"), "status"), &Json::str("refuted"));
}
#[test]
fn then_option_list_tuple_lexical_calls_and_endpoints_use_real_prior_refs() {
    let w = run(
        false,
        &[
            "nested=evaluate(Walk.join_nested,e=@v/e,f=@v/next)",
            "first=evaluate(Walk.join_first,e=@v/e,f=@v/next)",
            "last=evaluate(Walk.join_last,e=@v/e,f=@v/next)",
        ],
    );
    let list = node(&w, f(value(&w, "nested"), "some"));
    let rows = array(f(list, "value"));
    assert_eq!(rows.len(), 2);
    for row in rows {
        let row = node(&w, row);
        let fields = array(f(row, "value"));
        let path = node(&w, &fields[1]);
        assert_eq!(array(f(f(path, "value"), "generators")).len(), 2);
    }
    for (id, name) in [("first", "p"), ("last", "r")] {
        assert_eq!(
            value(&w, id),
            &Json::Arr(vec![Json::str("v"), Json::str(name)])
        );
    }
}
#[test]
fn then_unknown_endpoint_keeps_original_shared_completion_for_right_unit() {
    let w = run(
        true,
        &[
            "path=evaluate(Walk.join,e=@v/e,f=@v/next)",
            "same=evaluate(Walk.right_unit,e=@v/e)",
        ],
    );
    assert_eq!(f(answer(&w, "path"), "status"), &Json::str("undetermined"));
    assert_eq!(value(&w, "same"), &Json::Bool(true));
    for id in ["path", "same"] {
        assert!(
            array(f(answer(&w, id), "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("missing_observation")
                    && f(r, "missing").canonical().contains("Paths.Hop.to"))
        );
    }
}

#[test]
fn then_provenance_pair_preserves_math_and_current_checked_input_tables() {
    let mut outputs = Vec::new();
    for revision in ["r1", "r2"] {
        let input = fixture::input(false, revision);
        let mut c = Control::new(Limits::default(), |_| Usage::default());
        let checked = archsig::observed::input::check_inputs(input.clone(), &mut c).unwrap();
        assert_eq!(checked.archmap().sources[0].revision, revision);
        let r = evaluate_observed_bytes(
            input.clone(),
            &["x=evaluate(Walk.join,e=@v/e,f=@v/next)"],
            &mut c,
        )
        .unwrap();
        assert_eq!(r.status(), "complete");
        assert_eq!(r.prepared().inputs().sources(), &input);
        assert_eq!(r.prepared().inputs().definitions(), checked.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", checked.archmap())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", checked.law())
        );
        outputs.push(r.wire());
    }
    assert_eq!(f(&outputs[0], "answers"), f(&outputs[1], "answers"));
    assert_eq!(f(&outputs[0], "nodes"), f(&outputs[1], "nodes"));
    assert_ne!(f(&outputs[0], "inputs"), f(&outputs[1], "inputs"));
}
#[test]
fn then_value_can_be_bound_to_later_view_without_erasing_word_or_dependencies() {
    let w = run(
        false,
        &[
            "used=evaluate(Walk.keep,p=$x.value)",
            "x=evaluate(Walk.join,e=@v/e,f=@v/next)",
        ],
    );
    for id in ["x", "used"] {
        assert_eq!(f(answer(&w, id), "status"), &Json::str("established"));
        assert_eq!(array(f(value(&w, id), "generators")).len(), 2);
    }
    assert_eq!(
        array(f(&w, "answers"))
            .iter()
            .map(|a| f(a, "id"))
            .collect::<Vec<_>>(),
        vec![&Json::str("used"), &Json::str("x")]
    );
}
