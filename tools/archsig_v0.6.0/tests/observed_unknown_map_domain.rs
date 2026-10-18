use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
};
#[path = "common/unknown_map_domain.rs"]
#[allow(dead_code)]
mod fixture;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(o) = j else { panic!("object") };
    &o[k]
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn node<'a>(j: &'a Json, r: &Json) -> &'a Json {
    array(f(j, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn run(input: InputSources, asks: &[&str]) -> Json {
    let checked = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
    let result = evaluate_observed_bytes(input.clone(), asks, &mut quiet()).unwrap();
    assert_eq!(result.prepared().inputs().sources(), &input);
    assert_eq!(
        result.prepared().inputs().definitions(),
        checked.definitions()
    );
    assert_eq!(
        format!("{:?}", result.prepared().inputs().law()),
        format!("{:?}", checked.law())
    );
    assert_eq!(
        format!("{:?}", result.prepared().inputs().archmap()),
        format!("{:?}", checked.archmap())
    );
    assert!(matches!(result.status(), "complete" | "partial"));
    result.wire()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    array(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn missing(a: &Json) -> std::collections::BTreeSet<String> {
    array(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| array(f(r, "missing")))
        .map(Json::canonical)
        .collect()
}
fn p_missing() -> String {
    Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("p")),
        ("field", Json::str("MapCall.Item.owner")),
    ])
    .canonical()
}
fn domains(w: &Json, expected: &[&str]) {
    let ty = Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Root")]);
    let ds: Vec<_> = array(f(w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && matches!(f(n,"value"),Json::Obj(o)if o.get("type")==Some(&ty))
        })
        .collect();
    assert!(!ds.is_empty());
    let expected: std::collections::BTreeSet<_> = expected
        .iter()
        .map(|id| Json::Arr(vec![Json::str("v"), Json::str(*id)]).canonical())
        .collect();
    for d in ds {
        let values: std::collections::BTreeSet<_> = array(f(f(d, "value"), "elements"))
            .iter()
            .map(|r| f(node(w, r), "value").canonical())
            .collect();
        assert_eq!(values, expected);
    }
}
fn established(w: &Json, id: &str) {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert_eq!(
        f(node(w, f(f(a, "outputs"), "value")), "value"),
        &Json::Bool(true)
    );
    assert!(
        array(f(a, "reasons"))
            .iter()
            .all(|r| f(r, "code") != &Json::str("condition_failed"))
    );
}
#[test]
fn known_map_constraints_complete_unknown_owner_before_full_domain_call() {
    let w = run(
        fixture::input("constrained", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    established(&w, "x");
    assert_eq!(
        missing(answer(&w, "x")),
        [p_missing()].into_iter().collect()
    );
    domains(&w, &["A"]);
    assert_eq!(
        f(f(answer(&w, "x"), "scope"), "domain"),
        &Json::str("all_completions")
    );
}
#[test]
fn full_domain_call_keeps_both_consistent_owner_cases_and_original_missing() {
    let w = run(
        fixture::input("varying", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert_eq!(missing(a), [p_missing()].into_iter().collect());
    domains(&w, &["A", "B"]);
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
}
#[test]
fn empty_map_reads_unknown_nonkey_owner_and_keeps_consistent_empty_fiber() {
    let w = run(
        fixture::input("nonkey", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    established(&w, "x");
    assert_eq!(
        missing(answer(&w, "x")),
        [p_missing()].into_iter().collect()
    );
    domains(&w, &["B"]);
}
#[test]
fn empty_map_full_domain_condition_changes_across_owner_completions() {
    let w = run(
        fixture::input("empty_varying", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert_eq!(missing(a), [p_missing()].into_iter().collect());
    domains(&w, &["A", "B"]);
    let ty = Json::Arr(vec![
        Json::str("Set"),
        Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Item")]),
    ]);
    let evidence: Vec<_> = array(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(f(n, "value"), "kind") == &Json::str("counterexample")
        })
        .collect();
    assert!(!evidence.is_empty());
    for e in evidence {
        let data = f(f(e, "value"), "data");
        let l = node(&w, f(data, "left"));
        let r = node(&w, f(data, "right"));
        assert_eq!(f(l, "type"), &ty);
        assert_eq!(f(r, "type"), &ty);
        assert_eq!(f(l, "value"), &Json::Arr(vec![]));
        assert_eq!(
            f(r, "value"),
            &Json::Arr(vec![Json::Arr(vec![Json::str("v"), Json::str("p")])])
        );
    }
}
#[test]
fn observed_empty_map_with_empty_roster_is_complete_without_missing() {
    let w = run(
        fixture::input("empty", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    established(&w, "x");
    assert!(missing(answer(&w, "x")).is_empty());
}
#[test]
fn unknown_owner_map_return_and_nested_containers_retain_call_conditions() {
    for view in ["through", "containers"] {
        let ask = format!("x=evaluate(MapCall.{view},a=@v/A,h=@v/h)");
        let w = run(fixture::input("varying", "r1"), &[&ask]);
        let a = answer(&w, "x");
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert_eq!(missing(a), [p_missing()].into_iter().collect());
        domains(&w, &["A", "B"]);
        assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
        assert!(
            array(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("condition_failed"))
        );
    }
}
#[test]
fn unknown_owner_map_keeps_free_z_axis_and_all_consistent_owner_cases() {
    let w = run(
        fixture::input("varying", "r1"),
        &["x=check(MapCall.affine,a=@v/A,h=@v/h)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(missing(a), [p_missing()].into_iter().collect());
    domains(&w, &["A", "B"]);
    assert!(
        array(f(f(a, "scope"), "quantifiers"))
            .iter()
            .any(|q| f(q, "kind") == &Json::str("forall")
                && f(q, "name") == &Json::str("z")
                && f(q, "type") == &Json::str("Z"))
    );
}
#[test]
fn missing_map_and_owner_keep_five_joint_input_constrained_completions() {
    let w = run(
        fixture::input("missing_table", "r1"),
        &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"],
    );
    established(&w, "x");
    let expected = [
        p_missing(),
        Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("h")),
            ("field", Json::str("MapCall.Holder.table")),
        ])
        .canonical(),
    ]
    .into_iter()
    .collect();
    assert_eq!(missing(answer(&w, "x")), expected);
    let ty = Json::Arr(vec![
        Json::str("Tuple"),
        Json::Arr(vec![
            Json::str("Map"),
            Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Item")]),
            Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Item")]),
        ]),
        Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Root")]),
    ]);
    let ds: Vec<_> = array(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && matches!(f(n,"value"),Json::Obj(o)if o.get("type")==Some(&ty))
        })
        .collect();
    let reference = |s: &str| Json::Arr(vec![Json::str("v"), Json::str(s)]);
    let mut expected: std::collections::BTreeSet<_> = ["p", "q"]
        .into_iter()
        .flat_map(|first| {
            ["p", "q"].into_iter().map(move |second| {
                Json::Arr(vec![
                    Json::Arr(vec![
                        Json::Arr(vec![reference("p"), reference(first)]),
                        Json::Arr(vec![reference("q"), reference(second)]),
                    ]),
                    reference("A"),
                ])
                .canonical()
            })
        })
        .collect();
    expected.insert(
        Json::Arr(vec![
            Json::Arr(vec![Json::Arr(vec![reference("q"), reference("q")])]),
            reference("B"),
        ])
        .canonical(),
    );
    assert_eq!(expected.len(), 5);
    assert!(!ds.is_empty());
    for d in ds {
        assert_eq!(f(f(d, "value"), "kind"), &Json::str("finite"));
        let values: std::collections::BTreeSet<_> = array(f(f(d, "value"), "elements"))
            .iter()
            .map(|r| f(node(&w, r), "value").canonical())
            .collect();
        assert_eq!(values, expected);
    }
}
#[test]
fn unknown_owner_map_provenance_pair_preserves_math_and_current_sources() {
    let mut wires = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("varying", revision);
        let checked = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
        assert_eq!(checked.archmap().sources[0].revision, revision);
        let w = run(input, &["x=evaluate(MapCall.call,a=@v/A,h=@v/h)"]);
        domains(&w, &["A", "B"]);
        wires.push(w);
    }
    assert_eq!(f(&wires[0], "answers"), f(&wires[1], "answers"));
    assert_eq!(f(&wires[0], "nodes"), f(&wires[1], "nodes"));
    assert_ne!(f(&wires[0], "inputs"), f(&wires[1], "inputs"));
}

#[test]
fn unknown_owner_map_keeps_free_q_axis_and_original_missing() {
    let w = run(
        fixture::input("varying", "r1"),
        &["x=check(MapCall.rational,a=@v/A,h=@v/h)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(missing(a), [p_missing()].into_iter().collect());
    domains(&w, &["A", "B"]);
    assert!(
        array(f(f(a, "scope"), "quantifiers"))
            .iter()
            .any(|q| f(q, "kind") == &Json::str("forall")
                && f(q, "name") == &Json::str("q")
                && f(q, "type") == &Json::str("Q"))
    );
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
}
