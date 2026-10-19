use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
};
#[path = "common/unknown_owned_type.rs"]
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
fn run(input: InputSources, asks: &[&str]) -> Json {
    let c = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(input.clone(), asks, &mut quiet()).unwrap();
    assert_eq!(r.prepared().inputs().sources(), &input);
    assert_eq!(r.prepared().inputs().definitions(), c.definitions());
    assert_eq!(
        format!("{:?}", r.prepared().inputs().law()),
        format!("{:?}", c.law())
    );
    assert_eq!(
        format!("{:?}", r.prepared().inputs().archmap()),
        format!("{:?}", c.archmap())
    );
    assert!(matches!(r.status(), "complete" | "partial"));
    r.wire()
}
fn map_ty() -> Json {
    let item = Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Item")]);
    Json::Arr(vec![Json::str("Map"), item.clone(), item])
}
fn domains<'a>(w: &'a Json, ty: &Json) -> Vec<&'a Json> {
    let out: Vec<_> = array(f(w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && matches!(f(n,"value"),Json::Obj(o)if o.get("type")==Some(ty))
        })
        .collect();
    assert!(!out.is_empty());
    out
}
fn values(w: &Json, d: &Json) -> std::collections::BTreeSet<String> {
    array(f(f(d, "value"), "elements"))
        .iter()
        .map(|r| f(node(w, r), "value").canonical())
        .collect()
}
fn missing(w: &Json, id: &str) -> std::collections::BTreeSet<String> {
    array(f(answer(w, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| array(f(r, "missing")))
        .map(Json::canonical)
        .collect()
}
fn fact(subject: &str, field: &str) -> String {
    Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(subject)),
        ("field", Json::str(field)),
    ])
    .canonical()
}
fn no_algorithm(w: &Json, id: &str) {
    assert!(
        array(f(answer(w, id), "reasons"))
            .iter()
            .all(|r| f(r, "code") != &Json::str("unsupported_algorithm"))
    );
    assert_eq!(
        f(f(answer(w, id), "scope"), "domain"),
        &Json::str("all_completions")
    );
}
fn established(w: &Json, id: &str, value: bool) {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert_eq!(
        f(node(w, f(f(a, "outputs"), "value")), "value"),
        &Json::Bool(value)
    );
    no_algorithm(w, id);
}
fn both_owners(w: &Json) {
    let root = Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Root")]);
    let expected = ["A", "B"]
        .into_iter()
        .map(|s| Json::Arr(vec![Json::str("v"), Json::str(s)]).canonical())
        .collect();
    for d in domains(w, &root) {
        assert_eq!(values(w, d), expected);
    }
}
#[test]
fn unknown_owned_map_forall_keeps_both_complete_domains_and_true() {
    let w = run(
        fixture::input("plain", "r1"),
        &["x=evaluate(MapCall.typeEvery,a=@v/A,b=@v/A)"],
    );
    established(&w, "x", true);
    both_owners(&w);
    assert_eq!(
        missing(&w, "x"),
        [fact("p", "MapCall.Item.owner")].into_iter().collect()
    );
    let ds = domains(&w, &map_ty());
    assert_eq!(ds.len(), 2);
    let mut actual: Vec<_> = ds.iter().map(|d| values(&w, d)).collect();
    actual.sort();
    let p = Json::Arr(vec![Json::str("v"), Json::str("p")]);
    let mut expected = vec![
        [Json::Arr(vec![]).canonical()].into_iter().collect(),
        [Json::Arr(vec![Json::Arr(vec![p.clone(), p])]).canonical()]
            .into_iter()
            .collect(),
    ];
    expected.sort();
    assert_eq!(actual, expected);
}
#[test]
fn unknown_owned_map_exists_preserves_empty_source_and_empty_target_cases() {
    let w = run(
        fixture::input("plain", "r1"),
        &["x=evaluate(MapCall.typeAny,a=@v/A,b=@v/B)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    no_algorithm(&w, "x");
    both_owners(&w);
    assert_eq!(
        missing(&w, "x"),
        [fact("p", "MapCall.Item.owner")].into_iter().collect()
    );
    let mut actual: Vec<_> = domains(&w, &map_ty())
        .iter()
        .map(|d| values(&w, d))
        .collect();
    actual.sort();
    let mut expected = vec![
        std::collections::BTreeSet::new(),
        [Json::Arr(vec![]).canonical()].into_iter().collect(),
    ];
    expected.sort();
    assert_eq!(actual, expected);
}
#[test]
fn unknown_owned_map_forall_false_keeps_vacuous_case_and_actual_counterexample() {
    let w = run(
        fixture::input("plain", "r1"),
        &["x=evaluate(MapCall.typeFalse,a=@v/A,b=@v/B)"],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    no_algorithm(&w, "x");
    both_owners(&w);
    assert_eq!(
        missing(&w, "x"),
        [fact("p", "MapCall.Item.owner")].into_iter().collect()
    );
    let kinds: std::collections::BTreeSet<_> = array(f(&w, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evidence"))
        .map(|n| f(f(n, "value"), "kind").canonical())
        .collect();
    assert!(kinds.contains(&Json::str("counterexample").canonical()));
    assert!(kinds.contains(&Json::str("finite_exhaustion").canonical()));
}
#[test]
fn unknown_owned_map_option_tuple_set_keep_each_complete_finite_value() {
    let m = map_ty();
    for (view, ty, expected) in [
        (
            "typeOption",
            Json::Arr(vec![Json::str("Option"), m.clone()]),
            vec![
                vec![Json::obj([("none", Json::Bool(true))])],
                vec![
                    Json::obj([("none", Json::Bool(true))]),
                    Json::obj([("some", Json::Arr(vec![]))]),
                ],
            ],
        ),
        (
            "typeTuple",
            Json::Arr(vec![Json::str("Tuple"), Json::str("Unit"), m.clone()]),
            vec![
                vec![],
                vec![Json::Arr(vec![Json::Arr(vec![]), Json::Arr(vec![])])],
            ],
        ),
        (
            "typeSet",
            Json::Arr(vec![Json::str("Set"), m]),
            vec![
                vec![Json::Arr(vec![])],
                vec![Json::Arr(vec![]), Json::Arr(vec![Json::Arr(vec![])])],
            ],
        ),
    ] {
        let ask = format!("x=evaluate(MapCall.{view},a=@v/A,b=@v/B)");
        let w = run(fixture::input("plain", "r1"), &[&ask]);
        established(&w, "x", true);
        both_owners(&w);
        assert_eq!(
            missing(&w, "x"),
            [fact("p", "MapCall.Item.owner")].into_iter().collect()
        );
        let mut actual: Vec<_> = domains(&w, &ty).iter().map(|d| values(&w, d)).collect();
        actual.sort();
        let mut wanted: Vec<std::collections::BTreeSet<String>> = expected
            .into_iter()
            .map(|v| v.iter().map(Json::canonical).collect())
            .collect();
        wanted.sort();
        assert_eq!(actual, wanted);
    }
}
#[test]
fn explicit_owned_map_keeps_four_joint_owner_assignments_and_original_domains() {
    let w = run(
        fixture::input("two", "r1"),
        &["x=evaluate(MapCall.typeEvery,a=@v/A,b=@v/B)"],
    );
    established(&w, "x", true);
    assert_eq!(
        missing(&w, "x"),
        [
            fact("p", "MapCall.Item.owner"),
            fact("q", "MapCall.Item.owner")
        ]
        .into_iter()
        .collect()
    );
    let root = Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Root")]);
    let tuple = Json::Arr(vec![Json::str("Tuple"), root.clone(), root]);
    let expected: std::collections::BTreeSet<_> = ["A", "B"]
        .into_iter()
        .flat_map(|a| {
            ["A", "B"].into_iter().map(move |b| {
                Json::Arr(vec![
                    Json::Arr(vec![Json::str("v"), Json::str(a)]),
                    Json::Arr(vec![Json::str("v"), Json::str(b)]),
                ])
                .canonical()
            })
        })
        .collect();
    for d in domains(&w, &tuple) {
        assert_eq!(values(&w, d), expected);
    }
    let r = |s: &str| Json::Arr(vec![Json::str("v"), Json::str(s)]);
    let mut expected = vec![
        std::collections::BTreeSet::new(),
        [Json::Arr(vec![]).canonical()].into_iter().collect(),
        [Json::Arr(vec![Json::Arr(vec![r("p"), r("q")])]).canonical()]
            .into_iter()
            .collect(),
        [Json::Arr(vec![Json::Arr(vec![r("q"), r("p")])]).canonical()]
            .into_iter()
            .collect(),
    ];
    expected.sort();
    let mut actual: Vec<_> = domains(&w, &map_ty())
        .iter()
        .map(|d| values(&w, d))
        .collect();
    actual.sort();
    assert_eq!(actual, expected);
}
#[test]
fn owned_map_type_lexical_owner_rediscovers_roster_missing_without_stale_algorithm() {
    let w = run(
        fixture::input("lexical", "r1"),
        &["x=evaluate(MapCall.typeLexical,h=@v/h)"],
    );
    established(&w, "x", true);
    assert_eq!(
        missing(&w, "x"),
        [
            fact("h", "MapCall.Holder.owner"),
            fact("p", "MapCall.Item.owner")
        ]
        .into_iter()
        .collect()
    );
    let p = Json::Arr(vec![Json::str("v"), Json::str("p")]);
    let expected = [Json::Arr(vec![Json::Arr(vec![p.clone(), p])]).canonical()]
        .into_iter()
        .collect();
    let ds = domains(&w, &map_ty());
    assert_eq!(ds.len(), 2);
    for d in ds {
        assert_eq!(values(&w, d), expected);
    }
}
#[test]
fn owned_map_type_call_owner_keeps_actual_argument_producer_and_two_cases() {
    let w = run(
        fixture::input("lexical", "r1"),
        &["x=evaluate(MapCall.typeCall,h=@v/h)"],
    );
    established(&w, "x", true);
    assert_eq!(
        missing(&w, "x"),
        [
            fact("h", "MapCall.Holder.owner"),
            fact("p", "MapCall.Item.owner")
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(domains(&w, &map_ty()).len(), 2);
}
#[test]
fn owned_map_type_roster_completion_keeps_other_numeric_missing_and_exact_cancellation() {
    let w = run(
        fixture::numeric_input(),
        &["x=evaluate(Reservations.numeric,a=@v/A,b=@v/B,p=@v/p)"],
    );
    established(&w, "x", true);
    assert_eq!(
        missing(&w, "x"),
        [
            fact("p", "Reservations.State.owner"),
            fact("p", "Reservations.State.free")
        ]
        .into_iter()
        .collect()
    );
    let s = Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")]);
    let ty = Json::Arr(vec![Json::str("Map"), s.clone(), s]);
    let ds = domains(&w, &ty);
    assert_eq!(ds.len(), 1);
    assert_eq!(values(&w, ds[0]).len(), 4);
}
#[test]
fn owned_reference_type_uses_same_owner_completion_without_dropping_subject() {
    let w = run(
        fixture::input("plain", "r1"),
        &["x=evaluate(MapCall.typeRef,a=@v/A)"],
    );
    established(&w, "x", true);
    both_owners(&w);
    assert_eq!(
        missing(&w, "x"),
        [fact("p", "MapCall.Item.owner")].into_iter().collect()
    );
    let ty = Json::Arr(vec![Json::str("Ref"), Json::str("MapCall.Item")]);
    let mut sizes: Vec<_> = domains(&w, &ty)
        .iter()
        .map(|d| values(&w, d).len())
        .collect();
    sizes.sort();
    assert_eq!(sizes, vec![0, 1]);
}
#[test]
fn owned_map_type_provenance_pair_keeps_math_and_current_three_inputs() {
    let mut wires = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input("plain", revision);
        let c = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
        assert_eq!(c.archmap().sources[0].revision, revision);
        let w = run(input, &["x=evaluate(MapCall.typeEvery,a=@v/A,b=@v/A)"]);
        established(&w, "x", true);
        both_owners(&w);
        wires.push(w);
    }
    assert_eq!(f(&wires[0], "answers"), f(&wires[1], "answers"));
    assert_eq!(f(&wires[0], "nodes"), f(&wires[1], "nodes"));
    assert_ne!(f(&wires[0], "inputs"), f(&wires[1], "inputs"));
}
