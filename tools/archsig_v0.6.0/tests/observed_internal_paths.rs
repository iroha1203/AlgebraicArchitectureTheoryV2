use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
};
#[path = "common/finite_map.rs"]
#[allow(dead_code)]
mod fixture;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
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
fn input() -> InputSources {
    let d = archsig::definition::check_definitions(&[(
        "definition0",
        fixture::OWNED_DEFINITIONS.as_bytes(),
    )])
    .unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    let body = "view step(e:Reserve):Path<State,State> =path(e); view maybe(e:Reserve):Option<Path<State,State>> =some(path(e)); view first(e:Reserve):State=source(path(e)); view last(e:Reserve):State=target(path(e));";
    let law = fixture::owned_law(digest).replace(
        fixture::OWNED_SCRIPT,
        &(fixture::OWNED_SCRIPT.to_owned() + body),
    );
    InputSources::from_bytes(
        vec![fixture::OWNED_DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        fixture::owned_archmap(false).into_bytes(),
    )
}
#[test]
fn internal_arrow_path_keeps_original_generator_and_distinct_endpoints() {
    let inputs = input();
    let r = evaluate_observed_bytes(
        inputs.clone(),
        &["p=evaluate(Reservations.step,e=@v/e)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.prepared().inputs().sources(), &inputs);
    assert_eq!(r.status(), "complete", "{:?}", r.wire());
    let w = r.wire();
    let a = &array(f(&w, "answers"))[0];
    assert_eq!(f(a, "status"), &Json::str("established"));
    let path = node(&w, f(f(a, "outputs"), "value"));
    let value = f(path, "value");
    assert_eq!(f(value, "reading"), &Json::str("Reservations"));
    for (key, subject) in [("source", "p"), ("target", "q")] {
        let n = node(&w, f(value, key));
        assert_eq!(
            f(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(subject)])
        );
    }
    let generators = array(f(value, "generators"));
    assert_eq!(generators.len(), 1);
    assert_eq!(
        f(node(&w, &generators[0]), "value"),
        &Json::Arr(vec![Json::str("v"), Json::str("e")])
    );
}
#[path = "common/internal_paths.rs"]
#[allow(dead_code)]
mod small;
fn run_small(mode: &str, asks: &[&str]) -> Json {
    let inputs = small::input(mode, "r1");
    let r = evaluate_observed_bytes(inputs.clone(), asks, &mut quiet()).unwrap();
    assert_eq!(r.prepared().inputs().sources(), &inputs);
    assert!(
        matches!(r.status(), "complete" | "partial"),
        "{:?}",
        f(&r.wire(), "issues")
    );
    r.wire()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    array(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn answer_value<'a>(w: &'a Json, id: &str) -> &'a Json {
    f(node(w, f(f(answer(w, id), "outputs"), "value")), "value")
}
#[test]
fn one_step_named_generators_compare_actual_action_and_keep_empty_identity_distinct() {
    let w = run_small(
        "normal",
        &[
            "same=evaluate(Walk.same,e=@v/e,f=@v/alias)",
            "different=evaluate(Walk.same,e=@v/e,f=@v/different)",
            "identity=evaluate(Walk.self_action,e=@v/self)",
            "nonidentity=evaluate(Walk.self_action,e=@v/e)",
            "word=evaluate(Walk.step,e=@v/self)",
        ],
    );
    for (id, v) in [
        ("same", true),
        ("different", false),
        ("identity", true),
        ("nonidentity", false),
    ] {
        assert_eq!(f(answer(&w, id), "status"), &Json::str("established"));
        assert_eq!(answer_value(&w, id), &Json::Bool(v));
    }
    assert_eq!(array(f(answer_value(&w, "word"), "generators")).len(), 1);
}
#[test]
fn internal_path_known_reference_structure_mismatch_returns_original_condition_failure() {
    let w = run_small(
        "mismatch",
        &[
            "seed=evaluate(Walk.seed)",
            "x=evaluate(Walk.step,e=@v/e)",
            "later=evaluate(Walk.seed)",
        ],
    );
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
    assert_eq!(answer_value(&w, "seed"), &Json::str("1"));
    assert_eq!(answer_value(&w, "later"), &Json::str("1"));
}
#[test]
fn internal_path_missing_target_field_keeps_original_slot_without_fabricating_atom() {
    let w = run_small("missing_tag", &["x=evaluate(Walk.step,e=@v/e)"]);
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation")
                && f(r, "missing").canonical().contains("Paths.Node.mark"))
    );
}
#[test]
fn internal_path_unknown_endpoint_keeps_correlated_cases_and_original_missing() {
    let w = run_small(
        "missing_to",
        &[
            "path=evaluate(Walk.step,e=@v/e)",
            "same=evaluate(Walk.missing_same,e=@v/e)",
        ],
    );
    let a = answer(&w, "path");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert_eq!(f(answer(&w, "same"), "status"), &Json::str("established"));
    assert_eq!(answer_value(&w, "same"), &Json::Bool(true));
    for id in ["path", "same"] {
        let a = answer(&w, id);
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        assert!(
            array(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("missing_observation")
                    && f(r, "missing").canonical().contains("Paths.Hop.to"))
        );
        assert!(
            !array(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        );
    }
}
#[test]
fn internal_path_containers_lexical_calls_and_endpoints_keep_prior_typed_dependencies() {
    let w = run_small(
        "normal",
        &[
            "maybe=evaluate(Walk.maybe,e=@v/e)",
            "nested=evaluate(Walk.nested,e=@v/e)",
            "lexical=evaluate(Walk.lexical,e=@v/e)",
            "first=evaluate(Walk.first,e=@v/e)",
            "last=evaluate(Walk.last,e=@v/e)",
        ],
    );
    let path_ty = Json::Arr(vec![
        Json::str("Path"),
        Json::str("Paths.Node"),
        Json::str("Paths.Node"),
    ]);
    let p = node(&w, f(answer_value(&w, "maybe"), "some"));
    assert_eq!(f(p, "type"), &path_ty);
    assert_eq!(array(f(f(p, "value"), "generators")).len(), 1);
    let list = node(&w, f(answer_value(&w, "nested"), "some"));
    let rows = array(f(list, "value"));
    assert_eq!(rows.len(), 2);
    for (row, flag) in rows.iter().zip([true, false]) {
        let row = node(&w, row);
        let fields = array(f(row, "value"));
        assert_eq!(f(node(&w, &fields[0]), "value"), &Json::Bool(flag));
        let p = node(&w, &fields[1]);
        assert_eq!(f(p, "type"), &path_ty);
        assert_eq!(array(f(f(p, "value"), "generators")).len(), 1);
    }
    assert_eq!(array(f(answer_value(&w, "lexical"), "generators")).len(), 1);
    assert_eq!(
        answer_value(&w, "first"),
        &Json::Arr(vec![Json::str("v"), Json::str("p")])
    );
    assert_eq!(
        answer_value(&w, "last"),
        &Json::Arr(vec![Json::str("v"), Json::str("q")])
    );
}
#[test]
fn internal_path_provenance_pair_retains_math_and_returns_to_current_inputs() {
    let mut out = vec![];
    for revision in ["r1", "r2"] {
        let inputs = small::input("normal", revision);
        let checked = archsig::observed::input::check_inputs(inputs.clone(), &mut quiet()).unwrap();
        assert_eq!(checked.archmap().sources[0].revision, revision);
        let r = evaluate_observed_bytes(
            inputs.clone(),
            &["x=evaluate(Walk.maybe,e=@v/e)"],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "complete");
        assert_eq!(r.prepared().inputs().sources(), &inputs);
        assert_eq!(r.prepared().inputs().definitions(), checked.definitions());
        assert_eq!(
            format!("{:?}", r.prepared().inputs().law()),
            format!("{:?}", checked.law())
        );
        assert_eq!(
            format!("{:?}", r.prepared().inputs().archmap()),
            format!("{:?}", checked.archmap())
        );
        out.push(r.wire());
    }
    assert_eq!(f(&out[0], "answers"), f(&out[1], "answers"));
    assert_eq!(f(&out[0], "nodes"), f(&out[1], "nodes"));
    assert_ne!(f(&out[0], "inputs"), f(&out[1], "inputs"));
}

#[test]
fn internal_path_reference_list_order_and_duplicates_are_construction_conditions() {
    let w = run_small("list_mismatch", &["x=evaluate(Walk.step,e=@v/e)"]);
    assert_eq!(f(answer(&w, "x"), "status"), &Json::str("undetermined"));
    assert!(
        array(f(answer(&w, "x"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("condition_failed"))
    );
}
#[test]
fn internal_path_missing_source_field_keeps_original_requirement_without_partial_action() {
    let w = run_small("missing_source", &["x=evaluate(Walk.step,e=@v/e)"]);
    let a = answer(&w, "x");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(matches!(f(a,"outputs"),Json::Obj(o)if !o.contains_key("value")));
    assert!(
        array(f(a, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation")
                && f(r, "missing").canonical().contains("Paths.Node.mark"))
    );
}
