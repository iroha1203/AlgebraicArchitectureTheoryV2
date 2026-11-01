use crate::common::object_view_compatibility_data as fixture;
use crate::common::quiet;
use archsig::{
    canonical::Json,
    input::{CheckedInputs, InputSources, check_inputs},
    observed::{
        object_evaluate::ObjectEvaluationOutcome,
        object_view_compatibility::{
            ObjectViewCompatibility, ViewCompatibilityCondition as Failed,
            ViewCompatibilityOutcome as Outcome, object_view_compatibility,
        },
    },
};
use fixture::{A, D};
use std::sync::Arc;
fn inputs(body: &str, map: &str) -> Arc<CheckedInputs> {
    let defs = archsig::definition::check_definitions(&[("definition0", D.as_bytes())]).unwrap();
    let digest = &defs.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Pattern version \"1\" digest \"{digest}\"; {body} }}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![D.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn run(i: Arc<CheckedInputs>) -> ObjectViewCompatibility {
    object_view_compatibility(i, "Selected", "v", "root", &quiet()).unwrap()
}
fn second_part(map: &str) -> String {
    map.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"r\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.quantity\",\"value\":\"5\",\"origin\":\"model\"},")
}
#[test]
fn equal_patterns_keep_distinct_objects_and_compare_every_ground_view() {
    let i = inputs(
        "view amount(c:Part):Z=c.quantity; view flag(c:Part):Bool=false; view empty(c:Part):Option<Bool> = none<Bool>;",
        A,
    );
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.profiles().classes().unwrap(), [vec![0, 1]]);
    assert_eq!(
        r.readings()
            .objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["root", "p"]
    );
    assert_eq!(r.evaluations().len(), 6);
    assert_eq!(r.comparisons().len(), 3);
    for (check, expected) in r.comparisons().iter().zip([
        Json::str("2"),
        Json::obj([("none", Json::Bool(true))]),
        Json::Bool(false),
    ]) {
        assert_eq!((check.source_object(), check.target_object()), (0, 1));
        assert_eq!(check.outcome(), Some(&Outcome::Compatible));
        assert_eq!(check.points().len(), 1);
        let p = &check.points()[0];
        assert!(p.arguments().is_empty());
        assert_eq!(p.source().unwrap().wire(), expected);
        assert_eq!(p.target().unwrap().wire(), expected);
    }
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn the_same_pattern_rejects_application_and_contextual_value_disagreement() {
    for (body, expected) in [
        (
            "view atRoot(a:Root):Bool=true;",
            Outcome::Refuted(Failed::Applicability),
        ),
        (
            "view contextual(c:Part):Bool=forall a:Root . false;",
            Outcome::Refuted(Failed::Value),
        ),
    ] {
        let i = inputs(body, A);
        let r = run(Arc::clone(&i));
        assert_eq!(r.profiles().classes().unwrap(), [vec![0, 1]]);
        assert_eq!(r.outcome(), Some(&expected));
        assert_eq!(r.comparisons().len(), 1);
        let check = &r.comparisons()[0];
        assert_eq!(check.outcome(), Some(&expected));
        if expected == Outcome::Refuted(Failed::Value) {
            assert_eq!(
                check.points()[0].source().unwrap().wire(),
                Json::Bool(false)
            );
            assert_eq!(check.points()[0].target().unwrap().wire(), Json::Bool(true));
        } else {
            assert!(check.points().is_empty());
            assert!(matches!(
                r.evaluations()[1].evaluation().outcome(),
                ObjectEvaluationOutcome::NotApplicable
            ));
        }
        r.recheck(i, &quiet()).unwrap();
    }
}
#[test]
fn finite_parameters_compare_all_six_assignments_and_keep_a_partial_refutation() {
    let i = inputs(
        "view family(c:Part,b:Bool,x:Option<Bool>):(Bool,Option<Bool>)=(b,x);",
        A,
    );
    let r = run(Arc::clone(&i));
    let points = r.comparisons()[0].points();
    assert_eq!(points.len(), 6);
    let none = Json::obj([("none", Json::Bool(true))]);
    let some = |b| Json::obj([("some", Json::Bool(b))]);
    let expected = [
        (false, none.clone()),
        (false, some(false)),
        (false, some(true)),
        (true, none),
        (true, some(false)),
        (true, some(true)),
    ];
    for (point, (b, x)) in points.iter().zip(expected) {
        let values = vec![Json::Bool(b), x];
        assert_eq!(
            point
                .arguments()
                .iter()
                .map(|v| v.wire())
                .collect::<Vec<_>>(),
            values
        );
        assert_eq!(point.source().unwrap().wire(), Json::Arr(values.clone()));
        assert_eq!(point.target().unwrap().wire(), Json::Arr(values));
        assert_eq!(point.outcome(), &Outcome::Compatible);
    }
    r.recheck(i, &quiet()).unwrap();
    let i = inputs(
        "view family(c:Part,b:Bool):Bool=if b then (forall a:Root . false) else false;",
        A,
    );
    let r = run(Arc::clone(&i));
    let points = r.comparisons()[0].points();
    assert_eq!(points.len(), 2);
    assert_eq!(points[0].outcome(), &Outcome::Compatible);
    assert_eq!(points[1].outcome(), &Outcome::Refuted(Failed::Value));
    assert_eq!(r.outcome(), Some(&Outcome::Refuted(Failed::Value)));
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn different_patterns_do_not_impose_equal_values_on_distinct_parts() {
    let i = inputs("view amount(c:Part):Z=c.quantity;", &second_part(A));
    let r = run(Arc::clone(&i));
    assert!(r.profiles().is_complete());
    assert_eq!(r.profiles().classes().unwrap(), [vec![0], vec![1], vec![2]]);
    assert_eq!(r.evaluations().len(), 6);
    assert!(r.comparisons().is_empty());
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn unknown_values_stay_unknown_even_without_a_pair_to_compare() {
    let map=second_part(A).replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"x\",\"type\":\"Pattern.External\",\"origin\":\"model\"}");
    let i = inputs("view missing(c:Part,x:External):Z=x.quantity;", &map);
    let r = run(Arc::clone(&i));
    assert!(r.profiles().is_complete());
    assert!(r.comparisons().is_empty());
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert_eq!(r.evaluations().len(), 6);
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn empty_families_and_the_single_empty_list_are_distinct_known_domains() {
    for (ty, rows) in [("(Vacant,Bool)", 0), ("List<Vacant>", 1)] {
        let i = inputs(&format!("view family(c:Part,x:{ty}):Bool=false;"), A);
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Compatible));
        assert_eq!(r.comparisons()[0].points().len(), rows);
        for e in r.evaluations() {
            let ObjectEvaluationOutcome::FiniteView(f) = e.evaluation().outcome() else {
                panic!("finite")
            };
            assert!(f.is_complete());
            assert_eq!(f.rows().len(), rows);
        }
        r.recheck(i, &quiet()).unwrap();
    }
}
#[test]
fn current_input_bytes_body_and_unused_provenance_are_rechecked() {
    let body = "view amount(c:Part):Z=c.quantity;";
    let i = inputs(body, A);
    let r = run(Arc::clone(&i));
    for changed in [
        inputs(&body.replace("c.quantity;", "c.quantity+1;"), A),
        inputs(body, &A.replace("\"value\":\"2\"", "\"value\":\"9\"")),
        inputs(body, &A.replace("fixture-r1", "fixture-r2")),
    ] {
        assert!(r.recheck(changed, &quiet()).is_err());
    }
    r.recheck(i, &quiet()).unwrap();
}

#[test]
fn conditional_membership_and_known_conflicts_keep_their_separate_evidence() {
    let map=A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"t\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"quantity-t\",\"subject\":\"t\",\"field\":\"Pattern.Part.quantity\",\"value\":\"8\",\"origin\":\"model\"},");
    let i = inputs("view amount(c:Part):Z=c.quantity;", &map);
    let r = run(Arc::clone(&i));
    assert!(!r.profiles().is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert!(r.evaluations().iter().any(|e|matches!(e.evaluation().outcome(),ObjectEvaluationOutcome::Conditional(conditions) if conditions.iter().any(|c|c.slot().subject=="t" && c.slot().field.as_deref()==Some("Pattern.Part.owner")))));
    r.recheck(i, &quiet()).unwrap();
    let i = inputs("view family(c:Root,x:Option<Part[c]>):Bool=false;", &map);
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert!(r.evaluations().iter().any(|e|matches!(e.evaluation().outcome(),ObjectEvaluationOutcome::FiniteView(f) if f.missing().iter().any(|slot|slot.subject=="t" && slot.field.as_deref()==Some("Pattern.Part.owner")))));
    r.recheck(i, &quiet()).unwrap();
    let map=A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"x\",\"type\":\"Pattern.External\",\"origin\":\"model\"}");
    let i = inputs(
        "view atRoot(a:Root):Bool=true; view missing(c:Part,x:External):Z=x.quantity;",
        &map,
    );
    let r = run(Arc::clone(&i));
    assert!(r.profiles().is_complete());
    assert_eq!(r.evaluations().len(), 4);
    assert_eq!(r.comparisons().len(), 2);
    assert_eq!(
        r.comparisons()[0].outcome(),
        Some(&Outcome::Refuted(Failed::Applicability))
    );
    assert_eq!(r.comparisons()[1].outcome(), Some(&Outcome::Undetermined));
    assert_eq!(r.outcome(), Some(&Outcome::Refuted(Failed::Applicability)));
    r.recheck(i, &quiet()).unwrap();
}

#[test]
fn unsupported_parameter_evaluation_is_preserved_as_an_execution_failure() {
    use archsig::observed::object_evaluate::ObjectEvaluationFailure;
    let i = inputs("view family(c:Part,n:Z):Z=n+c.quantity;", A);
    let f = object_view_compatibility(i, "Selected", "v", "root", &quiet()).unwrap_err();
    assert!(matches!(
        f.cause(),
        ObjectEvaluationFailure::NotImplemented { .. }
    ));
    let r = f.partial().unwrap();
    assert!(r.evaluations().is_empty());
    assert!(!r.is_complete());
    assert!(r.outcome().is_none());
    assert_eq!(f.position().unwrap().object, 0);
}

#[test]
fn external_helpers_are_called_from_the_original_view_without_becoming_extra_axes() {
    let map=A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"x\",\"type\":\"Pattern.External\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"quantity-x\",\"subject\":\"x\",\"field\":\"Pattern.External.quantity\",\"value\":\"9\",\"origin\":\"model\"},");
    let i = inputs(
        "view helper(x:External):Z=x.quantity; view amount(c:Part,x:External):Z=c.quantity+helper(x);",
        &map,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.readings().declarations().len(), 2);
    assert_eq!(r.readings().instances().len(), 1);
    assert_eq!(
        r.readings().instances()[0].declaration().name,
        "Selected.amount"
    );
    assert_eq!(r.evaluations().len(), 2);
    assert_eq!(r.comparisons().len(), 1);
    assert_eq!(
        r.comparisons()[0].points()[0].source().unwrap().wire(),
        Json::str("11")
    );
    assert_eq!(
        r.comparisons()[0].points()[0].target().unwrap().wire(),
        Json::str("11")
    );
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    r.recheck(i, &quiet()).unwrap();
}

fn check_contextual_terms(body: &str, rows: usize) {
    let i = inputs(body, A);
    let r = run(Arc::clone(&i));
    assert_eq!(r.profiles().classes().unwrap(), [vec![0, 1]]);
    assert!(r.is_complete());
    let comparison = &r.comparisons()[0];
    assert_eq!(comparison.points().len(), rows);
    for point in comparison.points() {
        assert_ne!(
            point.source().unwrap().wire(),
            point.target().unwrap().wire()
        );
        assert_eq!(point.outcome(), &Outcome::Compatible);
    }
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    r.recheck(i, &quiet()).unwrap();
}
#[test]
fn ground_boolean_terms_use_function_extensional_equality_instead_of_program_identity() {
    check_contextual_terms(
        "view functions(c:Part):Term<(Bool)->Bool> = if (forall a:Root . false) then (fn(x:Bool)=>x) else (fn(y:Bool)=>not not y);",
        1,
    );
}
#[test]
fn ground_affine_terms_use_exact_normalization_instead_of_program_identity() {
    check_contextual_terms(
        "view functions(c:Part):Term<(Z)->Z> = if (forall a:Root . false) then (fn(x:Z)=>x+x) else (fn(y:Z)=>2*y);",
        1,
    );
}
#[test]
fn finite_family_option_terms_use_function_extensional_equality_at_every_argument() {
    check_contextual_terms(
        "view functions(c:Part,b:Bool):Option<Term<(Bool)->Bool>> = if (forall a:Root . false) then some(fn(x:Bool)=>x) else some(fn(y:Bool)=>not not y);",
        2,
    );
}

#[test]
fn nested_list_and_tuple_terms_use_mathematical_equality() {
    check_contextual_terms(
        "view functions(c:Part):List<(Term<(Bool)->Bool>,Z)> = if (forall a:Root . false) then list<(Term<(Bool)->Bool>,Z)>[((fn(x:Bool)=>x),3)] else list<(Term<(Bool)->Bool>,Z)>[((fn(y:Bool)=>not not y),3)];",
        1,
    );
}

#[test]
fn unequal_term_functions_keep_a_real_value_counterexample() {
    let i = inputs(
        "view functions(c:Part):Term<(Bool)->Bool> = if (forall a:Root . false) then (fn(x:Bool)=>x) else (fn(y:Bool)=>not y);",
        A,
    );
    let r = run(Arc::clone(&i));
    let point = &r.comparisons()[0].points()[0];
    assert!(point.source().is_some() && point.target().is_some());
    assert_eq!(point.outcome(), &Outcome::Refuted(Failed::Value));
    assert_eq!(r.outcome(), Some(&Outcome::Refuted(Failed::Value)));
    r.recheck(i, &quiet()).unwrap();
}

#[test]
fn nonlinear_unbounded_terms_are_unsupported_instead_of_refuted_or_missing() {
    let i = inputs(
        "view functions(c:Part):Term<(Z)->Z> = if (forall a:Root . false) then (fn(x:Z)=>x*x) else (fn(y:Z)=>y*y);",
        A,
    );
    let r = run(Arc::clone(&i));
    assert!(r.profiles().is_complete() && r.is_complete());
    let point = &r.comparisons()[0].points()[0];
    assert!(point.source().is_some() && point.target().is_some());
    assert_ne!(
        point.source().unwrap().wire(),
        point.target().unwrap().wire()
    );
    assert_eq!(point.outcome(), &Outcome::UnsupportedAlgorithm);
    assert_eq!(
        r.comparisons()[0].outcome(),
        Some(&Outcome::UnsupportedAlgorithm)
    );
    assert_eq!(r.outcome(), Some(&Outcome::UnsupportedAlgorithm));
    r.recheck(i, &quiet()).unwrap();
}

#[test]
fn path_and_nested_path_comparison_values_have_safe_original_node_representations() {
    fn field<'a>(j: &'a Json, key: &str) -> &'a Json {
        let Json::Obj(fields) = j else {
            panic!("object")
        };
        fields.get(key).unwrap()
    }
    fn find_node<'a>(nodes: &'a [Json], id: &Json) -> &'a Json {
        nodes.iter().find(|node| field(node, "id") == id).unwrap()
    }
    fn check_path(j: &Json, nodes: &[Json]) -> usize {
        match j {
            Json::Obj(fields) if fields.contains_key("reading") => {
                assert_eq!(field(j, "reading"), &Json::str("Selected"));
                assert_eq!(field(j, "generators"), &Json::Arr(vec![]));
                assert_eq!(field(j, "source"), field(j, "target"));
                let source = find_node(nodes, field(field(j, "source"), "node"));
                assert_eq!(
                    field(source, "value"),
                    &Json::Arr(vec![Json::str("v"), Json::str("p")])
                );
                1
            }
            Json::Obj(fields) if fields.contains_key("node") => {
                check_path(field(find_node(nodes, field(j, "node")), "value"), nodes)
            }
            Json::Obj(fields) if fields.contains_key("some") => check_path(field(j, "some"), nodes),
            Json::Arr(items) => items.iter().map(|j| check_path(j, nodes)).sum(),
            Json::Bool(false) => 0,
            _ => panic!("unexpected typed Path representation {j:?}"),
        }
    }
    for body in [
        "view route(c:Part):Path<Part,Part> = identity(c);",
        "view route(c:Part):Option<Path<Part,Part>> = some(identity(c));",
        "view route(c:Part):(Bool,Path<Part,Part>) = (false,identity(c));",
        "view route(c:Part,b:Bool):List<Path<Part,Part>> = list<Path<Part,Part>>[identity(c)];",
    ] {
        let i = inputs(body, A);
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Compatible));
        assert!(r.is_complete());
        let comparison = &r.comparisons()[0];
        for point in comparison.points() {
            for (object, row, value) in [
                (
                    comparison.source_object(),
                    point.source_row(),
                    point.source().unwrap(),
                ),
                (
                    comparison.target_object(),
                    point.target_row().unwrap(),
                    point.target().unwrap(),
                ),
            ] {
                let e = r
                    .evaluations()
                    .iter()
                    .find(|e| {
                        e.position().object == object
                            && e.position().instance == comparison.instance()
                    })
                    .unwrap();
                let evaluation = match e.evaluation().outcome() {
                    ObjectEvaluationOutcome::Evaluated(e) => e,
                    ObjectEvaluationOutcome::FiniteView(f) => f.rows()[row].evaluation(),
                    _ => panic!("original evaluated view"),
                };
                let graph = evaluation.wire();
                let Json::Arr(nodes) = field(&graph, "nodes") else {
                    panic!("nodes")
                };
                let producer = find_node(nodes, &Json::str(format!("n{}", value.producer())));
                let wire = value.wire();
                assert_eq!(&wire, field(producer, "value"));
                assert_eq!(check_path(&wire, nodes), 1);
            }
        }
        r.recheck(i, &quiet()).unwrap();
    }
}
