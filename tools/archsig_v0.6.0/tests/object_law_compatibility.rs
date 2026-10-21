use archsig::{
    construction::readings::{
        LawCompatibilityCondition as Failed, LawCompatibilityOutcome as Outcome,
        ObjectLawCompatibility, object_law_compatibility,
    },
    observed::{
        control::{Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
};
use std::sync::Arc;
#[path = "common/object_view_compatibility_data.rs"]
mod fixture;
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn inputs(body: &str, map: &str) -> Arc<CheckedInputs> {
    inputs_with_definitions(fixture::D, body, map)
}
fn inputs_with_definitions(definitions: &str, body: &str, map: &str) -> Arc<CheckedInputs> {
    let d =
        archsig::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Selected {{ use vocabulary Pattern version \"1\" digest \"{digest}\"; {body} }}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definitions.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &mut quiet(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues())),
    )
}
fn run(i: Arc<CheckedInputs>) -> ObjectLawCompatibility {
    object_law_compatibility(i, "Selected", "v", "root", &mut quiet())
        .unwrap_or_else(|f| panic!("{:?}", f.cause()))
}
#[test]
fn equal_pattern_ground_laws_keep_roles_original_truth_and_all_evaluations() {
    let i = inputs(
        "law required amount(c:Part):c.quantity=2; law optional refused(c:Part):false; law required guarded(c:Part) when false:false;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.profiles().classes().unwrap(), [vec![0, 1]]);
    assert_eq!(r.evaluations().len(), 6);
    assert_eq!(r.comparisons().len(), 3);
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert!(r.is_complete());
    for e in r.evaluations() {
        assert!(e.family().is_complete());
        assert_eq!(e.family().rows().len(), 1);
    }
    let refused = r
        .comparisons()
        .iter()
        .find(|p| r.readings().instances()[p.instance()].declaration().name == "Selected.refused")
        .unwrap();
    assert!(!refused.points()[0].source().required());
    assert_eq!(refused.points()[0].source().body(), Some(false));
    assert_eq!(refused.points()[0].target().body(), Some(false));
    let guarded = r
        .comparisons()
        .iter()
        .find(|p| r.readings().instances()[p.instance()].declaration().name == "Selected.guarded")
        .unwrap();
    assert_eq!(
        guarded.points()[0].source().application().value(),
        Some(false)
    );
    assert_eq!(guarded.points()[0].source().conditional(), Some(true));
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn ground_application_guard_and_body_disagreement_keep_the_original_counterexample() {
    for (body, condition) in [
        (
            "law required body(c:Part):forall a:Root . false;",
            Failed::Holds,
        ),
        (
            "law required guarded(c:Part) when (forall a:Root . false):true;",
            Failed::Applicability,
        ),
        ("law required rootOnly(a:Root):true;", Failed::Applicability),
    ] {
        let i = inputs(body, fixture::A);
        let r = run(Arc::clone(&i));
        assert_eq!(r.outcome(), Some(&Outcome::Refuted(condition.clone())));
        assert_eq!(
            r.comparisons()[0].outcome(),
            Some(&Outcome::Refuted(condition))
        );
        assert_eq!(r.evaluations().len(), 2);
        assert_eq!(r.comparisons()[0].points().len(), 1);
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn two_refuted_whole_laws_do_not_hide_disagreement_at_each_boolean_argument() {
    let i = inputs(
        "law required family(c:Part,b:Bool):if (forall a:Root . false) then b else not b;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Refuted(Failed::Holds)));
    for e in r.evaluations() {
        let archsig::construction::readings::ObjectEvaluationOutcome::Evaluated(graph) =
            e.evaluation().outcome()
        else {
            panic!("evaluated Law")
        };
        assert_eq!(graph.status(), "complete");
        let archsig::canonical::Json::Obj(ref wire) = graph.wire() else {
            panic!("graph")
        };
        let archsig::canonical::Json::Arr(answers) = &wire["answers"] else {
            panic!("answers")
        };
        let archsig::canonical::Json::Obj(answer) = &answers[0] else {
            panic!("answer")
        };
        assert_eq!(answer["status"], archsig::canonical::Json::str("refuted"));
        assert!(e.family().is_complete());
        assert_eq!(e.family().rows().len(), 2);
    }
    let points = r.comparisons()[0].points();
    assert_eq!(points.len(), 2);
    for (p, (argument, source, target)) in points
        .iter()
        .zip([(false, true, false), (true, false, true)])
    {
        assert_eq!(
            p.arguments()[0].wire(),
            archsig::canonical::Json::Bool(argument)
        );
        assert_eq!(p.source().application().value(), Some(true));
        assert_eq!(p.target().application().value(), Some(true));
        assert_eq!(p.source().body(), Some(source));
        assert_eq!(p.target().body(), Some(target));
        assert_eq!(p.source_evaluations().len(), 1);
        assert_eq!(p.target_evaluations().len(), 1);
        assert_eq!(p.outcome(), &Outcome::Refuted(Failed::Holds));
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn all_six_guarded_parameter_assignments_keep_false_none_and_conditional_truth_separate() {
    use archsig::canonical::Json;
    let i = inputs(
        "law optional family(c:Part,b:Bool,x:Option<Bool>) when x!=none<Bool>:not b;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    let points = r.comparisons()[0].points();
    assert_eq!(points.len(), 6);
    let values = [
        Json::obj([("none", Json::Bool(true))]),
        Json::obj([("some", Json::Bool(false))]),
        Json::obj([("some", Json::Bool(true))]),
    ];
    for (index, p) in points.iter().enumerate() {
        let b = index >= 3;
        let x = index % 3;
        assert_eq!(
            p.arguments().iter().map(|v| v.wire()).collect::<Vec<_>>(),
            vec![Json::Bool(b), values[x].clone()]
        );
        assert!(!p.source().required());
        assert_eq!(p.source().application().value(), Some(x != 0));
        assert_eq!(p.target().application().value(), Some(x != 0));
        if x != 0 {
            assert_eq!(p.source().body(), Some(!b));
            assert_eq!(p.target().body(), Some(!b));
        }
        assert_eq!(p.source().conditional(), Some(x == 0 || !b));
        assert_eq!(p.target().conditional(), Some(x == 0 || !b));
        assert_eq!(p.outcome(), &Outcome::Compatible);
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn empty_parameter_domains_are_known_while_missing_required_values_remain_undetermined() {
    let i = inputs(
        "law required empty(c:Part,x:(Vacant,Bool)):false;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert!(r.comparisons()[0].points().is_empty());
    for e in r.evaluations() {
        assert!(e.family().is_complete());
        assert!(e.family().rows().is_empty());
        assert!(e.family().domains()[0].values().is_empty());
    }
    r.recheck(i, &mut quiet()).unwrap();
    let map = fixture::A
        .lines()
        .filter(|line| !line.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs("law required missing(c:Part):c.quantity=2;", &map);
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert!(r.evaluations().iter().any(|e| {
        e.family()
            .rows()
            .iter()
            .any(|r| r.reading().body().is_none())
    }));
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn owner_domain_and_conditional_membership_remain_unknown_with_the_original_slots() {
    use archsig::construction::maps::LawApplication;
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"t\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}");
    let i = inputs(
        "law required belongs(c:Part):true; law optional ownerDomain(a:Root,x:Option<Part[a]>):true;",
        &map,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert!(r.evaluations().iter().any(|e| {
        e.family()
            .missing()
            .iter()
            .any(|f| f.subject == "t" && f.field.as_deref() == Some("Pattern.Part.owner"))
    }));
    assert!(r.evaluations().iter().any(|e| {
        e.family()
            .uniform()
            .is_some_and(|v| matches!(v.application(), LawApplication::ConditionalMembership(_)))
    }));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn an_empty_element_list_is_one_law_assignment_with_a_real_false_body() {
    use archsig::canonical::Json;
    let i = inputs(
        "law required singleton(c:Part,x:List<Vacant>):false;",
        fixture::A,
    );
    let r = run(Arc::clone(&i));
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    let point = &r.comparisons()[0].points()[0];
    assert_eq!(r.comparisons()[0].points().len(), 1);
    assert_eq!(point.arguments()[0].wire(), Json::Arr(vec![]));
    assert_eq!(point.source().body(), Some(false));
    assert_eq!(point.target().body(), Some(false));
    assert_eq!(point.source_evaluations().len(), 1);
    assert_eq!(point.target_evaluations().len(), 1);
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn different_patterns_keep_their_own_law_readings_without_imposing_equality() {
    let map=fixture::A.replace("{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}","{\"id\":\"p\",\"type\":\"Pattern.Part\",\"origin\":\"model\"},{\"id\":\"r\",\"type\":\"Pattern.Part\",\"origin\":\"model\"}")
        .replace("\"atoms\":[","\"atoms\":[{\"id\":\"owner-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.owner\",\"value\":[\"v\",\"root\"],\"origin\":\"model\"},{\"id\":\"quantity-r\",\"subject\":\"r\",\"field\":\"Pattern.Part.quantity\",\"value\":\"5\",\"origin\":\"model\"},");
    let i = inputs("law required amount(c:Part):c.quantity=2;", &map);
    let r = run(Arc::clone(&i));
    assert_eq!(r.profiles().classes().unwrap().len(), 3);
    assert!(r.comparisons().is_empty());
    assert_eq!(r.evaluations().len(), 6);
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert!(r.evaluations().iter().any(|e| {
        e.family()
            .rows()
            .iter()
            .any(|v| v.reading().body() == Some(false))
    }));
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn current_input_bytes_body_role_and_unused_provenance_are_rechecked() {
    let body = "law required amount(c:Part):c.quantity=c.quantity;";
    let i = inputs(body, fixture::A);
    let r = run(Arc::clone(&i));
    r.recheck(i, &mut quiet()).unwrap();
    for (body, map) in [
        (
            body.to_owned(),
            fixture::A.replace("\"value\":\"2\"", "\"value\":\"9\""),
        ),
        (
            body.replace("c.quantity=c.quantity", "c.quantity=2"),
            fixture::A.to_owned(),
        ),
        (body.replace("required", "optional"), fixture::A.to_owned()),
        (
            body.to_owned(),
            fixture::A.replace("fixture-r1", "fixture-r2"),
        ),
    ] {
        assert!(r.recheck(inputs(&body, &map), &mut quiet()).is_err());
    }
}
#[test]
fn unsupported_unbounded_law_reading_is_an_execution_failure_with_original_evidence() {
    use archsig::construction::readings::ObjectEvaluationFailure;
    let i = inputs("law required unbounded(c:Part,z:Z):z=z;", fixture::A);
    let f = object_law_compatibility(i, "Selected", "v", "root", &mut quiet()).unwrap_err();
    assert!(matches!(
        f.cause(),
        ObjectEvaluationFailure::NotImplemented { .. }
    ));
    let r = f.partial().unwrap();
    assert!(!r.is_complete());
    assert!(r.outcome().is_none());
    assert!(f.position().is_some());
}

#[test]
fn finite_missing_boolean_cases_retain_every_original_case_for_every_assignment() {
    let definitions = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    let map = fixture::A
        .lines()
        .filter(|line| !line.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with_definitions(
        &definitions,
        "law required family(c:Part,b:Bool):c.quantity=b;",
        &map,
    );
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Undetermined));
    assert_eq!(r.comparisons()[0].points().len(), 2);
    for (row, b) in r.comparisons()[0].points().iter().zip([false, true]) {
        assert_eq!(row.arguments()[0].wire(), archsig::canonical::Json::Bool(b));
        assert_eq!(row.source().application().value(), Some(true));
        assert_eq!(row.target().application().value(), Some(true));
        assert_eq!(row.source().body(), None);
        assert_eq!(row.target().body(), None);
        assert_eq!(row.source_evaluations().len(), 2);
        assert_eq!(row.target_evaluations().len(), 2);
        assert_ne!(row.source_evaluations()[0], row.source_evaluations()[1]);
        assert_eq!(row.outcome(), &Outcome::Undetermined);
    }
    r.recheck(i, &mut quiet()).unwrap();
}
#[test]
fn a_false_guard_with_missing_body_keeps_known_inapplicability() {
    let definitions = fixture::D.replace("\"type\":\"Z\"", "\"type\":\"Bool\"");
    let map = fixture::A
        .lines()
        .filter(|line| !line.contains("\"quantity-p\""))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]");
    let i = inputs_with_definitions(
        &definitions,
        "law required guarded(c:Part,b:Bool) when false:c.quantity=b;",
        &map,
    );
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.comparisons()[0].points().len(), 2);
    for p in r.comparisons()[0].points() {
        assert_eq!(p.source().application().value(), Some(false));
        assert_eq!(p.target().application().value(), Some(false));
        assert_eq!(p.source().conditional(), Some(true));
        assert_eq!(p.target().conditional(), Some(true));
        assert_eq!(p.outcome(), &Outcome::Compatible);
    }
    r.recheck(i, &mut quiet()).unwrap();
}

#[test]
fn ordinary_law_requests_keep_the_original_symbolic_list_domain() {
    use archsig::canonical::Json;
    let i = inputs(
        "law required singleton(c:Part,x:List<Vacant>):false;",
        fixture::A,
    );
    let prepared = archsig::observed::prepare_shared_observed(
        i,
        &["a=check(Selected.singleton,c=@v/p)"],
        &mut quiet(),
    )
    .unwrap();
    let e = archsig::observed::evaluate_observed(prepared, &mut quiet()).unwrap();
    assert_eq!(e.status(), "complete");
    let wire = e.wire();
    let Json::Obj(wire) = &wire else {
        panic!("wire")
    };
    let Json::Arr(answers) = &wire["answers"] else {
        panic!("answers")
    };
    let Json::Obj(answer) = &answers[0] else {
        panic!("answer")
    };
    assert_eq!(answer["status"], Json::str("refuted"));
    let Json::Arr(nodes) = &wire["nodes"] else {
        panic!("nodes")
    };
    assert!(nodes.iter().any(|node| {
        let Json::Obj(node) = node else { return false };
        if node.get("type") != Some(&Json::str("Domain")) {
            return false;
        }
        let Some(Json::Obj(value)) = node.get("value") else {
            return false;
        };
        value.get("kind") == Some(&Json::str("type"))
    }));
}

#[test]
fn outside_laws_keep_the_true_conditional_predicate_for_ground_and_finite_families() {
    use archsig::construction::maps::LawApplication;
    for body in [
        "law required outside(a:Root):true;",
        "law optional outside(a:Root,b:Bool):false;",
    ] {
        let i = inputs(body, fixture::A);
        let r = run(Arc::clone(&i));
        let e = r
            .evaluations()
            .iter()
            .find(|e| e.evaluation().object().subject().subject == "p")
            .unwrap();
        let family = e.family();
        assert!(family.is_complete());
        let readings = family
            .rows()
            .iter()
            .map(|row| row.reading())
            .chain(family.uniform());
        let mut count = 0;
        for reading in readings {
            count += 1;
            assert_eq!(reading.application(), &LawApplication::OutsideObject);
            assert_eq!(reading.body(), None);
            assert_eq!(reading.conditional(), Some(true));
            assert_eq!(reading.required(), body.contains("required"));
        }
        assert!(count > 0);
        assert_eq!(r.outcome(), Some(&Outcome::Refuted(Failed::Applicability)));
        for p in r.comparisons()[0].points() {
            assert_eq!(p.target().conditional(), Some(true));
            assert_eq!(p.target().body(), None);
        }
        r.recheck(i, &mut quiet()).unwrap();
    }
}
#[test]
fn empty_owner_list_domains_use_the_fixed_owner_and_keep_the_original_false_row() {
    use archsig::canonical::Json;
    let map=fixture::A.replace("{\"id\":\"root\",\"type\":\"Pattern.Root\",\"origin\":\"model\"}","{\"id\":\"root\",\"type\":\"Pattern.Root\",\"origin\":\"model\"},{\"id\":\"other\",\"type\":\"Pattern.Root\",\"origin\":\"model\"}").replace("\"value\":[\"v\",\"root\"]","\"value\":[\"v\",\"other\"]");
    let i = inputs("law required empty(a:Root,x:List<Part[a]>):false;", &map);
    let r = run(Arc::clone(&i));
    assert!(r.is_complete());
    assert_eq!(r.outcome(), Some(&Outcome::Compatible));
    assert_eq!(r.evaluations().len(), 1);
    assert!(r.comparisons().is_empty());
    let family = r.evaluations()[0].family();
    assert!(family.is_complete());
    assert_eq!(family.domains().len(), 1);
    assert_eq!(family.domains()[0].values().len(), 1);
    assert_eq!(family.domains()[0].values()[0].wire(), Json::Arr(vec![]));
    assert_eq!(family.rows().len(), 1);
    let row = &family.rows()[0];
    assert_eq!(row.bindings()[0].0, "x");
    assert_eq!(row.bindings()[0].1.wire(), Json::Arr(vec![]));
    assert_eq!(row.evaluations().len(), 1);
    assert_eq!(row.reading().application().value(), Some(true));
    assert_eq!(row.reading().body(), Some(false));
    assert_eq!(row.reading().conditional(), Some(false));
    assert!(row.reading().required());
    r.recheck(Arc::clone(&i), &mut quiet()).unwrap();
    // 同じ入力でもPartを持つownerのList全域は無限。空List一例で代用しない。
    let failure = object_law_compatibility(i, "Selected", "v", "other", &mut quiet()).unwrap_err();
    assert!(matches!(
        failure.cause(),
        archsig::construction::readings::ObjectEvaluationFailure::NotImplemented { .. }
    ));
    assert!(
        failure
            .partial()
            .is_some_and(|p| !p.is_complete() && p.outcome().is_none())
    );
}
