use super::*;
use crate::construction::{construct, readings::object_reading_instances};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../tests/common/primitive_valuation_data.rs");
}
use crate::control::quiet;
fn readings(i: &CheckedInputs) -> ObjectReadingInstances {
    let c = construct(i, "Selected", "v", "root", &quiet()).unwrap();
    object_reading_instances(i, &c, &quiet()).unwrap()
}
fn object(r: &ObjectReadingInstances, name: &str) -> usize {
    r.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
fn instance(r: &ObjectReadingInstances, law: &str, c: &str) -> usize {
    r.instances()
        .iter()
        .position(|i| {
            i.declaration().name == format!("Selected.{law}")
                && i.bindings()
                    .iter()
                    .any(|b| b.parameter().name == "c" && b.subject().subject == c)
        })
        .unwrap()
}
fn reference(name: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: name.into(),
        entity: "Pattern.Part".into(),
    }
}
fn bindings(name: &str) -> Vec<(String, Scalar)> {
    vec![("c".into(), reference(name))]
}
fn indicators(r: &FiniteLawFamilyValuations, column: usize) -> Vec<String> {
    r.integer_function(column, None, &quiet())
        .unwrap()
        .values()
        .iter()
        .map(ToString::to_string)
        .collect()
}

#[test]
fn original_not_applicable_rows_are_zero_without_fabricating_body_values() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let selected = vec![
        (object(&a, "p"), instance(&a, "zero", "p"), bindings("p")),
        (object(&a, "p"), instance(&a, "zero", "q"), bindings("q")),
    ];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(
        r.positions()
            .iter()
            .map(|f| f.subject.as_str())
            .collect::<Vec<_>>(),
        ["p"]
    );
    assert_eq!(r.domain().len(), 2);
    assert_eq!(indicators(&r, 0), ["0", "1"]);
    assert_eq!(indicators(&r, 1), ["0", "0"]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    for row in r.columns()[1].rows() {
        assert_eq!(row.application, Some(false));
        assert_eq!(row.guard, None);
        assert_eq!(row.predicate, None);
        assert_eq!(row.operands, None);
        let component = &row.components.as_ref().unwrap()[0];
        assert_eq!(component.left, None);
        assert_eq!(component.right, None);
        assert_eq!(component.equal, None);
        assert_eq!(component.indicator, Some(0.into()));
    }
    assert_eq!(r.columns()[1].source_instance(), Some(selected[1].1));
    assert!(matches!(
        r.instance_source(1).unwrap().1,
        InstanceApplication::NotApplicable
    ));
    r.recheck_on_instances(
        &i,
        &a,
        &selected
            .iter()
            .map(|(o, n, _)| (*o, *n))
            .collect::<Vec<_>>(),
        &quiet(),
    )
    .unwrap();
}
#[test]
fn conditional_membership_is_evaluated_on_the_shared_owner_coordinates() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let selected = vec![(object(&a, "q"), instance(&a, "zero", "q"), bindings("q"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.domain().len(), 4);
    assert_eq!(
        r.positions()
            .iter()
            .map(|f| f.field.as_deref())
            .collect::<Vec<_>>(),
        [Some("Pattern.Part.owner"), Some("Pattern.Part.quantity")]
    );
    assert_eq!(indicators(&r, 0), ["0", "0", "0", "1"]);
    assert_eq!(
        r.columns()[0]
            .rows()
            .iter()
            .map(|r| r.application)
            .collect::<Vec<_>>(),
        [Some(false), Some(false), Some(true), Some(true)]
    );
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.required_zero(), Some([0, 1, 2].as_slice()));
    assert!(
        matches!(r.instance_source(0).unwrap().1,InstanceApplication::Applicable{conditions} if !conditions.is_empty())
    );
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_false_original_guard_is_distinct_from_false_instance_application() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part) when false:c.integer=0;",
    );
    let a = readings(&i);
    let selected = vec![(object(&a, "p"), instance(&a, "guarded", "p"), bindings("p"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.positions().is_empty());
    assert_eq!(r.domain(), [Vec::<Scalar>::new()]);
    assert_eq!(indicators(&r, 0), ["0"]);
    let row = &r.columns()[0].rows()[0];
    assert_eq!(row.application, Some(true));
    assert_eq!(row.guard, Some(false));
    assert_eq!(row.predicate, None);
    assert_eq!(row.operands, None);
    assert_eq!(row.components.as_ref().unwrap()[0].left, None);
    assert_eq!(row.components.as_ref().unwrap()[0].ty, Type::Z);
    r.recheck(&i, &quiet()).unwrap();
}

fn foreign_inputs() -> Arc<CheckedInputs> {
    let base = fixture::inputs();
    let definitions=String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap().replacen(r#""declarations":["#,r#""declarations":[{"kind":"entity","name":"Pattern.ForeignRoot","meaning":"外部の根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Pattern.ForeignPart","meaning":"外部の部分。","parameters":[{"name":"owner","type":["Ref","Pattern.ForeignRoot"],"meaning":"所属。"}],"fields":[],"alignments":[]},"#,1);
    let checked =
        crate::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map=fixture::MAP.replace(r#""subjects":["#,r#""subjects":[{"id":"f1","type":"Pattern.ForeignRoot","origin":"model"},{"id":"f2","type":"Pattern.ForeignRoot","origin":"model"},{"id":"s","type":"Pattern.ForeignPart","origin":"model"},"#).replace(r#""atoms":["#,r#""atoms":[{"id":"os","subject":"s","field":"Pattern.ForeignPart.owner","value":["v","f1"],"origin":"model"},"#).replace("@DIGEST@",digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required first(c:Part,r:ForeignRoot,x:Option<ForeignPart[r]>):false;law optional second(c:Part,r:ForeignRoot,x:Option<ForeignPart[r]>):false;}}"
    );
    Arc::new(
        crate::input::check_inputs(
            crate::input::InputSources::from_bytes(
                vec![definitions.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &quiet(),
        )
        .unwrap(),
    )
}
fn foreign_selection(a: &ObjectReadingInstances) -> Vec<(usize, usize, Vec<(String, Scalar)>)> {
    [("first", "f1"), ("second", "f2")]
        .iter()
        .map(|(law, owner)| {
            let n = a
                .instances()
                .iter()
                .position(|i| {
                    i.declaration().name == format!("Selected.{law}")
                        && i.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "c" && b.subject().subject == "p")
                        && i.bindings()
                            .iter()
                            .any(|b| b.parameter().name == "r" && b.subject().subject == *owner)
                })
                .unwrap();
            (
                object(a, "p"),
                n,
                vec![
                    ("c".into(), reference("p")),
                    (
                        "r".into(),
                        Scalar::Subject {
                            snapshot: "v".into(),
                            subject: (*owner).into(),
                            entity: "Pattern.ForeignRoot".into(),
                        },
                    ),
                    (
                        "x".into(),
                        Scalar::Option {
                            element: Type::Ref("Pattern.ForeignPart".into()),
                            value: Some(Box::new(Scalar::Subject {
                                snapshot: "v".into(),
                                subject: "s".into(),
                                entity: "Pattern.ForeignPart".into(),
                            })),
                        },
                    ),
                ],
            )
        })
        .collect()
}
#[test]
fn mutually_exclusive_owned_bindings_remain_conditional_functions_on_the_same_d() {
    let i = foreign_inputs();
    let a = readings(&i);
    let selected = foreign_selection(&a);
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.positions().len(), 1);
    assert_eq!(r.positions()[0].subject, "s");
    assert_eq!(
        r.positions()[0].field.as_deref(),
        Some("Pattern.ForeignPart.owner")
    );
    assert_eq!(r.domain().len(), 2);
    assert_eq!(r.observed_point(), Some(0));
    assert_eq!(indicators(&r, 0), ["1", "0"]);
    assert_eq!(indicators(&r, 1), ["0", "1"]);
    assert_eq!(
        r.columns()[0]
            .rows()
            .iter()
            .map(|r| r.application)
            .collect::<Vec<_>>(),
        [Some(true), Some(false)]
    );
    assert_eq!(
        r.columns()[1]
            .rows()
            .iter()
            .map(|r| r.application)
            .collect::<Vec<_>>(),
        [Some(false), Some(true)]
    );
    assert_eq!(r.required_zero(), Some([1].as_slice()));
    assert!(r.columns()[0].required());
    assert!(!r.columns()[1].required());
    let quotient = r.required_quotient(&quiet()).unwrap();
    assert_eq!(quotient.points(), [1]);
    assert_eq!(
        quotient
            .project(&r.integer_function(1, None, &quiet()).unwrap(), &quiet())
            .unwrap()
            .values(),
        &[1.into()]
    );
    let ordinary = selected
        .iter()
        .map(|(o, n, b)| (*o, a.instances()[*n].declaration().name.clone(), b.clone()))
        .collect::<Vec<_>>();
    let legacy = finite_multi_object_law_family_valuations(&i, &a, &ordinary, &quiet()).unwrap();
    assert!(legacy.is_complete());
    assert!(legacy.domain().is_empty());
    assert_eq!(legacy.required_zero(), Some([].as_slice()));
    r.recheck_on_instances(
        &i,
        &a,
        &selected
            .iter()
            .map(|(o, n, _)| (*o, *n))
            .collect::<Vec<_>>(),
        &quiet(),
    )
    .unwrap();
}
#[test]
fn tuple_mask_keeps_types_and_zero_functions_without_zeroing_original_values() {
    let i = fixture::with_body(fixture::MAP, "law required pair(c:Part):c.pair=(0,true);");
    let a = readings(&i);
    let selected = vec![
        (object(&a, "p"), instance(&a, "pair", "p"), bindings("p")),
        (object(&a, "p"), instance(&a, "pair", "q"), bindings("q")),
    ];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert_eq!(r.domain().len(), 4);
    assert_eq!(indicators(&r, 0), ["1", "0", "1", "1"]);
    assert_eq!(indicators(&r, 1), ["0", "0", "0", "0"]);
    assert_eq!(r.required_zero(), Some([1].as_slice()));
    for row in r.columns()[1].rows() {
        let cs = row.components.as_ref().unwrap();
        assert_eq!(cs.len(), 2);
        assert_eq!(cs[0].ty, Type::Fp("2".into()));
        assert_eq!(cs[1].ty, Type::Bool);
        for c in cs {
            assert_eq!(c.left, None);
            assert_eq!(c.right, None);
            assert_eq!(c.equal, None);
            assert_eq!(c.indicator, Some(0.into()));
        }
    }
    let generators = r.required_generators(&quiet()).unwrap();
    assert_eq!(generators.len(), 4);
    for g in generators.iter().filter(|g| g.column() == 1) {
        assert!(g.value().values().iter().all(|n| *n == 0.into()));
    }
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_dynamic_original_guard_keeps_actual_operands_only_where_it_is_true() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part) when c.flag:c.quantity=0;",
    );
    let a = readings(&i);
    let selected = vec![(object(&a, "p"), instance(&a, "guarded", "p"), bindings("p"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 4);
    assert_eq!(indicators(&r, 0), ["0", "0", "0", "1"]);
    assert_eq!(
        r.columns()[0]
            .rows()
            .iter()
            .map(|r| r.guard)
            .collect::<Vec<_>>(),
        [Some(false), Some(false), Some(true), Some(true)]
    );
    for row in &r.columns()[0].rows()[..2] {
        assert_eq!(row.application, Some(true));
        assert_eq!(row.predicate, None);
        assert_eq!(row.operands, None);
        assert_eq!(row.components.as_ref().unwrap()[0].equal, None);
    }
    let row = &r.columns()[0].rows()[3];
    assert_eq!(row.application, Some(true));
    assert_eq!(row.predicate, Some(false));
    assert!(row.operands.is_some());
    assert_eq!(row.components.as_ref().unwrap()[0].equal, Some(false));
    assert_eq!(
        row.components.as_ref().unwrap()[0].indicator,
        Some(1.into())
    );
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn missing_observed_values_do_not_become_zero_observations() {
    let map=fixture::MAP.replace(r#",{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let selected = vec![(object(&a, "p"), instance(&a, "zero", "p"), bindings("p"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.observed_point(), None);
    assert_eq!(r.domain().len(), 2);
    assert_eq!(indicators(&r, 0), ["0", "1"]);
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn conditional_body_membership_is_read_at_each_primitive_assignment_without_zero_filling() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(
        &map,
        "law required all(c:Part):forall x:Part . x.quantity=0;",
    );
    let a = readings(&i);
    let selected = vec![(object(&a, "root"), instance(&a, "all", "p"), bindings("p"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert!(r.domain_complete());
    assert_eq!(r.domain().len(), 8);
    assert_eq!(r.observed_point(), None);
    assert_eq!(
        r.positions()
            .iter()
            .map(|p| (p.subject.as_str(), p.field.as_deref()))
            .collect::<Vec<_>>(),
        [
            ("p", Some("Pattern.Part.quantity")),
            ("q", Some("Pattern.Part.owner")),
            ("q", Some("Pattern.Part.quantity")),
        ]
    );
    assert_eq!(indicators(&r, 0), ["0", "0", "0", "1", "1", "1", "1", "1"]);
    assert_eq!(r.required_zero().unwrap(), &[0, 1, 2]);
    assert!(
        r.column_reference_domain_conditions(0)
            .unwrap()
            .iter()
            .any(|p| p.subject == "q" && p.field.as_deref() == Some("Pattern.Part.owner"))
    );
    for row in r.columns()[0].rows() {
        assert!(row.scope.assignments);
        assert!(row.support.iter().any(|p| p.subject == "q"
            && p.field.as_deref() == Some("Pattern.Part.owner")
            && p.atom.is_none()));
    }
    assert_eq!(r.integer_ring(&quiet()).unwrap().dimension(), 8);
    assert!(r.required_quotient(&quiet()).is_ok());
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn nonfinite_active_operands_keep_their_position_type_and_original_instance() {
    let i = fixture::with_body(fixture::MAP, "law required infinite(c:Part):c.integer=0;");
    let a = readings(&i);
    let selected = vec![(
        object(&a, "p"),
        instance(&a, "infinite", "p"),
        bindings("p"),
    )];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite{position,ty:Type::Z} if position.subject=="p"&&position.field.as_deref()==Some("Pattern.Part.integer"))
    );
    assert_eq!(r.columns()[0].source_instance(), Some(selected[0].1));
    assert!(!r.domain_complete());
    assert!(r.integer_ring(&quiet()).is_err());
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_false_guard_keeps_conditional_membership_and_avoids_nonfinite_body_evaluation() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required guarded(c:Part) when false:c.integer=0;");
    let a = readings(&i);
    let selected = vec![(object(&a, "q"), instance(&a, "guarded", "q"), bindings("q"))];
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 2);
    assert_eq!(r.positions().len(), 1);
    assert_eq!(
        r.positions()[0].field.as_deref(),
        Some("Pattern.Part.owner")
    );
    assert_eq!(indicators(&r, 0), ["0", "0"]);
    assert_eq!(
        r.columns()[0]
            .rows()
            .iter()
            .map(|r| (r.application, r.guard))
            .collect::<Vec<_>>(),
        [(Some(false), None), (Some(true), Some(false))]
    );
    assert_eq!(r.observed_point(), None);
    r.recheck(&i, &quiet()).unwrap();
}
#[test]
fn source_instance_application_missing_guard_and_coordinates_are_rechecked() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law required same(c:Part):c.quantity=0;",
    );
    let a = readings(&i);
    let selected = vec![(object(&a, "p"), instance(&a, "zero", "p"), bindings("p"))];
    let expected = vec![(selected[0].0, selected[0].1)];
    for mode in 0..8 {
        let mut r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
        match mode {
            0 => r.columns[0].source_instance = Some(instance(&a, "same", "p")),
            1 => r.columns[0].rows[0].application = Some(false),
            2 => r.columns[0].rows[0].application_missing.push(Fact {
                snapshot: "v".into(),
                subject: "q".into(),
                field: Some("Pattern.Part.owner".into()),
                atom: None,
            }),
            3 => r.instance_mode = false,
            4 => r.columns[0].rows[0].guard = Some(false),
            5 => r.columns[0].rows[0].point = usize::MAX,
            6 => r.domain.reverse(),
            _ => r.columns[0].rows[0].support.clear(),
        };
        assert!(
            r.recheck_on_instances(&i, &a, &expected, &quiet()).is_err(),
            "mode={mode}"
        );
    }
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(
        r.recheck_on_instances(
            &i,
            &a,
            &[(selected[0].0, instance(&a, "same", "p"))],
            &quiet()
        )
        .is_err()
    );
    assert!(
        r.recheck_on_instances(&i, &a, &[(object(&a, "q"), selected[0].1)], &quiet())
            .is_err()
    );
    let changed = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law required same(c:Part):c.quantity=0; ",
    );
    assert!(r.recheck(&changed, &quiet()).is_err());
}
#[test]
fn unknown_view_and_replaced_reference_selections_fail_without_a_family() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;view helper(c:Part):Fp(2)=c.quantity;",
    );
    let a = readings(&i);
    let p = object(&a, "p");
    let n = instance(&a, "zero", "p");
    let helper = instance(&a, "helper", "p");
    for selected in [
        vec![(p, usize::MAX, bindings("p"))],
        vec![(usize::MAX, n, bindings("p"))],
        vec![(p, helper, bindings("p"))],
        vec![(p, n, bindings("q"))],
        vec![(p, n, vec![])],
        vec![(
            p,
            n,
            vec![("c".into(), reference("p")), ("c".into(), reference("p"))],
        )],
    ] {
        assert!(finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).is_err());
    }
}
#[test]
fn an_empty_instance_family_still_retains_the_original_reading_anchor() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let c = construct(&i, "Selected", "v", "r2", &quiet()).unwrap();
    let other = object_reading_instances(&i, &c, &quiet()).unwrap();
    let r = finite_instance_law_family_valuations(&i, &a, &[], &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain(), [Vec::<Scalar>::new()]);
    assert_eq!(r.required_zero(), Some([0].as_slice()));
    r.recheck_on_instances(&i, &a, &[], &quiet()).unwrap();
    assert!(r.recheck_on_instances(&i, &other, &[], &quiet()).is_err());
    let ordinary = finite_multi_object_law_family_valuations(&i, &a, &[], &quiet()).unwrap();
    assert!(
        ordinary
            .recheck_on_instances(&i, &a, &[], &quiet())
            .is_err()
    );
}
#[test]
fn fixed_stops_keep_finished_instance_rows_and_do_not_offer_complete_functions() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let selected = vec![
        (object(&a, "p"), instance(&a, "zero", "p"), bindings("p")),
        (object(&a, "p"), instance(&a, "zero", "q"), bindings("q")),
    ];
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawEvaluation {
            count.set(count.get() + 1);
        }
        (count.get() >= 3).then_some(Signal::Term)
    });
    let failure = finite_instance_law_family_valuations(&i, &a, &selected, &c)
        .err()
        .unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Stop(_)));
    let r = failure.partial.unwrap();
    assert!(r.domain_complete());
    assert!(!r.is_complete());
    assert_eq!(r.columns()[0].rows().len(), 1);
    assert!(r.columns()[1].rows().is_empty());
    assert_eq!(r.columns()[1].source_instance(), Some(selected[1].1));
    assert!(matches!(
        r.instance_source(1).unwrap().1,
        InstanceApplication::NotApplicable
    ));
    assert!(r.integer_function(0, None, &quiet()).is_err());
    assert!(r.required_quotient(&quiet()).is_err());
}
#[test]
fn interruption_before_d_keeps_original_instance_indices_and_conditions() {
    use crate::result::Signal;
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = readings(&i);
    let selected = vec![(object(&a, "q"), instance(&a, "zero", "q"), bindings("q"))];
    let c = Control::new(|p| (p == Checkpoint::FiniteLawDomain).then_some(Signal::Int));
    let failure = finite_instance_law_family_valuations(&i, &a, &selected, &c)
        .err()
        .unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Stop(_)));
    let r = failure.partial.unwrap();
    assert!(!r.domain_complete());
    assert_eq!(r.columns()[0].source_instance(), Some(selected[0].1));
    assert!(
        matches!(r.instance_source(0).unwrap().1,InstanceApplication::Applicable{conditions} if !conditions.is_empty())
    );
    assert!(r.integer_ring(&quiet()).is_err());
}
#[test]
fn all_parameter_rows_and_not_applicable_objects_share_the_same_original_instance_axes() {
    use super::super::instances::finite_object_law_instances;
    let i = fixture::with_body(
        fixture::MAP,
        "law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;",
    );
    let a = readings(&i);
    let parameters = finite_object_law_instances(&i, &a, object(&a, "root"), &quiet()).unwrap();
    assert!(parameters.is_complete());
    let mut selected = vec![];
    for name in ["root", "p", "q"] {
        for entry in parameters.entries() {
            for row in &entry.rows {
                selected.push((object(&a, name), entry.instance, row.bindings.clone()));
            }
        }
    }
    assert_eq!(selected.len(), 24);
    let r = finite_instance_law_family_valuations(&i, &a, &selected, &quiet()).unwrap();
    assert!(r.is_complete());
    assert_eq!(r.domain().len(), 4);
    assert_eq!(r.columns().len(), 24);
    assert_eq!(r.required_zero(), Some([].as_slice()));
    let mut outside = 0;
    for (column, (o, n, bindings)) in selected.iter().enumerate() {
        let original = &a.instances()[*n];
        assert_eq!(r.columns()[column].source_instance(), Some(*n));
        assert_eq!(r.columns()[column].bindings(), bindings);
        let app = matches!(
            original.applications()[*o],
            InstanceApplication::Applicable { .. }
        );
        if !app {
            outside += 1;
        }
        let subject = &original
            .bindings()
            .iter()
            .find(|b| b.parameter().name == "c")
            .unwrap()
            .subject()
            .subject;
        let value = &bindings.iter().find(|(name, _)| name == "n").unwrap().1;
        let Scalar::Fp { value, .. } = value else {
            panic!("scalar")
        };
        for point in 0..4 {
            let actual = if subject == "p" { point / 2 } else { point % 2 };
            assert_eq!(
                r.integer_function(column, None, &quiet()).unwrap().values()[point].to_string(),
                if !app || value.to_string() == actual.to_string() {
                    "0"
                } else {
                    "1"
                }
            );
            assert_eq!(r.columns()[column].rows()[point].application, Some(app));
        }
    }
    assert_eq!(outside, 8);
    r.recheck_on_instances(
        &i,
        &a,
        &selected
            .iter()
            .map(|(o, n, _)| (*o, *n))
            .collect::<Vec<_>>(),
        &quiet(),
    )
    .unwrap();
}

mod conditional_objects;
