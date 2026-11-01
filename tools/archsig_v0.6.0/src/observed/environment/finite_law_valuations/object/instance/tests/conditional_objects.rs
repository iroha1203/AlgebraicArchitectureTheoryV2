use super::*;
const ALL: &str = "law required all(c:Part):forall x:Part . x.quantity=0;";
fn missing_map() -> String {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    assert!(!map.contains(r#""id":"oq""#));
    map
}
fn owner() -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: "q".into(),
        field: Some("Pattern.Part.owner".into()),
        atom: None,
    }
}
fn root_value(subject: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: subject.into(),
        entity: "Pattern.Root".into(),
    }
}
fn evaluate(
    i: &CheckedInputs,
    a: &ObjectReadingInstances,
    name: &str,
) -> FiniteLawFamilyValuations {
    let selected = vec![(object(a, name), instance(a, "all", "p"), bindings("p"))];
    finite_instance_law_family_valuations(i, a, &selected, &quiet()).unwrap()
}
#[test]
fn plain_target_quantification_uses_each_conditional_owner_and_both_body_values() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    assert!(f.is_complete());
    assert_eq!(f.domain().len(), 8);
    let mut zero = vec![];
    for (point, values) in f.domain().iter().enumerate() {
        let p = matches!(&values[0],Scalar::Fp{value,..} if value==&0.into());
        let included = matches!(&values[1],Scalar::Subject{subject,..} if subject=="root");
        let q = matches!(&values[2],Scalar::Fp{value,..} if value==&0.into());
        let expected = !(p && (!included || q));
        let row = &f.columns()[0].rows()[point];
        assert_eq!(row.indicator, Some(u8::from(expected).into()));
        assert_eq!(row.predicate, Some(!expected));
        assert!(row.scope.assignments);
        assert!(row.support.contains(&owner()));
        assert!(!row.support.iter().any(|p| p.subject == "q"
            && p.field.as_deref() == Some("Pattern.Part.owner")
            && p.atom.is_some()));
        if !expected {
            zero.push(point);
        }
    }
    assert_eq!(f.required_zero(), Some(zero.as_slice()));
    assert_eq!(zero, [0, 1, 2]);
    let ring = f.integer_ring(&quiet()).unwrap();
    assert_eq!(ring.dimension(), 8);
    let quotient = f.required_quotient(&quiet()).unwrap();
    assert_eq!(quotient.points(), &[0, 1, 2]);
    f.recheck(&i, &quiet()).unwrap();
}
#[test]
fn native_observation_stays_undetermined_without_a_primitive_or_completion_assignment() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let selected = Selection::compute(&i, &a, object(&a, "root"), &quiet()).unwrap();
    let mut e = Environment::new(&i, &quiet()).unwrap();
    e.indexes.object = Some(Arc::clone(&selected.domain));
    *e.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
    let p = probe_mode(
        &e,
        &i.law().declarations()["Selected.all"],
        &bindings("p"),
        0,
        true,
    )
    .unwrap();
    assert_eq!(p.row.indicator, None);
    assert_eq!(p.row.predicate, None);
    assert!(p.row.scope.completions);
    assert!(
        e.state
            .primitive_reads
            .borrow()
            .as_ref()
            .unwrap()
            .contains(&owner())
    );
}
#[test]
fn existing_completion_assignments_still_include_and_exclude_the_conditional_member() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let selected = Selection::compute(&i, &a, object(&a, "root"), &quiet()).unwrap();
    for (target, indicator) in [("root", 1u8), ("r2", 0)] {
        let mut e = Environment::new(&i, &quiet()).unwrap();
        e.indexes.object = Some(Arc::clone(&selected.domain));
        // この内部probeはGraph証拠を生成しない。既存補完の値読取りを対照する。
        *e.state.completion_values.borrow_mut() = vec![(owner(), NodeRef(0), root_value(target))];
        let p = probe_mode(
            &e,
            &i.law().declarations()["Selected.all"],
            &bindings("p"),
            0,
            true,
        )
        .unwrap();
        assert_eq!(p.row.indicator, Some(indicator.into()));
        assert!(p.row.scope.completions);
        assert!(!p.row.support.contains(&owner()));
    }
}
#[test]
fn primitive_valuation_has_the_same_precedence_as_other_primitive_reads() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let selected = Selection::compute(&i, &a, object(&a, "root"), &quiet()).unwrap();
    let mut e = Environment::with_primitive_valuation(&i, &[(owner(), root_value("r2"))], &quiet())
        .unwrap();
    e.indexes.object = Some(Arc::clone(&selected.domain));
    *e.state.completion_values.borrow_mut() = vec![(owner(), NodeRef(0), root_value("root"))];
    let p = probe_mode(
        &e,
        &i.law().declarations()["Selected.all"],
        &bindings("p"),
        0,
        true,
    )
    .unwrap();
    assert_eq!(p.row.indicator, Some(0.into()));
    assert!(p.row.scope.assignments);
    assert!(p.row.support.contains(&owner()));
}
#[test]
fn a_partial_object_does_not_gain_another_subjects_membership_dependency() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let f = evaluate(&i, &a, "p");
    assert!(f.is_complete());
    assert_eq!(f.positions().len(), 1);
    assert_eq!(f.positions()[0].subject, "p");
    assert_eq!(
        f.positions()[0].field.as_deref(),
        Some("Pattern.Part.quantity")
    );
    assert_eq!(f.domain().len(), 2);
    assert_eq!(indicators(&f, 0), ["0", "1"]);
    assert!(f.column_reference_domain_conditions(0).unwrap().is_empty());
    f.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_false_guard_does_not_read_the_unused_conditional_body_domain() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part) when false:forall x:Part . x.integer=0;",
    );
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    assert!(f.is_complete());
    assert_eq!(f.domain(), [vec![]]);
    assert!(f.positions().is_empty());
    let row = &f.columns()[0].rows()[0];
    assert_eq!(row.application, Some(true));
    assert_eq!(row.guard, Some(false));
    assert_eq!(row.predicate, None);
    assert_eq!(row.indicator, Some(0.into()));
    assert!(!row.support.contains(&owner()));
}
#[test]
fn a_compound_reference_domain_keeps_the_full_roster_without_local_membership_axes() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part):forall xs:Option<Part> . true;",
    );
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    assert!(f.is_complete());
    assert!(f.positions().is_empty());
    assert_eq!(f.domain(), [vec![]]);
    assert_eq!(indicators(&f, 0), ["0"]);
    let native = Environment::new(&i, &quiet()).unwrap();
    let ty = Type::Option(Box::new(Type::Ref("Pattern.Part".into())));
    let values = native.finite_values(&ty, &mut |_, _| {}).unwrap();
    assert_eq!(values.values.len(), 3);
}
#[test]
fn a_nonfinite_active_body_keeps_its_original_position_and_type() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part):forall x:Part . x.integer=0;",
    );
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    assert!(!f.is_complete());
    assert!(!f.domain_complete());
    assert!(
        matches!(f.state(),FiniteLawState::OutsideFinite {position,ty:Type::Z} if position.subject=="p" && position.field.as_deref()==Some("Pattern.Part.integer"))
    );
    assert!(f.positions().contains(&owner()));
    assert!(f.integer_ring(&quiet()).is_err());
}
#[test]
fn membership_support_scope_and_every_domain_coordinate_are_rechecked() {
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    for mutation in 0..6 {
        let mut bad = evaluate(&i, &a, "root");
        match mutation {
            0 => bad.columns[0].rows[0].support.retain(|p| p != &owner()),
            1 => bad.columns[0].rows[0].scope.assignments = false,
            2 => bad.domain.swap(0, 1),
            3 => bad.columns[0].rows[0].indicator = Some(1.into()),
            4 => bad.columns[0].rows[0].point = 1,
            _ => bad.positions.swap(0, 1),
        }
        assert!(bad.recheck(&i, &quiet()).is_err(), "mutation {mutation}");
    }
    assert!(
        f.recheck_on_instances(
            &i,
            &a,
            &[(object(&a, "p"), instance(&a, "all", "p"))],
            &quiet()
        )
        .is_err()
    );
}
#[test]
fn a_stop_keeps_one_finished_row_and_no_completed_function_or_quotient() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(&missing_map(), ALL);
    let a = readings(&i);
    let selected = vec![(object(&a, "root"), instance(&a, "all", "p"), bindings("p"))];
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawEvaluation {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= 3).then_some(Signal::Term)
    });
    let error = finite_instance_law_family_valuations(&i, &a, &selected, &c)
        .err()
        .unwrap();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    assert!(partial.domain_complete());
    assert_eq!(partial.domain().len(), 8);
    assert_eq!(partial.columns()[0].rows().len(), 1);
    assert_eq!(partial.columns()[0].rows()[0].indicator, Some(0.into()));
    assert!(partial.columns()[0].rows()[0].support.contains(&owner()));
    assert!(partial.integer_function(0, None, &quiet()).is_err());
    assert!(partial.required_quotient(&quiet()).is_err());
}
#[test]
fn an_explicit_external_owner_keeps_its_whole_fiber_outside_the_partial_object() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part,r:Root):forall x:Part[r] . x.quantity=0;",
    );
    let a = readings(&i);
    let selected = vec![(
        "Selected.all".into(),
        vec![
            (
                "c".into(),
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    entity: "Pattern.Part".into(),
                },
            ),
            ("r".into(), root_value("r2")),
        ],
    )];
    let f =
        finite_object_law_family_valuations(&i, &a, object(&a, "p"), &selected, &quiet()).unwrap();
    assert!(f.is_complete());
    assert_eq!(f.positions().len(), 4);
    assert_eq!(f.domain().len(), 16);
    for (point, values) in f.domain().iter().enumerate() {
        let mut violation = false;
        for name in ["p", "q"] {
            let own = f
                .positions()
                .iter()
                .position(|p| p.subject == name && p.field.as_deref() == Some("Pattern.Part.owner"))
                .unwrap();
            let qty = f
                .positions()
                .iter()
                .position(|p| {
                    p.subject == name && p.field.as_deref() == Some("Pattern.Part.quantity")
                })
                .unwrap();
            violation |= matches!(&values[own],Scalar::Subject{subject,..} if subject=="r2")
                && matches!(&values[qty],Scalar::Fp{value,..} if value!=&0.into());
        }
        assert_eq!(
            f.columns()[0].rows()[point].indicator,
            Some(u8::from(violation).into())
        );
    }
    f.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_same_root_owned_quantifier_is_intersected_with_the_partial_object() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part,r:Root):forall x:Part[r] . x.quantity=0;",
    );
    let a = readings(&i);
    let selected = vec![(
        "Selected.all".into(),
        vec![
            (
                "c".into(),
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    entity: "Pattern.Part".into(),
                },
            ),
            ("r".into(), root_value("root")),
        ],
    )];
    let f =
        finite_object_law_family_valuations(&i, &a, object(&a, "p"), &selected, &quiet()).unwrap();
    assert!(f.is_complete());
    assert!(
        f.positions()
            .iter()
            .any(|p| p.subject == "p" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    assert!(
        !f.positions()
            .iter()
            .any(|p| p.subject == "q" && p.field.as_deref() == Some("Pattern.Part.quantity"))
    );
    for (point, values) in f.domain().iter().enumerate() {
        let own = f
            .positions()
            .iter()
            .position(|p| p.subject == "p" && p.field.as_deref() == Some("Pattern.Part.owner"))
            .unwrap();
        let qty = f
            .positions()
            .iter()
            .position(|p| p.subject == "p" && p.field.as_deref() == Some("Pattern.Part.quantity"))
            .unwrap();
        let violation = matches!(&values[own],Scalar::Subject{subject,..} if subject=="root")
            && matches!(&values[qty],Scalar::Fp{value,..} if value!=&0.into());
        assert_eq!(
            f.columns()[0].rows()[point].indicator,
            Some(u8::from(violation).into())
        );
    }
    f.recheck(&i, &quiet()).unwrap();
}
#[test]
fn a_different_reference_type_does_not_read_part_membership_conditions() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part):forall x:Root . true;",
    );
    let a = readings(&i);
    let f = evaluate(&i, &a, "root");
    assert!(f.is_complete());
    assert!(f.positions().is_empty());
    assert_eq!(f.domain(), [vec![]]);
    assert_eq!(indicators(&f, 0), ["0"]);
    assert!(!f.columns()[0].rows()[0].support.contains(&owner()));
}
