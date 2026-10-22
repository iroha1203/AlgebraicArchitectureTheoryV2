use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    observed::control::{Limits, Usage},
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn reading(inputs: &CheckedInputs) -> ObjectReadingInstances {
    let c = construct(inputs, "Selected", "v", "root", &mut quiet()).unwrap();
    object_reading_instances(inputs, &c, &mut quiet()).unwrap()
}
fn object(r: &ObjectReadingInstances, name: &str) -> usize {
    r.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
fn input(body: &str) -> Arc<CheckedInputs> {
    fixture::with_body(fixture::MAP, body)
}
fn family(i: &CheckedInputs, r: &ObjectReadingInstances, name: &str) -> ObjectLawInstances {
    finite_object_law_instances(i, r, object(r, name), &mut quiet()).unwrap()
}
fn entry<'a>(f: &'a ObjectLawInstances, law: &str, subject: &str) -> &'a InstanceParameters {
    f.entries()
        .iter()
        .find(|e| {
            e.source.declaration().name == format!("Selected.{law}")
                && e.source
                    .bindings()
                    .iter()
                    .any(|b| b.subject().subject == subject)
        })
        .unwrap()
}
fn fp(n: u8) -> Scalar {
    Scalar::Fp {
        modulus: "2".into(),
        value: n.into(),
    }
}
const GRID: &str = "view helper(c:Part):Fp(2)=c.quantity;law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;law optional scalar(n:Fp(2)):n=0;";
#[test]
fn all_law_instances_and_the_whole_parameter_product_keep_their_original_identity() {
    let i = input(GRID);
    let r = reading(&i);
    let f = family(&i, &r, "root");
    assert!(f.is_complete());
    assert_eq!(f.entries().len(), 2);
    for (subject, index) in [("p", 0), ("q", 1)] {
        let e = entry(&f, "grid", subject);
        assert_eq!(e.state, ParameterFamilyState::Ready);
        assert_eq!(&e.source, &r.instances()[e.instance]);
        assert_eq!(
            e.source.declaration().role,
            Some(crate::law::ast::Role::Required)
        );
        assert_eq!(e.rows.len(), 4);
        assert!(e.scope.snapshots.contains("v"));
        assert!(e.scope.modes.contains("specification"));
        assert!(
            e.support
                .iter()
                .any(|f| f.subject == subject && f.field.is_none())
        );
        assert_eq!(
            e.domains[0].values.as_deref(),
            Some([fp(0), fp(1)].as_slice())
        );
        assert_eq!(
            e.domains[1].values.as_deref(),
            Some([Scalar::Bool(false), Scalar::Bool(true)].as_slice())
        );
        assert_eq!(
            e.rows
                .iter()
                .map(|r| r.coordinates.clone())
                .collect::<Vec<_>>(),
            [vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]]
        );
        assert_eq!(
            e.rows
                .iter()
                .map(|r| r.bindings[1..].to_vec())
                .collect::<Vec<_>>(),
            vec![
                vec![("n".into(), fp(0)), ("b".into(), Scalar::Bool(false))],
                vec![("n".into(), fp(0)), ("b".into(), Scalar::Bool(true))],
                vec![("n".into(), fp(1)), ("b".into(), Scalar::Bool(false))],
                vec![("n".into(), fp(1)), ("b".into(), Scalar::Bool(true))]
            ]
        );
        assert!(
            matches!(&e.rows[0].bindings[0],(name,Scalar::Subject{subject:s,..}) if name=="c" && s==subject)
        );
        assert_eq!(e.instance, index);
        for d in &e.domains {
            assert!(d.scope.readings.contains("Selected"));
            assert_eq!(d.scope.quantifiers.len(), 1);
            let q = &d.scope.quantifiers[0];
            assert_eq!(
                (&q.name, &q.ty, q.occurrence),
                (&d.parameter.name, &d.parameter.ty, d.parameter.span)
            );
        }
    }
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn partial_object_retains_inapplicable_instances_without_inventing_parameter_rows() {
    let i = input(GRID);
    let r = reading(&i);
    let f = family(&i, &r, "p");
    assert_eq!(f.entries().len(), 2);
    assert_eq!(entry(&f, "grid", "p").rows.len(), 4);
    let q = entry(&f, "grid", "q");
    assert_eq!(q.state, ParameterFamilyState::NotApplicable);
    assert_eq!(q.application, InstanceApplication::NotApplicable);
    assert_eq!(q.source.parameters().len(), 2);
    assert!(q.rows.is_empty());
    assert!(q.domains.is_empty());
    assert!(f.is_complete());
    f.recheck_on_object(&i, &r, object(&r, "p"), &mut quiet())
        .unwrap();
}
#[test]
fn complete_bindings_follow_declaration_order_when_reference_parameters_are_interleaved() {
    let i = input("law required order(n:Fp(2),c:Part,b:Bool):c.quantity=n;");
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let e = entry(&f, "order", "p");
    assert_eq!(e.rows.len(), 4);
    assert_eq!(
        e.rows[0]
            .bindings
            .iter()
            .map(|b| b.0.as_str())
            .collect::<Vec<_>>(),
        ["n", "c", "b"]
    );
    assert_eq!(e.rows[2].bindings[0].1, fp(1));
    assert_eq!(e.rows[2].bindings[2].1, Scalar::Bool(false));
}
#[test]
fn no_parameter_one_row_and_empty_finite_domain_zero_rows_are_distinct() {
    let i = input(
        "law required ground(c:Part):false;law required empty(c:Part,x:Map<Root,Vacant>):false;law optional singleton(c:Part,x:List<Vacant>):true;",
    );
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let ground = entry(&f, "ground", "p");
    assert_eq!(ground.rows.len(), 1);
    assert!(ground.rows[0].coordinates.is_empty());
    assert!(ground.domains.is_empty());
    let empty = entry(&f, "empty", "p");
    assert_eq!(empty.state, ParameterFamilyState::Ready);
    assert_eq!(empty.domains[0].values.as_deref(), Some([].as_slice()));
    assert!(empty.rows.is_empty());
    let singleton = entry(&f, "singleton", "p");
    assert_eq!(singleton.rows.len(), 1);
    assert!(matches!(&singleton.rows[0].bindings[1].1,Scalar::List{items,..} if items.is_empty()));
    assert!(f.is_complete());
}
#[test]
fn infinite_parameter_keeps_its_original_type_and_does_not_become_an_empty_finite_domain() {
    let i = input("law required infinite(c:Part,b:Bool,n:Z,k:Fp(2)):true;");
    let r = reading(&i);
    let f = family(&i, &r, "p");
    assert!(!f.is_complete());
    let p = entry(&f, "infinite", "p");
    assert_eq!(p.state, ParameterFamilyState::OutsideFinite);
    assert!(p.rows.is_empty());
    assert_eq!(p.domains.len(), 3);
    assert_eq!(p.domains[1].parameter.ty, Type::Z);
    assert_eq!(p.domains[1].values, None);
    assert_eq!(p.domains[0].values.as_ref().unwrap().len(), 2);
    assert_eq!(p.domains[2].values.as_ref().unwrap().len(), 2);
    let q = entry(&f, "infinite", "q");
    assert_eq!(q.state, ParameterFamilyState::NotApplicable);
    assert_eq!(q.source.parameters()[1].ty, Type::Z);
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn composite_reference_leaves_keep_other_root_subjects_in_their_full_typed_domain() {
    let map=fixture::MAP.replace(r#""subjects":["#,r#""subjects":[{"id":"r","type":"Pattern.Part","origin":"model"},"#).replace(r#""atoms":["#,r#""atoms":[{"id":"or","subject":"r","field":"Pattern.Part.owner","value":["v","r2"],"origin":"model"},"#);
    let i = fixture::with_body(&map, "law required compound(c:Part,xs:Set<Part>):true;");
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let e = entry(&f, "compound", "p");
    assert_eq!(e.rows.len(), 8);
    assert!(e.rows.iter().any(|row|matches!(&row.bindings[1].1,Scalar::Set{items,..} if items.len()==1 && matches!(&items[0],Scalar::Subject{subject,..} if subject=="r"))));
    assert!(e.domains[0].scope.snapshots.contains("v"));
    assert!(
        e.domains[0]
            .support
            .iter()
            .any(|f| f.subject == "r" && f.field.is_none())
    );
}
#[test]
fn composite_owned_parameters_use_the_original_fixed_owner_fiber() {
    let i = input("law required owned(r:Root,c:Part,x:Option<Part[r]>):true;");
    let r = reading(&i);
    let f = family(&i, &r, "root");
    let e = entry(&f, "owned", "p");
    assert_eq!(e.rows.len(), 3);
    let values = e.domains[0].values.as_ref().unwrap();
    assert!(
        values
            .iter()
            .any(|v| matches!(v, Scalar::Option { value: None, .. }))
    );
    for name in ["p", "q"] {
        assert!(values.iter().any(|v|matches!(v,Scalar::Option{value:Some(v),..} if matches!(v.as_ref(),Scalar::Subject{subject,..} if subject==name))));
    }
    assert!(
        e.domains[0]
            .support
            .iter()
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
    );
    f.recheck(&i, &mut quiet()).unwrap();
    // 部分対象pはroot参照rを含まず、この宣言のinstanceは非適用。
    let partial = family(&i, &r, "p");
    assert!(
        partial
            .entries()
            .iter()
            .all(|e| e.state == ParameterFamilyState::NotApplicable)
    );
    assert!(partial.entries().iter().all(|e| e.rows.is_empty()));
}
#[test]
fn unknown_membership_and_missing_parameter_fibers_are_retained_without_rows() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(
        &map,
        "law required owned(r:Root,c:Part,x:Option<Part[r]>):true;",
    );
    let r = reading(&i);
    let f = family(&i, &r, "root");
    assert_eq!(f.entries().len(), 2);
    assert!(!f.is_complete());
    for e in f.entries() {
        assert_eq!(e.state, ParameterFamilyState::Undetermined);
        assert!(e.rows.is_empty());
        assert!(
            e.domains[0]
                .missing
                .iter()
                .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
        );
        assert!(e.domains[0].scope.completions);
    }
    assert!(
        matches!(&entry(&f,"owned","q").application,InstanceApplication::Applicable{conditions} if conditions.len()==1)
    );
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn source_object_and_every_coordinate_are_rebuilt_for_recheck() {
    let i = input(GRID);
    let r = reading(&i);
    let f = family(&i, &r, "p");
    assert!(
        f.recheck_on_object(&i, &r, object(&r, "q"), &mut quiet())
            .is_err()
    );
    for mutation in 0..10 {
        let mut bad = f.clone();
        let e = &mut bad.entries[0];
        match mutation {
            0 => e.instance = usize::MAX,
            1 => e.domains[0].parameter.span.0 += 1,
            2 => e.domains[0].values.as_mut().unwrap().swap(0, 1),
            3 => e.rows[0].coordinates[0] = 1,
            4 => e.rows[0].bindings[1].1 = fp(1),
            5 => e.application = InstanceApplication::NotApplicable,
            6 => e.domains[0].scope.readings.clear(),
            7 => e.rows.pop().map(|_| ()).unwrap(),
            8 => e.state = ParameterFamilyState::NotApplicable,
            _ => bad.complete = false,
        }
        assert!(
            bad.recheck(&i, &mut quiet()).is_err(),
            "mutation {mutation}"
        );
    }
    let changed = fixture::with_body(&(fixture::MAP.to_string() + " "), GRID);
    assert!(f.recheck(&changed, &mut quiet()).is_err());
    assert!(finite_object_law_instances(&i, &r, usize::MAX, &mut quiet()).is_err());
}
#[test]
fn fixed_stops_keep_finished_rows_without_completing_the_instance() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = input(GRID);
    let r = reading(&i);
    for mode in 0..3 {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut c = Control::new(
            Limits {
                time_ms: (mode == 1).then_some(1),
                memory_mib: (mode == 2).then_some(1),
            },
            move |p| {
                if p == Checkpoint::FiniteLawEvaluation {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= 2;
                Usage {
                    signal: (stop && mode == 0).then_some(Signal::Term),
                    elapsed_ms: u128::from(stop && mode == 1),
                    memory_mib: u128::from(stop && mode == 2),
                }
            },
        );
        let error = finite_object_law_instances(&i, &r, object(&r, "p"), &mut c).unwrap_err();
        assert!(matches!(error.cause, ValidationFailure::Stop(_)));
        let partial = error.partial.unwrap();
        assert!(!partial.is_complete());
        assert_eq!(
            partial.object_identity(),
            r.objects()[object(&r, "p")].identity()
        );
        assert_eq!(partial.entries.len(), 1);
        assert_eq!(partial.entries[0].state, ParameterFamilyState::Pending);
        assert_eq!(partial.entries[0].rows.len(), 1);
        assert_eq!(partial.entries[0].domains.len(), 2);
        assert!(partial.recheck(&i, &mut quiet()).is_err());
    }
}
#[test]
fn domain_cancellation_retains_only_finished_parameter_domains() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = input(GRID);
    let r = reading(&i);
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::FiniteLawDomain {
            seen.set(seen.get() + 1);
        }
        Usage {
            signal: (seen.get() >= 2).then_some(Signal::Int),
            ..Usage::default()
        }
    });
    let error = finite_object_law_instances(&i, &r, object(&r, "p"), &mut c).unwrap_err();
    let partial = error.partial.unwrap();
    assert!(!partial.is_complete());
    assert_eq!(partial.entries[0].domains.len(), 1);
    assert_eq!(partial.entries[0].domains[0].parameter.name, "n");
    assert!(partial.entries[0].rows.is_empty());
    assert_eq!(partial.entries[0].state, ParameterFamilyState::Pending);
}
#[test]
fn all_finite_bindings_feed_the_existing_object_law_evaluator_without_using_a_sample_value() {
    let i = input(GRID);
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let e = entry(&f, "grid", "p");
    let selected = e
        .rows
        .iter()
        .map(|row| (e.source.declaration().name.clone(), row.bindings.clone()))
        .collect::<Vec<_>>();
    let evaluated =
        finite_object_law_family_valuations(&i, &r, object(&r, "p"), &selected, &mut quiet())
            .unwrap();
    assert!(evaluated.is_complete());
    assert_eq!(evaluated.domain().len(), 2);
    assert_eq!(evaluated.columns().len(), 4);
    assert_eq!(evaluated.required_zero(), Some([].as_slice()));
    for (column, expected) in [[0, 1], [0, 1], [1, 0], [1, 0]].iter().enumerate() {
        assert_eq!(
            evaluated
                .integer_function(column, None, &mut quiet())
                .unwrap()
                .values(),
            expected
                .iter()
                .map(|n| (*n).into())
                .collect::<Vec<_>>()
                .as_slice()
        );
    }
    evaluated
        .recheck_on_object(&i, &r, object(&r, "p"), &mut quiet())
        .unwrap();
}

#[test]
fn conditional_object_without_scalar_parameters_does_not_acquire_a_ground_row() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required ground(c:Part):true;");
    let r = reading(&i);
    let f = family(&i, &r, "q");
    let q = entry(&f, "ground", "q");
    assert_eq!(q.state, ParameterFamilyState::Undetermined);
    assert!(q.source.parameters().is_empty());
    assert!(q.domains.is_empty());
    assert!(q.rows.is_empty());
    assert!(q.scope.completions);
    assert!(!f.is_complete());
    assert!(
        matches!(&q.application,InstanceApplication::Applicable{conditions} if conditions.len()==1 && conditions[0].slot().subject=="q")
    );
    assert_eq!(
        entry(&f, "ground", "p").state,
        ParameterFamilyState::NotApplicable
    );
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn data_option_and_tuple_parameters_use_every_typed_value_in_their_product() {
    let i = input("law optional product(c:Part,x:Token,o:Option<Bool>,t:(Fp(2),Bool)):true;");
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let e = entry(&f, "product", "p");
    assert_eq!(
        e.domains
            .iter()
            .map(|d| d.values.as_ref().unwrap().len())
            .collect::<Vec<_>>(),
        [4, 3, 4]
    );
    assert_eq!(e.rows.len(), 48);
    assert!(f.is_complete());
    for row in &e.rows {
        assert_eq!(row.bindings[1].1.ty(), Type::Data("Pattern.Token".into()));
        assert_eq!(row.bindings[2].1.ty(), Type::Option(Box::new(Type::Bool)));
        assert_eq!(
            row.bindings[3].1.ty(),
            Type::Tuple(vec![Type::Fp("2".into()), Type::Bool])
        );
    }
    assert_eq!(e.scope.quantifiers.len(), 3);
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn an_empty_factor_makes_a_composite_domain_empty_even_with_an_infinite_factor() {
    let i = input("law required empty(c:Part,x:(Z,Map<Root,Vacant>)):false;");
    let r = reading(&i);
    let f = family(&i, &r, "p");
    let e = entry(&f, "empty", "p");
    assert_eq!(e.state, ParameterFamilyState::Ready);
    assert_eq!(e.domains[0].values.as_deref(), Some([].as_slice()));
    assert!(e.rows.is_empty());
    assert!(f.is_complete());
    assert_eq!(
        e.domains[0].parameter.ty,
        Type::Tuple(vec![
            Type::Z,
            Type::Map(
                Box::new(Type::Ref("Pattern.Root".into())),
                Box::new(Type::Ref("Pattern.Vacant".into()))
            )
        ])
    );
}

#[test]
fn separate_infinite_and_empty_parameters_have_an_empty_complete_product_in_either_order() {
    for body in [
        "law required empty(c:Part,n:Z,x:Map<Root,Vacant>):false;",
        "law required empty(c:Part,x:Map<Root,Vacant>,n:Z):false;",
    ] {
        let i = input(body);
        let r = reading(&i);
        let f = family(&i, &r, "p");
        let e = entry(&f, "empty", "p");
        let n = e.domains.iter().find(|d| d.parameter.name == "n").unwrap();
        let x = e.domains.iter().find(|d| d.parameter.name == "x").unwrap();
        assert_eq!(n.parameter.ty, Type::Z);
        assert_eq!(n.values, None);
        assert_eq!(x.values.as_deref(), Some([].as_slice()));
        assert!(x.missing.is_empty());
        assert_eq!(e.state, ParameterFamilyState::Ready);
        assert!(e.rows.is_empty());
        assert!(f.is_complete());
        assert_eq!(e.scope.quantifiers.len(), 2);
        f.recheck(&i, &mut quiet()).unwrap();
    }
}
#[test]
fn an_independent_empty_factor_keeps_unknown_fiber_and_application_evidence_without_rows() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(
        &map,
        "law required empty(r:Root,c:Part,x:Option<Part[r]>,void:Map<Root,Vacant>):false;",
    );
    let r = reading(&i);
    let f = family(&i, &r, "root");
    assert!(f.is_complete());
    assert_eq!(f.entries().len(), 2);
    for e in f.entries() {
        assert_eq!(e.state, ParameterFamilyState::Ready);
        assert!(e.rows.is_empty());
        assert!(e.domains[0].missing.iter().any(|p| p.subject == "q"));
        assert_eq!(e.domains[1].values.as_deref(), Some([].as_slice()));
        assert!(e.domains[1].missing.is_empty());
        assert!(e.scope.completions);
    }
    assert!(
        matches!(&entry(&f,"empty","q").application,InstanceApplication::Applicable{conditions} if conditions.len()==1)
    );
    f.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn a_fiber_with_no_known_members_and_missing_owners_is_not_a_known_empty_factor() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(
        &map,
        "law required unknown(c:Root,x:Map<Root,Part[c]>,n:Z):false;",
    );
    let construction = construct(&i, "Selected", "v", "r2", &mut quiet()).unwrap();
    let r = object_reading_instances(&i, &construction, &mut quiet()).unwrap();
    let f = family(&i, &r, "r2");
    let e = entry(&f, "unknown", "r2");
    assert_eq!(e.state, ParameterFamilyState::Undetermined);
    assert!(!f.is_complete());
    assert!(e.rows.is_empty());
    assert_eq!(e.domains[0].values.as_deref(), Some([].as_slice()));
    assert!(e.domains[0].missing.iter().any(|p| p.subject == "q"));
    assert_eq!(e.domains[1].values, None);
    f.recheck(&i, &mut quiet()).unwrap();
}
