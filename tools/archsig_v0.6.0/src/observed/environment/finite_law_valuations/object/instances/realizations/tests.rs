use super::*;
use crate::construction::{construct, readings::object_reading_instances};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
fn reading(i: &CheckedInputs, root: &str) -> ObjectReadingInstances {
    let construction = construct(i, "Selected", "v", root, &mut quiet()).unwrap();
    object_reading_instances(i, &construction, &mut quiet()).unwrap()
}
fn object(r: &ObjectReadingInstances, name: &str) -> usize {
    r.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
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
fn result(i: &CheckedInputs, r: &ObjectReadingInstances) -> FiniteParameterRealizations {
    finite_parameter_realizations(i, r, &mut quiet()).unwrap()
}
fn root_members(f: &FiniteParameterRealizations, point: usize) -> usize {
    f.domain[point]
        .iter()
        .filter(|value| matches!(value,Scalar::Subject{subject,..} if subject=="root"))
        .count()
}
const OWNED: &str = "law required owned(r:Root,c:Part,x:Option<Part[r]>):true;";
#[test]
fn every_primitive_owner_assignment_has_its_actual_parameter_fiber() {
    let i = fixture::with_body(fixture::MAP, OWNED);
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert_eq!(f.readings(), &r);
    assert_eq!(
        f.positions
            .iter()
            .map(|p| p.subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
    assert!(
        f.positions
            .iter()
            .all(|p| p.field.as_deref() == Some("Pattern.Part.owner"))
    );
    assert_eq!(f.types, vec![Type::Ref("Pattern.Root".into()); 2]);
    assert_eq!(f.domain.len(), 4);
    assert_eq!(f.rows.len(), 4);
    assert_eq!(f.observed_point, Some(3));
    let root = object(&r, "root");
    for (point, row) in f.rows.iter().enumerate() {
        assert_eq!(row.point, point);
        assert_eq!(row.objects.len(), r.objects().len());
        for (index, obj) in row.objects.iter().enumerate() {
            assert_eq!(obj.object_identity(), r.objects()[index].identity());
            assert_eq!(obj.entries().len(), 2);
            assert_eq!(obj.valuation.as_ref().unwrap().len(), 2);
        }
        for subject in ["p", "q"] {
            let e = entry(&row.objects[root], "owned", subject);
            assert_eq!(e.source, r.instances()[e.instance]);
            assert_eq!(e.application_value, Some(Some(true)));
            assert_eq!(e.state, ParameterFamilyState::Ready);
            assert_eq!(e.rows.len(), 1 + root_members(&f, point));
            assert_eq!(e.domains[0].values.as_ref().unwrap().len(), e.rows.len());
            assert!(e.domains[0].scope.assignments);
            assert!(e.domains[0].missing.is_empty());
            assert_eq!(
                e.domains[0].scope.quantifiers[0].occurrence,
                e.domains[0].parameter.span
            );
            for candidate in ["p", "q"] {
                let position = f
                    .positions
                    .iter()
                    .position(|p| p.subject == candidate)
                    .unwrap();
                let contained = matches!(&f.domain[point][position],Scalar::Subject{subject,..} if subject=="root");
                assert_eq!(e.rows.iter().any(|b|matches!(&b.bindings[2].1,Scalar::Option{value:Some(v),..} if matches!(v.as_ref(),Scalar::Subject{subject,..} if subject==candidate))),contained);
            }
            assert_eq!(
                e.rows.iter().map(|b| b.coordinates[0]).collect::<Vec<_>>(),
                (0..e.rows.len()).collect::<Vec<_>>()
            );
            assert!(e.rows.iter().all(|b| {
                b.bindings.iter().map(|b| b.0.as_str()).collect::<Vec<_>>() == ["r", "c", "x"]
            }));
        }
        for name in ["p", "q"] {
            assert!(
                row.objects[object(&r, name)]
                    .entries()
                    .iter()
                    .all(|e| e.application_value == Some(Some(false))
                        && e.state == ParameterFamilyState::NotApplicable
                        && e.rows.is_empty())
            );
        }
    }
    f.rows[3].objects[root]
        .recheck_on_object(&i, &r, root, &mut quiet())
        .unwrap();
    f.recheck(&i, &r, &mut quiet()).unwrap();
}
#[test]
fn missing_observation_does_not_drop_parameters_that_exist_in_other_assignments() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    assert!(!map.contains(r#""id":"oq""#));
    let i = fixture::with_body(&map, OWNED);
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert_eq!(f.domain.len(), 4);
    assert_eq!(f.observed_point, None);
    let root = object(&r, "root");
    for (point, row) in f.rows.iter().enumerate() {
        let e = entry(&row.objects[root], "owned", "q");
        assert!(
            matches!(&e.application,InstanceApplication::Applicable{conditions} if conditions.len()==1)
        );
        let qroot = matches!(&f.domain[point][1],Scalar::Subject{subject,..} if subject=="root");
        assert_eq!(e.application_value, Some(Some(qroot)));
        assert_eq!(
            e.state,
            if qroot {
                ParameterFamilyState::Ready
            } else {
                ParameterFamilyState::NotApplicable
            }
        );
        assert_eq!(
            e.rows.len(),
            if qroot {
                1 + root_members(&f, point)
            } else {
                0
            }
        );
        assert!(e.scope.assignments);
        assert!(e.support.iter().any(|p| p.subject == "q"
            && p.field.as_deref() == Some("Pattern.Part.owner")
            && p.atom.is_none()));
    }
    let observed = finite_object_law_instances(&i, &r, root, &mut quiet()).unwrap();
    assert!(!observed.is_complete());
    assert_eq!(entry(&observed, "owned", "q").application_value, None);
    assert_eq!(
        entry(&observed, "owned", "q").state,
        ParameterFamilyState::Undetermined
    );
    f.recheck(&i, &r, &mut quiet()).unwrap();
}
#[test]
fn map_parameter_is_total_on_each_actual_owned_domain() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required tables(r:Root,x:Map<Part[r],Part[r]>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert_eq!(f.domain.len(), 4);
    for (point, row) in f.rows.iter().enumerate() {
        let e = entry(&row.objects[object(&r, "root")], "tables", "root");
        let n = root_members(&f, point);
        assert_eq!(e.rows.len(), n.pow(n as u32));
        for binding in &e.rows {
            let Scalar::Map { pairs: entries, .. } = &binding.bindings[1].1 else {
                panic!("expected map")
            };
            assert_eq!(entries.len(), n);
            for (key, value) in entries {
                let Scalar::Subject { subject, .. } = key else {
                    panic!("expected subject")
                };
                let position = f
                    .positions
                    .iter()
                    .position(|p| &p.subject == subject)
                    .unwrap();
                assert!(
                    matches!(&f.domain[point][position],Scalar::Subject{subject,..} if subject=="root")
                );
                let Scalar::Subject { subject, .. } = value else {
                    panic!("expected target")
                };
                let position = f
                    .positions
                    .iter()
                    .position(|p| &p.subject == subject)
                    .unwrap();
                assert!(
                    matches!(&f.domain[point][position],Scalar::Subject{subject,..} if subject=="root")
                );
            }
        }
    }
}
#[test]
fn nondependent_reference_parameters_use_the_full_roster_without_owner_axes() {
    let i = fixture::with_body(
        fixture::MAP,
        "view ignored(c:Part):Fp(2)=c.quantity;law required global(c:Part,x:Set<Part>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert!(f.positions.is_empty());
    assert_eq!(f.domain, vec![vec![]]);
    assert_eq!(f.observed_point, Some(0));
    for subject in ["p", "q"] {
        let e = entry(&f.rows[0].objects[object(&r, "root")], "global", subject);
        assert_eq!(e.rows.len(), 4);
        assert!(
            e.rows
                .iter()
                .any(|b| matches!(&b.bindings[1].1,Scalar::Set{items,..} if items.len()==2))
        );
    }
    assert_eq!(f.rows[0].objects[0].entries().len(), 2);
}
#[test]
fn declared_scalar_product_and_interleaved_reference_order_are_preserved() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required grid(n:Fp(2),c:Part,b:Bool):c.quantity=n;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert!(f.positions.is_empty()); // body quantities are not parameter-domain dependencies.
    let e = entry(&f.rows[0].objects[object(&r, "root")], "grid", "p");
    assert_eq!(e.rows.len(), 4);
    assert_eq!(
        e.rows
            .iter()
            .map(|row| row.coordinates.clone())
            .collect::<Vec<_>>(),
        [vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]]
    );
    for row in &e.rows {
        assert_eq!(
            row.bindings
                .iter()
                .map(|b| b.0.as_str())
                .collect::<Vec<_>>(),
            ["n", "c", "b"]
        );
    }
    assert!(matches!(e.rows[2].bindings[0].1,Scalar::Fp{ref value,..} if value==&1.into()));
    assert_eq!(e.rows[2].bindings[2].1, Scalar::Bool(false));
}
#[test]
fn infinite_parameter_keeps_type_and_does_not_become_completed_empty_product() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required unbounded(c:Part,b:Bool,n:Z,k:Fp(2)):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(!f.is_complete());
    assert!(f.domain_complete);
    assert_eq!(f.state, ParameterRealizationState::Incomplete);
    assert_eq!(f.domain, vec![vec![]]);
    let e = entry(&f.rows[0].objects[object(&r, "root")], "unbounded", "p");
    assert_eq!(e.state, ParameterFamilyState::OutsideFinite);
    assert_eq!(e.domains[1].parameter.ty, Type::Z);
    assert_eq!(e.domains[1].values, None);
    assert!(e.domains[1].missing.is_empty());
    assert_eq!(e.domains[0].values.as_ref().unwrap().len(), 2);
    assert_eq!(e.domains[2].values.as_ref().unwrap().len(), 2);
    assert!(e.rows.is_empty());
    f.recheck(&i, &r, &mut quiet()).unwrap();
}
#[test]
fn known_empty_parameter_annihilates_nonfinite_factor_without_erasing_it() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required empty(c:Part,n:Z,x:Map<Root,Vacant>):true;law optional singleton(c:Part,x:List<Vacant>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    let root = &f.rows[0].objects[object(&r, "root")];
    let empty = entry(root, "empty", "p");
    assert_eq!(empty.state, ParameterFamilyState::Ready);
    assert!(empty.rows.is_empty());
    assert_eq!(empty.domains[0].values, None);
    assert_eq!(empty.domains[0].parameter.ty, Type::Z);
    assert_eq!(empty.domains[1].values, Some(vec![]));
    let unit = entry(root, "singleton", "p");
    assert_eq!(unit.rows.len(), 1);
    assert!(matches!(&unit.rows[0].bindings[1].1,Scalar::List{items,..} if items.is_empty()));
    assert_eq!(
        unit.source.declaration().role,
        Some(crate::law::ast::Role::Optional)
    );
}
#[test]
fn empty_law_set_keeps_all_objects_and_the_single_empty_assignment() {
    let i = fixture::with_body(fixture::MAP, "view only(c:Part):Fp(2)=c.quantity;");
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert_eq!(f.domain, vec![vec![]]);
    assert_eq!(f.rows[0].objects.len(), r.objects().len());
    assert!(
        f.rows[0]
            .objects
            .iter()
            .all(|o| o.entries().is_empty() && o.is_complete())
    );
    f.recheck(&i, &r, &mut quiet()).unwrap();
    assert!(f.recheck(&i, &reading(&i, "r2"), &mut quiet()).is_err());
}
#[test]
fn every_domain_row_application_and_source_is_rebuilt_before_reuse() {
    let i = fixture::with_body(fixture::MAP, OWNED);
    let r = reading(&i, "root");
    let f = result(&i, &r);
    let root = object(&r, "root");
    for mutation in 0..12 {
        let mut bad = f.clone();
        match mutation {
            0 => bad.positions.swap(0, 1),
            1 => bad.types[0] = Type::Bool,
            2 => bad.domain.swap(0, 1),
            3 => bad.rows[0].point = 1,
            4 => bad.rows[0].objects.swap(root, object(&r, "p")),
            5 => bad.rows[0].objects[root].entries[0].instance = usize::MAX,
            6 => bad.rows[0].objects[root].entries[0].application_value = Some(Some(false)),
            7 => {
                bad.rows[0].objects[root].entries[0].domains[0]
                    .parameter
                    .span
                    .0 += 1
            }
            8 => bad.rows[0].objects[root].entries[0].rows[0]
                .bindings
                .pop()
                .map(drop)
                .unwrap(),
            9 => bad.rows[0].objects[root].entries[0].domains[0]
                .scope
                .readings
                .clear(),
            10 => bad.observed_point = Some(0),
            _ => bad.domain_complete = false,
        }
        assert!(
            bad.recheck(&i, &r, &mut quiet()).is_err(),
            "mutation {mutation}"
        );
    }
    let changed = fixture::with_body(&(fixture::MAP.to_string() + " "), OWNED);
    assert!(f.recheck(&changed, &r, &mut quiet()).is_err());
    assert!(f.recheck(&i, &reading(&i, "r2"), &mut quiet()).is_err());
}
#[test]
fn set_parameter_contains_every_subset_of_the_current_fiber() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required sets(r:Root,x:Set<Part[r]>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    for (point, row) in f.rows.iter().enumerate() {
        let e = entry(&row.objects[object(&r, "root")], "sets", "root");
        let n = root_members(&f, point);
        assert_eq!(e.rows.len(), 2usize.pow(n as u32));
        for binding in &e.rows {
            let Scalar::Set { items, .. } = &binding.bindings[1].1 else {
                panic!("expected set")
            };
            assert!(items.len() <= n);
            for item in items {
                let Scalar::Subject { subject, .. } = item else {
                    panic!("expected member")
                };
                let position = f
                    .positions
                    .iter()
                    .position(|p| &p.subject == subject)
                    .unwrap();
                assert!(
                    matches!(&f.domain[point][position],Scalar::Subject{subject,..} if subject=="root")
                );
            }
        }
        assert!(
            e.rows
                .iter()
                .any(|b| matches!(&b.bindings[1].1,Scalar::Set{items,..} if items.len()==n))
        );
    }
}
#[test]
fn mixed_infinite_and_dependent_domains_keep_each_point_metadata() {
    let map=fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"");
    let i = fixture::with_body(
        &map,
        "law required mixed(r:Root,c:Part,n:Z,x:Option<Part[r]>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(!f.is_complete());
    assert!(f.domain_complete);
    assert_eq!(f.domain.len(), 4);
    assert_eq!(f.observed_point, None);
    for (point, row) in f.rows.iter().enumerate() {
        let e = entry(&row.objects[object(&r, "root")], "mixed", "p");
        assert_eq!(e.state, ParameterFamilyState::OutsideFinite);
        assert_eq!(e.domains[0].values, None);
        assert_eq!(e.domains[0].parameter.ty, Type::Z);
        assert!(e.domains[0].parameter.span.1 > e.domains[0].parameter.span.0);
        assert_eq!(
            e.domains[1].values.as_ref().unwrap().len(),
            1 + root_members(&f, point)
        );
        assert!(e.domains[1].missing.is_empty());
        assert!(e.domains[1].scope.assignments);
        assert!(e.domains[1].support.iter().any(|p| p.subject == "q"
            && p.field.as_deref() == Some("Pattern.Part.owner")
            && p.atom.is_none()));
        assert!(e.rows.is_empty());
    }
    f.recheck(&i, &r, &mut quiet()).unwrap();
}
#[test]
fn fixed_stops_publish_only_finished_points_and_keep_the_original_readings() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(fixture::MAP, OWNED);
    let r = reading(&i, "root");
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawRequired {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= 1).then_some(Signal::Term)
    });
    let error = finite_parameter_realizations(&i, &r, &mut c).unwrap_err();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    assert_eq!(partial.readings(), &r);
    assert!(!partial.is_complete());
    assert_eq!(partial.state, ParameterRealizationState::Pending);
    assert!(partial.domain_complete);
    assert_eq!(partial.domain.len(), 4);
    assert_eq!(partial.rows.len(), 1);
    assert_eq!(partial.rows[0].point, 0);
    assert_eq!(partial.rows[0].objects.len(), r.objects().len());
    assert!(
        partial.rows[0]
            .objects
            .iter()
            .all(ObjectLawInstances::is_complete)
    );
    assert!(partial.recheck(&i, &r, &mut quiet()).is_err());
}
#[test]
fn domain_interrupt_keeps_source_and_never_claims_a_finished_empty_domain() {
    use crate::result::Signal;
    let i = fixture::with_body(fixture::MAP, OWNED);
    let r = reading(&i, "root");
    let mut c = Control::new(|p| (p == Checkpoint::FiniteLawDomain).then_some(Signal::Int));
    let error = finite_parameter_realizations(&i, &r, &mut c).unwrap_err();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    assert_eq!(partial.readings(), &r);
    assert_eq!(partial.sources, *i.sources());
    assert!(!partial.domain_complete);
    assert!(!partial.is_complete());
    assert!(partial.rows.is_empty());
    assert!(partial.recheck(&i, &r, &mut quiet()).is_err());
}
#[test]
fn fixed_owned_reference_binder_is_rechecked_even_when_original_conditions_were_empty() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required owned(r:Root,c:Part[r],x:Option<Part[r]>):true;",
    );
    let r = reading(&i, "root");
    let f = result(&i, &r);
    assert!(f.is_complete());
    assert_eq!(f.domain.len(), 4);
    let root = object(&r, "root");
    for (point, row) in f.rows.iter().enumerate() {
        for subject in ["p", "q"] {
            let e = entry(&row.objects[root], "owned", subject);
            assert!(
                matches!(&e.application, InstanceApplication::Applicable {conditions} if conditions.is_empty())
            );
            let position = f
                .positions
                .iter()
                .position(|p| p.subject == subject)
                .unwrap();
            let applicable = matches!(&f.domain[point][position], Scalar::Subject {subject,..} if subject=="root");
            assert_eq!(
                e.application_value,
                Some(Some(applicable)),
                "point {point}, subject {subject}"
            );
            assert_eq!(
                e.rows.len(),
                if applicable {
                    1 + root_members(&f, point)
                } else {
                    0
                }
            );
            assert_eq!(
                e.state,
                if applicable {
                    ParameterFamilyState::Ready
                } else {
                    ParameterFamilyState::NotApplicable
                }
            );
            assert!(e.scope.assignments);
            assert!(e.support.iter().any(|p| p.subject == subject
                && p.field.as_deref() == Some("Pattern.Part.owner")
                && p.atom.is_none()));
        }
    }
}
#[test]
fn owned_binder_alone_discovers_owner_axes_without_a_dependent_value_parameter() {
    for missing in [false, true] {
        let map = if missing {
            fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#, "")
        } else {
            fixture::MAP.to_string()
        };
        let i = fixture::with_body(&map, "law required binders(r:Root,c:Part[r],b:Bool):true;");
        let r = reading(&i, "root");
        let f = result(&i, &r);
        assert!(f.is_complete());
        assert_eq!(
            f.positions
                .iter()
                .map(|p| p.subject.as_str())
                .collect::<Vec<_>>(),
            ["p", "q"]
        );
        assert_eq!(f.domain.len(), 4);
        assert_eq!(f.observed_point, if missing { None } else { Some(3) });
        let root = object(&r, "root");
        for (point, row) in f.rows.iter().enumerate() {
            for subject in ["p", "q"] {
                let e = entry(&row.objects[root], "binders", subject);
                let position = f
                    .positions
                    .iter()
                    .position(|p| p.subject == subject)
                    .unwrap();
                let applicable = matches!(&f.domain[point][position], Scalar::Subject {subject,..} if subject=="root");
                assert_eq!(e.application_value, Some(Some(applicable)));
                assert_eq!(e.rows.len(), if applicable { 2 } else { 0 });
                if applicable {
                    assert_eq!(e.rows[0].bindings[2].1, Scalar::Bool(false));
                    assert_eq!(e.rows[1].bindings[2].1, Scalar::Bool(true));
                    assert_eq!(e.rows[0].coordinates, [0]);
                    assert_eq!(e.rows[1].coordinates, [1]);
                } else {
                    assert_eq!(e.state, ParameterFamilyState::NotApplicable);
                }
            }
        }
        f.recheck(&i, &r, &mut quiet()).unwrap();
    }
}
