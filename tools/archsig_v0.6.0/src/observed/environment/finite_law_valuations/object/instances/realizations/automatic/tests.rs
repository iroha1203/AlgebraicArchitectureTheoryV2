use super::*;
use crate::construction::{construct, readings::object_reading_instances};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../../../tests/common/primitive_valuation_data.rs");
}
use crate::control::quiet;
fn reading(i: &CheckedInputs, root: &str) -> ObjectReadingInstances {
    let c = construct(i, "Selected", "v", root, &quiet()).unwrap();
    object_reading_instances(i, &c, &quiet()).unwrap()
}
fn run(i: &CheckedInputs, r: &ObjectReadingInstances) -> FiniteAutomaticLawFamily {
    finite_automatic_law_family(i, r, &quiet()).unwrap()
}
fn missing_map() -> String {
    fixture::MAP.replace(r#",{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}"#,"")
}
#[test]
fn all_original_instances_and_parameter_rows_are_automatically_evaluated_on_every_object() {
    let i = fixture::with_body(
        fixture::MAP,
        "view helper(c:Part):Fp(2)=c.quantity;law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    assert!(result.is_complete());
    let p = result.parameters();
    let f = result.family().unwrap();
    assert!(p.law_dependencies);
    assert_eq!(p.domain.len(), 4);
    assert_eq!(f.positions(), p.positions);
    assert_eq!(f.domain(), p.domain);
    assert_eq!(f.columns().len(), 24);
    assert_eq!(f.observed_point(), Some(1)); // p=0,q=1.
    let mut outside = 0;
    for (index, column) in f.columns().iter().enumerate() {
        let (source, application) = f.instance_source(index).unwrap();
        assert_eq!(source.declaration().name, "Selected.grid");
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        let subject = &source.bindings()[0].subject().subject;
        let applicable = target == "root" || target == subject;
        assert_eq!(
            matches!(application, InstanceApplication::Applicable { .. }),
            applicable
        );
        if !applicable {
            outside += 1;
        }
        let n = match &column.bindings()[1].1 {
            Scalar::Fp { value, .. } => value.to_string().parse::<u8>().unwrap(),
            _ => panic!("Fp parameter"),
        };
        assert_eq!(
            column
                .bindings()
                .iter()
                .map(|b| b.0.as_str())
                .collect::<Vec<_>>(),
            ["c", "n", "b"]
        );
        for (point, row) in column.rows().iter().enumerate() {
            let value = if subject == "p" { point / 2 } else { point % 2 };
            assert_eq!(row.application, Some(applicable));
            assert_eq!(
                row.indicator,
                Some(u8::from(applicable && value != n as usize).into())
            );
            if !applicable {
                assert_eq!(row.operands, None);
                assert_eq!(row.guard, None);
            }
        }
    }
    assert_eq!(outside, 8);
    assert_eq!(f.required_zero(), Some([].as_slice()));
    assert_eq!(f.required_generators(&quiet()).unwrap().len(), 24);
    assert!(f.required_quotient(&quiet()).unwrap().points().is_empty());
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn optional_values_survive_the_same_required_quotient_and_other_rings_are_rejected() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law optional suggest(c:Part):c.quantity=1;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.columns().len(), 12);
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    let optional = (0..f.columns().len())
        .find(|&index| {
            f.columns()[index].declaration().name == "Selected.suggest"
                && f.column_object_identity(index).unwrap().subject().subject == "root"
        })
        .unwrap();
    let value = f.integer_function(optional, None, &quiet()).unwrap();
    let quotient = f.required_quotient(&quiet()).unwrap();
    assert_eq!(
        quotient.project(&value, &quiet()).unwrap().values(),
        &[BigInt::from(1)]
    );
    let membership = quotient.ideal_membership(&value, &quiet()).unwrap();
    quotient
        .recheck_membership(&i, &a, &value, &membership, &quiet())
        .unwrap();
    let projected = quotient.project(&value, &quiet()).unwrap();
    assert!(
        !quotient
            .integer_ring(&quiet())
            .unwrap()
            .is_zero(&projected, &quiet())
            .unwrap()
    );
    let other = run(&i, &a);
    let foreign = other
        .family()
        .unwrap()
        .integer_function(optional, None, &quiet())
        .unwrap();
    assert!(
        f.integer_ring(&quiet())
            .unwrap()
            .member(&foreign, &quiet())
            .is_err()
    );
}
#[test]
fn varying_owned_parameter_fibers_form_one_carrier_without_pruning_the_shared_domain() {
    let i = fixture::with_body(
        &missing_map(),
        "law required owned(r:Root,c:Part[r],x:Option<Part[r]>):true;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.columns().len(), 18);
    assert_eq!(f.observed_point(), None);
    assert_eq!(f.required_zero(), Some([0, 1, 2, 3].as_slice()));
    for (index, column) in f.columns().iter().enumerate() {
        let source = f.instance_source(index).unwrap().0;
        let c = &source
            .bindings()
            .iter()
            .find(|b| b.parameter().name == "c")
            .unwrap()
            .subject()
            .subject;
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        for (point, row) in column.rows().iter().enumerate() {
            let cpos = f.positions().iter().position(|p| &p.subject == c).unwrap();
            let c_here =
                matches!(&f.domain()[point][cpos],Scalar::Subject{subject,..} if subject=="root");
            let x_here = match &column.bindings()[2].1 {
                Scalar::Option { value: None, .. } => true,
                Scalar::Option { value: Some(x), .. } => {
                    let Scalar::Subject { subject, .. } = x.as_ref() else {
                        panic!("subject")
                    };
                    let pos = f
                        .positions()
                        .iter()
                        .position(|p| &p.subject == subject)
                        .unwrap();
                    matches!(&f.domain()[point][pos],Scalar::Subject{subject,..} if subject=="root")
                }
                _ => panic!("Option parameter"),
            };
            assert_eq!(row.application, Some(target == "root" && c_here && x_here));
            assert_eq!(row.indicator, Some(0.into()));
        }
    }
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn parameter_and_conditional_body_dependencies_share_the_same_exhausted_domain() {
    let i = fixture::with_body(
        &missing_map(),
        "law required all(c:Part,b:Bool):forall x:Part . x.quantity=0;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.domain().len(), 8);
    assert_eq!(f.columns().len(), 12);
    assert_eq!(
        f.positions()
            .iter()
            .map(|p| (p.subject.as_str(), p.field.as_deref()))
            .collect::<Vec<_>>(),
        [
            ("p", Some("Pattern.Part.quantity")),
            ("q", Some("Pattern.Part.owner")),
            ("q", Some("Pattern.Part.quantity"))
        ]
    );
    assert_eq!(f.observed_point(), None);
    for (index, column) in f.columns().iter().enumerate() {
        let c = &f.instance_source(index).unwrap().0.bindings()[0]
            .subject()
            .subject;
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        for (point, row) in column.rows().iter().enumerate() {
            let values = &f.domain()[point];
            let p = matches!(&values[0],Scalar::Fp{value,..} if value==&0.into());
            let included = matches!(&values[1],Scalar::Subject{subject,..} if subject=="root");
            let q = matches!(&values[2],Scalar::Fp{value,..} if value==&0.into());
            let applies = (target == "root" || target == c) && (c != "q" || included);
            let holds = if target == "root" {
                p && (!included || q)
            } else if target == "p" {
                p
            } else {
                q
            };
            assert_eq!(row.application, Some(applies));
            assert_eq!(row.indicator, Some(u8::from(applies && !holds).into()));
        }
    }
    assert_eq!(f.required_zero(), Some([0, 1, 2].as_slice()));
    result.recheck(&i, &a, &quiet()).unwrap();
}
fn coupled_inputs() -> Arc<CheckedInputs> {
    let base = fixture::inputs();
    let original = String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap();
    let definitions = original.replacen(
        r#""name":"link","type":["Ref","Pattern.Part"]"#,
        r#""name":"link","type":["Owned","Pattern.Part","owner"]"#,
        1,
    );
    assert_ne!(definitions, original);
    let checked =
        crate::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map=fixture::MAP.replace(r#""field":"Pattern.Part.link","value":["v","p"]"#,r#""field":"Pattern.Part.link","value":["v","q"]"#)
        .replace(r#""atoms":["#,r#""atoms":[{"id":"lq","subject":"q","field":"Pattern.Part.link","value":["v","p"],"origin":"model"},"#)
        .replace("@DIGEST@",digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required joint(r:Root,c:Part,x:Option<Part[r]>):c.link=c;}}"
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
#[test]
fn body_positions_are_discovered_before_constraints_prune_a_parameter_only_assignment() {
    let i = coupled_inputs();
    let a = reading(&i, "root");
    let parameters = finite_parameter_realizations(&i, &a, &quiet()).unwrap();
    assert_eq!(parameters.positions.len(), 2);
    assert_eq!(parameters.domain.len(), 2); // fixed cross-links require equal owners.
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.positions().len(), 4);
    assert_eq!(f.domain().len(), 10);
    assert_eq!(f.columns().len(), 18);
    let position = |subject: &str, field: &str| {
        f.positions()
            .iter()
            .position(|p| p.subject == subject && p.field.as_deref() == Some(field))
            .unwrap()
    };
    let po = position("p", "Pattern.Part.owner");
    let qo = position("q", "Pattern.Part.owner");
    let pl = position("p", "Pattern.Part.link");
    let ql = position("q", "Pattern.Part.link");
    let mut new_points = 0;
    let mut expected_zero = vec![];
    for (point, values) in f.domain().iter().enumerate() {
        let owner = |index| match &values[index] {
            Scalar::Subject { subject, .. } => subject.as_str(),
            _ => panic!("owner"),
        };
        if owner(po) != owner(qo) {
            new_points += 1;
            assert_eq!(owner(pl), "p");
            assert_eq!(owner(ql), "q");
        }
        if owner(pl) == "p" && owner(ql) == "q" {
            expected_zero.push(point);
        }
        for (index, column) in f.columns().iter().enumerate() {
            let subject = &f
                .instance_source(index)
                .unwrap()
                .0
                .bindings()
                .iter()
                .find(|b| b.parameter().name == "c")
                .unwrap()
                .subject()
                .subject;
            let target = &f.column_object_identity(index).unwrap().subject().subject;
            let x_applies = match &column.bindings()[2].1 {
                Scalar::Option { value: None, .. } => true,
                Scalar::Option { value: Some(x), .. } => {
                    let Scalar::Subject { subject, .. } = x.as_ref() else {
                        panic!("parameter ref")
                    };
                    owner(if subject == "p" { po } else { qo }) == "root"
                }
                _ => panic!("Option"),
            };
            let applies = target == "root" && x_applies;
            let holds = owner(if subject == "p" { pl } else { ql }) == subject;
            assert_eq!(
                column.rows()[point].indicator,
                Some(u8::from(applies && !holds).into())
            );
        }
    }
    assert_eq!(new_points, 2);
    assert_eq!(expected_zero.len(), 4);
    assert_eq!(f.required_zero(), Some(expected_zero.as_slice()));
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn nonfinite_parameter_and_nonfinite_body_keep_separate_original_reasons() {
    for (body, parameter) in [
        ("law required infinite(c:Part,n:Z):true;", true),
        ("law required infinite(c:Part):c.integer=0;", false),
    ] {
        let i = fixture::with_body(fixture::MAP, body);
        let a = reading(&i, "root");
        let result = run(&i, &a);
        assert!(!result.is_complete());
        assert!(result.family().is_none());
        if parameter {
            assert_eq!(
                result.parameters().state,
                ParameterRealizationState::Incomplete
            );
            assert!(result.parameters().domain_complete);
            let e = result
                .parameters()
                .rows
                .iter()
                .flat_map(|r| &r.objects)
                .flat_map(|o| o.entries())
                .find(|e| e.state == ParameterFamilyState::OutsideFinite)
                .unwrap();
            assert_eq!(e.domains[0].parameter.ty, Type::Z);
            assert_eq!(e.domains[0].values, None);
            assert!(e.rows.is_empty());
        } else {
            assert!(
                matches!(&result.parameters().state,ParameterRealizationState::OutsideFinite{position,ty:Type::Z} if position.field.as_deref()==Some("Pattern.Part.integer"))
            );
            assert!(!result.parameters().domain_complete);
            assert_eq!(result.parameters().readings(), &a);
        }
        result.recheck(&i, &a, &quiet()).unwrap();
    }
}
#[test]
fn empty_laws_and_known_empty_parameter_products_keep_the_anchored_empty_family() {
    for body in [
        "view helper(c:Part):Fp(2)=c.quantity;",
        "law required empty(c:Part,x:Map<Root,Vacant>):false;",
    ] {
        let i = fixture::with_body(fixture::MAP, body);
        let a = reading(&i, "root");
        let result = run(&i, &a);
        let f = result.family().unwrap();
        assert!(result.is_complete());
        assert!(f.columns().is_empty());
        assert!(f.positions().is_empty());
        assert_eq!(f.domain(), [vec![]]);
        assert_eq!(f.required_zero(), Some([0].as_slice()));
        assert_eq!(f.required_quotient(&quiet()).unwrap().points(), [0]);
        assert_eq!(result.parameters().rows[0].objects.len(), a.objects().len());
        result.recheck(&i, &a, &quiet()).unwrap();
        assert!(result.recheck(&i, &reading(&i, "r2"), &quiet()).is_err());
    }
}
#[test]
fn a_false_guard_keeps_nonfinite_operands_unevaluated_without_losing_typed_zero_components() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part,n:Fp(2)) when false:c.integer=0;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.columns().len(), 12);
    assert!(f.positions().is_empty());
    assert_eq!(f.domain(), [vec![]]);
    for column in f.columns() {
        let row = &column.rows()[0];
        assert_eq!(row.indicator, Some(0.into()));
        assert_eq!(row.operands, None);
        assert_eq!(row.predicate, None);
        let leaf = &row.components.as_ref().unwrap()[0];
        assert_eq!(leaf.ty, Type::Z);
        assert_eq!(leaf.indicator, Some(0.into()));
        assert_eq!(leaf.left, None);
        assert_eq!(leaf.right, None);
        assert_eq!(leaf.equal, None);
    }
}
#[test]
fn fixed_stops_keep_the_completed_parameter_plan_and_only_finished_law_rows() {
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let started = Rc::new(Cell::new(false));
    let stage = started.clone();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let c = Control::new(move |p| {
        if p == Checkpoint::FiniteLawAutomatic {
            stage.set(true);
        }
        if stage.get() && p == Checkpoint::FiniteLawEvaluation {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= 3).then_some(Signal::Term)
    });
    let error = finite_automatic_law_family(&i, &a, &c).err().unwrap();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    assert!(partial.parameters().is_complete());
    assert!(!partial.is_complete());
    let f = partial.family().unwrap();
    assert!(f.domain_complete());
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.columns()[0].rows().len(), 1);
    assert!(f.columns()[1..].iter().all(|c| c.rows().is_empty()));
    assert!(f.integer_function(0, None, &quiet()).is_err());
    assert!(f.required_quotient(&quiet()).is_err());
    assert!(partial.recheck(&i, &a, &quiet()).is_err());
}
#[test]
fn an_interrupt_before_automatic_column_selection_keeps_the_completed_source_plan() {
    use crate::result::Signal;
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let c = Control::new(|p| (p == Checkpoint::FiniteLawAutomatic).then_some(Signal::Int));
    let error = finite_automatic_law_family(&i, &a, &c).err().unwrap();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    assert!(partial.parameters().is_complete());
    assert_eq!(partial.parameters().domain.len(), 4);
    assert_eq!(partial.parameters().readings(), &a);
    assert!(partial.family().is_none());
    assert!(!partial.is_complete());
    assert!(partial.recheck(&i, &a, &quiet()).is_err());
}
#[test]
fn missing_primitive_observations_are_not_filled_by_the_completed_function_table() {
    let map=fixture::MAP.replace(r#",{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), None);
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    let index = (0..f.columns().len())
        .find(|&index| {
            f.column_object_identity(index).unwrap().subject().subject == "root"
                && f.instance_source(index).unwrap().0.bindings()[0]
                    .subject()
                    .subject
                    == "p"
        })
        .unwrap();
    assert_eq!(
        f.integer_function(index, None, &quiet()).unwrap().values(),
        &[0.into(), 0.into(), 1.into(), 1.into()]
    );
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn an_unsupported_component_preserves_the_known_whole_refutation_and_original_type() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required parts(c:Part):(0,fn(n:Z)=>n*n)=(1,fn(n:Z)=>n*n+0);",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.parameters().is_complete());
    assert!(!result.is_complete());
    assert!(f.domain_complete());
    assert!(
        matches!(f.state(),FiniteLawState::Unavailable{location:Location::Law{..},feature} if feature=="元等式の成分外延比較に必要な算法")
    );
    let index = (0..f.columns().len())
        .find(|&index| f.column_object_identity(index).unwrap().subject().subject == "root")
        .unwrap();
    let row = &f.columns()[index].rows()[0];
    assert_eq!(row.predicate, Some(false));
    assert_eq!(row.indicator, Some(1.into()));
    let components = row.components.as_ref().unwrap();
    assert_eq!(components[0].equal, Some(false));
    assert_eq!(components[0].indicator, Some(1.into()));
    assert!(components[1].left.is_some() && components[1].right.is_some());
    assert_eq!(components[1].equal, None);
    assert_eq!(components[1].indicator, None);
    assert_eq!(f.required_zero(), None);
    assert!(f.required_quotient(&quiet()).is_err());
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn total_owned_map_parameters_keep_all_seven_carrier_values_and_pointwise_type_conditions() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required maps(r:Root,x:Map<Part[r],Part[r]>):true;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.columns().len(), 21);
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.required_zero(), Some([0, 1, 2, 3].as_slice()));
    let mut active = vec![0usize; 4];
    for (index, column) in f.columns().iter().enumerate() {
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        let Scalar::Map { pairs, .. } = &column.bindings()[1].1 else {
            panic!("Map")
        };
        for (point, row) in column.rows().iter().enumerate() {
            let members = f
                .positions()
                .iter()
                .zip(&f.domain()[point])
                .filter_map(|(p, v)| {
                    matches!(v,Scalar::Subject{subject,..} if subject=="root")
                        .then_some(p.subject.as_str())
                })
                .collect::<BTreeSet<_>>();
            let keys = pairs
                .iter()
                .map(|(k, _)| match k {
                    Scalar::Subject { subject, .. } => subject.as_str(),
                    _ => panic!("key"),
                })
                .collect::<BTreeSet<_>>();
            let images=pairs.iter().all(|(_,v)|matches!(v,Scalar::Subject{subject,..} if members.contains(subject.as_str())));
            let applies = target == "root" && keys == members && images;
            assert_eq!(row.application, Some(applies));
            assert_eq!(row.indicator, Some(0.into()));
            if applies {
                active[point] += 1;
            }
        }
    }
    assert_eq!(active, [1, 1, 1, 4]);
    result.recheck(&i, &a, &quiet()).unwrap();
}
#[test]
fn real_tuple_components_keep_their_original_types_values_and_twelve_generators() {
    let i = fixture::with_body(fixture::MAP, "law required pair(c:Part):c.pair=(0,false);");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(result.is_complete());
    assert_eq!(f.domain().len(), 16);
    assert_eq!(f.columns().len(), 6);
    assert_eq!(f.required_generators(&quiet()).unwrap().len(), 12);
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    assert_eq!(f.observed_point(), None);
    for (index, column) in f.columns().iter().enumerate() {
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        let subject = &f.instance_source(index).unwrap().0.bindings()[0]
            .subject()
            .subject;
        let applies = target == "root" || target == subject;
        for (point, row) in column.rows().iter().enumerate() {
            let coordinate = if subject == "p" { point / 4 } else { point % 4 };
            let components = row.components.as_ref().unwrap();
            assert_eq!(components.len(), 2);
            assert_eq!(components[0].ty, Type::Fp("2".into()));
            assert_eq!(components[1].ty, Type::Bool);
            assert_eq!(
                row.indicator,
                Some(u8::from(applies && coordinate != 0).into())
            );
            assert_eq!(
                components[0].indicator,
                Some(u8::from(applies && coordinate / 2 != 0).into())
            );
            assert_eq!(
                components[1].indicator,
                Some(u8::from(applies && coordinate % 2 != 0).into())
            );
            if applies {
                assert!(
                    components
                        .iter()
                        .all(|c| c.left.is_some() && c.right.is_some() && c.equal.is_some())
                );
            } else {
                assert!(
                    components
                        .iter()
                        .all(|c| c.left.is_none() && c.right.is_none() && c.equal.is_none())
                );
            }
        }
    }
    result.recheck(&i, &a, &quiet()).unwrap();
}

#[test]
fn extracted_automatic_family_and_quotient_keep_required_consumer_readings_after_all_inner_state_is_replaced()
 {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):true;");
    let a = reading(&i, "root");
    let valid: AutomaticLawValuations = run(&i, &a).into_family().unwrap();
    assert_eq!(valid.columns().len(), 6);
    assert_eq!(valid.required_zero(), Some([0].as_slice()));
    valid.recheck(&i, &a, &quiet()).unwrap();
    let quotient: AutomaticLawQuotient<'_> = valid.required_quotient(&quiet()).unwrap();
    quotient.recheck(&i, &a, &quiet()).unwrap();
    let other = reading(&i, "r2");
    assert!(valid.recheck(&i, &other, &quiet()).is_err());
    assert!(quotient.recheck(&i, &other, &quiet()).is_err());
    let independent = run(&i, &a).into_family().unwrap();
    let mut wrong_quotient = valid.required_quotient(&quiet()).unwrap();
    wrong_quotient.value = independent.value.required_quotient(&quiet()).unwrap();
    assert!(wrong_quotient.recheck(&i, &a, &quiet()).is_err());
    for mutation in 0..3 {
        let mut bad = run(&i, &a).into_family().unwrap();
        if mutation == 1 {
            // 明示入口で正当に作った空族を、全ての内部metadataごと差し替える。
            let (objects, selected) =
                super::super::super::super::multi_selection(&i, &a, &[], &quiet()).unwrap();
            let explicit = super::super::super::super::family_with_instances(
                &i,
                &selected,
                None,
                Some(objects),
                Some(vec![]),
                &quiet(),
            )
            .unwrap();
            assert!(explicit.columns().is_empty());
            explicit.recheck(&i, &quiet()).unwrap();
            bad.value = explicit;
        } else {
            bad.value.columns.clear();
            bad.value.selection.clear();
            bad.value.column_objects.as_mut().unwrap().columns.clear();
            if mutation == 2 {
                bad.readings = other.clone();
            }
        }
        assert!(
            bad.recheck(&i, &a, &quiet()).is_err(),
            "family mutation {mutation}"
        );
        assert!(
            bad.required_quotient(&quiet())
                .unwrap()
                .recheck(&i, &a, &quiet())
                .is_err(),
            "quotient mutation {mutation}"
        );
    }
}

#[test]
fn empty_parameter_products_keep_the_parameter_only_shared_domain_in_quotient_rechecks() {
    let i = fixture::with_body(
        &missing_map(),
        "law required empty(r:Root,c:Part,x:Option<Part[r]>,void:Map<Root,Vacant>):false;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    assert!(result.is_complete());
    let f = result.family().unwrap();
    assert!(f.columns().is_empty());
    assert_eq!(f.positions().len(), 2);
    assert!(
        f.positions()
            .iter()
            .all(|p| p.field.as_deref() == Some("Pattern.Part.owner"))
    );
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), None);
    assert_eq!(f.required_zero(), Some([0, 1, 2, 3].as_slice()));
    f.recheck(&i, &a, &quiet()).unwrap();
    let q = f.required_quotient(&quiet()).unwrap();
    assert_eq!(q.points(), [0, 1, 2, 3]);
    assert_eq!(q.integer_ring(&quiet()).unwrap().dimension(), 4);
    q.recheck(&i, &a, &quiet()).unwrap();
}
