use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    control::{Limits, Usage},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn reading(i: &CheckedInputs) -> ObjectReadingInstances {
    let base = construct(i, "Selected", "v", "root", &mut quiet()).unwrap();
    object_reading_instances(i, &base, &mut quiet()).unwrap()
}
fn run(i: &CheckedInputs, r: &ObjectReadingInstances) -> FiniteAutomaticLawFamily {
    finite_automatic_law_family(i, r, &mut quiet()).unwrap()
}
fn object(a: &ObjectReadingInstances, name: &str) -> usize {
    a.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
#[test]
fn all_parameter_rows_keep_original_indices_and_the_same_shared_ring_on_every_object() {
    let i = fixture::with_body(
        fixture::MAP,
        "view helper(c:Part):Fp(2)=c.quantity;law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), Some(1));
    let mut count = 0;
    let mut nonzero = 0;
    for (o, selected) in a.objects().iter().enumerate() {
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        assert_eq!(p.object(), o);
        assert!(std::ptr::eq(p.family(), f));
        assert!(p.evaluated());
        assert_eq!(p.columns().len(), 8);
        assert_eq!(p.equations().len(), 8);
        for q in p.equations() {
            count += 1;
            let column = &f.columns()[q.column()];
            let source = &a.instances()[q.instance()];
            assert_eq!(source, f.instance_source(q.column()).unwrap().0);
            assert_eq!(source.declaration().name, "Selected.grid");
            assert_eq!(
                column
                    .bindings()
                    .iter()
                    .map(|b| b.0.as_str())
                    .collect::<Vec<_>>(),
                ["c", "n", "b"]
            );
            assert_eq!(q.component(), Some([].as_slice()));
            assert_eq!(q.ty(), &Type::Fp("2".into()));
            assert!(q.required());
            let subject = &source.bindings()[0].subject().subject;
            let target = &selected.identity().subject().subject;
            let applies = target == "root" || target == subject;
            let Scalar::Fp { value: n, .. } = &column.bindings()[1].1 else {
                panic!("n")
            };
            let n = n.to_string().parse::<usize>().unwrap();
            let expected = BigInt::from(applies && (subject == "q") != (n == 1));
            assert_eq!(q.epsilon(), Some(&expected));
            nonzero += usize::from(!expected.is_zero());
            assert_eq!(q.constant().unwrap().values(), vec![expected; 4]);
            for (point, value) in q.nu().values().iter().enumerate() {
                let original = if subject == "p" { point / 2 } else { point % 2 };
                assert_eq!(value, &BigInt::from(applies && original != n));
            }
            f.integer_ring(&mut quiet())
                .unwrap()
                .member(q.nu(), &mut quiet())
                .unwrap();
            f.integer_ring(&mut quiet())
                .unwrap()
                .member(q.constant().unwrap(), &mut quiet())
                .unwrap();
        }
        assert!(p.required_zero().is_empty());
        p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
    }
    assert_eq!(count, 24);
    assert_eq!(nonzero, 8);
}
#[test]
fn each_object_ideal_uses_its_own_required_columns_and_never_optional_or_global_constraints() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law optional suggest(c:Part):c.quantity=1;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    for (name, zeros, nonzeros) in [
        ("root", vec![0], 2),
        ("p", vec![0, 1], 1),
        ("q", vec![0, 2], 1),
    ] {
        let o = object(&a, name);
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        assert_eq!(p.columns().len(), 4);
        assert_eq!(p.equations().len(), 4);
        assert_eq!(p.required_zero(), zeros);
        assert_eq!(
            p.equations()
                .iter()
                .filter(|q| !q.epsilon().unwrap().is_zero())
                .count(),
            nonzeros
        );
        assert_eq!(p.equations().iter().filter(|q| q.required()).count(), 2);
        p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
    }
}
#[test]
fn the_original_quantifier_domain_is_retained_in_the_selected_objects_function() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required all(c:Part):forall x:Part . x.quantity=0;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.domain().len(), 4);
    for (name, expected) in [
        ("root", vec![0, 1, 1, 1]),
        ("p", vec![0, 0, 1, 1]),
        ("q", vec![0, 1, 0, 1]),
    ] {
        let o = object(&a, name);
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        assert_eq!(p.equations().len(), 2);
        for q in p.equations() {
            let subject = &a.instances()[q.instance()].bindings()[0].subject().subject;
            let applies = name == "root" || name == subject;
            let values: Vec<BigInt> = expected
                .iter()
                .map(|&v| BigInt::from(if applies { v } else { 0 }))
                .collect();
            assert_eq!(q.nu().values(), values);
            assert_eq!(q.epsilon(), Some(&values[1]));
            assert_eq!(q.component(), None);
            assert_eq!(q.ty(), &Type::Bool);
            let row = &f.columns()[q.column()].rows()[1];
            assert_eq!(row.application, Some(applies));
            assert_eq!(row.predicate, applies.then_some(name == "p"));
        }
        p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
    }
}
#[test]
fn tuple_leaves_retain_types_raw_values_and_separate_residuals_without_changing_rows() {
    let map=fixture::MAP.replacen(r#"{"id":"cp","#,r#"{"id":"qp","subject":"q","field":"Pattern.Part.pair","value":["1",false],"origin":"model"},{"id":"cp","#,1);
    let i = fixture::with_body(&map, "law required pair(c:Part):c.pair=(0,false);");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let before: Vec<_> = f.columns().iter().map(|c| c.rows().to_vec()).collect();
    assert_eq!(f.domain().len(), 16);
    assert_eq!(f.observed_point(), Some(6));
    for (o, selected) in a.objects().iter().enumerate() {
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        assert_eq!(p.columns().len(), 2);
        assert_eq!(p.equations().len(), 4);
        for q in p.equations() {
            let component = q.component().unwrap()[0];
            let expected_type = if component == 0 {
                Type::Fp("2".into())
            } else {
                Type::Bool
            };
            assert_eq!(q.ty(), &expected_type);
            let source = &a.instances()[q.instance()].bindings()[0].subject().subject;
            let target = &selected.identity().subject().subject;
            let applicable = target == "root" || target == source;
            let expected = BigInt::from(
                applicable
                    && ((source == "p" && component == 1) || (source == "q" && component == 0)),
            );
            assert_eq!(q.epsilon(), Some(&expected));
            assert_eq!(q.constant().unwrap().values(), vec![expected; 16]);
            let row = &f.columns()[q.column()].rows()[6];
            if applicable {
                let raw = &row.components.as_ref().unwrap()[component];
                assert_eq!(&raw.ty, q.ty());
                if component == 0 {
                    assert!(
                        matches!(&raw.left,Some(Scalar::Fp{value,..}) if value.to_string()==if source=="p" {"0"}else{"1"})
                    );
                } else {
                    assert_eq!(raw.left, Some(Scalar::Bool(source == "p")));
                }
            } else {
                assert!(row.operands.is_none());
            }
        }
        p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
    }
    assert!(f.columns().iter().zip(before).all(|(c, b)| c.rows() == b));
}
#[test]
fn contradictory_required_ideals_do_not_zero_out_observed_nonzero_equations() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required zero(c:Part):c.quantity=0;law required one(c:Part):c.quantity=1;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert!(p.required_zero().is_empty());
    assert_eq!(p.equations().len(), 4);
    assert_eq!(
        p.equations()
            .iter()
            .filter(|q| q.epsilon() == Some(&1.into()))
            .count(),
        2
    );
    assert!(
        f.required_quotient(&mut quiet())
            .unwrap()
            .points()
            .is_empty()
    );
    p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn false_and_varying_guards_keep_original_values_and_conditioned_integer_indicators() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required guarded(c:Part) when c.quantity=1:c.quantity=0;law optional never(c:Part) when false:c.quantity=1;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert_eq!(p.required_zero(), [0]);
    for q in p.equations() {
        let c = &f.columns()[q.column()];
        let row = &c.rows()[1];
        let subject = &a.instances()[q.instance()].bindings()[0].subject().subject;
        let never = c.declaration().name == "Selected.never";
        assert_eq!(q.epsilon(), Some(&BigInt::from(!never && subject == "q")));
        if never || subject == "p" {
            assert_eq!(row.guard, Some(false));
            assert!(row.operands.is_none());
        } else {
            assert!(
                matches!(&row.operands,Some((Type::Fp(_),Some(Scalar::Fp{value,..}),_)) if value==&1.into())
            );
        }
    }
    p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn missing_observations_leave_only_dependent_equations_undetermined() {
    let map=fixture::MAP.replace(r#",{"id":"xq","subject":"q","field":"Pattern.Part.quantity","value":"1","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), None);
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert!(!p.evaluated());
    assert_eq!(p.required_zero(), [0]);
    for q in p.equations() {
        assert_eq!(q.nu().values().len(), 4);
        let source = &a.instances()[q.instance()].bindings()[0].subject().subject;
        if source == "p" {
            assert_eq!(q.epsilon(), Some(&0.into()));
            assert_eq!(
                q.constant().unwrap().values(),
                &[0.into(), 0.into(), 0.into(), 0.into()]
            );
        } else {
            assert!(q.epsilon().is_none());
            assert!(q.constant().is_none());
        }
    }
    p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
    assert_eq!(
        f.positions()
            .iter()
            .find(|p| p.subject == "q")
            .unwrap()
            .atom,
        None
    );
}
#[test]
fn empty_law_and_empty_parameter_families_have_a_zero_ideal_and_preserve_the_shared_domain() {
    for body in [
        "view helper(c:Part):Fp(2)=c.quantity;",
        "law required empty(r:Root,c:Part,x:Option<Part[r]>,void:Map<Root,Vacant>):false;",
    ] {
        let i = fixture::with_body(fixture::MAP, body);
        let a = reading(&i);
        let result = run(&i, &a);
        let f = result.family().unwrap();
        for o in 0..a.objects().len() {
            let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
            assert!(p.columns().is_empty());
            assert!(p.equations().is_empty());
            assert_eq!(p.required_zero(), (0..f.domain().len()).collect::<Vec<_>>());
            p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
        }
    }
}
#[test]
fn rechecking_rejects_all_index_value_ideal_origin_and_owner_substitutions() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let other = run(&i, &a);
    let foreign = other.family().unwrap();
    for mode in 0..16 {
        let mut p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        match mode {
            0 => p.object = object(&a, "p"),
            1 => p.columns.clear(),
            2 => p.columns.reverse(),
            3 => {
                p.equations.pop();
            }
            4 => p.equations[0].column += 1,
            5 => p.equations[0].instance += 1,
            6 => p.equations[0].component = None,
            7 => p.equations[0].ty = Type::Bool,
            8 => p.equations[0].required = false,
            9 => p.equations[0].nu.values[0] = 1.into(),
            10 => p.equations[0].epsilon = Some(1.into()),
            11 => p.equations[0].constant.as_mut().unwrap().values[0] = 1.into(),
            12 => p.required_zero.clear(),
            13 => p.family = foreign,
            14 => {
                p.equations[0].nu = foreign
                    .integer_function(0, Some(&[]), &mut quiet())
                    .unwrap()
            }
            _ => {
                p = foreign
                    .object_presentation(&i, o, &mut quiet())
                    .unwrap()
                    .unwrap();
            }
        }
        assert!(
            p.recheck(f, o, &i, &a, &mut quiet()).is_err(),
            "mode {mode}"
        );
    }
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert!(p.recheck(f, object(&a, "q"), &i, &a, &mut quiet()).is_err());
    let base = construct(&i, "Selected", "v", "r2", &mut quiet()).unwrap();
    let wrong = object_reading_instances(&i, &base, &mut quiet()).unwrap();
    assert!(p.recheck(f, o, &i, &wrong, &mut quiet()).is_err());
    let changed = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=1;");
    assert!(p.recheck(f, o, &changed, &a, &mut quiet()).is_err());
    assert!(
        f.object_presentation(&i, a.objects().len(), &mut quiet())
            .is_err()
    );
    p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
}
fn stopping(mode: usize, at: usize) -> Control {
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    Control::new(
        Limits {
            time_ms: (mode == 2).then_some(1),
            memory_mib: (mode == 3).then_some(1),
        },
        move |p| {
            if p == Checkpoint::FiniteLawFunction {
                count.set(count.get() + 1);
            }
            let stop = count.get() >= at;
            Usage {
                signal: if stop && mode < 2 {
                    Some(if mode == 0 { Signal::Int } else { Signal::Term })
                } else {
                    None
                },
                elapsed_ms: u128::from(stop && mode == 2),
                memory_mib: u128::from(stop && mode == 3),
            }
        },
    )
}
#[test]
fn interruption_and_budgets_never_publish_an_unfinished_presentation() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    for mode in 0..4 {
        for at in [1, 10, 35, 65] {
            assert!(matches!(
                f.object_presentation(&i, o, &mut stopping(mode, at)),
                Err(ValidationFailure::Stop(_))
            ));
        }
        assert!(matches!(
            p.recheck(f, o, &i, &a, &mut stopping(mode, 1)),
            Err(ValidationFailure::Stop(_))
        ));
    }
    p.recheck(f, o, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn incomplete_or_unsupported_sources_retain_their_data_without_a_numeric_presentation() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let stage = Rc::new(Cell::new(false));
    let started = stage.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::FiniteLawAutomatic {
            started.set(true);
        }
        if started.get() && p == Checkpoint::FiniteLawEvaluation {
            count.set(count.get() + 1);
        }
        Usage {
            signal: (count.get() >= 3).then_some(Signal::Term),
            ..Usage::default()
        }
    });
    let error = finite_automatic_law_family(&i, &a, &mut c).err().unwrap();
    assert!(matches!(error.cause, ValidationFailure::Stop(_)));
    let partial = error.partial.unwrap();
    let f = partial.family().unwrap();
    assert!(f.domain_complete());
    assert!(!f.is_complete());
    assert_eq!(f.columns()[0].rows().len(), 1);
    assert!(
        f.object_presentation(&i, 0, &mut quiet())
            .unwrap()
            .is_none()
    );
    let i = fixture::with_body(
        fixture::MAP,
        "law required parts(c:Part):(0,fn(n:Z)=>n*n)=(1,fn(n:Z)=>n*n+0);",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(matches!(f.state(), FiniteLawState::Unavailable { .. }));
    assert_eq!(f.columns()[0].rows()[0].predicate, Some(false));
    assert!(
        f.object_presentation(&i, 0, &mut quiet())
            .unwrap()
            .is_none()
    );
}
