use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    control::{Limits, Usage},
    input::{InputSources, check_inputs},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../../../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn reading(i: &CheckedInputs, root: &str) -> ObjectReadingInstances {
    let base = construct(i, "Selected", "v", root, &mut quiet()).unwrap();
    object_reading_instances(i, &base, &mut quiet()).unwrap()
}
fn run(i: &CheckedInputs, r: &ObjectReadingInstances) -> FiniteAutomaticLawFamily {
    finite_automatic_law_family(i, r, &mut quiet()).unwrap()
}
fn inputs(body: &str) -> Arc<CheckedInputs> {
    fixture::with_body(fixture::MAP, body)
}
fn missing_quantity() -> String {
    fixture::MAP.replace(r#",{"id":"xq","subject":"q","field":"Pattern.Part.quantity","value":"1","origin":"model"}"#, "")
}
#[test]
fn the_observed_point_determines_every_basis_image_unit_and_product() {
    let i = inputs("law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    assert_eq!(
        f.positions()
            .iter()
            .map(|p| p.subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
    assert_eq!(f.domain().len(), 4);
    assert_eq!(ev.point(), 1); // independent observations p=0, q=1.
    assert_eq!(ev.basis_images(), &[0.into(), 1.into(), 0.into(), 0.into()]);
    let ring = f.integer_ring(&mut quiet()).unwrap();
    let mut sum = ring.zero(&mut quiet()).unwrap();
    for p in 0..4 {
        let basis = ring.basis(p, &mut quiet()).unwrap();
        assert_eq!(
            ev.apply(&basis, &mut quiet()).unwrap(),
            BigInt::from(p == 1)
        );
        sum = ring.add(&sum, &basis, &mut quiet()).unwrap();
        for q in 0..4 {
            let other = ring.basis(q, &mut quiet()).unwrap();
            let product = ring.mul(&basis, &other, &mut quiet()).unwrap();
            assert_eq!(
                ev.apply(&product, &mut quiet()).unwrap(),
                BigInt::from(p == 1 && q == 1)
            );
        }
    }
    assert!(
        ring.equal(&sum, &ring.one(&mut quiet()).unwrap(), &mut quiet())
            .unwrap()
    );
    assert_eq!(ev.apply(&sum, &mut quiet()).unwrap(), BigInt::one());
    ev.recheck(f, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn arbitrary_integer_functions_preserve_ring_operations_and_return_to_the_same_ring_as_constants() {
    let i = inputs("law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    let ring = f.integer_ring(&mut quiet()).unwrap();
    let x = ring
        .computed(
            vec![(-2).into(), 3.into(), 5.into(), 7.into()],
            &mut quiet(),
        )
        .unwrap();
    let y = ring
        .computed(
            vec![11.into(), (-13).into(), 17.into(), 19.into()],
            &mut quiet(),
        )
        .unwrap();
    assert_eq!(ev.apply(&x, &mut quiet()).unwrap(), BigInt::from(3));
    assert_eq!(ev.apply(&y, &mut quiet()).unwrap(), BigInt::from(-13));
    for (value, expected) in [
        (ring.add(&x, &y, &mut quiet()).unwrap(), -10),
        (ring.sub(&x, &y, &mut quiet()).unwrap(), 16),
        (ring.mul(&x, &y, &mut quiet()).unwrap(), -39),
    ] {
        assert_eq!(
            ev.apply(&value, &mut quiet()).unwrap(),
            BigInt::from(expected)
        );
    }
    assert_eq!(
        ev.apply(&ring.one(&mut quiet()).unwrap(), &mut quiet())
            .unwrap(),
        BigInt::one()
    );
    assert_eq!(
        ev.apply(&ring.zero(&mut quiet()).unwrap(), &mut quiet())
            .unwrap(),
        BigInt::zero()
    );
    let huge = BigInt::parse_bytes(b"1361129467683753853853498429727072845827", 10).unwrap();
    let constant = ring.constant(-&huge, &mut quiet()).unwrap();
    assert_eq!(ev.apply(&constant, &mut quiet()).unwrap(), -&huge);
    let image = ev.constant_image(&x, &mut quiet()).unwrap();
    assert_eq!(image.values(), &[3.into(), 3.into(), 3.into(), 3.into()]);
    ring.member(&image, &mut quiet()).unwrap();
    assert_eq!(ev.apply(&image, &mut quiet()).unwrap(), BigInt::from(3));
    assert_eq!(x.values(), &[(-2).into(), 3.into(), 5.into(), 7.into()]);
}
#[test]
fn every_original_parameter_and_object_is_evaluated_without_quotienting_its_nonzero_residual() {
    let i = inputs("law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let before = f
        .columns()
        .iter()
        .map(|c| c.rows().to_vec())
        .collect::<Vec<_>>();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    assert_eq!(f.columns().len(), 24);
    assert_eq!(f.required_zero(), Some([].as_slice()));
    assert!(
        f.required_quotient(&mut quiet())
            .unwrap()
            .points()
            .is_empty()
    );
    let mut positive = 0;
    for (index, column) in f.columns().iter().enumerate() {
        let subject = &f.instance_source(index).unwrap().0.bindings()[0]
            .subject()
            .subject;
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        let n = match &column.bindings()[1].1 {
            Scalar::Fp { value, .. } => value.to_string().parse::<u8>().unwrap(),
            _ => panic!("Fp parameter"),
        };
        let original = if subject == "p" { 0 } else { 1 };
        let applicable = target == "root" || target == subject;
        let expected = BigInt::from(applicable && original != n);
        let nu = f.integer_function(index, None, &mut quiet()).unwrap();
        assert_eq!(ev.apply(&nu, &mut quiet()).unwrap(), expected);
        assert!(
            ev.constant_image(&nu, &mut quiet())
                .unwrap()
                .values()
                .iter()
                .all(|v| v == &expected)
        );
        assert_eq!(
            column.rows()[ev.point()].indicator.as_ref(),
            Some(&expected)
        );
        positive += usize::from(!expected.is_zero());
        if !applicable {
            assert_eq!(column.rows()[ev.point()].operands, None);
        }
    }
    assert_eq!(positive, 8);
    assert!(
        f.columns()
            .iter()
            .map(|c| c.rows().to_vec())
            .collect::<Vec<_>>()
            == before
    );
    ev.recheck(f, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn a_required_ideal_does_not_change_the_actual_nonzero_evaluation() {
    let i =
        inputs("law required zero(c:Part):c.quantity=0;law optional hint(c:Part):c.quantity=1;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    assert_eq!(ev.point(), 1);
    let column = (0..f.columns().len())
        .find(|&p| {
            f.column_object_identity(p).unwrap().subject().subject == "root"
                && f.columns()[p].declaration().name == "Selected.zero"
                && f.instance_source(p).unwrap().0.bindings()[0]
                    .subject()
                    .subject
                    == "q"
        })
        .unwrap();
    let nu = f.integer_function(column, None, &mut quiet()).unwrap();
    assert_eq!(
        f.required_quotient(&mut quiet())
            .unwrap()
            .project(&nu, &mut quiet())
            .unwrap()
            .values(),
        &[0.into()]
    );
    assert_eq!(ev.apply(&nu, &mut quiet()).unwrap(), BigInt::one());
    assert_eq!(
        ev.constant_image(&nu, &mut quiet()).unwrap().values(),
        &[1.into(), 1.into(), 1.into(), 1.into()]
    );
    assert_eq!(f.columns()[column].rows()[1].predicate, Some(false));
}
#[test]
fn typed_tuple_components_keep_their_actual_values_and_separate_indicators() {
    let map = fixture::MAP.replacen(r#"{"id":"cp","#,r#"{"id":"qp","subject":"q","field":"Pattern.Part.pair","value":["1",false],"origin":"model"},{"id":"cp","#,1);
    let i = fixture::with_body(&map, "law required pair(c:Part):c.pair=(0,false);");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    assert_eq!(f.domain().len(), 16);
    assert_eq!(ev.point(), 6);
    for index in 0..f.columns().len() {
        let subject = &f.instance_source(index).unwrap().0.bindings()[0]
            .subject()
            .subject;
        let target = &f.column_object_identity(index).unwrap().subject().subject;
        let applicable = target == "root" || target == subject;
        let whole = f.integer_function(index, None, &mut quiet()).unwrap();
        assert_eq!(
            ev.apply(&whole, &mut quiet()).unwrap(),
            BigInt::from(applicable)
        );
        for component in 0..2 {
            let nu = f
                .integer_function(index, Some(&[component]), &mut quiet())
                .unwrap();
            let expected = applicable
                && ((subject == "p" && component == 1) || (subject == "q" && component == 0));
            assert_eq!(ev.apply(&nu, &mut quiet()).unwrap(), BigInt::from(expected));
        }
        if applicable {
            let row = &f.columns()[index].rows()[6];
            let components = row.components.as_ref().unwrap();
            assert_eq!(components[0].ty, Type::Fp("2".into()));
            assert_eq!(components[1].ty, Type::Bool);
            assert!(
                matches!(&components[0].left,Some(Scalar::Fp{value,..}) if value.to_string()==if subject=="p" {"0"} else {"1"})
            );
            assert!(
                matches!(&components[1].left,Some(Scalar::Bool(value)) if *value==(subject=="p"))
            );
        }
    }
    ev.recheck(f, &i, &a, &mut quiet()).unwrap();
}
#[test]
fn missing_observations_do_not_choose_a_completion_or_construct_an_evaluation() {
    let i = fixture::with_body(
        &missing_quantity(),
        "law required zero(c:Part):c.quantity=0;",
    );
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(f.is_complete());
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), None);
    assert!(f.object_evaluation(&mut quiet()).unwrap().is_none());
    assert_eq!(f.positions().len(), 2);
    assert!(f.columns().iter().all(|c| c.rows().len() == 4));
    result.recheck(&i, &a, &mut quiet()).unwrap();
}
#[test]
fn empty_laws_and_false_guards_keep_the_single_observed_empty_assignment() {
    for body in [
        "view helper(c:Part):Fp(2)=c.quantity;",
        "law required off(c:Part) when false:c.integer=0;",
    ] {
        let i = inputs(body);
        let a = reading(&i, "root");
        let result = run(&i, &a);
        let f = result.family().unwrap();
        let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
        assert_eq!(ev.point(), 0);
        assert_eq!(ev.basis_images(), &[1.into()]);
        assert!(f.positions().is_empty());
        let one = f
            .integer_ring(&mut quiet())
            .unwrap()
            .one(&mut quiet())
            .unwrap();
        assert_eq!(ev.apply(&one, &mut quiet()).unwrap(), BigInt::one());
        for index in 0..f.columns().len() {
            let nu = f.integer_function(index, None, &mut quiet()).unwrap();
            assert_eq!(ev.apply(&nu, &mut quiet()).unwrap(), BigInt::zero());
            assert_eq!(f.columns()[index].rows()[0].operands, None);
        }
        ev.recheck(f, &i, &a, &mut quiet()).unwrap();
    }
}
fn empty_primitive_sources() -> InputSources {
    let base = inputs("law required zero(c:Part):c.quantity=0;");
    let original = std::str::from_utf8(base.sources().definitions()[0].bytes()).unwrap();
    let definition=original.replacen(r#"{"name":"quantity","#,r#"{"name":"vacant","type":["Ref","Pattern.Vacant"],"meaning":"空の参照域。"},{"name":"quantity","#,1);
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &defs.vocabularies["Pattern"].digest;
    let map = std::str::from_utf8(base.sources().archmap().bytes())
        .unwrap()
        .replace(&base.definitions().vocabularies["Pattern"].digest, digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";law required empty(c:Part):c.vacant=c.vacant;}}"
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
#[test]
fn inconsistent_empty_carriers_and_forged_empty_domains_never_become_integer_evaluations() {
    let failure = check_inputs(empty_primitive_sources(), &mut quiet())
        .err()
        .unwrap();
    assert!(
        failure
            .issues()
            .iter()
            .any(|issue| issue.canonical().contains("inconsistent_observation"))
    );
    // 補完のない入力は入力検査で拒否される。下は空Dを偽装した内部値の負系。
    let i = inputs("view helper(c:Part):Fp(2)=c.quantity;");
    let a = reading(&i, "root");
    let mut result = run(&i, &a);
    let f = result.family.as_mut().unwrap();
    f.value.domain.clear();
    f.value.observed_point = None;
    f.value.required_zero = Some(vec![]);
    assert!(f.is_complete());
    assert!(f.domain_complete());
    assert!(f.domain().is_empty());
    assert!(f.object_evaluation(&mut quiet()).unwrap().is_none());
    let invalid = FiniteLawObjectEvaluation {
        family: f,
        point: 0,
        basis_images: vec![],
    };
    assert!(invalid.recheck(f, &i, &a, &mut quiet()).is_err());
    let zero = f
        .integer_ring(&mut quiet())
        .unwrap()
        .zero(&mut quiet())
        .unwrap();
    assert!(invalid.apply(&zero, &mut quiet()).is_err());
    f.value.observed_point = Some(0);
    assert!(f.object_evaluation(&mut quiet()).is_err());
}
#[test]
fn forged_basis_points_families_and_foreign_functions_are_rejected_at_the_consumer() {
    let i = inputs("law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let other = run(&i, &a);
    let other = other.family().unwrap();
    let foreign = other
        .integer_ring(&mut quiet())
        .unwrap()
        .one(&mut quiet())
        .unwrap();
    for mutation in 0..6 {
        let mut bad = f.object_evaluation(&mut quiet()).unwrap().unwrap();
        match mutation {
            0 => bad.point = 0,
            1 => bad.basis_images[1] = 2.into(),
            2 => {
                bad.basis_images.swap(0, 1);
                bad.point = 0;
            }
            3 => bad.basis_images.clear(),
            4 => bad.family = other,
            _ => {
                bad.family = other;
                bad.point = 1;
                bad.basis_images = vec![0.into(), 1.into(), 0.into(), 0.into()];
            }
        }
        assert!(
            bad.recheck(f, &i, &a, &mut quiet()).is_err(),
            "mutation {mutation}"
        );
        if mutation < 4 {
            assert!(
                bad.apply(
                    &f.integer_ring(&mut quiet())
                        .unwrap()
                        .one(&mut quiet())
                        .unwrap(),
                    &mut quiet()
                )
                .is_err()
            );
        }
    }
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    assert!(ev.apply(&foreign, &mut quiet()).is_err());
    assert!(ev.constant_image(&foreign, &mut quiet()).is_err());
    let mut short = f
        .integer_ring(&mut quiet())
        .unwrap()
        .one(&mut quiet())
        .unwrap();
    short.values.pop();
    assert!(ev.apply(&short, &mut quiet()).is_err());
    assert!(ev.constant_image(&short, &mut quiet()).is_err());
    assert!(ev.recheck(other, &i, &a, &mut quiet()).is_err());
    assert!(ev.recheck(f, &i, &reading(&i, "r2"), &mut quiet()).is_err());
    let changed = fixture::with_body(
        &(fixture::MAP.to_string() + " "),
        "law required zero(c:Part):c.quantity=0;",
    );
    assert!(ev.recheck(f, &changed, &a, &mut quiet()).is_err());
}
fn stopping(mode: usize, at: usize) -> Control {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    Control::new(
        Limits {
            time_ms: (mode == 2).then_some(1),
            memory_mib: (mode == 3).then_some(1),
        },
        move |p| {
            if p == Checkpoint::FiniteLawFunction {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() >= at;
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
fn cancellation_and_budget_stops_do_not_return_partial_maps_values_or_constant_images() {
    let i = inputs("law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let ev = f.object_evaluation(&mut quiet()).unwrap().unwrap();
    let one = f
        .integer_ring(&mut quiet())
        .unwrap()
        .one(&mut quiet())
        .unwrap();
    for mode in 0..4 {
        let mut c = stopping(mode, 3);
        let failure = f.object_evaluation(&mut c).err().unwrap();
        assert!(matches!(failure, ValidationFailure::Stop(_)));
        let mut c = stopping(mode, 10);
        let failure = ev.apply(&one, &mut c).err().unwrap();
        assert!(matches!(failure, ValidationFailure::Stop(_)));
        let mut c = stopping(mode, 18);
        let failure = ev.constant_image(&one, &mut c).err().unwrap();
        assert!(matches!(failure, ValidationFailure::Stop(_)));
        let mut c = stopping(mode, 1);
        let failure = ev.recheck(f, &i, &a, &mut c).err().unwrap();
        assert!(matches!(failure, ValidationFailure::Stop(_)));
    }
    ev.recheck(f, &i, &a, &mut quiet()).unwrap();
    assert_eq!(ev.apply(&one, &mut quiet()).unwrap(), BigInt::one());
}
#[test]
fn unfinished_or_unsupported_law_families_are_preserved_without_a_completed_object_evaluation() {
    let i = inputs("law required zero(c:Part):c.quantity=0;");
    let a = reading(&i, "root");
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
    let failure = finite_automatic_law_family(&i, &a, &mut c).err().unwrap();
    assert!(matches!(failure.cause, ValidationFailure::Stop(_)));
    let partial = failure.partial.unwrap();
    let f = partial.family().unwrap();
    assert!(!f.is_complete());
    assert!(f.domain_complete());
    assert_eq!(f.columns()[0].rows().len(), 1);
    assert!(f.object_evaluation(&mut quiet()).unwrap().is_none());
    let i = inputs("law required parts(c:Part):(0,fn(n:Z)=>n*n)=(1,fn(n:Z)=>n*n+0);");
    let a = reading(&i, "root");
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert!(matches!(f.state(), FiniteLawState::Unavailable { .. }));
    assert!(f.object_evaluation(&mut quiet()).unwrap().is_none());
    assert_eq!(f.columns()[0].rows()[0].predicate, Some(false));
}
