use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../../../../tests/common/primitive_valuation_data.rs");
}
use crate::control::quiet;
fn missing_q() -> String {
    fixture::MAP.replace(r#",{"id":"xq","subject":"q","field":"Pattern.Part.quantity","value":"1","origin":"model"}"#,"")
}
fn reading(i: &CheckedInputs) -> ObjectReadingInstances {
    let base = construct(i, "Selected", "v", "root", &quiet()).unwrap();
    object_reading_instances(i, &base, &quiet()).unwrap()
}
fn run(i: &CheckedInputs, a: &ObjectReadingInstances) -> FiniteAutomaticLawFamily {
    finite_automatic_law_family(i, a, &quiet()).unwrap()
}
fn object(a: &ObjectReadingInstances, name: &str) -> usize {
    a.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
fn column(f: &AutomaticLawValuations, subject: &str) -> usize {
    (0..f.columns().len())
        .find(|&c| {
            f.column_object_identity(c).unwrap().subject().subject == "root"
                && f.instance_source(c).unwrap().0.bindings()[0]
                    .subject()
                    .subject
                    == subject
        })
        .unwrap()
}
#[test]
fn partial_observations_determine_only_functions_constant_on_the_full_compatible_fiber() {
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.domain().len(), 4);
    assert_eq!(f.observed_point(), None);
    assert!(f.object_evaluation(&quiet()).unwrap().is_none());
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    assert_eq!(observation.points(), [0, 1]);
    assert_eq!(observation.known().len(), 1);
    let (coordinate, fact, value) = &observation.known()[0];
    assert_eq!(*coordinate, 0);
    assert_eq!(fact.subject, "p");
    assert_eq!(fact.field.as_deref(), Some("Pattern.Part.quantity"));
    assert_eq!(fact.atom.as_deref(), Some("xp"));
    assert!(matches!(value,Scalar::Fp{modulus,value} if modulus=="2"&&value==&0.into()));
    let p = f
        .integer_function(column(f, "p"), Some(&[]), &quiet())
        .unwrap();
    let q = f
        .integer_function(column(f, "q"), Some(&[]), &quiet())
        .unwrap();
    assert_eq!(p.values(), &[0.into(), 0.into(), 1.into(), 1.into()]);
    assert_eq!(q.values(), &[0.into(), 1.into(), 0.into(), 1.into()]);
    assert_eq!(
        observation.evaluate(&p, &quiet()).unwrap(),
        ObservedInteger::Determined(0.into())
    );
    assert_eq!(
        observation.evaluate(&q, &quiet()).unwrap(),
        ObservedInteger::Varying { left: 0, right: 1 }
    );
    assert_eq!(
        observation
            .constant_image(&p, &quiet())
            .unwrap()
            .unwrap()
            .values(),
        &[0.into(), 0.into(), 0.into(), 0.into()]
    );
    assert!(observation.constant_image(&q, &quiet()).unwrap().is_none());
    observation.recheck(f, &i, &a, &quiet()).unwrap();
    assert!(f.object_evaluation(&quiet()).unwrap().is_none());
}
#[test]
fn arbitrary_negative_and_large_integers_are_read_without_bool_or_finite_characteristic_conversion()
{
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    let ring = f.integer_ring(&quiet()).unwrap();
    let huge = BigInt::parse_bytes(b"1361129467683753853853498429727072845827", 10).unwrap();
    let same = ring
        .computed(vec![-&huge, -&huge, 5.into(), 7.into()], &quiet())
        .unwrap();
    let different = ring
        .computed(vec![-&huge, huge.clone(), 5.into(), 7.into()], &quiet())
        .unwrap();
    assert_eq!(
        observation.evaluate(&same, &quiet()).unwrap(),
        ObservedInteger::Determined(-&huge)
    );
    assert_eq!(
        observation
            .constant_image(&same, &quiet())
            .unwrap()
            .unwrap()
            .values(),
        vec![-&huge; 4]
    );
    assert_eq!(
        observation.evaluate(&different, &quiet()).unwrap(),
        ObservedInteger::Varying { left: 0, right: 1 }
    );
    for op in [
        ring.add(&same, &same, &quiet()).unwrap(),
        ring.mul(&same, &ring.one(&quiet()).unwrap(), &quiet())
            .unwrap(),
    ] {
        assert!(matches!(
            observation.evaluate(&op, &quiet()).unwrap(),
            ObservedInteger::Determined(_)
        ));
    }
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
#[test]
fn no_known_coordinates_keep_every_candidate_and_only_unanimous_values() {
    let map=missing_q().replace(r#",{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    assert!(observation.known().is_empty());
    assert_eq!(observation.points(), [0, 1, 2, 3]);
    let ring = f.integer_ring(&quiet()).unwrap();
    let value = ring.constant((-17).into(), &quiet()).unwrap();
    assert_eq!(
        observation.evaluate(&value, &quiet()).unwrap(),
        ObservedInteger::Determined((-17).into())
    );
    let varied = ring
        .computed(vec![0.into(), 0.into(), 0.into(), 1.into()], &quiet())
        .unwrap();
    assert_eq!(
        observation.evaluate(&varied, &quiet()).unwrap(),
        ObservedInteger::Varying { left: 0, right: 3 }
    );
    assert!(f.object_evaluation(&quiet()).unwrap().is_none());
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
#[test]
fn fully_known_fibers_agree_with_the_existing_ring_map_for_all_basis_values_and_integers() {
    let i = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    assert_eq!(observation.points(), [1]);
    assert_eq!(observation.known().len(), 2);
    let evaluation = f.object_evaluation(&quiet()).unwrap().unwrap();
    let ring = f.integer_ring(&quiet()).unwrap();
    let mut functions = vec![
        ring.computed(vec![(-2).into(), 3.into(), 5.into(), 7.into()], &quiet())
            .unwrap(),
    ];
    for p in 0..4 {
        functions.push(ring.basis(p, &quiet()).unwrap());
    }
    for function in functions {
        let expected = evaluation.apply(&function, &quiet()).unwrap();
        assert_eq!(
            observation.evaluate(&function, &quiet()).unwrap(),
            ObservedInteger::Determined(expected.clone())
        );
        assert_eq!(
            observation
                .constant_image(&function, &quiet())
                .unwrap()
                .unwrap()
                .values(),
            vec![expected; 4]
        );
    }
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
#[test]
fn known_tuple_fields_constrain_whole_original_values_and_preserve_missing_field_identity() {
    let i = fixture::with_body(fixture::MAP, "law required pair(c:Part):c.pair=(0,false);");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    assert_eq!(f.domain().len(), 16);
    assert_eq!(observation.points(), [4, 5, 6, 7]);
    assert_eq!(observation.known().len(), 1);
    assert_eq!(observation.known()[0].1.atom.as_deref(), Some("pp"));
    assert!(
        matches!(&observation.known()[0].2,Scalar::Tuple(items) if matches!(&items[0],Scalar::Fp{value,..} if value==&0.into()) && items[1]==Scalar::Bool(true))
    );
    let p = column(f, "p");
    let q = column(f, "q");
    for (component, expected) in [(0, 0), (1, 1)] {
        let function = f.integer_function(p, Some(&[component]), &quiet()).unwrap();
        assert_eq!(
            observation.evaluate(&function, &quiet()).unwrap(),
            ObservedInteger::Determined(expected.into())
        );
    }
    let function = f.integer_function(q, Some(&[0]), &quiet()).unwrap();
    assert_eq!(
        observation.evaluate(&function, &quiet()).unwrap(),
        ObservedInteger::Varying { left: 4, right: 6 }
    );
    assert_eq!(f.positions()[1].atom, None);
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
#[test]
fn object_presentations_keep_known_independent_components_and_leave_dependent_ones_unknown() {
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    for name in ["root", "p", "q"] {
        let o = object(&a, name);
        let presentation = f.object_presentation(&i, o, &quiet()).unwrap().unwrap();
        assert_eq!(presentation.observation().points(), [0, 1]);
        assert_eq!(presentation.evaluated(), name == "p");
        for equation in presentation.equations() {
            let subject = &a.instances()[equation.instance()].bindings()[0]
                .subject()
                .subject;
            let dependent = subject == "q" && (name == "root" || name == "q");
            if dependent {
                assert!(equation.epsilon().is_none());
                assert!(equation.constant().is_none());
            } else {
                assert_eq!(equation.epsilon(), Some(&0.into()));
                assert_eq!(
                    equation.constant().unwrap().values(),
                    &[0.into(), 0.into(), 0.into(), 0.into()]
                );
            }
        }
        presentation.recheck(f, o, &i, &a, &quiet()).unwrap();
    }
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    assert!(f.object_evaluation(&quiet()).unwrap().is_none());
    let environment = Environment::new(&i, &quiet()).unwrap();
    let field = environment
        .indexes
        .field(&environment.state, "v", "q", "Pattern.Part.quantity")
        .unwrap();
    assert!(matches!(field.slot, Slot::Missing));
}
#[test]
fn a_proved_constant_indicator_does_not_turn_the_unknown_operand_into_an_observation() {
    let i = fixture::with_body(
        &missing_q(),
        "law required self_equal(c:Part):c.quantity=c.quantity;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &quiet()).unwrap().unwrap();
    assert!(p.evaluated());
    assert_eq!(p.observation().points(), [0, 1]);
    assert_eq!(p.observation().known().len(), 1);
    assert!(p.equations().iter().all(|q| q.epsilon() == Some(&0.into())));
    assert!(f.object_evaluation(&quiet()).unwrap().is_none());
    assert!(
        f.positions()
            .iter()
            .any(|p| p.subject == "q" && p.atom.is_none())
    );
    let environment = Environment::new(&i, &quiet()).unwrap();
    let field = environment
        .indexes
        .field(&environment.state, "v", "q", "Pattern.Part.quantity")
        .unwrap();
    assert!(matches!(field.slot, Slot::Missing));
    p.recheck(f, o, &i, &a, &quiet()).unwrap();
}
#[test]
fn empty_fibers_never_prove_values_and_the_forged_source_is_rejected_by_full_rechecking() {
    // 有効な空域入力の例ではなく、内部Dを偽装した負系。
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let mut result = run(&i, &a);
    let f = result.family.as_mut().unwrap();
    f.value.domain.clear();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    assert!(observation.points().is_empty());
    let ring = f.integer_ring(&quiet()).unwrap();
    let empty = ring.computed(vec![], &quiet()).unwrap();
    assert_eq!(
        observation.evaluate(&empty, &quiet()).unwrap(),
        ObservedInteger::Empty
    );
    assert!(
        observation
            .constant_image(&empty, &quiet())
            .unwrap()
            .is_none()
    );
    assert!(observation.recheck(f, &i, &a, &quiet()).is_err());
}
#[test]
fn fiber_constraints_points_sources_and_foreign_functions_cannot_be_substituted() {
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let other = run(&i, &a);
    let foreign = other.family().unwrap();
    let function = f
        .integer_function(column(f, "p"), Some(&[]), &quiet())
        .unwrap();
    for mode in 0..9 {
        let mut observation = f.observation(&i, &quiet()).unwrap().unwrap();
        match mode {
            0 => observation.points.clear(),
            1 => observation.points.reverse(),
            2 => observation.points.push(1),
            3 => observation.points = vec![0],
            4 => observation.known.clear(),
            5 => observation.known[0].0 = 1,
            6 => observation.known[0].1.atom = None,
            7 => observation.known[0].2 = Scalar::Bool(false),
            _ => observation.family = foreign,
        };
        assert!(
            observation.recheck(f, &i, &a, &quiet()).is_err(),
            "mode {mode}"
        );
        assert!(
            observation.evaluate(&function, &quiet()).is_err(),
            "mode {mode}"
        );
    }
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    let bad = foreign
        .integer_function(column(foreign, "p"), Some(&[]), &quiet())
        .unwrap();
    assert!(observation.evaluate(&bad, &quiet()).is_err());
    assert!(observation.constant_image(&bad, &quiet()).is_err());
    let mut short = function.clone();
    short.values.pop();
    assert!(observation.evaluate(&short, &quiet()).is_err());
    let changed = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=0;");
    assert!(f.observation(&changed, &quiet()).is_err());
    assert!(observation.recheck(f, &changed, &a, &quiet()).is_err());
    let base = construct(&i, "Selected", "v", "r2", &quiet()).unwrap();
    let wrong = object_reading_instances(&i, &base, &quiet()).unwrap();
    assert!(observation.recheck(f, &i, &wrong, &quiet()).is_err());
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
fn stopping(signal: Signal, at: usize) -> Control {
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    Control::new(move |p| {
        if p == Checkpoint::FiniteLawFunction {
            count.set(count.get() + 1);
        }
        (count.get() >= at).then_some(signal)
    })
}
#[test]
fn cancellation_stops_preserve_unfinished_observation_value_and_presentation_boundaries() {
    let i = fixture::with_body(&missing_q(), "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let observation = f.observation(&i, &quiet()).unwrap().unwrap();
    let function = f
        .integer_function(column(f, "p"), Some(&[]), &quiet())
        .unwrap();
    for signal in [Signal::Int, Signal::Term] {
        for at in [1, 5, 11] {
            assert!(matches!(
                f.observation(&i, &stopping(signal, at)),
                Err(ValidationFailure::Stop(_))
            ));
        }
        assert!(matches!(
            observation.evaluate(&function, &stopping(signal, 8)),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(matches!(
            observation.constant_image(&function, &stopping(signal, 8)),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(matches!(
            observation.recheck(f, &i, &a, &stopping(signal, 1)),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(matches!(
            f.object_presentation(&i, 0, &stopping(signal, 8)),
            Err(ValidationFailure::Stop(_))
        ));
    }
    observation.recheck(f, &i, &a, &quiet()).unwrap();
}
