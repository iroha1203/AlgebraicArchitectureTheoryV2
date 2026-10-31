use super::*;
use crate::{
    construction::{construct, readings::object_reading_instances},
    control::{Limits, Usage},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../../../../../../tests/common/primitive_valuation_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn reading(i: &CheckedInputs) -> ObjectReadingInstances {
    let base = construct(i, "Selected", "v", "root", &mut quiet()).unwrap();
    object_reading_instances(i, &base, &mut quiet()).unwrap()
}
fn run(i: &CheckedInputs, a: &ObjectReadingInstances) -> FiniteAutomaticLawFamily {
    finite_automatic_law_family(i, a, &mut quiet()).unwrap()
}
fn object(a: &ObjectReadingInstances, name: &str) -> usize {
    a.objects()
        .iter()
        .position(|o| o.identity().subject().subject == name)
        .unwrap()
}
const LAWS: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;law optional same(c:Part):c.quantity=c.quantity;";
#[test]
fn symbolic_witness_generators_are_not_observed_epsilon_and_required_excludes_other_roles() {
    let i = fixture::with_body(fixture::MAP, LAWS);
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert_eq!(p.equations().len(), 6);
    let required = p.required_ideal(&mut quiet()).unwrap();
    assert_eq!(required.kind(), FiniteObjectIdealKind::Obstruction);
    assert!(std::ptr::eq(required.base(), &p));
    assert_eq!(required.zero_points(), [0]);
    assert!(!required.is_zero(&mut quiet()).unwrap());
    let expected: Vec<_> = p
        .equations()
        .iter()
        .enumerate()
        .filter(|(_, q)| f.columns()[q.column()].declaration().name == "Selected.zero")
        .map(|(n, _)| n)
        .collect();
    assert_eq!(required.equations(), expected);
    assert_eq!(required.generators(&mut quiet()).unwrap().len(), 2);
    for (index, equation) in p.equations().iter().enumerate() {
        let ideal = p.witness_ideal(index, &mut quiet()).unwrap();
        assert_eq!(
            ideal.kind(),
            FiniteObjectIdealKind::Witness { equation: index }
        );
        assert_eq!(ideal.equations(), [index]);
        let generators = ideal.generators(&mut quiet()).unwrap();
        assert_eq!(generators.len(), 1);
        assert!(std::ptr::eq(generators[0], equation.nu()));
        let name = f.columns()[equation.column()].declaration().name.as_str();
        let source = &a.instances()[equation.instance()].bindings()[0]
            .subject()
            .subject;
        if name == "Selected.same" {
            assert!(ideal.is_zero(&mut quiet()).unwrap());
            assert_eq!(ideal.zero_points(), [0, 1, 2, 3]);
        } else {
            assert!(!ideal.is_zero(&mut quiet()).unwrap());
            let zeros = match (name, source.as_str()) {
                ("Selected.zero", "p") => vec![0, 1],
                ("Selected.zero", "q") => vec![0, 2],
                ("Selected.one", "p") => vec![2, 3],
                ("Selected.one", "q") => vec![1, 3],
                _ => panic!("original declaration"),
            };
            assert_eq!(ideal.zero_points(), zeros);
            if (name == "Selected.zero" && source == "p")
                || (name == "Selected.one" && source == "q")
            {
                assert_eq!(equation.epsilon(), Some(&0.into()));
                assert!(
                    equation
                        .constant()
                        .unwrap()
                        .values()
                        .iter()
                        .all(Zero::is_zero)
                );
                assert!(!generators[0].values().iter().all(Zero::is_zero));
            }
        }
        ideal
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Witness { equation: index },
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
    required
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
}
#[test]
fn each_objects_required_ideal_keeps_its_own_domain_of_application_and_zero_generators() {
    let i = fixture::with_body(fixture::MAP, LAWS);
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    assert_eq!(f.required_zero(), Some([0].as_slice()));
    for (name, zeros) in [("root", vec![0]), ("p", vec![0, 1]), ("q", vec![0, 2])] {
        let o = object(&a, name);
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        let required = p.required_ideal(&mut quiet()).unwrap();
        assert_eq!(required.zero_points(), zeros);
        assert_eq!(required.equations().len(), 2);
        assert_eq!(p.equations().len(), 6);
        for (index, q) in p.equations().iter().enumerate() {
            let ideal = p.witness_ideal(index, &mut quiet()).unwrap();
            let source = &a.instances()[q.instance()].bindings()[0].subject().subject;
            if name != "root" && name != source {
                assert!(ideal.is_zero(&mut quiet()).unwrap());
                assert_eq!(ideal.generators(&mut quiet()).unwrap().len(), 1);
                assert_eq!(ideal.zero_points(), [0, 1, 2, 3]);
            }
            ideal
                .recheck(
                    &p,
                    f,
                    o,
                    FiniteObjectIdealKind::Witness { equation: index },
                    &i,
                    &a,
                    &mut quiet(),
                )
                .unwrap();
        }
        required
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Obstruction,
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
}
#[test]
fn every_typed_tuple_leaf_has_its_own_original_witness_ideal_in_the_same_ring() {
    let map=fixture::MAP.replacen(r#"{"id":"cp","#,r#"{"id":"qp","subject":"q","field":"Pattern.Part.pair","value":["1",false],"origin":"model"},{"id":"cp","#,1);
    let i = fixture::with_body(&map, "law required pair(c:Part):c.pair=(0,false);");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert_eq!(f.domain().len(), 16);
    assert_eq!(p.equations().len(), 4);
    for (index, q) in p.equations().iter().enumerate() {
        let source = &a.instances()[q.instance()].bindings()[0].subject().subject;
        let component = q.component().unwrap()[0];
        let ideal = p.witness_ideal(index, &mut quiet()).unwrap();
        let zeros = match (source.as_str(), component) {
            ("p", 0) => (0..8).collect::<Vec<_>>(),
            ("p", 1) => vec![0, 1, 2, 3, 8, 9, 10, 11],
            ("q", 0) => vec![0, 1, 4, 5, 8, 9, 12, 13],
            ("q", 1) => vec![0, 2, 4, 6, 8, 10, 12, 14],
            _ => panic!("original component"),
        };
        assert_eq!(ideal.zero_points(), zeros);
        assert!(!ideal.is_zero(&mut quiet()).unwrap());
        assert_eq!(
            ideal.generators(&mut quiet()).unwrap()[0].values(),
            q.nu().values()
        );
        let expected = if component == 0 {
            Type::Fp("2".into())
        } else {
            Type::Bool
        };
        assert_eq!(q.ty(), &expected);
        ideal
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Witness { equation: index },
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
    let required = p.required_ideal(&mut quiet()).unwrap();
    assert_eq!(required.equations(), [0, 1, 2, 3]);
    assert_eq!(required.zero_points(), [0]);
    assert_eq!(required.generators(&mut quiet()).unwrap().len(), 4);
    required
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
}
#[test]
fn all_parameter_assignments_keep_distinct_witness_indices_even_when_functions_coincide() {
    let i = fixture::with_body(
        fixture::MAP,
        "law required grid(c:Part,n:Fp(2),b:Bool):c.quantity=n;",
    );
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert_eq!(p.equations().len(), 8);
    let required = p.required_ideal(&mut quiet()).unwrap();
    assert!(required.zero_points().is_empty());
    assert_eq!(required.equations(), (0..8).collect::<Vec<_>>());
    let mut keys = std::collections::BTreeSet::new();
    for (index, q) in p.equations().iter().enumerate() {
        let column = &f.columns()[q.column()];
        assert_eq!(
            column
                .bindings()
                .iter()
                .map(|b| b.0.as_str())
                .collect::<Vec<_>>(),
            ["c", "n", "b"]
        );
        let subject = &a.instances()[q.instance()].bindings()[0].subject().subject;
        let Scalar::Fp { value: n, .. } = &column.bindings()[1].1 else {
            panic!("n")
        };
        let Scalar::Bool(b) = column.bindings()[2].1 else {
            panic!("b")
        };
        keys.insert((subject.clone(), n.to_string(), b));
        let ideal = p.witness_ideal(index, &mut quiet()).unwrap();
        assert_eq!(ideal.equations(), [index]);
        let zeros = match (subject.as_str(), n.to_string().as_str()) {
            ("p", "0") => vec![0, 1],
            ("p", "1") => vec![2, 3],
            ("q", "0") => vec![0, 2],
            ("q", "1") => vec![1, 3],
            _ => panic!("parameters"),
        };
        assert_eq!(ideal.zero_points(), zeros);
        ideal
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Witness { equation: index },
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
    assert_eq!(keys.len(), 8);
    required
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
}
#[test]
fn empty_families_and_false_guards_keep_zero_ideals_without_losing_existing_indices() {
    for body in [
        "view helper(c:Part):Fp(2)=c.quantity;",
        "law required empty(r:Root,c:Part,x:Option<Part[r]>,void:Map<Root,Vacant>):false;",
        "law required never(c:Part) when false:c.quantity=1;",
    ] {
        let i = fixture::with_body(fixture::MAP, body);
        let a = reading(&i);
        let result = run(&i, &a);
        let f = result.family().unwrap();
        let o = object(&a, "root");
        let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
        let ideal = p.required_ideal(&mut quiet()).unwrap();
        assert!(ideal.is_zero(&mut quiet()).unwrap());
        assert_eq!(
            ideal.zero_points(),
            (0..f.domain().len()).collect::<Vec<_>>()
        );
        if body.contains("never") {
            assert_eq!(p.equations().len(), 2);
            assert_eq!(ideal.equations(), [0, 1]);
            for index in 0..2 {
                let w = p.witness_ideal(index, &mut quiet()).unwrap();
                assert_eq!(w.generators(&mut quiet()).unwrap().len(), 1);
                assert!(w.is_zero(&mut quiet()).unwrap());
                assert_eq!(w.zero_points(), [0]);
            }
        } else {
            assert!(ideal.equations().is_empty());
            assert!(ideal.generators(&mut quiet()).unwrap().is_empty());
            assert!(p.witness_ideal(0, &mut quiet()).is_err());
        }
        ideal
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Obstruction,
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
}
#[test]
fn unknown_observations_do_not_prune_symbolic_ideal_coordinates_or_fill_dependent_epsilon() {
    let map=fixture::MAP.replace(r#",{"id":"xq","subject":"q","field":"Pattern.Part.quantity","value":"1","origin":"model"}"#,"");
    let i = fixture::with_body(&map, "law required zero(c:Part):c.quantity=0;");
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    assert_eq!(p.observation().points(), [0, 1]);
    for (index, q) in p.equations().iter().enumerate() {
        let ideal = p.witness_ideal(index, &mut quiet()).unwrap();
        let source = &a.instances()[q.instance()].bindings()[0].subject().subject;
        if source == "q" {
            assert_eq!(ideal.zero_points(), [0, 2]);
            assert!(q.epsilon().is_none());
            assert!(q.constant().is_none());
        } else {
            assert_eq!(ideal.zero_points(), [0, 1]);
            assert_eq!(q.epsilon(), Some(&0.into()));
        }
        assert!(!ideal.is_zero(&mut quiet()).unwrap());
        ideal
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Witness { equation: index },
                &i,
                &a,
                &mut quiet(),
            )
            .unwrap();
    }
    let required = p.required_ideal(&mut quiet()).unwrap();
    assert_eq!(required.zero_points(), [0]);
    required
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
    assert_eq!(f.observed_point(), None);
}
#[test]
fn changing_kind_indices_zero_points_or_entire_origin_never_satisfies_the_consumers_recheck() {
    let i = fixture::with_body(fixture::MAP, LAWS);
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    let other = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    for mode in 0..9 {
        let mut ideal = p.required_ideal(&mut quiet()).unwrap();
        match mode {
            0 => ideal.equations.clear(),
            1 => ideal.equations.reverse(),
            2 => ideal.equations.push(ideal.equations[0]),
            3 => ideal.zero_points.clear(),
            4 => ideal.zero_points.push(4),
            5 => ideal.base = &other,
            6 => ideal.kind = FiniteObjectIdealKind::Witness { equation: 0 },
            7 => {
                ideal = p.witness_ideal(0, &mut quiet()).unwrap();
            }
            _ => {
                ideal = other.required_ideal(&mut quiet()).unwrap();
            }
        }
        assert!(
            ideal
                .recheck(
                    &p,
                    f,
                    o,
                    FiniteObjectIdealKind::Obstruction,
                    &i,
                    &a,
                    &mut quiet()
                )
                .is_err(),
            "mode {mode}"
        );
    }
    let w = p.witness_ideal(0, &mut quiet()).unwrap();
    assert!(
        w.recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Witness { equation: 1 },
            &i,
            &a,
            &mut quiet()
        )
        .is_err()
    );
    assert!(p.witness_ideal(p.equations().len(), &mut quiet()).is_err());
    let required = p.required_ideal(&mut quiet()).unwrap();
    let other_family = run(&i, &a);
    assert!(
        required
            .recheck(
                &p,
                other_family.family().unwrap(),
                o,
                FiniteObjectIdealKind::Obstruction,
                &i,
                &a,
                &mut quiet()
            )
            .is_err()
    );
    assert!(
        required
            .recheck(
                &p,
                f,
                object(&a, "p"),
                FiniteObjectIdealKind::Obstruction,
                &i,
                &a,
                &mut quiet()
            )
            .is_err()
    );
    let changed = fixture::with_body(fixture::MAP, "law required zero(c:Part):c.quantity=1;");
    assert!(
        required
            .recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Obstruction,
                &changed,
                &a,
                &mut quiet()
            )
            .is_err()
    );
    let mut forged = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    forged.equations[0].nu.values[0] = 2.into();
    assert!(forged.witness_ideal(0, &mut quiet()).is_err());
    let other_family = run(&i, &a);
    let mut forged = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    forged.equations[0].nu = other_family
        .family()
        .unwrap()
        .integer_function(
            forged.equations[0].column(),
            forged.equations[0].component(),
            &mut quiet(),
        )
        .unwrap();
    assert!(forged.witness_ideal(0, &mut quiet()).is_err());
    required
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
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
            if p == Checkpoint::FiniteLawQuotient {
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
fn interruptions_and_budgets_never_return_unfinished_ideals_or_generator_lists() {
    let i = fixture::with_body(fixture::MAP, LAWS);
    let a = reading(&i);
    let result = run(&i, &a);
    let f = result.family().unwrap();
    let o = object(&a, "root");
    let p = f.object_presentation(&i, o, &mut quiet()).unwrap().unwrap();
    let ideal = p.required_ideal(&mut quiet()).unwrap();
    for mode in 0..4 {
        for at in [1, 4, 10] {
            assert!(matches!(
                p.witness_ideal(0, &mut stopping(mode, at)),
                Err(ValidationFailure::Stop(_))
            ));
            assert!(matches!(
                p.required_ideal(&mut stopping(mode, at)),
                Err(ValidationFailure::Stop(_))
            ));
        }
        assert!(matches!(
            ideal.generators(&mut stopping(mode, 4)),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(matches!(
            ideal.is_zero(&mut stopping(mode, 4)),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(matches!(
            ideal.recheck(
                &p,
                f,
                o,
                FiniteObjectIdealKind::Obstruction,
                &i,
                &a,
                &mut stopping(mode, 1)
            ),
            Err(ValidationFailure::Stop(_))
        ));
    }
    ideal
        .recheck(
            &p,
            f,
            o,
            FiniteObjectIdealKind::Obstruction,
            &i,
            &a,
            &mut quiet(),
        )
        .unwrap();
}

#[test]
fn the_result_only_derived_role_is_not_added_to_authored_law_declarations() {
    use crate::input::{InputSources, check_inputs};
    let i = fixture::with_body(fixture::MAP, LAWS);
    let original = i.sources();
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replace("law optional same", "law derived same");
    let sources = InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        original.archmap().bytes().to_vec(),
    );
    let failure = check_inputs(sources, &mut quiet()).err().unwrap();
    assert!(
        failure
            .issues()
            .iter()
            .any(|issue| issue.canonical().contains("\"code\":\"syntax\""))
    );
    assert!(failure.declarations().is_empty());
}
