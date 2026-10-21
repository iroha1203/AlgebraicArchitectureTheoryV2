use archsig::{
    archmap::Value,
    construction::{
        ConstructionFailure,
        maps::{
            DeclarationCorrespondence, DeclarationValuePosition as Position, NumericValueTransport,
            correspondence, declaration_correspondence, numeric_declaration_value_transport,
        },
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
    types::Type,
};
use std::{cell::Cell, rc::Rc};
const L: &str = include_str!("fixtures/numeric-value-transport.law");
const A: &str = include_str!("fixtures/reference-type.archmap.json");
fn inputs(law: &str) -> CheckedInputs {
    let left = include_bytes!("fixtures/configuration-map-left.atoms.json");
    let right = include_bytes!("fixtures/configuration-map-right.atoms.json");
    let defs = archsig::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
    let ld = &defs.vocabularies["Left"].digest;
    let rd = &defs.vocabularies["Right"].digest;
    let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = archsig::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
            .into_bytes()
    };
    check_inputs(
        InputSources::from_bytes(
            vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
            expand(law),
            expand(A),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn declarations(i: &CheckedInputs) -> DeclarationCorrespondence {
    let r = correspondence(
        i,
        "v",
        "m",
        "Before",
        Some("After"),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(r.counterexamples().is_empty(), "{:?}", r.counterexamples());
    assert!(r.missing().is_empty(), "{:?}", r.missing());
    declaration_correspondence(i, r.map().unwrap(), &mut Control::unlimited()).unwrap()
}
fn result(i: &CheckedInputs, p: usize) -> NumericValueTransport {
    numeric_declaration_value_transport(
        i,
        &declarations(i),
        "Before.axes",
        Position::Parameter(p),
        &mut Control::unlimited(),
    )
    .unwrap()
}
fn nested() -> Value {
    Value::Tuple(vec![
        Value::Z("-1234567890123456789012345678901234567890".parse().unwrap()),
        Value::Tuple(vec![
            Value::Q((-19).into(), 17.into()),
            Value::Fp(2u32.into()),
        ]),
    ])
}
#[test]
fn whole_numeric_types_have_identity_maps_without_finite_enumeration() {
    let i = inputs(L);
    for (p, ty) in [(1, Type::Z), (2, Type::Q), (3, Type::Fp("3".into()))] {
        let r = result(&i, p);
        assert_eq!(r.source_type(), &ty);
        assert_eq!(r.target_type(), &ty);
        assert_eq!(r.forward().ty(), &ty);
        assert_eq!(r.inverse().ty(), &ty);
        r.recheck(&i, &mut Control::unlimited()).unwrap();
    }
    let r = result(&i, 4);
    assert_eq!(
        r.source_type(),
        &Type::Tuple(vec![
            Type::Z,
            Type::Tuple(vec![Type::Q, Type::Fp("3".into())])
        ])
    );
}
#[test]
fn both_compositions_preserve_large_negative_rationals_fp_and_nested_positions() {
    let i = inputs(L);
    for (p, value, expected) in [
        (
            1,
            Value::Z("9876543210987654321098765432109876543210".parse().unwrap()),
            "\"9876543210987654321098765432109876543210\"",
        ),
        (1, Value::Z((-13).into()), "\"-13\""),
        (2, Value::Q((-19).into(), 17.into()), "[\"-19\",\"17\"]"),
        (2, Value::Q(0.into(), 1.into()), "[\"0\",\"1\"]"),
        (3, Value::Fp(2u32.into()), "\"2\""),
        (
            4,
            nested(),
            "[\"-1234567890123456789012345678901234567890\",[[\"-19\",\"17\"],\"2\"]]",
        ),
    ] {
        let r = result(&i, p);
        let f = r
            .forward()
            .apply(&value, &mut Control::unlimited())
            .unwrap();
        let g = r
            .inverse()
            .apply(&value, &mut Control::unlimited())
            .unwrap();
        assert_eq!(f.wire().canonical(), expected);
        assert_eq!(g.wire().canonical(), expected);
        assert_eq!(
            r.inverse()
                .apply_value(&f, &mut Control::unlimited())
                .unwrap(),
            f
        );
        assert_eq!(
            r.forward()
                .apply_value(&g, &mut Control::unlimited())
                .unwrap(),
            g
        );
    }
}
#[test]
fn return_position_and_operation_survive_separate_body_and_signature_failures() {
    let i = inputs(L);
    let d = declarations(&i);
    assert!(!d.all_signatures_compatible());
    let r = numeric_declaration_value_transport(
        &i,
        &d,
        "Before.returned",
        Position::Return,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.declaration(), "Before.returned");
    assert_eq!(r.position(), Position::Return);
    assert_eq!(r.operation(), d.operation());
    assert_eq!(
        r.forward()
            .apply(&nested(), &mut Control::unlimited())
            .unwrap()
            .wire()
            .canonical(),
        "[\"-1234567890123456789012345678901234567890\",[[\"-19\",\"17\"],\"2\"]]"
    );
    // 同じ数値型の対応は式・値の可換性を主張しない。After.changedのbodyはz+1。
    let changed = numeric_declaration_value_transport(
        &i,
        &d,
        "Before.changed",
        Position::Return,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(changed.operation(), d.operation());
    assert_eq!(changed.source_type(), &Type::Z);
}
#[test]
fn bad_selection_wrong_types_and_noncanonical_values_are_rejected() {
    let i = inputs(L);
    let d = declarations(&i);
    for (name, pos) in [
        ("Before.axes", Position::Parameter(0)),
        ("Before.axes", Position::Parameter(5)),
        ("Before.axes", Position::Parameter(6)),
        ("Before.axes", Position::Parameter(100)),
        ("Before.axes", Position::Return),
        ("Before.missing", Position::Return),
        ("After.changed", Position::Return),
        ("Before.mismatch", Position::Return),
    ] {
        assert!(
            matches!(
                numeric_declaration_value_transport(&i, &d, name, pos, &mut Control::unlimited()),
                Err(ConstructionFailure::InvalidSelection(_))
            ),
            "{name} {pos:?}"
        );
    }
    for (p, v) in [
        (1, Value::Q(1.into(), 1.into())),
        (2, Value::Z(1.into())),
        (2, Value::Q(2.into(), 4.into())),
        (2, Value::Q(1.into(), 0.into())),
        (2, Value::Q(1.into(), (-2).into())),
        (3, Value::Fp(3u32.into())),
        (3, Value::Z(2.into())),
        (4, Value::Tuple(vec![Value::Z(1.into())])),
        (
            4,
            Value::Tuple(vec![
                Value::Z(1.into()),
                Value::Tuple(vec![Value::Z(1.into()), Value::Fp(1u32.into())]),
            ]),
        ),
    ] {
        assert!(matches!(
            result(&i, p).forward().apply(&v, &mut Control::unlimited()),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
    let z = result(&i, 1)
        .forward()
        .apply(&Value::Z(2.into()), &mut Control::unlimited())
        .unwrap();
    assert!(matches!(
        result(&i, 2)
            .inverse()
            .apply_value(&z, &mut Control::unlimited()),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
}
#[test]
fn current_declaration_types_are_rechecked_instead_of_reusing_stale_correspondence() {
    let i = inputs(L);
    let r = result(&i, 1);
    let changed = inputs(
        &L.replace("c: Left.Child, z: Z", "c: Left.Child, z: Q")
            .replace("c: Right.Child, z: Z", "c: Right.Child, z: Q"),
    );
    assert!(r.recheck(&changed, &mut Control::unlimited()).is_err());
    assert_eq!(result(&changed, 1).source_type(), &Type::Q);
    let changed = inputs(&L.replace("nested: (Z, (Q, Fp(3)))", "nested: ((Z, Q), Fp(3))"));
    assert!(
        result(&i, 4)
            .recheck(&changed, &mut Control::unlimited())
            .is_err()
    );
}
#[test]
fn fixed_checkpoints_stop_construction_application_and_recheck_without_reentry() {
    let i = inputs(L);
    let d = declarations(&i);
    let r = result(&i, 4);
    let v = r
        .forward()
        .apply(&nested(), &mut Control::unlimited())
        .unwrap();
    for action in 0..4 {
        for point in [
            Checkpoint::NumericValueTransport,
            Checkpoint::FiniteIteration,
        ] {
            let invoke = |c: &mut Control| -> Result<(), ConstructionFailure> {
                match action {
                    0 => numeric_declaration_value_transport(
                        &i,
                        &d,
                        "Before.axes",
                        Position::Parameter(4),
                        c,
                    )
                    .map(|_| ()),
                    1 => r.forward().apply(&nested(), c).map(|_| ()),
                    2 => r.inverse().apply_value(&v, c).map(|_| ()),
                    _ => r.recheck(&i, c),
                }
            };
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            invoke(&mut Control::new(Limits::default(), move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                Usage::default()
            }))
            .unwrap();
            let total = count.get();
            assert!(total > 0);
            let mut positions = vec![1, (total + 1) / 2, total];
            positions.sort();
            positions.dedup();
            for at in positions {
                for mode in 0..4 {
                    let count = Rc::new(Cell::new(0));
                    let seen = count.clone();
                    let mut c = Control::new(
                        Limits {
                            time_ms: Some(1),
                            memory_mib: Some(1),
                        },
                        move |p| {
                            if p == point {
                                seen.set(seen.get() + 1);
                            }
                            let stop = seen.get() >= at;
                            Usage {
                                elapsed_ms: if stop && mode == 0 { 1 } else { 0 },
                                memory_mib: if stop && mode == 1 { 1 } else { 0 },
                                signal: if stop {
                                    match mode {
                                        2 => Some(Signal::Int),
                                        3 => Some(Signal::Term),
                                        _ => None,
                                    }
                                } else {
                                    None
                                },
                            }
                        },
                    );
                    let f = invoke(&mut c).unwrap_err();
                    assert_eq!(f, ConstructionFailure::Stopped(c.stop_reason().unwrap()));
                    assert_eq!(count.get(), at);
                    assert_eq!(invoke(&mut c).unwrap_err(), f);
                    assert_eq!(count.get(), at);
                }
            }
        }
    }
}
