use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{
            DeclarationCorrespondence, ReferenceConditionFailure as Failure,
            ReferenceTypeTransport, correspondence, declaration_correspondence,
            reference_type_transport,
        },
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
const L: &str = include_str!("fixtures/declaration-correspondence.law");
const A: &str = include_str!("fixtures/reference-type.archmap.json");
fn inputs(a: &str) -> CheckedInputs {
    with_left(
        include_bytes!("fixtures/configuration-map-left.atoms.json"),
        a,
    )
}
fn with_left(left: &[u8], a: &str) -> CheckedInputs {
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
    let a = a
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd)
        .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest);
    check_inputs(
        InputSources::from_bytes(
            vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
            L.replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd)
                .into_bytes(),
            a.into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn declarations(i: &CheckedInputs) -> DeclarationCorrespondence {
    let m = correspondence(
        i,
        "v",
        "m",
        "Before",
        Some("After"),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(m.counterexamples().is_empty(), "{:?}", m.counterexamples());
    assert!(m.missing().is_empty(), "{:?}", m.missing());
    declaration_correspondence(i, m.map().unwrap(), &mut Control::unlimited()).unwrap()
}
fn result(i: &CheckedInputs, ty: &str) -> ReferenceTypeTransport {
    reference_type_transport(i, &declarations(i), ty, &mut Control::unlimited()).unwrap()
}
fn fact(snapshot: &str, subject: &str) -> FactPointer {
    FactPointer {
        snapshot: snapshot.into(),
        subject: subject.into(),
        field: None,
        atom: None,
    }
}
fn v(s: &str) -> FactPointer {
    fact("v", s)
}
fn add(a: &str, subject: &str, ty: &str) -> String {
    a.replace(
        "\"subjects\": [",
        &format!(
            "\"subjects\": [\n{{\"id\":\"{subject}\",\"type\":\"{ty}\",\"origin\":\"model\"}},"
        ),
    )
}
fn extra_snapshot(a: &str, ty: &str) -> String {
    let (root, owner) = match ty {
        "Left.Child" => (
            ",{\"id\":\"root\",\"type\":\"Left.Root\",\"origin\":\"model\"}",
            "{\"id\":\"owner\",\"subject\":\"p\",\"field\":\"Left.Child.owner\",\"value\":[\"w\",\"root\"],\"origin\":\"model\"}",
        ),
        "Right.Child" => (
            ",{\"id\":\"root\",\"type\":\"Right.Root\",\"origin\":\"model\"}",
            "{\"id\":\"owner\",\"subject\":\"p\",\"field\":\"Right.Child.owner\",\"value\":[\"w\",\"root\"],\"origin\":\"model\"}",
        ),
        "Left.ExternalChild" => (
            ",{\"id\":\"root\",\"type\":\"Left.ExternalRoot\",\"origin\":\"model\"}",
            "",
        ),
        _ => ("", ""),
    };
    a.replace("\"snapshots\":[", &format!("\"snapshots\":[{{\"id\":\"w\",\"origin\":\"model\",\"subjects\":[{{\"id\":\"p\",\"type\":\"{ty}\",\"origin\":\"model\"}}{root}],\"atoms\":[{owner}]}},"))
}
#[test]
fn root_and_child_bijections_check_both_whole_domains_without_quantity_equality() {
    let i = inputs(A);
    for (ty, to, a, b) in [
        ("Left.Root", "Right.Root", "a", "b"),
        ("Left.Child", "Right.Child", "p", "q"),
    ] {
        let r = result(&i, ty);
        assert_eq!(r.source_type(), ty);
        assert_eq!(r.target_type(), to);
        assert_eq!(r.source(), [v(a)]);
        assert_eq!(r.target(), [v(b)]);
        assert_eq!(r.images(), [v(b)]);
        assert!(r.failures().is_empty());
        let iso = r.bijection().unwrap();
        assert_eq!(iso.forward().iter().collect::<Vec<_>>(), [(&v(a), &v(b))]);
        assert_eq!(iso.inverse().iter().collect::<Vec<_>>(), [(&v(b), &v(a))]);
        assert_eq!(iso.forward().get(&v("absent")), None);
        r.recheck(&i, &mut Control::unlimited()).unwrap();
        r.operation()
            .recheck(&i, &mut Control::unlimited())
            .unwrap();
    }
}
#[test]
fn external_reference_values_are_fixed_even_when_atom_action_collapses_them() {
    let i = inputs(&extra_snapshot(A, "Bridge.Move"));
    let r = result(&i, "Bridge.Move");
    assert_eq!(r.source(), [v("m"), fact("w", "p")]);
    assert_eq!(r.target(), r.source());
    assert_eq!(r.images(), r.source());
    assert_eq!(
        r.operation().map().candidate().image(&v("m")),
        Some(&v("b"))
    );
    let iso = r.bijection().unwrap();
    for a in r.source() {
        assert_eq!(iso.forward().get(a), Some(a));
        assert_eq!(iso.inverse().get(a), Some(a));
    }
}
#[test]
fn outside_family_references_from_other_roots_and_snapshots_fail_typed_image() {
    let i = inputs(&extra_snapshot(A, "Left.Child"));
    let r = result(&i, "Left.Child");
    assert_eq!(r.source(), [v("p"), fact("w", "p")]);
    assert_eq!(r.images(), [v("q"), fact("w", "p")]);
    assert_eq!(
        r.failures(),
        [Failure::ImageType {
            source: fact("w", "p"),
            image: fact("w", "p"),
            expected: "Right.Child".into(),
            actual: "Left.Child".into()
        }]
    );
    assert!(r.bijection().is_none());
    assert_eq!(
        r.operation().map().candidate().image(&fact("w", "p")),
        Some(&v("b"))
    );
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
    let i = inputs(&add(A, "outside", "Left.Root"));
    let r = result(&i, "Left.Root");
    assert_eq!(r.source(), [v("a"), v("outside")]);
    assert_eq!(r.images(), [v("b"), v("outside")]);
    assert!(matches!(r.failures(),[Failure::ImageType {source,..}] if source == &v("outside")));
}
#[test]
fn unreached_targets_from_another_snapshot_are_not_silently_discarded() {
    let i = inputs(&extra_snapshot(A, "Right.Child"));
    let r = result(&i, "Left.Child");
    assert_eq!(r.target(), [v("q"), fact("w", "p")]);
    assert_eq!(
        r.failures(),
        [Failure::Unreached {
            target: fact("w", "p")
        }]
    );
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn collisions_and_unreached_targets_retain_every_reference_and_base_operation() {
    let a = add(A,"r","Left.Child").replace("\"atoms\": [", "\"atoms\": [\n{\"id\":\"r-owner\",\"subject\":\"r\",\"field\":\"Left.Child.owner\",\"value\":[\"v\",\"a\"],\"origin\":\"model\"},{\"id\":\"r-count\",\"subject\":\"r\",\"field\":\"Left.Child.count\",\"value\":\"20\",\"origin\":\"model\"},")
        .replace("[[[\"v\",\"p\"],[\"v\",\"q\"]]]", "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]");
    let i = inputs(&extra_snapshot(&a, "Right.Child"));
    let r = result(&i, "Left.Child");
    assert_eq!(r.source(), [v("p"), v("r")]);
    assert_eq!(r.images(), [v("q"), v("q")]);
    assert_eq!(
        r.failures(),
        [
            Failure::Collision {
                image: v("q"),
                sources: vec![v("p"), v("r")]
            },
            Failure::Unreached {
                target: fact("w", "p")
            }
        ]
    );
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn empty_source_and_target_are_a_bijection_and_one_empty_side_is_not() {
    let a = A
        .lines()
        .filter(|l| {
            !l.contains("\"id\":\"p\"")
                && !l.contains("\"id\":\"q\"")
                && !l.contains("\"subject\":\"p\"")
                && !l.contains("\"subject\":\"q\"")
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace("[[[\"v\",\"p\"],[\"v\",\"q\"]]]", "[]");
    let r = result(&inputs(&a), "Left.Child");
    assert!(r.source().is_empty());
    assert!(r.target().is_empty());
    assert!(r.images().is_empty());
    assert!(r.bijection().unwrap().forward().is_empty());
    assert!(r.bijection().unwrap().inverse().is_empty());
    let r = result(&inputs(&extra_snapshot(&a, "Right.Child")), "Left.Child");
    assert_eq!(
        r.failures(),
        [Failure::Unreached {
            target: fact("w", "p")
        }]
    );
    assert!(r.bijection().is_none());
    let r = result(&inputs(&extra_snapshot(&a, "Left.Child")), "Left.Child");
    assert!(matches!(r.failures(), [Failure::ImageType { .. }]));
    assert!(r.bijection().is_none());
}
#[test]
fn same_type_mapping_does_not_invent_inverse_by_reversing_only_selected_table() {
    let d = include_bytes!("fixtures/reservations.atoms.json");
    let i = check_inputs(
        InputSources::from_bytes(
            vec![d.to_vec()],
            include_bytes!("fixtures/configuration-operation.law").to_vec(),
            include_bytes!("fixtures/object-configuration-map.archmap.json").to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let m = correspondence(
        &i,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    let d = declaration_correspondence(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
    let r =
        reference_type_transport(&i, &d, "Reservations.State", &mut Control::unlimited()).unwrap();
    assert_eq!(r.source(), [v("p"), v("q"), v("r"), v("s"), v("u"), v("w")]);
    assert_eq!(r.images(), [v("r"), v("s"), v("r"), v("s"), v("w"), v("w")]);
    assert_eq!(
        r.failures(),
        [
            Failure::Collision {
                image: v("r"),
                sources: vec![v("p"), v("r")]
            },
            Failure::Collision {
                image: v("s"),
                sources: vec![v("q"), v("s")]
            },
            Failure::Collision {
                image: v("w"),
                sources: vec![v("u"), v("w")]
            },
            Failure::Unreached { target: v("p") },
            Failure::Unreached { target: v("q") },
            Failure::Unreached { target: v("u") }
        ]
    );
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn legal_entity_arrow_transport_is_a_value_condition_instead_of_input_error() {
    let d = include_bytes!("fixtures/cross-kind-transport.atoms.json");
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["V"].digest;
    let i = check_inputs(
        InputSources::from_bytes(
            vec![d.to_vec()],
            include_str!("fixtures/cross-kind-transport.law")
                .replace("@DIGEST@", digest)
                .into_bytes(),
            include_str!("fixtures/cross-kind-transport.archmap.json")
                .replace("@DIGEST@", digest)
                .into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let m = correspondence(&i, "v", "m", "Read", None, &mut Control::unlimited()).unwrap();
    let d = declaration_correspondence(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
    for (from, to, source, images, wrong, unreached) in [
        ("V.S", "V.E", ["s", "t"], ["f", "t"], "t", "e"),
        ("V.E", "V.S", ["e", "f"], ["t", "f"], "f", "s"),
    ] {
        let r = reference_type_transport(&i, &d, from, &mut Control::unlimited()).unwrap();
        assert_eq!(r.target_type(), to);
        assert_eq!(r.source(), source.map(v));
        assert_eq!(r.images(), images.map(v));
        assert_eq!(
            r.failures(),
            [
                Failure::ImageType {
                    source: v(wrong),
                    image: v(wrong),
                    expected: to.into(),
                    actual: from.into()
                },
                Failure::Unreached {
                    target: v(unreached)
                }
            ]
        );
        assert!(r.bijection().is_none());
        r.operation()
            .recheck(&i, &mut Control::unlimited())
            .unwrap();
    }
}
#[test]
fn current_whole_input_roster_is_rechecked_and_quantity_is_not_value_bijection_evidence() {
    let i = inputs(A);
    let d = declarations(&i);
    let r = result(&i, "Left.Child");
    let changed = inputs(&extra_snapshot(A, "Right.Child"));
    assert!(d.recheck(&changed, &mut Control::unlimited()).is_err());
    assert!(matches!(
        r.recheck(&changed, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let changed = inputs(&A.replace("\"value\":\"2\"", "\"value\":\"19\""));
    r.recheck(&changed, &mut Control::unlimited()).unwrap();
    for ty in ["Z", "Left.Unknown", "List<Left.Child>", "Left.Child[a]"] {
        assert!(matches!(
            reference_type_transport(&i, &d, ty, &mut Control::unlimited()),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
}
#[test]
fn source_order_does_not_change_canonical_whole_domain_or_images() {
    let a = extra_snapshot(&add(A, "z", "Bridge.Move"), "Bridge.Move");
    let b = a
        .replace(
            "{\"id\":\"m\",\"type\":\"Bridge.Move\",\"origin\":\"model\"}",
            "{\"id\":\"z-temp\",\"type\":\"Bridge.Move\",\"origin\":\"model\"}",
        )
        .replace("\"id\":\"z\"", "\"id\":\"m\"")
        .replace("\"id\":\"z-temp\"", "\"id\":\"z\"");
    let ra = result(&inputs(&a), "Bridge.Move");
    let rb = result(&inputs(&b), "Bridge.Move");
    assert_eq!(ra.source(), rb.source());
    assert_eq!(ra.target(), rb.target());
    assert_eq!(ra.images(), rb.images());
    assert_eq!(ra.bijection(), rb.bijection());
}
#[test]
fn fixed_reference_checkpoints_stop_before_returning_any_unfinished_bijection() {
    let i = inputs(A);
    let d = declarations(&i);
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::ReferenceTypeTransport {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    reference_type_transport(&i, &d, "Left.Child", &mut c).unwrap();
    let total = count.get();
    assert!(total > 20);
    for at in [1, total / 2, total] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0usize));
            let seen = count.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |p| {
                    if p == Checkpoint::ReferenceTypeTransport {
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
            let f = reference_type_transport(&i, &d, "Left.Child", &mut c).unwrap_err();
            assert_eq!(f, ConstructionFailure::Stopped(c.stop_reason().unwrap()));
            assert_eq!(count.get(), at);
            assert_eq!(
                reference_type_transport(&i, &d, "Left.Child", &mut c).unwrap_err(),
                f
            );
            assert_eq!(count.get(), at);
        }
    }
}

#[test]
fn external_owned_subjects_with_unknown_owner_remain_in_plain_ref_domain() {
    let a = extra_snapshot(A, "Left.ExternalChild");
    let i = with_left(include_bytes!("fixtures/reference-external.atoms.json"), &a);
    let r = result(&i, "Left.ExternalChild");
    assert_eq!(r.source(), [fact("w", "p")]);
    assert_eq!(r.target(), r.source());
    assert_eq!(r.images(), r.source());
    assert_eq!(
        r.bijection().unwrap().forward().get(&fact("w", "p")),
        Some(&fact("w", "p"))
    );
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn entity_to_arrow_type_with_full_bijection_is_accepted() {
    let d = include_bytes!("fixtures/cross-kind-transport.atoms.json");
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["V"].digest;
    let i = check_inputs(
        InputSources::from_bytes(
            vec![d.to_vec()],
            include_str!("fixtures/cross-kind-transport.law")
                .replace("@DIGEST@", digest)
                .into_bytes(),
            include_str!("fixtures/reference-cross-kind.archmap.json")
                .replace("@DIGEST@", digest)
                .into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let m = correspondence(&i, "v", "m", "Read", None, &mut Control::unlimited()).unwrap();
    assert!(m.counterexamples().is_empty());
    assert!(m.missing().is_empty());
    let d = declaration_correspondence(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
    let r = reference_type_transport(&i, &d, "V.S", &mut Control::unlimited()).unwrap();
    assert_eq!(r.target_type(), "V.E");
    assert_eq!(r.source(), [v("s")]);
    assert_eq!(r.target(), [v("f")]);
    assert!(r.failures().is_empty());
    assert_eq!(r.bijection().unwrap().forward().get(&v("s")), Some(&v("f")));
    assert_eq!(r.bijection().unwrap().inverse().get(&v("f")), Some(&v("s")));
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
