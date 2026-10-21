use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{ConfigurationOperation, OperationStep, correspondence, identity, internal_arrow},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const L: &[u8] = include_bytes!("fixtures/configuration-operation.law");
const A: &str = include_str!("fixtures/configuration-operation.archmap.json");
fn inputs(map: &str) -> CheckedInputs {
    check_inputs(
        InputSources::from_bytes(vec![D.to_vec()], L.to_vec(), map.as_bytes().to_vec()),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn fact(id: &str, field: Option<&str>) -> FactPointer {
    let ty = match id {
        "A" | "B" => "System",
        "p" | "q" | "r" | "s" => "State",
        "e" | "f" | "h" | "k" | "l" | "t" => "Reserve",
        "m" | "n" | "mm" | "z" => "Migration",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Reservations.{ty}.{f}")),
        atom: field.map(|f| format!("{id}-{f}")),
    }
}
fn arrow(i: &CheckedInputs, id: &str) -> ConfigurationOperation {
    let r = internal_arrow(
        i,
        "Reservations",
        "v",
        "A",
        "v",
        id,
        &mut Control::unlimited(),
    )
    .unwrap();
    ConfigurationOperation::from_map(i, r.map().unwrap(), &mut Control::unlimited()).unwrap()
}
fn migration(i: &CheckedInputs, id: &str) -> ConfigurationOperation {
    let r = correspondence(i, "v", id, "Reservations", None, &mut Control::unlimited()).unwrap();
    assert!(r.counterexamples().is_empty(), "{:?}", r.counterexamples());
    ConfigurationOperation::from_map(i, r.map().unwrap(), &mut Control::unlimited()).unwrap()
}
fn ident(i: &CheckedInputs, root: &str, part: Option<&str>) -> ConfigurationOperation {
    identity(
        i,
        "Reservations",
        "v",
        root,
        part.map(|p| ("v", p)),
        &mut Control::unlimited(),
    )
    .unwrap()
    .operation()
    .unwrap()
    .clone()
}
fn edit(map: &str, id: &str, before: &str, after: &str) -> String {
    let mut hits = 0;
    let result = map
        .lines()
        .map(|l| {
            if l.contains(&format!("\"id\":\"{id}\"")) {
                assert!(l.contains(before));
                hits += 1;
                l.replace(before, after)
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(hits, 1);
    result
}
fn remove(map: &str, id: &str) -> String {
    map.lines()
        .filter(|l| !l.contains(&format!("\"id\":\"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
#[test]
fn base_and_component_identities_fix_every_universe_atom_and_keep_typed_objects() {
    let i = inputs(A);
    for (root, part) in [("A", None), ("A", Some("p")), ("B", None), ("B", Some("r"))] {
        let op = ident(&i, root, part);
        assert!(op.word().is_empty());
        assert_eq!(op.source(), op.target());
        assert_eq!(op.source().root(), &fact(root, None));
        assert_eq!(op.source().subject(), &fact(part.unwrap_or(root), None));
        assert_eq!(op.map().candidate().universe().len(), 62);
        assert_eq!(
            op.map().candidate().universe(),
            op.map().candidate().images()
        );
        assert!(op.map().candidate().subject().is_none());
        assert!(op.map().candidate().correspondence().is_none());
        assert!(matches!(op.derivation(),[OperationStep::Identity{object}]if object==&op.source()));
        op.recheck(&i, &mut Control::unlimited()).unwrap();
    }
    assert_ne!(
        ident(&i, "A", None).source(),
        ident(&i, "A", Some("p")).source()
    );
}
#[test]
fn self_correspondence_is_not_the_empty_word_identity_on_the_whole_universe() {
    let i = inputs(A);
    let z = migration(&i, "z");
    let id = ident(&i, "A", None);
    assert_eq!(z.word(), &[fact("z", None)]);
    assert!(id.word().is_empty());
    assert_eq!(
        z.map().candidate().image(&fact("p", None)),
        Some(&fact("p", None))
    );
    assert_eq!(
        z.map().candidate().image(&fact("B", None)),
        Some(&fact("A", None))
    );
    assert_eq!(
        id.map().candidate().image(&fact("B", None)),
        Some(&fact("B", None))
    );
    assert!(!z.word_equal(&i, &id, &mut Control::unlimited()).unwrap());
    let diff = z
        .action_difference(&i, &id, &mut Control::unlimited())
        .unwrap()
        .unwrap();
    assert_ne!(diff.left(), diff.right());
    assert_eq!(z.map().candidate().image(diff.fact()), Some(diff.left()));
    assert_eq!(id.map().candidate().image(diff.fact()), Some(diff.right()));
}
#[test]
fn same_action_different_generators_remain_different_words() {
    let i = inputs(A);
    for (a, b) in [
        (arrow(&i, "e"), arrow(&i, "k")),
        (migration(&i, "m"), migration(&i, "mm")),
    ] {
        assert_ne!(a.word(), b.word());
        assert!(!a.word_equal(&i, &b, &mut Control::unlimited()).unwrap());
        assert!(
            a.action_difference(&i, &b, &mut Control::unlimited())
                .unwrap()
                .is_none()
        );
        assert_eq!(a.derivation().len(), 1);
        assert!(
            matches!(&a.derivation()[0],OperationStep::Generator{subject,..}if Some(subject)==a.map().candidate().subject())
        );
    }
}
#[test]
fn composition_uses_g_after_f_on_all_atoms_without_resetting_the_complement() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let eh = e.compose(&i, &h, &mut Control::unlimited()).unwrap();
    let he = h.compose(&i, &e, &mut Control::unlimited()).unwrap();
    assert_eq!(eh.word(), &[fact("e", None), fact("h", None)]);
    assert_eq!(he.word(), &[fact("h", None), fact("e", None)]);
    assert_eq!(eh.source().subject(), &fact("p", None));
    assert_eq!(eh.target().subject(), &fact("p", None));
    assert_eq!(he.source().subject(), &fact("q", None));
    assert_eq!(he.target().subject(), &fact("q", None));
    for f in eh.map().candidate().universe() {
        let mut expected_eh = f.clone();
        let mut expected_he = f.clone();
        if f.subject == "q" {
            expected_eh.subject = "p".into();
            expected_eh.atom = expected_eh.atom.map(|a| a.replacen("q-", "p-", 1));
        }
        if f.subject == "p" {
            expected_he.subject = "q".into();
            expected_he.atom = expected_he.atom.map(|a| a.replacen("p-", "q-", 1));
        }
        assert_eq!(eh.map().candidate().image(f), Some(&expected_eh), "{f:?}");
        assert_eq!(he.map().candidate().image(f), Some(&expected_he), "{f:?}");
    }
    let diff = ident(&i, "A", Some("p"))
        .action_difference(&i, &eh, &mut Control::unlimited())
        .unwrap()
        .unwrap();
    assert_eq!(diff.fact(), &fact("q", Some("free")));
    assert_eq!(diff.left(), &fact("q", Some("free")));
    assert_eq!(diff.right(), &fact("p", Some("free")));
    assert!(matches!(
        eh.derivation().last(),
        Some(OperationStep::Compose { first: 0, then: 1 })
    ));
    assert!(eh.map().candidate().subject().is_none());
    eh.map().recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn correspondence_composition_and_self_map_keep_distinct_named_words() {
    let i = inputs(A);
    let m = migration(&i, "m");
    let n = migration(&i, "n");
    let z = migration(&i, "z");
    let mn = m.compose(&i, &n, &mut Control::unlimited()).unwrap();
    assert_eq!(mn.word(), &[fact("m", None), fact("n", None)]);
    assert!(!mn.word_equal(&i, &z, &mut Control::unlimited()).unwrap());
    assert!(
        mn.action_difference(&i, &z, &mut Control::unlimited())
            .unwrap()
            .is_none()
    );
    for f in mn.map().candidate().universe() {
        let expected = if ["A", "p", "q", "e", "h", "k"].contains(&f.subject.as_str()) {
            f.clone()
        } else {
            fact("A", None)
        };
        assert_eq!(mn.map().candidate().image(f), Some(&expected), "{f:?}");
    }
    assert!(mn.map().candidate().correspondence().is_none());
}
#[test]
fn identities_are_removed_and_association_is_flattened_without_erasing_generators() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let idp = ident(&i, "A", Some("p"));
    let idq = ident(&i, "A", Some("q"));
    for op in [
        idp.compose(&i, &e, &mut Control::unlimited()).unwrap(),
        e.compose(&i, &idq, &mut Control::unlimited()).unwrap(),
    ] {
        assert!(op.word_equal(&i, &e, &mut Control::unlimited()).unwrap());
        assert!(
            op.action_difference(&i, &e, &mut Control::unlimited())
                .unwrap()
                .is_none()
        );
        assert_eq!(op.derivation().len(), 3);
    }
    let left = e
        .compose(&i, &h, &mut Control::unlimited())
        .unwrap()
        .compose(&i, &e, &mut Control::unlimited())
        .unwrap();
    let right = e
        .compose(
            &i,
            &h.compose(&i, &e, &mut Control::unlimited()).unwrap(),
            &mut Control::unlimited(),
        )
        .unwrap();
    assert_eq!(
        left.word(),
        &[fact("e", None), fact("h", None), fact("e", None)]
    );
    assert!(
        left.word_equal(&i, &right, &mut Control::unlimited())
            .unwrap()
    );
    assert!(
        left.action_difference(&i, &right, &mut Control::unlimited())
            .unwrap()
            .is_none()
    );
    assert_ne!(
        left.derivation(),
        right.derivation(),
        "結合前の元操作を由来へ残す"
    );
}
#[test]
fn endpoint_reading_and_operation_layers_are_checked() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let m = migration(&i, "m");
    let alternate = internal_arrow(
        &i,
        "Alternative",
        "v",
        "A",
        "v",
        "h",
        &mut Control::unlimited(),
    )
    .unwrap();
    let alternate =
        ConfigurationOperation::from_map(&i, alternate.map().unwrap(), &mut Control::unlimited())
            .unwrap();
    for (first, then) in [
        (&e, &e),
        (&e, &m),
        (&e, &alternate),
        (&m, &ident(&i, "A", None)),
    ] {
        assert!(
            matches!(first.compose(&i,then,&mut Control::unlimited()),Err(ConstructionFailure::InvalidSelection(ref message))if !message.is_empty())
        );
    }
    for other in [ident(&i, "A", None), arrow(&i, "h"), alternate] {
        assert!(matches!(
            e.action_difference(&i, &other, &mut Control::unlimited()),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
}
#[test]
fn identity_keeps_missing_structure_and_rejects_invalid_object_selection() {
    let i = inputs(&remove(A, "p-owner"));
    for component in [None, Some(("v", "p"))] {
        let r = identity(
            &i,
            "Reservations",
            "v",
            "A",
            component,
            &mut Control::unlimited(),
        )
        .unwrap();
        let mut missing = fact("p", Some("owner"));
        missing.atom = None;
        assert!(r.missing().contains(&missing));
        assert!(r.operation().is_none());
        r.recheck(&i, &mut Control::unlimited()).unwrap();
    }
    let i = inputs(&remove(A, "p-free"));
    assert!(
        identity(
            &i,
            "Reservations",
            "v",
            "A",
            Some(("v", "p")),
            &mut Control::unlimited()
        )
        .unwrap()
        .operation()
        .is_some()
    );
    let i = inputs(A);
    for (reading, root, component) in [
        ("missing", "A", None),
        ("Reservations", "p", None),
        ("Reservations", "A", Some(("v", "e"))),
        ("Reservations", "A", Some(("v", "A"))),
        ("Reservations", "B", Some(("v", "p"))),
    ] {
        assert!(matches!(
            identity(&i, reading, "v", root, component, &mut Control::unlimited()),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
}
#[test]
fn current_input_recheck_rejects_changed_maps_and_retains_structural_quantity_independence() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let both = e.compose(&i, &h, &mut Control::unlimited()).unwrap();
    let changed = inputs(&edit(A, "e-to", r#"["v","q"]"#, r#"["v","p"]"#));
    assert!(e.recheck(&changed, &mut Control::unlimited()).is_err());
    assert!(both.recheck(&changed, &mut Control::unlimited()).is_err());
    assert!(
        ConfigurationOperation::from_map(&changed, e.map(), &mut Control::unlimited()).is_err()
    );
    let quantity = inputs(&edit(A, "p-free", r#""2""#, r#""99""#));
    e.recheck(&quantity, &mut Control::unlimited()).unwrap();
    both.recheck(&quantity, &mut Control::unlimited()).unwrap();
    let missing = inputs(&remove(A, "q-free"));
    assert!(both.recheck(&missing, &mut Control::unlimited()).is_err());
}
#[test]
fn repeated_composition_has_a_flat_finite_derivation_and_preserves_order() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let mut op = e.compose(&i, &h, &mut Control::unlimited()).unwrap();
    for _ in 0..3 {
        op = op.compose(&i, &op, &mut Control::unlimited()).unwrap();
    }
    assert_eq!(op.word().len(), 16);
    assert_eq!(op.derivation().len(), 31);
    for pair in op.word().chunks_exact(2) {
        assert_eq!(pair, &[fact("e", None), fact("h", None)]);
    }
    op.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn every_fixed_operation_stop_latches_without_new_probes() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let original = e.compose(&i, &h, &mut Control::unlimited()).unwrap();
    let run = |kind, control: &mut Control| -> Result<(), ConstructionFailure> {
        match kind {
            0 => identity(&i, "Reservations", "v", "A", None, control).map(|_| ()),
            1 => ConfigurationOperation::from_map(&i, e.map(), control).map(|_| ()),
            2 => e.compose(&i, &h, control).map(|_| ()),
            3 => original.word_equal(&i, &original, control).map(|_| ()),
            4 => original
                .action_difference(&i, &original, control)
                .map(|_| ()),
            _ => original.recheck(&i, control),
        }
    };
    for kind in 0..6 {
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut control = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ConfigurationOperation {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        run(kind, &mut control).unwrap();
        let total = count.get();
        assert!(total > 2);
        for at in [1, total / 2, total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0usize));
                let seen = count.clone();
                let mut control = Control::new(
                    Limits {
                        time_ms: (mode == 0).then_some(1),
                        memory_mib: (mode == 1).then_some(1),
                    },
                    move |p| {
                        if p == Checkpoint::ConfigurationOperation {
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
                let failure = run(kind, &mut control).unwrap_err();
                assert_eq!(
                    failure,
                    ConstructionFailure::Stopped(control.stop_reason().unwrap()),
                    "{kind}/{at}/{mode}"
                );
                assert_eq!(count.get(), at);
                assert_eq!(original.recheck(&i, &mut control).unwrap_err(), failure);
                assert_eq!(count.get(), at);
                assert_eq!(
                    identity(&i, "Reservations", "v", "A", None, &mut control).unwrap_err(),
                    failure
                );
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn retained_composition_keeps_only_completed_operations_at_fixed_stops() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let m = migration(&i, "m");
    let n = migration(&i, "n");
    for (kind, (first, then)) in [(&e, &h), (&m, &n)].into_iter().enumerate() {
        let operations = Rc::new(Cell::new(0usize));
        let seen = operations.clone();
        let mut counting = Control::new(Limits::default(), move |point| {
            if point == Checkpoint::ConfigurationOperation {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let normal = first.compose_retained(&i, then, &mut counting).unwrap();
        let legacy = first.compose(&i, then, &mut Control::unlimited()).unwrap();
        assert_eq!(normal, legacy);
        let total = operations.get();
        assert!(total > 5);
        for at in [1, total / 2, total - 2, total - 1, total] {
            for mode in 0..4 {
                let probes = Rc::new(Cell::new(0usize));
                let operations = Rc::new(Cell::new(0usize));
                let calls = probes.clone();
                let seen = operations.clone();
                let mut control = Control::new(
                    Limits {
                        time_ms: (mode == 0).then_some(1),
                        memory_mib: (mode == 1).then_some(1),
                    },
                    move |point| {
                        calls.set(calls.get() + 1);
                        if point == Checkpoint::ConfigurationOperation {
                            seen.set(seen.get() + 1);
                        }
                        let stop = seen.get() >= at;
                        Usage {
                            elapsed_ms: u128::from(stop && mode == 0),
                            memory_mib: u128::from(stop && mode == 1),
                            signal: match (stop, mode) {
                                (true, 2) => Some(Signal::Int),
                                (true, 3) => Some(Signal::Term),
                                _ => None,
                            },
                        }
                    },
                );
                let failure = first.compose_retained(&i, then, &mut control).unwrap_err();
                let stop = ConstructionFailure::Stopped(control.stop_reason().unwrap());
                assert_eq!(failure.cause(), &stop, "{at}/{mode}");
                assert_eq!(operations.get(), at);
                let frozen = probes.get();
                if at == total {
                    let retained = failure.partial().expect("最後の確認では操作が完成済み");
                    assert_eq!(retained, &normal);
                    retained.recheck(&i, &mut Control::unlimited()).unwrap();
                    let candidate = retained.map().candidate();
                    let names = if kind == 0 { ["e", "h"] } else { ["m", "n"] };
                    assert_eq!(retained.word(), &names.map(|name| fact(name, None)));
                    for atom in candidate.universe() {
                        let expected = if kind == 0 {
                            let mut image = atom.clone();
                            if atom.subject == "q" {
                                image.subject = "p".into();
                                image.atom = image.atom.map(|a| a.replacen("q-", "p-", 1));
                            }
                            image
                        } else if ["A", "p", "q", "e", "h", "k"].contains(&atom.subject.as_str()) {
                            atom.clone()
                        } else {
                            fact("A", None)
                        };
                        assert_eq!(candidate.image(atom), Some(&expected), "{kind}/{atom:?}");
                    }
                    assert_eq!(retained.recheck(&i, &mut control).unwrap_err(), stop);
                } else {
                    assert!(
                        failure.partial().is_none(),
                        "{at}/{mode}: 未完成操作を保持した"
                    );
                }
                assert_eq!(first.compose(&i, then, &mut control).unwrap_err(), stop);
                assert_eq!(probes.get(), frozen, "停止後に新しいprobeを実行した");
                assert_eq!(operations.get(), at);
            }
        }
    }
}

#[test]
fn retained_composition_rejects_changed_inputs_and_incompatible_endpoints_without_partial() {
    let i = inputs(A);
    let e = arrow(&i, "e");
    let h = arrow(&i, "h");
    let m = migration(&i, "m");
    let alternate = internal_arrow(
        &i,
        "Alternative",
        "v",
        "A",
        "v",
        "h",
        &mut Control::unlimited(),
    )
    .unwrap();
    let alternate =
        ConfigurationOperation::from_map(&i, alternate.map().unwrap(), &mut Control::unlimited())
            .unwrap();
    for (first, then) in [
        (&e, &e),
        (&e, &m),
        (&e, &alternate),
        (&m, &ident(&i, "A", None)),
    ] {
        let failure = first
            .compose_retained(&i, then, &mut Control::unlimited())
            .unwrap_err();
        assert!(
            matches!(failure.cause(), ConstructionFailure::InvalidSelection(message) if !message.is_empty())
        );
        assert!(failure.partial().is_none());
        assert_eq!(
            &first
                .compose(&i, then, &mut Control::unlimited())
                .unwrap_err(),
            failure.cause()
        );
    }
    let changed = inputs(&edit(A, "e-to", "[\"v\",\"q\"]", "[\"v\",\"p\"]"));
    for (first, then) in [(&e, &h), (&h, &e)] {
        let failure = first
            .compose_retained(&changed, then, &mut Control::unlimited())
            .unwrap_err();
        assert!(!matches!(failure.cause(), ConstructionFailure::Stopped(_)));
        assert!(failure.partial().is_none());
        assert_eq!(
            &first
                .compose(&changed, then, &mut Control::unlimited())
                .unwrap_err(),
            failure.cause()
        );
    }
}
