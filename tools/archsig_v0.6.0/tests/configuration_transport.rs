use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{
            ConfigurationTransport, Naturality, TransportConditionFailure, configuration_transport,
            correspondence, identity, internal_arrow,
        },
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const L: &str = include_str!("fixtures/configuration-operation.law");
const A: &str = include_str!("fixtures/object-configuration-map.archmap.json");
const DIGEST: &str = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
fn with_definition(d: &[u8], a: &str) -> CheckedInputs {
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["Reservations"].digest;
    check_inputs(
        InputSources::from_bytes(
            vec![d.to_vec()],
            L.replace(DIGEST, digest).into_bytes(),
            a.replace(DIGEST, digest).into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn inputs(a: &str) -> CheckedInputs {
    with_definition(D, a)
}
fn cross_kind_inputs() -> CheckedInputs {
    let d = include_bytes!("fixtures/cross-kind-transport.atoms.json");
    let defs = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &defs.vocabularies["V"].digest;
    check_inputs(
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
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn fact(id: &str, f: Option<&str>) -> FactPointer {
    let ty = match id {
        "A" | "B" => "System",
        "p" | "q" | "u" | "r" | "s" | "w" => "State",
        "e" | "f" => "Reserve",
        "m" => "Migration",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: f.map(|f| format!("Reservations.{ty}.{f}")),
        atom: f.map(|f| format!("{id}-{f}")),
    }
}
fn result(i: &CheckedInputs) -> ConfigurationTransport {
    let map = correspondence(i, "v", "m", "Reservations", None, &mut Control::unlimited()).unwrap();
    assert!(
        map.counterexamples().is_empty(),
        "{:?}",
        map.counterexamples()
    );
    assert!(map.missing().is_empty(), "{:?}", map.missing());
    configuration_transport(i, map.map().unwrap(), &mut Control::unlimited()).unwrap()
}
fn remove(a: &str, id: &str) -> String {
    let marker = format!("\"id\":\"{id}\"");
    assert_eq!(a.lines().filter(|l| l.contains(&marker)).count(), 1);
    a.lines()
        .filter(|l| !l.contains(&marker))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
fn edit(a: &str, id: &str, before: &str, after: &str) -> String {
    let marker = format!("\"id\":\"{id}\"");
    let mut found = 0;
    let result = a
        .lines()
        .map(|l| {
            if l.contains(&marker) {
                found += 1;
                assert!(l.contains(before));
                l.replace(before, after)
            } else {
                l.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(found, 1);
    result
}
fn mu(f: &FactPointer) -> FactPointer {
    let to = match f.subject.as_str() {
        "A" => "B",
        "p" => "r",
        "q" => "s",
        "u" => "w",
        "e" => "f",
        _ => return fact("B", None),
    };
    fact(to, f.field.as_ref().map(|f| f.rsplit('.').next().unwrap()))
}
fn arrow(f: &FactPointer, from: &str, to: &str) -> FactPointer {
    if f.subject == from {
        fact(to, f.field.as_ref().map(|f| f.rsplit('.').next().unwrap()))
    } else {
        f.clone()
    }
}
#[test]
fn actual_objects_share_the_base_action_and_all_universe_naturality() {
    let i = inputs(A);
    let r = result(&i);
    assert!(r.all_preserved());
    assert_eq!(r.action().universe().len(), 39);
    assert_eq!(r.objects().len(), 4);
    for (row, (a, b)) in r
        .objects()
        .iter()
        .zip([("A", "B"), ("p", "r"), ("q", "s"), ("u", "w")])
    {
        assert_eq!(row.source().subject(), &fact(a, None));
        assert_eq!(row.target().unwrap().subject(), &fact(b, None));
        assert_eq!(row.source().root(), &fact("A", None));
        assert_eq!(row.target().unwrap().root(), &fact("B", None));
        assert!(row.is_preserved());
        for f in row.source_configuration().family() {
            assert!(
                row.target_configuration()
                    .unwrap()
                    .family()
                    .contains(&mu(f))
            );
        }
    }
    assert_eq!(
        r.objects()[0].source_configuration(),
        r.action().source_configuration()
    );
    assert_eq!(
        r.objects()[0].target_configuration(),
        Some(r.action().target_configuration())
    );
    let [g] = r.generators() else {
        panic!("all generators")
    };
    assert_eq!(g.source(), &fact("e", None));
    assert_eq!(g.target(), &fact("f", None));
    assert_eq!(g.endpoints_preserved(), Some(true));
    assert_eq!(g.naturality(), Some(&Naturality::Preserved));
    for f in r.action().universe() {
        assert_eq!(r.action().image(f), Some(&mu(f)));
        assert_eq!(mu(&arrow(f, "p", "q")), arrow(&mu(f), "r", "s"));
    }
    assert_eq!(r.operation().word(), [fact("m", None)]);
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn third_object_collision_refutes_only_global_naturality_and_retains_operation() {
    let a = edit(
        A,
        "m-states",
        r#"[["v","u"],["v","w"]]"#,
        r#"[["v","u"],["v","r"]]"#,
    );
    let i = inputs(&a);
    let r = result(&i);
    assert!(r.objects().iter().all(|o| o.is_preserved()));
    assert!(r.source().all_preserved());
    assert!(r.target().all_preserved());
    assert!(!r.all_preserved());
    assert_eq!(r.objects()[1].target(), r.objects()[3].target());
    assert_ne!(r.objects()[1].source(), r.objects()[3].source());
    let [g] = r.generators() else {
        panic!("generator")
    };
    assert_eq!(g.endpoints_preserved(), Some(true));
    let Some(Naturality::Refuted {
        fact: f,
        left,
        right,
    }) = g.naturality()
    else {
        panic!("naturality counterexample")
    };
    assert_eq!(f, &fact("u", Some("free")));
    assert_eq!(left, &fact("r", Some("free")));
    assert_eq!(right, &fact("s", Some("free")));
    assert!(
        !r.source().arrows()[0]
            .source()
            .unwrap()
            .candidate()
            .known()
            .family()
            .contains(f)
    );
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn unconfirmed_target_generator_is_retained_with_missing_slot() {
    let a = remove(&remove(&remove(A, "p-free"), "q-free"), "s-free");
    let i = inputs(&a);
    let r = result(&i);
    assert!(r.source().all_preserved());
    assert!(!r.target().all_preserved());
    assert!(!r.all_preserved());
    let [target] = r.target().arrows() else {
        panic!("target generator")
    };
    assert!(target.map().is_none());
    let mut s = fact("s", Some("free"));
    s.atom = None;
    assert!(target.missing().contains(&s));
    assert_eq!(r.generators().len(), 1);
    assert_eq!(r.generators()[0].naturality(), None);
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn refuted_target_reference_structure_does_not_erase_counterexamples_or_operation() {
    let d = include_bytes!("fixtures/object-configuration-map-reference.atoms.json");
    let a = include_str!("fixtures/object-configuration-map-reference.archmap.json");
    assert!(result(&with_definition(d, a)).all_preserved());
    let mut a = edit(
        a,
        "m-states",
        r#"[["v","u"],["v","w"]]"#,
        r#"[["v","u"],["v","r"]]"#,
    );
    for id in ["r-friend", "s-friend", "w-friend"] {
        a = edit(&a, id, r#"["v","w"]"#, r#"["v","r"]"#);
    }
    let i = with_definition(d, &a);
    let r = result(&i);
    assert!(r.source().all_preserved());
    assert!(!r.all_preserved());
    let [target] = r.target().arrows() else {
        panic!("target")
    };
    assert!(target.map().is_none());
    assert!(target.missing().is_empty());
    assert!(!target.counterexamples().is_empty());
    assert_eq!(r.generators()[0].naturality(), None);
    assert_eq!(r.generators()[0].endpoints_preserved(), None);
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn all_named_generators_and_separate_readings_remain_in_transport() {
    let i = inputs(include_str!(
        "fixtures/configuration-operation.archmap.json"
    ));
    let r = result(&i);
    assert!(r.all_preserved());
    assert_eq!(
        r.generators()
            .iter()
            .map(|g| (g.source().subject.as_str(), g.target().subject.as_str()))
            .collect::<Vec<_>>(),
        [("e", "f"), ("h", "l"), ("k", "t")]
    );
    let m = correspondence(
        &i,
        "v",
        "m",
        "Reservations",
        Some("Alternative"),
        &mut Control::unlimited(),
    )
    .unwrap();
    let r = configuration_transport(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
    assert!(r.all_preserved());
    for o in r.objects() {
        assert_eq!(o.source().reading(), "Reservations");
        assert_eq!(o.target().unwrap().reading(), "Alternative");
    }
}
#[test]
fn internal_identity_and_composite_maps_are_not_raw_correspondences() {
    let i = inputs(A);
    let e = internal_arrow(
        &i,
        "Reservations",
        "v",
        "A",
        "v",
        "e",
        &mut Control::unlimited(),
    )
    .unwrap();
    let id = identity(
        &i,
        "Reservations",
        "v",
        "A",
        None,
        &mut Control::unlimited(),
    )
    .unwrap()
    .operation()
    .unwrap()
    .clone();
    let composed = id.compose(&i, &id, &mut Control::unlimited()).unwrap();
    for map in [e.map().unwrap(), id.map(), composed.map()] {
        assert!(
            matches!(configuration_transport(&i,map,&mut Control::unlimited()),Err(ConstructionFailure::InvalidSelection(message))if !message.is_empty())
        );
    }
}
#[test]
fn current_raw_maps_and_universe_are_rechecked_but_quantities_do_not_define_structure() {
    let i = inputs(A);
    let r = result(&i);
    let changed = inputs(&edit(
        A,
        "m-states",
        r#"[["v","u"],["v","w"]]"#,
        r#"[["v","u"],["v","r"]]"#,
    ));
    assert!(r.recheck(&changed, &mut Control::unlimited()).is_err());
    assert!(
        configuration_transport(&changed, r.operation().map(), &mut Control::unlimited()).is_err()
    );
    let quantity = inputs(&edit(A, "u-free", r#""19""#, r#""103""#));
    r.recheck(&quantity, &mut Control::unlimited()).unwrap();
    let missing = inputs(&remove(A, "u-free"));
    assert!(r.recheck(&missing, &mut Control::unlimited()).is_err());
}
#[test]
fn every_fixed_transport_stop_latches_without_new_probes() {
    for (i, reading) in [(inputs(A), "Reservations"), (cross_kind_inputs(), "Read")] {
        let m = correspondence(&i, "v", "m", reading, None, &mut Control::unlimited()).unwrap();
        let r = configuration_transport(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
        let map = r.operation().map();
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut c = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ConfigurationTransport {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        configuration_transport(&i, map, &mut c).unwrap();
        let total = count.get();
        assert!(total > 39);
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
                        if p == Checkpoint::ConfigurationTransport {
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
                let f = configuration_transport(&i, map, &mut c).unwrap_err();
                assert_eq!(f, ConstructionFailure::Stopped(c.stop_reason().unwrap()));
                assert_eq!(count.get(), at);
                assert_eq!(r.recheck(&i, &mut c).unwrap_err(), f);
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn cross_kind_configuration_maps_keep_object_and_generator_condition_failures_and_operation() {
    let i = cross_kind_inputs();
    let m = correspondence(&i, "v", "m", "Read", None, &mut Control::unlimited()).unwrap();
    assert!(m.missing().is_empty());
    assert!(m.counterexamples().is_empty());
    let r = configuration_transport(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
    assert!(!r.all_preserved());
    assert!(r.source().all_preserved());
    assert!(r.target().all_preserved());
    let f = |id: &str| FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: None,
        atom: None,
    };
    assert_eq!(r.objects().len(), 3);
    assert!(r.objects()[0].is_preserved());
    assert!(r.objects()[1].is_preserved());
    let object = &r.objects()[2];
    assert_eq!(object.source().subject(), &f("s"));
    assert!(object.target().is_none());
    assert!(object.target_configuration().is_none());
    assert!(!object.is_preserved());
    assert_eq!(
        object.condition_failure(),
        Some(&TransportConditionFailure::TargetObject {
            source: f("s"),
            image: f("f")
        })
    );
    let [generator] = r.generators() else {
        panic!("source generator retained")
    };
    assert_eq!(generator.source(), &f("e"));
    assert_eq!(generator.target(), &f("t"));
    assert_eq!(
        generator.condition_failure(),
        Some(&TransportConditionFailure::TargetGenerator {
            source: f("e"),
            image: f("t")
        })
    );
    assert_eq!(generator.endpoints_preserved(), None);
    assert_eq!(generator.naturality(), None);
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
