use archsig::{
    archmap::{Slot, Value},
    construction::{ConstructionFailure, FactPointer, construct},
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, collections::BTreeSet, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/configuration.atoms.json");
const L: &str = include_str!("fixtures/configuration.law");
const A: &str = include_str!("fixtures/configuration.archmap.json");
fn sources(map: &str) -> InputSources {
    let checked = archsig::definition::check_definitions(&[("definition0", D)]).unwrap();
    let digest = &checked.vocabularies["Mesh"].digest;
    InputSources::from_bytes(
        vec![D.to_vec()],
        L.replace("@MESH_DIGEST@", digest).into_bytes(),
        map.replace("@MESH_DIGEST@", digest).into_bytes(),
    )
}
fn checked(map: &str) -> CheckedInputs {
    check_inputs(sources(map), &mut Control::unlimited())
        .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn fact(subject: &str, field: Option<&str>, atom: bool) -> FactPointer {
    let ty = match subject {
        "A" | "B" => "Root",
        "p" | "q" | "r" => "Node",
        "e" => "Edge",
        "x" | "y" | "z" => "External",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: subject.into(),
        field: field.map(|s| format!("Mesh.{ty}.{s}")),
        atom: if atom {
            Some(format!("{subject}-{}", field.unwrap()))
        } else {
            None
        },
    }
}
fn set<T: Ord + Clone>(items: &[T]) -> BTreeSet<T> {
    items.iter().cloned().collect()
}
fn remove(map: &str, id: &str) -> String {
    map.lines()
        .filter(|l| !l.contains(&format!("\"id\": \"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
}
fn primary_fields() -> Vec<(&'static str, &'static str)> {
    vec![
        ("A", "links"),
        ("A", "pair"),
        ("A", "choice"),
        ("A", "tagged"),
        ("A", "mapping"),
        ("A", "members"),
        ("p", "owner"),
        ("p", "quantity"),
        ("q", "owner"),
        ("q", "quantity"),
        ("e", "owner"),
        ("e", "from"),
        ("e", "to"),
    ]
}
#[test]
fn base_and_owned_components_match_independent_exact_families_relations_and_slots() {
    let inputs = checked(A);
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert_eq!(result.reading(), "MeshRead");
    assert_eq!(result.root(), &fact("A", None, false));
    let base = result.base().configuration().unwrap();
    let mut family: Vec<_> = ["A", "p", "q", "r", "e", "x", "y"]
        .iter()
        .map(|s| fact(s, None, false))
        .collect();
    family.extend(primary_fields().iter().map(|(s, f)| fact(s, Some(f), true)));
    assert_eq!(set(base.family()), set(&family));
    assert_eq!(family.len(), 20);
    let mut requirements: Vec<_> = primary_fields()
        .iter()
        .map(|(s, f)| fact(s, Some(f), false))
        .collect();
    requirements.extend([
        fact("A", Some("quantity"), false),
        fact("r", Some("owner"), false),
        fact("r", Some("quantity"), false),
        fact("x", Some("next"), false),
        fact("x", Some("quantity"), false),
        fact("y", Some("next"), false),
        fact("y", Some("quantity"), false),
    ]);
    assert_eq!(set(base.requirements()), set(&requirements));
    assert_eq!(requirements.len(), 20);
    let mut relations: Vec<_> = primary_fields()
        .iter()
        .map(|(s, f)| (fact(s, None, false), fact(s, Some(f), true)))
        .collect();
    for (s, f, targets) in [
        ("A", "links", vec!["x", "y"]),
        ("A", "pair", vec!["x", "y"]),
        ("A", "choice", vec!["x"]),
        ("A", "tagged", vec!["y"]),
        ("A", "mapping", vec!["p", "q", "r", "x", "y"]),
        ("A", "members", vec!["x", "y"]),
        ("p", "owner", vec!["A"]),
        ("q", "owner", vec!["A"]),
        ("e", "owner", vec!["A"]),
        ("e", "from", vec!["p"]),
        ("e", "to", vec!["q"]),
    ] {
        for target in targets {
            relations.push((fact(s, Some(f), true), fact(target, None, false)));
        }
    }
    assert_eq!(set(base.relations()), set(&relations));
    assert_eq!(relations.len(), 31);
    assert_eq!(
        set(base.identifications()),
        family.iter().map(|f| (f.clone(), f.clone())).collect()
    );
    assert!(
        !base.family().contains(&fact("z", None, false)),
        "外部fieldの参照を推移的に取り込まない"
    );
    assert!(
        !base
            .relations()
            .contains(&(fact("A", None, false), fact("x", None, false))),
        "Rの推移閉包を加えない"
    );
    assert_eq!(result.components().len(), 2);
    for (component, id) in result.components().iter().zip(["p", "q"]) {
        assert_eq!(component.subject(), &fact(id, None, false));
        let part = component.candidate().configuration().unwrap();
        assert_eq!(
            set(part.family()),
            set(&[
                fact(id, None, false),
                fact(id, Some("owner"), true),
                fact(id, Some("quantity"), true),
                fact("A", None, false)
            ])
        );
        assert_eq!(part.relations().len(), 3);
        assert_eq!(part.identifications().len(), 4);
        assert_eq!(part.requirements().len(), 9);
    }
    assert_ne!(
        result.components()[0].candidate().known(),
        result.components()[1].candidate().known(),
        "同値の数量でsubject identityを潰さない"
    );
    result
        .recheck(&inputs, "MeshRead", "v", "A", &mut Control::unlimited())
        .unwrap();
}
#[test]
fn universe_is_canonical_and_keeps_all_known_positions_and_snapshot_identity() {
    let map=A.replace("  ]}]", "  ]},{\"id\":\"w\",\"origin\":\"model\",\"subjects\":[{\"id\":\"x\",\"type\":\"Mesh.External\",\"origin\":\"model\"}],\"atoms\":[{\"id\":\"x-quantity\",\"subject\":\"x\",\"field\":\"Mesh.External.quantity\",\"value\":\"9\",\"origin\":\"model\"}] }]");
    let inputs = checked(&map);
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    let mut expected: Vec<_> = ["A", "B", "p", "q", "r", "e", "x", "y", "z"]
        .iter()
        .map(|s| fact(s, None, false))
        .collect();
    expected.extend(primary_fields().iter().map(|(s, f)| fact(s, Some(f), true)));
    for (s, f) in [
        ("r", "owner"),
        ("r", "quantity"),
        ("x", "next"),
        ("x", "quantity"),
        ("y", "next"),
        ("y", "quantity"),
        ("z", "next"),
        ("z", "quantity"),
    ] {
        expected.push(fact(s, Some(f), true));
    }
    for field in [None, Some("quantity")] {
        let mut f = fact("x", field, field.is_some());
        f.snapshot = "w".into();
        expected.push(f);
    }
    assert_eq!(set(result.universe()), set(&expected));
    assert_eq!(result.universe().len(), 32);
    assert!(
        !result
            .universe()
            .contains(&fact("A", Some("quantity"), false)),
        "未観測slotはAtomでない"
    );
    let keys: Vec<_> = result
        .universe()
        .iter()
        .map(|f| {
            let mut items = vec![
                ("snapshot", archsig::canonical::Json::str(&f.snapshot)),
                ("subject", archsig::canonical::Json::str(&f.subject)),
            ];
            if let Some(field) = &f.field {
                items.push(("field", archsig::canonical::Json::str(field)));
            }
            if let Some(atom) = &f.atom {
                items.push(("atom", archsig::canonical::Json::str(atom)));
            }
            archsig::canonical::Json::Obj(
                items.into_iter().map(|(k, v)| (k.to_owned(), v)).collect(),
            )
            .canonical()
        })
        .collect();
    assert!(keys.windows(2).all(|p| p[0] < p[1]));
}
#[test]
fn missing_quantities_are_requirements_and_missing_membership_or_references_block_completion() {
    let inputs = checked(&remove(A, "p-quantity"));
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert!(result.base().configuration().is_some());
    assert!(
        result
            .base()
            .known()
            .requirements()
            .contains(&fact("p", Some("quantity"), false))
    );
    assert!(
        !result
            .base()
            .known()
            .family()
            .contains(&fact("p", Some("quantity"), true))
    );
    let inputs = checked(&remove(
        &remove(&remove(A, "p-owner"), "e-from"),
        "A-tagged",
    ));
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert!(result.base().configuration().is_none());
    assert_eq!(
        set(result.base().blocking_slots()),
        set(&[
            fact("p", Some("owner"), false),
            fact("e", Some("from"), false),
            fact("A", Some("tagged"), false)
        ])
    );
    assert!(
        !result
            .components()
            .iter()
            .any(|p| p.subject() == &fact("p", None, false))
    );
    assert!(!result.universe().contains(&fact("p", Some("owner"), true)));
    let inputs = checked(&remove(A, "A-choice"));
    assert!(
        construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited())
            .unwrap()
            .base()
            .configuration()
            .is_none()
    );
}
#[test]
fn ownership_uses_the_full_root_reference_across_snapshots() {
    let map=remove(A,"A-mapping").replace("  ]}]", "  ]},{\"id\":\"w\",\"origin\":\"model\",\"subjects\":[{\"id\":\"p\",\"type\":\"Mesh.Node\",\"origin\":\"model\"}],\"atoms\":[{\"id\":\"p-owner\",\"subject\":\"p\",\"field\":\"Mesh.Node.owner\",\"value\":[\"v\",\"A\"],\"origin\":\"model\"},{\"id\":\"p-quantity\",\"subject\":\"p\",\"field\":\"Mesh.Node.quantity\",\"value\":\"0\",\"origin\":\"model\"}]}]");
    let inputs = checked(&map);
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    let mut wp = fact("p", None, false);
    wp.snapshot = "w".into();
    assert!(result.base().known().family().contains(&wp));
    assert!(result.components().iter().any(|c| c.subject() == &wp));
    assert_eq!(result.components().len(), 3);
    assert!(
        result.base().configuration().is_none(),
        "Mapは未観測のまま保持する"
    );
}
#[test]
fn explicit_none_and_container_order_remain_primitive_values() {
    let map = A
        .lines()
        .map(|line| {
            if line.contains("\"id\": \"A-choice\"") {
                line.replace(
                    "\"value\": {\"some\": [\"v\", \"x\"]}",
                    "\"value\": {\"none\": true}",
                )
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let inputs = checked(&map);
    let result = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    let base = result.base().configuration().unwrap();
    assert!(base.family().contains(&fact("A", Some("choice"), true)));
    assert!(
        !base
            .relations()
            .contains(&(fact("A", Some("choice"), true), fact("x", None, false)))
    );
    let subject = &inputs.archmap().snapshots[0].subjects[0];
    let field = subject
        .fields
        .iter()
        .find(|f| f.name == "Mesh.Root.links")
        .unwrap();
    let Slot::Known {
        value: Value::List(values),
        ..
    } = &field.slot
    else {
        panic!("links")
    };
    assert_eq!(values.len(), 3);
    assert_eq!(values[0], values[2]);
    assert_ne!(values[0], values[1]);
}
#[test]
fn invalid_reading_root_and_owned_root_selections_are_explicit() {
    let inputs = checked(A);
    for (reading, snapshot, root) in [
        ("missing", "v", "A"),
        ("MeshRead", "missing", "A"),
        ("MeshRead", "v", "absent"),
        ("MeshRead", "v", "p"),
        ("MeshRead", "v", "e"),
    ] {
        let failure =
            construct(&inputs, reading, snapshot, root, &mut Control::unlimited()).unwrap_err();
        assert!(
            matches!(failure,ConstructionFailure::InvalidSelection(ref message) if !message.is_empty())
        );
    }
}
#[test]
fn reading_definition_closure_excludes_unused_definitions_and_includes_transitive_dependencies() {
    const CD: &[u8] = include_bytes!("fixtures/counter.atoms.json");
    const CL: &[u8] = include_bytes!("fixtures/counter.law");
    const CA: &[u8] = include_bytes!("fixtures/counter.archmap.json");
    let baseline = check_inputs(
        InputSources::from_bytes(vec![CD.to_vec()], CL.to_vec(), CA.to_vec()),
        &mut Control::unlimited(),
    )
    .unwrap();
    let extended = check_inputs(
        InputSources::from_bytes(vec![CD.to_vec(), D.to_vec()], CL.to_vec(), CA.to_vec()),
        &mut Control::unlimited(),
    )
    .unwrap();
    let a = construct(&baseline, "CountCheck", "v", "s", &mut Control::unlimited()).unwrap();
    let b = construct(&extended, "CountCheck", "v", "s", &mut Control::unlimited()).unwrap();
    assert_eq!(a, b, "未使用別定義を登録しても構成は増えない");
    assert_eq!(
        a.base().configuration().unwrap().wire().canonical(),
        include_str!("fixtures/configuration-counter.expected.json").trim()
    );
    let definitions =
        archsig::definition::check_definitions(&[("definition0", CD), ("definition1", D)]).unwrap();
    let mesh_digest = &definitions.vocabularies["Mesh"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Select {{use vocabulary Mesh version \"1\" digest \"{mesh_digest}\";}}"
    );
    let isolated = check_inputs(
        InputSources::from_bytes(vec![CD.to_vec(), D.to_vec()], law.into_bytes(), CA.to_vec()),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(matches!(
        construct(&isolated, "Select", "v", "s", &mut Control::unlimited()),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
    let counter_digest = &definitions.vocabularies["Counter"].digest;
    let mesh=std::str::from_utf8(D).unwrap().replace("\"dependencies\": []",&format!("\"dependencies\": [{{\"namespace\":\"Counter\",\"version\":\"1\",\"digest\":\"{counter_digest}\"}}]"));
    let definitions = archsig::definition::check_definitions(&[
        ("definition0", CD),
        ("definition1", mesh.as_bytes()),
    ])
    .unwrap();
    let digest = &definitions.vocabularies["Mesh"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Select {{use vocabulary Mesh version \"1\" digest \"{digest}\";}}"
    );
    let dependent = check_inputs(
        InputSources::from_bytes(
            vec![CD.to_vec(), mesh.into_bytes()],
            law.into_bytes(),
            CA.to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let d = construct(&dependent, "Select", "v", "s", &mut Control::unlimited()).unwrap();
    assert_eq!(d.base(), a.base());
    assert_eq!(d.universe(), a.universe());
}
#[test]
fn recheck_uses_the_current_input_reference_graph() {
    let inputs = checked(A);
    let original = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    let map = A
        .lines()
        .map(|line| {
            if line.contains("\"id\": \"A-links\"") {
                line.replace("[\"v\", \"y\"]", "[\"v\", \"z\"]")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let current = checked(&map);
    assert!(matches!(
        original.recheck(&current, "MeshRead", "v", "A", &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let fresh = construct(&current, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert!(
        fresh
            .base()
            .known()
            .relations()
            .contains(&(fact("A", Some("links"), true), fact("z", None, false)))
    );
    fresh
        .recheck(&current, "MeshRead", "v", "A", &mut Control::unlimited())
        .unwrap();
}
#[test]
fn every_fixed_stop_rejects_unfinished_construction_and_latches_without_new_probes() {
    let inputs = checked(A);
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        assert_eq!(p, Checkpoint::Configuration);
        seen.set(seen.get() + 1);
        Usage::default()
    });
    construct(&inputs, "MeshRead", "v", "A", &mut control).unwrap();
    let total = count.get();
    assert!(total > 20);
    for at in [1, total / 2, total] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0usize));
            let seen = count.clone();
            let mut control = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |_| {
                    seen.set(seen.get() + 1);
                    let stopped = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stopped && mode == 0 { 1 } else { 0 },
                        memory_mib: if stopped && mode == 1 { 1 } else { 0 },
                        signal: if stopped {
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
            let failure = construct(&inputs, "MeshRead", "v", "A", &mut control).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(control.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(
                construct(&inputs, "MeshRead", "v", "A", &mut control).unwrap_err(),
                failure
            );
            assert_eq!(count.get(), at, "停止後probeなし");
        }
    }
}
