use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{Counterexample, correspondence},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
const D: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const L: &[u8] = include_bytes!("fixtures/reservations.law");
const A: &str = include_str!("fixtures/reservations.archmap.json");
fn inputs(map: &str) -> CheckedInputs {
    check_inputs(
        InputSources::from_bytes(vec![D.to_vec()], L.to_vec(), map.as_bytes().to_vec()),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn reference_inputs(map: &str) -> CheckedInputs {
    let definition = include_bytes!("fixtures/configuration-map.atoms.json");
    let old = archsig::definition::check_definitions(&[("definition0", D)]).unwrap();
    let definitions =
        archsig::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &definitions.vocabularies["Reservations"].digest;
    let law = std::str::from_utf8(L)
        .unwrap()
        .replace(&old.vocabularies["Reservations"].digest, digest);
    check_inputs(
        InputSources::from_bytes(
            vec![definition.to_vec()],
            law.into_bytes(),
            map.replace("@DIGEST@", digest).into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn graph_inputs(
    list: bool,
    mapping: bool,
    links_a: &str,
    links_b: &str,
    members_a: &str,
    members_b: &str,
) -> CheckedInputs {
    let definition = include_str!("fixtures/configuration-map-graph.atoms.json");
    let definition = if list {
        definition.replace("\"Set\"", "\"List\"")
    } else {
        definition.into()
    };
    let definitions =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies["Graph"].digest;
    let map = include_str!("fixtures/configuration-map-graph.archmap.json")
        .replace("@DIGEST@", digest)
        .replace(r#""@LINKS_A@""#, links_a)
        .replace(r#""@LINKS_B@""#, links_b)
        .replace(r#""@MEMBERS_A@""#, members_a)
        .replace(r#""@MEMBERS_B@""#, members_b);
    let map = if mapping {
        map
    } else {
        map.lines()
            .filter(|line| !line.contains("m-entries"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    let law = include_str!("fixtures/configuration-map-graph.law").replace("@DIGEST@", digest);
    check_inputs(
        InputSources::from_bytes(
            vec![definition.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn bridge_inputs(rename_root_field: bool) -> CheckedInputs {
    let left = include_bytes!("fixtures/configuration-map-left.atoms.json");
    let right = include_str!("fixtures/configuration-map-right.atoms.json");
    let right = if rename_root_field {
        right.replacen("\"name\": \"count\"", "\"name\": \"other\"", 1)
    } else {
        right.into()
    };
    let definitions = archsig::definition::check_definitions(&[
        ("definition0", left),
        ("definition1", right.as_bytes()),
    ])
    .unwrap();
    let left_digest = &definitions.vocabularies["Left"].digest;
    let right_digest = &definitions.vocabularies["Right"].digest;
    let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", left_digest)
        .replace("@RIGHT_DIGEST@", right_digest);
    let definitions = archsig::definition::check_definitions(&[
        ("definition0", left),
        ("definition1", right.as_bytes()),
        ("definition2", bridge.as_bytes()),
    ])
    .unwrap();
    let law = include_str!("fixtures/configuration-map-bridge.law")
        .replace("@LEFT_DIGEST@", left_digest)
        .replace("@RIGHT_DIGEST@", right_digest);
    let map = include_str!("fixtures/configuration-map-bridge.archmap.json")
        .replace("@LEFT_DIGEST@", left_digest)
        .replace("@RIGHT_DIGEST@", right_digest)
        .replace(
            "@BRIDGE_DIGEST@",
            &definitions.vocabularies["Bridge"].digest,
        );
    let map = if rename_root_field {
        map.replace("Right.Root.count", "Right.Root.other")
    } else {
        map
    };
    check_inputs(
        InputSources::from_bytes(
            vec![left.to_vec(), right.into_bytes(), bridge.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn fact(id: &str, field: Option<&str>) -> FactPointer {
    let ty = match id {
        "A" | "B" => "System",
        "p" | "q" | "r" | "s" => "State",
        "e" | "f" => "Reserve",
        "m" => "Migration",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Reservations.{ty}.{f}")),
        atom: field.map(|f| format!("{id}-{f}")),
    }
}
fn slot(id: &str, field: &str) -> FactPointer {
    let mut f = fact(id, Some(field));
    f.atom = None;
    f
}
fn remove(map: &str, id: &str) -> String {
    map.lines()
        .filter(|l| !l.contains(&format!("\"id\": \"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n    ]", "\n    ]")
}
fn bad_endpoints() -> String {
    A.lines()
        .map(|l| {
            if l.contains("\"id\": \"m-states\"") {
                l.replace("[\"v\", \"r\"]", "[\"v\", \"temp\"]")
                    .replace("[\"v\", \"s\"]", "[\"v\", \"r\"]")
                    .replace("[\"v\", \"temp\"]", "[\"v\", \"s\"]")
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
#[test]
fn reservations_has_the_independently_expected_total_action_without_quantity_equality() {
    let inputs = inputs(A);
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.reading(), "Reservations");
    assert_eq!(result.to_reading(), "Reservations");
    assert!(result.missing().is_empty());
    assert!(result.counterexamples().is_empty());
    assert!(result.map().is_some());
    let candidate = result.candidate().unwrap();
    assert_eq!(candidate.universe().len(), 31);
    assert_eq!(candidate.images().len(), 31);
    let mut expected = BTreeMap::new();
    for (source, target, fields) in [
        ("A", "B", vec![]),
        ("p", "r", vec!["owner", "free", "held"]),
        ("q", "s", vec!["owner", "free", "held"]),
        ("e", "f", vec!["owner", "from", "to"]),
    ] {
        expected.insert(fact(source, None), fact(target, None));
        for field in fields {
            expected.insert(fact(source, Some(field)), fact(target, Some(field)));
        }
    }
    for (source, image) in candidate.universe().iter().zip(candidate.images()) {
        assert_eq!(
            image,
            expected.get(source).unwrap_or(&fact("B", None)),
            "{source:?}"
        );
    }
    let universe: BTreeSet<_> = candidate.universe().iter().collect();
    assert!(candidate.images().iter().all(|f| universe.contains(f)));
    assert_eq!(
        candidate.image(&fact("p", Some("free"))),
        Some(&fact("r", Some("free")))
    );
    assert_eq!(candidate.image(&fact("m", None)), Some(&fact("B", None)));
    assert_eq!(result.map().unwrap().candidate(), candidate);
    assert_eq!(
        candidate.source_configuration(),
        result.source().unwrap().base().configuration().unwrap()
    );
    assert_eq!(
        candidate.target_configuration(),
        result.target().unwrap().base().configuration().unwrap()
    );
    assert_eq!(candidate.reading(), "Reservations");
    assert_eq!(candidate.to_reading(), "Reservations");
    candidate
        .recheck(&inputs, &mut Control::unlimited())
        .unwrap();
    result
        .map()
        .unwrap()
        .recheck(&inputs, &mut Control::unlimited())
        .unwrap();
    result
        .recheck(
            &inputs,
            "v",
            "m",
            "Reservations",
            Some("Reservations"),
            &mut Control::unlimited(),
        )
        .unwrap();
}

#[test]
fn noninjective_sets_use_the_image_set_while_lists_retain_duplicates() {
    for list in [false, true] {
        let inputs = graph_inputs(
            list,
            true,
            "[]",
            "[]",
            r#"[["v","p"],["v","q"]]"#,
            if list {
                r#"[["v","r"],["v","r"]]"#
            } else {
                r#"[["v","r"]]"#
            },
        );
        let result = correspondence(
            &inputs,
            "v",
            "m",
            "GraphRead",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(result.missing().is_empty());
        assert!(
            result.counterexamples().is_empty(),
            "{:?}",
            result.counterexamples()
        );
        let map = result.map().expect("全域作用とF/R/Eと参照構造を保存する");
        let c = map.candidate();
        assert_eq!(
            c.image(&FactPointer {
                snapshot: "v".into(),
                subject: "p".into(),
                field: None,
                atom: None
            }),
            c.image(&FactPointer {
                snapshot: "v".into(),
                subject: "q".into(),
                field: None,
                atom: None
            })
        );
        for f in c.source_configuration().family() {
            assert!(
                c.target_configuration()
                    .family()
                    .contains(c.image(f).unwrap())
            );
        }
        for (a, b) in c.source_configuration().relations() {
            assert!(
                c.target_configuration()
                    .relations()
                    .contains(&(c.image(a).unwrap().clone(), c.image(b).unwrap().clone()))
            );
        }
        map.recheck(&inputs, &mut Control::unlimited()).unwrap();
    }
    let inputs = graph_inputs(
        true,
        true,
        "[]",
        "[]",
        r#"[["v","p"],["v","q"]]"#,
        r#"[["v","r"]]"#,
    );
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "GraphRead",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(result.candidate().is_some());
    assert!(result.map().is_none());
    assert!(matches!(
        result.counterexamples(),
        [Counterexample::ReferenceStructure { .. }]
    ));
}

#[test]
fn missing_correspondence_keeps_fixed_list_and_set_violations_without_inventing_images() {
    for (links_a, links_b, members_a, members_b, violated) in [
        (
            r#"[["v","p"]]"#,
            r#"[["v","r"],["v","r"]]"#,
            "[]",
            "[]",
            Some("links"),
        ),
        (r#"[["v","p"]]"#, r#"[["v","r"]]"#, "[]", "[]", None),
        (
            r#"[["v","p"],["v","p"]]"#,
            r#"[["v","r"],["v","s"]]"#,
            "[]",
            "[]",
            Some("links"),
        ),
        (
            r#"[["v","p"],["v","p"]]"#,
            r#"[["v","r"],["v","r"]]"#,
            "[]",
            "[]",
            None,
        ),
        (
            "[]",
            "[]",
            r#"[["v","p"]]"#,
            r#"[["v","r"],["v","s"]]"#,
            Some("members"),
        ),
        (
            "[]",
            "[]",
            r#"[["v","p"],["v","q"]]"#,
            r#"[["v","r"],["v","s"]]"#,
            None,
        ),
        (
            "[]",
            "[]",
            r#"[["v","p"],["v","q"]]"#,
            r#"[["v","r"]]"#,
            None,
        ),
    ] {
        let inputs = graph_inputs(false, false, links_a, links_b, members_a, members_b);
        let result = correspondence(
            &inputs,
            "v",
            "m",
            "GraphRead",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(result.candidate().is_none());
        assert!(result.map().is_none());
        assert_eq!(
            result.missing(),
            &[FactPointer {
                snapshot: "v".into(),
                subject: "m".into(),
                field: Some("Graph.Move.entries".into()),
                atom: None
            }]
        );
        match violated {
            Some(field) => assert!(
                matches!(result.counterexamples(), [Counterexample::ReferenceStructure {source, target}] if source.subject=="A" && target.subject=="B" && source.field.as_deref()==Some(format!("Graph.Root.{field}").as_str()))
            ),
            None => assert!(
                result.counterexamples().is_empty(),
                "{:?}",
                result.counterexamples()
            ),
        }
        result
            .recheck(
                &inputs,
                "v",
                "m",
                "GraphRead",
                None,
                &mut Control::unlimited(),
            )
            .unwrap();
    }
}

#[test]
fn empty_root_values_cannot_bypass_reference_type_transport() {
    for target_ref in ["Right.Root", "Right.Child"] {
        let left = include_str!("fixtures/configuration-map-left.atoms.json").replacen(
            "\"type\": \"Z\"",
            r#""type": ["Option", ["Ref", "Left.Child"]]"#,
            1,
        );
        let right = include_str!("fixtures/configuration-map-right.atoms.json").replacen(
            "\"type\": \"Q\"",
            &format!(r#""type": ["Option", ["Ref", "{target_ref}"]]"#),
            1,
        );
        let defs = archsig::definition::check_definitions(&[
            ("definition0", left.as_bytes()),
            ("definition1", right.as_bytes()),
        ])
        .unwrap();
        let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", &defs.vocabularies["Left"].digest)
            .replace("@RIGHT_DIGEST@", &defs.vocabularies["Right"].digest);
        let result = archsig::definition::check_definitions(&[
            ("definition0", left.as_bytes()),
            ("definition1", right.as_bytes()),
            ("definition2", bridge.as_bytes()),
        ]);
        if target_ref == "Right.Root" {
            let failure = result.unwrap_err();
            assert_eq!(failure.issue.code, archsig::issue::Code::Type);
            assert!(failure.issue.message.contains("Left.Root.count"));
            assert!(failure.issue.message.contains("Right.Root.count"));
        } else {
            let defs = result.expect("宣言の参照型が対応すれば空値も許す");
            let law = include_str!("fixtures/configuration-map-bridge.law")
                .replace("@LEFT_DIGEST@", &defs.vocabularies["Left"].digest)
                .replace("@RIGHT_DIGEST@", &defs.vocabularies["Right"].digest);
            let map = include_str!("fixtures/configuration-map-bridge.archmap.json")
                .replace("@LEFT_DIGEST@", &defs.vocabularies["Left"].digest)
                .replace("@RIGHT_DIGEST@", &defs.vocabularies["Right"].digest)
                .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
                .replacen("\"value\": \"2\"", r#""value": {"none":true}"#, 1)
                .replacen(
                    "\"value\": [\n            \"1\",\n            \"1\"\n          ]",
                    r#""value": {"none":true}"#,
                    1,
                );
            let inputs = check_inputs(
                InputSources::from_bytes(
                    vec![left.into_bytes(), right.into_bytes(), bridge.into_bytes()],
                    law.into_bytes(),
                    map.into_bytes(),
                ),
                &mut Control::unlimited(),
            )
            .unwrap();
            let result = correspondence(
                &inputs,
                "v",
                "m",
                "LeftRead",
                Some("RightRead"),
                &mut Control::unlimited(),
            )
            .unwrap();
            assert!(result.map().is_some());
            assert!(result.counterexamples().is_empty());
        }
    }
}
#[test]
fn quantity_only_root_options_do_not_require_equal_value_types() {
    let left = include_str!("fixtures/configuration-map-left.atoms.json").replacen(
        "\"type\": \"Z\"",
        r#""type": ["Option", "Z"]"#,
        1,
    );
    let right = include_str!("fixtures/configuration-map-right.atoms.json").replacen(
        "\"type\": \"Q\"",
        r#""type": ["Option", "Q"]"#,
        1,
    );
    let defs = archsig::definition::check_definitions(&[
        ("definition0", left.as_bytes()),
        ("definition1", right.as_bytes()),
    ])
    .unwrap();
    let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", &defs.vocabularies["Left"].digest)
        .replace("@RIGHT_DIGEST@", &defs.vocabularies["Right"].digest);
    assert!(
        archsig::definition::check_definitions(&[
            ("definition0", left.as_bytes()),
            ("definition1", right.as_bytes()),
            ("definition2", bridge.as_bytes())
        ])
        .is_ok()
    );
}
#[test]
fn endpoint_failure_keeps_the_candidate_and_original_reference_and_relation_counterexamples() {
    let inputs = inputs(&bad_endpoints());
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(result.candidate().is_some());
    assert!(result.map().is_none());
    assert!(result.missing().is_empty());
    assert!(
        result
            .counterexamples()
            .contains(&Counterexample::ReferenceStructure {
                source: fact("e", Some("from")),
                target: fact("f", Some("from"))
            })
    );
    assert!(
        result
            .counterexamples()
            .contains(&Counterexample::Relation {
                source: (fact("e", Some("from")), fact("p", None)),
                image: (fact("f", Some("from")), fact("s", None))
            })
    );
    assert_eq!(
        result.candidate().unwrap().image(&fact("p", None)),
        Some(&fact("s", None))
    );
}
#[test]
fn missing_endpoints_tables_and_target_atoms_never_become_complete_maps() {
    for (id, missing) in [
        ("m-from", slot("m", "from")),
        ("m-to", slot("m", "to")),
        ("m-states", slot("m", "states")),
        ("m-reserves", slot("m", "reserves")),
        ("r-free", slot("r", "free")),
    ] {
        let inputs = inputs(&remove(A, id));
        let result = correspondence(
            &inputs,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(result.candidate().is_none(), "{id}");
        assert!(result.map().is_none(), "{id}");
        assert!(result.missing().contains(&missing), "{id}");
        assert!(
            result.counterexamples().is_empty(),
            "未知の像を外部固定として反証しない: {id}"
        );
    }
}
#[test]
fn completed_counterexamples_survive_an_unrelated_missing_target_quantity() {
    let inputs = inputs(&remove(&bad_endpoints(), "r-free"));
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(result.candidate().is_none());
    assert!(result.map().is_none());
    assert!(result.missing().contains(&slot("r", "free")));
    assert!(
        result
            .counterexamples()
            .contains(&Counterexample::ReferenceStructure {
                source: fact("e", Some("from")),
                target: fact("f", Some("from"))
            })
    );
}
#[test]
fn self_correspondence_keeps_its_action_outside_the_source_family() {
    let map = A
        .lines()
        .map(|line| match () {
            _ if line.contains("\"id\": \"m-to\"") => {
                line.replace("[\"v\", \"B\"]", "[\"v\", \"A\"]")
            }
            _ if line.contains("\"id\": \"m-states\"") => line
                .replace("[\"v\", \"r\"]", "[\"v\", \"p\"]")
                .replace("[\"v\", \"s\"]", "[\"v\", \"q\"]"),
            _ if line.contains("\"id\": \"m-reserves\"") => {
                line.replace("[\"v\", \"f\"]", "[\"v\", \"e\"]")
            }
            _ => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    let inputs = inputs(&map);
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(result.map().is_some());
    let candidate = result.candidate().unwrap();
    assert_eq!(candidate.image(&fact("p", None)), Some(&fact("p", None)));
    assert_eq!(candidate.image(&fact("B", None)), Some(&fact("A", None)));
    assert_ne!(
        candidate.universe(),
        candidate.images(),
        "自己対応を全Uの空語恒等にしない"
    );
}
#[test]
fn reference_containers_are_checked_beyond_the_same_family_relation_and_action_tables() {
    let map = include_str!("fixtures/configuration-map.archmap.json");
    let inputs = reference_inputs(map);
    let good = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(good.map().is_some());
    assert!(good.counterexamples().is_empty());
    assert_eq!(good.candidate().unwrap().universe().len(), 59);
    let outside = FactPointer {
        snapshot: "v".into(),
        subject: "x".into(),
        field: Some("Reservations.External.quantity".into()),
        atom: Some("x-quantity".into()),
    };
    let external = FactPointer {
        snapshot: "v".into(),
        subject: "x".into(),
        field: None,
        atom: None,
    };
    assert_eq!(
        good.candidate().unwrap().image(&outside),
        Some(&fact("B", None))
    );
    assert_eq!(good.candidate().unwrap().image(&external), Some(&external));
    let bad = map
        .lines()
        .map(|l| {
            if l.contains("\"id\": \"r-links\"") {
                l.replace(
                    "[[\"v\", \"x\"], [\"v\", \"y\"], [\"v\", \"x\"]]",
                    "[[\"v\", \"x\"], [\"v\", \"x\"], [\"v\", \"y\"]]",
                )
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let current = reference_inputs(&bad);
    let failed = correspondence(
        &current,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(
        good.candidate(),
        failed.candidate(),
        "総作用表だけではListの順序を判定できない"
    );
    assert_eq!(
        good.target().unwrap().base(),
        failed.target().unwrap().base(),
        "F/R/Eは同じでも参照の順序は違う"
    );
    assert!(failed.map().is_none());
    good.candidate()
        .unwrap()
        .recheck(&current, &mut Control::unlimited())
        .unwrap();
    assert!(
        matches!(
            good.map()
                .unwrap()
                .recheck(&current, &mut Control::unlimited()),
            Err(ConstructionFailure::Inconsistent(_))
        ),
        "同じ作用表を保存証明として採用しない"
    );
    assert_eq!(
        failed.counterexamples(),
        &[Counterexample::ReferenceStructure {
            source: fact("p", Some("links")),
            target: fact("r", Some("links"))
        }]
    );
    assert!(matches!(
        good.recheck(
            &current,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited()
        ),
        Err(ConstructionFailure::Inconsistent(_))
    ));
}
#[test]
fn map_and_set_enumeration_order_is_ignored_while_reference_structure_is_checked() {
    let map = include_str!("fixtures/configuration-map.archmap.json");
    let baseline = reference_inputs(map);
    let expected = correspondence(
        &baseline,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    let reordered = map
        .lines()
        .map(|l| {
            if l.contains("\"id\": \"r-lookup\"") {
                l.replace(
                    "[[[\"v\", \"x\"], [\"v\", \"y\"]], [[\"v\", \"y\"], [\"v\", \"x\"]]]",
                    "[[[\"v\", \"y\"], [\"v\", \"x\"]], [[\"v\", \"x\"], [\"v\", \"y\"]]]",
                )
            } else if l.contains("\"id\": \"r-members\"") {
                l.replace(
                    "[[\"v\", \"y\"], [\"v\", \"x\"]]",
                    "[[\"v\", \"x\"], [\"v\", \"y\"]]",
                )
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let current = reference_inputs(&reordered);
    assert_eq!(
        expected,
        correspondence(
            &current,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited()
        )
        .unwrap(),
        "Map/Setの列挙順では変えない"
    );
    for (id, before, after, field) in [
        (
            "r-links",
            "[[\"v\", \"x\"], [\"v\", \"y\"], [\"v\", \"x\"]]",
            "[[\"v\", \"x\"], [\"v\", \"y\"]]",
            "links",
        ),
        (
            "r-choice",
            "{\"some\": [\"v\", \"x\"]}",
            "{\"none\": true}",
            "choice",
        ),
        (
            "r-tagged",
            "{\"tag\": \"Link\", \"args\": [[\"v\", \"y\"]]}",
            "{\"tag\": \"Link\", \"args\": [[\"v\", \"x\"]]}",
            "tagged",
        ),
    ] {
        let changed = map
            .lines()
            .map(|l| {
                if l.contains(&format!("\"id\": \"{id}\"")) {
                    assert!(l.contains(before));
                    l.replace(before, after)
                } else {
                    l.to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let inputs = reference_inputs(&changed);
        let result = correspondence(
            &inputs,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(result.candidate().is_some());
        assert!(result.map().is_none());
        assert!(
            result
                .counterexamples()
                .contains(&Counterexample::ReferenceStructure {
                    source: fact("p", Some(field)),
                    target: fact("r", Some(field))
                })
        );
    }
}
#[test]
fn different_readings_and_explicit_alignment_transport_the_actual_fields() {
    let inputs = bridge_inputs(false);
    assert!(
        matches!(
            correspondence(
                &inputs,
                "v",
                "m",
                "LeftRead",
                None,
                &mut Control::unlimited()
            ),
            Err(ConstructionFailure::InvalidSelection(_))
        ),
        "終域の読みをcorrespondence namespaceから推測しない"
    );
    assert!(matches!(
        correspondence(
            &inputs,
            "v",
            "m",
            "RightRead",
            Some("LeftRead"),
            &mut Control::unlimited()
        ),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "LeftRead",
        Some("RightRead"),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.reading(), "LeftRead");
    assert_eq!(result.to_reading(), "RightRead");
    assert!(result.map().is_some());
    let source = FactPointer {
        snapshot: "v".into(),
        subject: "p".into(),
        field: Some("Left.Child.count".into()),
        atom: Some("p-count".into()),
    };
    let target = FactPointer {
        snapshot: "v".into(),
        subject: "q".into(),
        field: Some("Right.Child.amount".into()),
        atom: Some("q-amount".into()),
    };
    assert_eq!(result.candidate().unwrap().image(&source), Some(&target));
    assert!(result.missing().is_empty());
    assert!(result.counterexamples().is_empty());
}
#[test]
fn an_absent_target_declaration_is_a_failed_rule_rather_than_a_missing_observation() {
    let inputs = bridge_inputs(true);
    let result = correspondence(
        &inputs,
        "v",
        "m",
        "LeftRead",
        Some("RightRead"),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(result.candidate().is_none());
    assert!(result.map().is_none());
    assert!(result.missing().is_empty());
    assert!(result.counterexamples().contains(&Counterexample::Field {
        source: FactPointer {
            snapshot: "v".into(),
            subject: "a".into(),
            field: Some("Left.Root.count".into()),
            atom: Some("a-count".into())
        },
        target_subject: FactPointer {
            snapshot: "v".into(),
            subject: "b".into(),
            field: None,
            atom: None
        },
        target_field: "Right.Root.count".into()
    }));
}
#[test]
fn reading_and_correspondence_selections_are_explicit() {
    let inputs = inputs(A);
    for (id, reading, to_reading) in [
        ("missing", "Reservations", None),
        ("A", "Reservations", None),
        ("m", "missing", None),
        ("m", "Reservations", Some("missing")),
    ] {
        assert!(
            matches!(correspondence(&inputs,"v",id,reading,to_reading,&mut Control::unlimited()),Err(ConstructionFailure::InvalidSelection(ref message)) if !message.is_empty())
        );
    }
}
#[test]
fn current_mapping_changes_are_rechecked_and_all_fixed_stops_latch() {
    let inputs = inputs(A);
    let original = correspondence(
        &inputs,
        "v",
        "m",
        "Reservations",
        None,
        &mut Control::unlimited(),
    )
    .unwrap();
    let current = self::inputs(&bad_endpoints());
    assert!(matches!(
        original.recheck(
            &current,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited()
        ),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::ConfigurationMap {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    correspondence(&inputs, "v", "m", "Reservations", None, &mut control).unwrap();
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
                move |p| {
                    if p == Checkpoint::ConfigurationMap {
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
            let failure =
                correspondence(&inputs, "v", "m", "Reservations", None, &mut control).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(control.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(
                original
                    .recheck(&inputs, "v", "m", "Reservations", None, &mut control)
                    .unwrap_err(),
                failure
            );
            assert_eq!(count.get(), at);
        }
    }
}
