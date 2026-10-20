use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        maps::{Counterexample, internal_arrow, internal_arrows},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, collections::BTreeMap, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/internal-arrow.atoms.json");
const L: &str = include_str!("fixtures/internal-arrow.law");
const A: &str = include_str!("fixtures/internal-arrow.archmap.json");
fn inputs(map: &str) -> CheckedInputs {
    let definitions = archsig::definition::check_definitions(&[("definition0", D)]).unwrap();
    let digest = &definitions.vocabularies["Flow"].digest;
    check_inputs(
        InputSources::from_bytes(
            vec![D.to_vec()],
            L.replace("@FLOW_DIGEST@", digest).into_bytes(),
            map.replace("@FLOW_DIGEST@", digest).into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn fact(id: &str, field: Option<&str>) -> FactPointer {
    let ty = match id {
        "A" | "B" => "Root",
        "p" | "q" | "r" => "Node",
        "e" | "f" | "g" => "Step",
        "x" | "y" => "External",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Flow.{ty}.{f}")),
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
        .filter(|l| !l.contains(&format!("\"id\":\"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
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
fn result(i: &CheckedInputs, arrow: &str) -> archsig::construction::maps::InternalArrowResult {
    internal_arrow(
        i,
        "FlowRead",
        "v",
        "A",
        "v",
        arrow,
        &mut Control::unlimited(),
    )
    .unwrap()
}
#[test]
fn internal_arrow_has_an_independent_total_action_and_fixed_complement() {
    let i = inputs(A);
    let r = result(&i, "e");
    assert!(r.map().is_some());
    assert!(r.missing().is_empty());
    assert!(r.counterexamples().is_empty());
    let c = r.candidate().unwrap();
    assert_eq!(c.subject(), &fact("e", None));
    assert!(c.correspondence().is_none());
    assert_eq!(c.source_object().root(), &fact("A", None));
    assert_eq!(c.source_object().subject(), &fact("p", None));
    assert_eq!(c.target_object().subject(), &fact("q", None));
    assert_eq!(c.source_object().reading(), "FlowRead");
    assert_eq!(c.universe().len(), 45);
    assert_eq!(c.images().len(), 45);
    assert_eq!(r.source().unwrap().candidate().known().family().len(), 13);
    assert_eq!(
        r.source().unwrap().candidate().known().relations().len(),
        21
    );
    assert_eq!(
        r.source()
            .unwrap()
            .candidate()
            .known()
            .identifications()
            .len(),
        13
    );
    let moved: BTreeMap<_, _> = [
        None,
        Some("owner"),
        Some("quantity"),
        Some("links"),
        Some("pair"),
        Some("choice"),
        Some("tagged"),
        Some("lookup"),
        Some("members"),
    ]
    .into_iter()
    .map(|f| (fact("p", f), fact("q", f)))
    .collect();
    for f in c.universe() {
        assert_eq!(c.image(f), Some(moved.get(f).unwrap_or(f)), "{f:?}");
    }
    assert_eq!(
        c.image(&fact("x", Some("quantity"))),
        Some(&fact("x", Some("quantity")))
    );
    assert_eq!(
        c.image(&fact("e", Some("from"))),
        Some(&fact("e", Some("from")))
    );
    c.recheck(&i, &mut Control::unlimited()).unwrap();
    r.map()
        .unwrap()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn all_internal_arrows_are_kept_instead_of_dropping_failed_or_unknown_ones() {
    let i = inputs(A);
    let all = internal_arrows(&i, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert_eq!(
        all.arrows()
            .iter()
            .map(|a| a.arrow().subject.as_str())
            .collect::<Vec<_>>(),
        vec!["e", "f"]
    );
    assert!(all.all_preserved());
    let other = internal_arrows(&i, "FlowRead", "v", "B", &mut Control::unlimited()).unwrap();
    assert_eq!(
        other
            .arrows()
            .iter()
            .map(|a| a.arrow().subject.as_str())
            .collect::<Vec<_>>(),
        vec!["g"]
    );
    let bad = edit(
        A,
        "q-links",
        r#"[["v","q"],["v","r"],["v","q"]]"#,
        r#"[["v","r"],["v","q"],["v","q"]]"#,
    );
    let i = inputs(&remove(&bad, "g-owner"));
    let all = internal_arrows(&i, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert_eq!(
        all.arrows()
            .iter()
            .map(|a| a.arrow().subject.as_str())
            .collect::<Vec<_>>(),
        vec!["e", "f", "g"]
    );
    assert!(!all.all_preserved());
    assert!(all.arrows()[0].candidate().is_some());
    assert!(all.arrows()[0].map().is_none());
    assert!(
        all.arrows()[0]
            .counterexamples()
            .contains(&Counterexample::ReferenceStructure {
                source: fact("p", Some("links")),
                target: fact("q", Some("links"))
            })
    );
    assert_eq!(all.arrows()[2].missing(), &[slot("g", "owner")]);
    assert!(all.arrows()[2].candidate().is_none());
    assert!(all.arrows()[2].map().is_none());
    assert!(all.arrows()[2].source().is_none());
    all.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn quantity_differences_do_not_replace_reference_structure_preservation() {
    let good = inputs(A);
    let r = result(&good, "e");
    for (id, before, after) in [
        (
            "q-links",
            r#"[["v","q"],["v","r"],["v","q"]]"#,
            r#"[["v","r"],["v","q"],["v","q"]]"#,
        ),
        (
            "q-links",
            r#"[["v","q"],["v","r"],["v","q"]]"#,
            r#"[["v","q"],["v","r"]]"#,
        ),
        (
            "q-pair",
            r#"[["v","q"],{"some":["v","x"]}]"#,
            r#"[["v","p"],{"some":["v","x"]}]"#,
        ),
        ("q-choice", r#"{"some":["v","q"]}"#, r#"{"none":true}"#),
        (
            "q-tagged",
            r#"{"tag":"Link","args":[["v","q"]]}"#,
            r#"{"tag":"Link","args":[["v","p"]]}"#,
        ),
        (
            "q-lookup",
            r#"[[["v","x"],["v","q"]],[["v","y"],["v","r"]]]"#,
            r#"[[["v","x"],["v","r"]],[["v","y"],["v","q"]]]"#,
        ),
        ("q-members", r#"[["v","q"],["v","r"]]"#, r#"[["v","q"]]"#),
    ] {
        let current = inputs(&edit(A, id, before, after));
        let failed = result(&current, "e");
        assert!(failed.candidate().is_some(), "{id}");
        assert!(failed.map().is_none(), "{id}");
        assert!(
            failed
                .counterexamples()
                .iter()
                .any(|c| matches!(c, Counterexample::ReferenceStructure { .. })),
            "{id}"
        );
        assert!(
            matches!(
                r.map()
                    .unwrap()
                    .recheck(&current, &mut Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "{id}"
        );
    }
    let current = inputs(&edit(
        A,
        "q-links",
        r#"[["v","q"],["v","r"],["v","q"]]"#,
        r#"[["v","r"],["v","q"],["v","q"]]"#,
    ));
    let failed = result(&current, "e");
    assert_eq!(
        r.candidate(),
        failed.candidate(),
        "同じF/R/Eと作用でも順序変更は保存されない"
    );
    r.candidate()
        .unwrap()
        .recheck(&current, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn missing_endpoints_owners_references_and_target_atoms_do_not_make_complete_maps() {
    for (id, who, f) in [
        ("e-owner", "e", "owner"),
        ("e-from", "e", "from"),
        ("e-to", "e", "to"),
        ("p-owner", "p", "owner"),
        ("q-owner", "q", "owner"),
        ("p-links", "p", "links"),
        ("q-links", "q", "links"),
        ("q-quantity", "q", "quantity"),
    ] {
        let i = inputs(&remove(A, id));
        let r = result(&i, "e");
        assert!(r.candidate().is_none(), "{id}");
        assert!(r.map().is_none(), "{id}");
        assert!(
            r.missing().contains(&slot(who, f)),
            "{id}: {:?}",
            r.missing()
        );
        r.recheck(&i, &mut Control::unlimited()).unwrap();
    }
    let i = inputs(&remove(A, "p-quantity"));
    let r = result(&i, "e");
    assert!(r.map().is_some(), "未観測のsource数量は参照構成を妨げない");
    assert!(
        r.source()
            .unwrap()
            .candidate()
            .known()
            .requirements()
            .contains(&slot("p", "quantity"))
    );
}
#[test]
fn unknown_membership_does_not_erase_an_independent_reference_counterexample() {
    let bad = edit(
        A,
        "q-links",
        r#"[["v","q"],["v","r"],["v","q"]]"#,
        r#"[["v","r"],["v","q"],["v","q"]]"#,
    );
    let i = inputs(&remove(&bad, "e-owner"));
    let r = result(&i, "e");
    assert_eq!(r.missing(), &[slot("e", "owner")]);
    assert!(r.candidate().is_none());
    assert!(r.map().is_none());
    assert!(
        r.counterexamples()
            .contains(&Counterexample::ReferenceStructure {
                source: fact("p", Some("links")),
                target: fact("q", Some("links"))
            })
    );
}
#[test]
fn map_and_set_order_does_not_change_a_preserved_internal_arrow() {
    let map = edit(
        A,
        "q-lookup",
        r#"[[["v","x"],["v","q"]],[["v","y"],["v","r"]]]"#,
        r#"[[["v","y"],["v","r"]],[["v","x"],["v","q"]]]"#,
    );
    let map = edit(
        &map,
        "q-members",
        r#"[["v","q"],["v","r"]]"#,
        r#"[["v","r"],["v","q"]]"#,
    );
    assert_eq!(result(&inputs(A), "e"), result(&inputs(&map), "e"));
}
#[test]
fn selections_and_current_arrow_provenance_are_checked() {
    let i = inputs(A);
    let r = result(&i, "e");
    for (reading, root, arrow) in [
        ("missing", "A", "e"),
        ("FlowRead", "p", "e"),
        ("FlowRead", "A", "p"),
        ("FlowRead", "B", "e"),
        ("FlowRead", "A", "missing"),
    ] {
        assert!(matches!(
            internal_arrow(
                &i,
                reading,
                "v",
                root,
                "v",
                arrow,
                &mut Control::unlimited()
            ),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
    let other = internal_arrow(
        &i,
        "OtherRead",
        "v",
        "A",
        "v",
        "e",
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_ne!(
        r.candidate().unwrap().source_object(),
        other.candidate().unwrap().source_object()
    );
    let current = inputs(&edit(A, "e-to", r#"["v","q"]"#, r#"["v","p"]"#));
    assert!(matches!(
        r.recheck(&current, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    assert!(matches!(
        r.candidate()
            .unwrap()
            .recheck(&current, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let all = internal_arrows(&i, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
    assert!(matches!(
        all.recheck(&current, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
}
#[test]
fn endpoint_and_object_identity_keep_full_snapshot_references() {
    let mut target = Vec::new();
    for line in A.lines() {
        if line.contains("\"subject\":\"q\"") || line.contains("\"subject\":\"e\"") {
            target.push(
                line.replace("[\"v\",\"q\"]", "[\"next\",\"q\"]")
                    .replace("[\"v\",\"p\"]", "[\"next\",\"q\"]")
                    .replace("[\"v\",\"A\"]", "[\"next\",\"A\"]")
                    .trim_end_matches(',')
                    .to_owned(),
            );
        }
    }
    let map = A.replace("\n}]\n}", &format!(
        "\n}},{{\"id\":\"next\",\"origin\":\"model\",\"subjects\":[{{\"id\":\"A\",\"type\":\"Flow.Root\",\"origin\":\"model\"}},{{\"id\":\"q\",\"type\":\"Flow.Node\",\"origin\":\"model\"}},{{\"id\":\"e\",\"type\":\"Flow.Step\",\"origin\":\"model\"}}],\"atoms\":[{}]}}]\n}}", target.join(",")));
    let i = inputs(&map);
    let r = result(&i, "e");
    assert!(r.map().is_some());
    let c = r.candidate().unwrap();
    assert_eq!(c.universe().len(), 59);
    let mut q = fact("q", None);
    q.snapshot = "next".into();
    assert_eq!(c.image(&q), Some(&q));
    assert!(c.universe().contains(&q));
    assert!(c.universe().contains(&fact("q", None)));
    let next = internal_arrows(&i, "FlowRead", "next", "A", &mut Control::unlimited()).unwrap();
    assert_eq!(next.arrows().len(), 1);
    assert!(next.all_preserved());
    let selected = next.arrows()[0].candidate().unwrap().source_object();
    assert_eq!(selected.subject(), &q);
    assert_eq!(selected.root().snapshot, "next");
    assert_ne!(c.target_object(), selected);
    assert_eq!(
        internal_arrows(&i, "FlowRead", "v", "A", &mut Control::unlimited())
            .unwrap()
            .arrows()
            .len(),
        2
    );
    r.recheck(&i, &mut Control::unlimited()).unwrap();
    next.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn reservations_internal_arrow_moves_only_its_source_subject_and_fields() {
    let i = check_inputs(
        InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
            include_bytes!("fixtures/reservations.law").to_vec(),
            include_bytes!("fixtures/reservations.archmap.json").to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let all = internal_arrows(&i, "Reservations", "v", "A", &mut Control::unlimited()).unwrap();
    assert_eq!(all.arrows().len(), 1);
    assert!(all.all_preserved());
    let r = &all.arrows()[0];
    let c = r.candidate().unwrap();
    assert_eq!(r.arrow().subject, "e");
    assert_eq!(c.universe().len(), 31);
    assert_eq!(c.source_configuration().family().len(), 5);
    assert_eq!(c.source_configuration().relations().len(), 4);
    assert_eq!(c.source_configuration().identifications().len(), 5);
    for f in c.universe() {
        let mut expected = f.clone();
        if f.subject == "p" {
            expected.subject = "q".into();
            expected.atom = expected.atom.map(|a| a.replacen("p-", "q-", 1));
        }
        assert_eq!(c.image(f), Some(&expected), "{f:?}");
    }
    assert!(c.correspondence().is_none());
    all.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn noninjective_internal_set_images_and_reference_relations_are_checked() {
    let map = edit(
        A,
        "p-members",
        r#"[["v","p"],["v","r"]]"#,
        r#"[["v","p"],["v","q"]]"#,
    );
    let map = edit(
        &map,
        "q-members",
        r#"[["v","q"],["v","r"]]"#,
        r#"[["v","q"]]"#,
    );
    let i = inputs(&map);
    let r = result(&i, "e");
    assert!(r.map().is_some(), "集合の像ではpとqの重複を縮約する");
    let i = inputs(&edit(
        A,
        "q-members",
        r#"[["v","q"],["v","r"]]"#,
        r#"[["v","q"]]"#,
    ));
    let r = result(&i, "e");
    assert!(r.candidate().is_some());
    assert!(r.map().is_none());
    assert!(r.counterexamples().contains(&Counterexample::Relation {
        source: (fact("p", Some("members")), fact("r", None)),
        image: (fact("q", Some("members")), fact("r", None)),
    }));
}
#[test]
fn all_fixed_internal_arrow_stops_latch_the_shared_control() {
    let i = inputs(A);
    let original = internal_arrows(&i, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::InternalArrow {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    internal_arrows(&i, "FlowRead", "v", "A", &mut control).unwrap();
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
                    if p == Checkpoint::InternalArrow {
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
            let failure = internal_arrows(&i, "FlowRead", "v", "A", &mut control).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(control.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(original.recheck(&i, &mut control).unwrap_err(), failure);
            assert_eq!(count.get(), at);
            assert_eq!(
                original.arrows()[0]
                    .map()
                    .unwrap()
                    .recheck(&i, &mut control)
                    .unwrap_err(),
                failure
            );
            assert_eq!(count.get(), at);
        }
    }
}
