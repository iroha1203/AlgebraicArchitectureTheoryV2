use archsig::{
    construction::{
        ConstructionFailure, FactPointer,
        profiles::{CircuitQuery, ConfigurationProfiles, construct_profiles},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, collections::BTreeSet, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/configuration-profile.atoms.json");
const L: &str = include_str!("fixtures/configuration-profile.law");
const A: &str = include_str!("fixtures/configuration-profile.archmap.json");
fn bundle(d: &[u8], l: &str, a: &str, namespace: &str, placeholder: &str) -> CheckedInputs {
    let definitions = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &definitions.vocabularies[namespace].digest;
    check_inputs(
        InputSources::from_bytes(
            vec![d.to_vec()],
            l.replace(placeholder, digest).into_bytes(),
            a.replace(placeholder, digest).into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn inputs(a: &str) -> CheckedInputs {
    bundle(D, L, a, "Profile", "@PROFILE_DIGEST@")
}
fn profiles(i: &CheckedInputs) -> ConfigurationProfiles {
    construct_profiles(i, "ProfileRead", "v", "A", &mut Control::unlimited()).unwrap()
}
fn fact(id: &str, field: Option<&str>) -> FactPointer {
    let ty = match id {
        "A" | "B" => "Root",
        "p" | "q" => "Part",
        "x" => "External",
        _ => panic!("fixture subject"),
    };
    FactPointer {
        snapshot: "v".into(),
        subject: id.into(),
        field: field.map(|f| format!("Profile.{ty}.{f}")),
        atom: field.map(|f| format!("{id}-{f}")),
    }
}
fn slot(id: &str, field: &str) -> FactPointer {
    let mut f = fact(id, Some(field));
    f.atom = None;
    f
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
fn reverse_array(a: &str, key: &str) -> String {
    let start = a.find(&format!("\"{key}\":[\n")).unwrap() + key.len() + 5;
    let end = start + a[start..].find("\n]").unwrap();
    let mut rows: Vec<_> = a[start..end]
        .lines()
        .map(|l| l.trim_end_matches(','))
        .collect();
    rows.reverse();
    format!("{}{}{}", &a[..start], rows.join(",\n"), &a[end..])
}
#[test]
fn complete_queries_match_independent_universe_family_and_ordered_relations() {
    let i = inputs(A);
    let p = profiles(&i);
    let mut u = vec![
        fact("p", Some("owner")),
        fact("p", Some("quantity")),
        fact("q", Some("owner")),
        fact("q", Some("quantity")),
        fact("x", Some("quantity")),
    ];
    u.extend(["A", "B", "p", "q", "x"].map(|id| fact(id, None)));
    let f: BTreeSet<_> = [
        fact("A", None),
        fact("p", None),
        fact("p", Some("owner")),
        fact("p", Some("quantity")),
    ]
    .into_iter()
    .collect();
    let r: BTreeSet<_> = [
        (fact("p", None), fact("p", Some("owner"))),
        (fact("p", None), fact("p", Some("quantity"))),
        (fact("p", Some("owner")), fact("A", None)),
    ]
    .into_iter()
    .collect();
    assert_eq!(p.construction().universe(), u);
    assert!(p.is_complete());
    assert_eq!(p.classes(), Some([vec![0, 1]].as_slice()));
    for row in p.profiles() {
        let pattern = row.pattern().unwrap();
        assert_eq!(pattern.universe(), u);
        assert_eq!(
            pattern.membership(),
            u.iter().map(|a| f.contains(a)).collect::<Vec<_>>()
        );
        let mut expected = Vec::new();
        for a in &u {
            expected.push(CircuitQuery::Atom {
                atom: a,
                present: f.contains(a),
            });
        }
        for a in &u {
            for b in &u {
                expected.push(CircuitQuery::Relation {
                    left: a,
                    right: b,
                    present: r.contains(&(a.clone(), b.clone())),
                });
            }
        }
        for a in &u {
            for b in &u {
                expected.push(CircuitQuery::Identification {
                    left: a,
                    right: b,
                    present: a == b && f.contains(a),
                });
            }
        }
        assert_eq!(expected.len(), 210);
        assert_eq!(pattern.queries().collect::<Vec<_>>(), expected);
        assert_eq!(pattern.relations().iter().filter(|v| **v).count(), 3);
        assert_eq!(pattern.identifications().iter().filter(|v| **v).count(), 4);
    }
    let [base, part] = p.profiles() else {
        panic!("two objects")
    };
    assert_eq!(base.pattern(), part.pattern());
    assert_ne!(base.object(), part.object());
    assert_eq!(base.object().subject(), &fact("A", None));
    assert_eq!(part.object().subject(), &fact("p", None));
    assert_eq!(base.domain().known(), [fact("A", None), fact("p", None)]);
    assert_eq!(part.domain().known(), [fact("p", None)]);
    assert!(base.domain().is_complete());
    assert!(part.domain().is_complete());
    p.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn applicability_uses_ownership_and_does_not_follow_bare_references_in_family() {
    let i = bundle(
        include_bytes!("fixtures/configuration.atoms.json"),
        include_str!("fixtures/configuration.law"),
        include_str!("fixtures/configuration.archmap.json"),
        "Mesh",
        "@MESH_DIGEST@",
    );
    let p = construct_profiles(&i, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
    let base = &p.profiles()[0];
    let ids: Vec<_> = base
        .domain()
        .known()
        .iter()
        .map(|f| f.subject.as_str())
        .collect();
    assert_eq!(ids, ["A", "e", "p", "q"]);
    for id in ["r", "x", "y"] {
        assert!(
            base.configuration()
                .known()
                .family()
                .iter()
                .any(|f| f.subject == id && f.field.is_none())
        );
        assert!(!ids.contains(&id));
    }
    for part in &p.profiles()[1..] {
        assert_eq!(part.domain().known(), [part.object().subject().clone()]);
    }
}
#[test]
fn unknown_entity_membership_retains_condition_and_fragments_without_complete_pattern() {
    let i = inputs(&remove(A, "p-owner"));
    let p = profiles(&i);
    assert_eq!(p.construction().universe().len(), 9);
    assert!(!p.is_complete());
    assert!(p.classes().is_none());
    assert!(p.known_classes().is_empty());
    let base = &p.profiles()[0];
    assert!(base.pattern().is_none());
    assert_eq!(base.domain().known(), [fact("A", None)]);
    let [condition] = base.domain().conditional() else {
        panic!("membership condition")
    };
    assert_eq!(condition.subject(), &fact("p", None));
    assert_eq!(condition.owner_slot(), &slot("p", "owner"));
    assert_eq!(condition.owner(), &fact("A", None));
    assert!(condition.is_entity());
    let part = &p.profiles()[1];
    assert_eq!(part.membership(), Some(condition));
    assert!(part.pattern().is_none());
    assert_eq!(part.configuration().blocking_slots(), [slot("p", "owner")]);
    assert!(
        part.configuration()
            .known()
            .family()
            .contains(&fact("p", Some("quantity")))
    );
    assert!(
        !part
            .configuration()
            .known()
            .family()
            .contains(&fact("p", Some("owner")))
    );
    p.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn unknown_arrow_membership_and_reference_leave_other_known_patterns_available() {
    let d = include_bytes!("fixtures/internal-arrow.atoms.json");
    let l = include_str!("fixtures/internal-arrow.law");
    let a = include_str!("fixtures/internal-arrow.archmap.json");
    for id in ["e-owner", "p-links"] {
        let i = bundle(d, l, &remove(a, id), "Flow", "@FLOW_DIGEST@");
        let p = construct_profiles(&i, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
        assert!(!p.is_complete());
        assert!(p.classes().is_none());
        assert!(p.profiles()[0].pattern().is_none());
        assert_eq!(
            p.profiles()
                .iter()
                .map(|p| p.object().subject().subject.as_str())
                .collect::<Vec<_>>(),
            ["A", "p", "q"]
        );
        if id == "e-owner" {
            let [c] = p.profiles()[0].domain().conditional() else {
                panic!("arrow condition")
            };
            assert_eq!(c.subject().subject, "e");
            assert!(!c.is_entity());
            assert!(p.profiles()[1..].iter().all(|p| p.pattern().is_some()));
            assert_eq!(
                p.known_classes()
                    .iter()
                    .flatten()
                    .copied()
                    .collect::<BTreeSet<_>>(),
                BTreeSet::from([1, 2])
            );
        } else {
            assert!(p.construction().local_domain().is_complete());
            assert!(p.profiles()[1].pattern().is_none());
            assert!(p.profiles()[2].pattern().is_some());
            assert_eq!(
                p.profiles()[1].configuration().blocking_slots()[0]
                    .field
                    .as_deref(),
                Some("Flow.Node.links")
            );
            assert_eq!(p.known_classes(), [vec![2]]);
        }
        p.recheck(&i, &mut Control::unlimited()).unwrap();
    }
}
#[test]
fn missing_quantity_is_a_requirement_while_patterns_only_use_known_atoms() {
    let i = inputs(&remove(A, "p-quantity"));
    let p = profiles(&i);
    assert!(p.is_complete());
    assert_eq!(p.construction().universe().len(), 9);
    for row in p.profiles() {
        assert!(
            row.configuration()
                .known()
                .requirements()
                .contains(&slot("p", "quantity"))
        );
        let pattern = row.pattern().unwrap();
        assert!(!pattern.universe().contains(&fact("p", Some("quantity"))));
        assert_eq!(pattern.queries().count(), 171);
    }
    assert_eq!(p.classes(), Some([vec![0, 1]].as_slice()));
}
#[test]
fn recheck_observes_geometry_and_whole_universe_without_claiming_quantity_equality() {
    let i = inputs(A);
    let p = profiles(&i);
    let quantity = inputs(&A.replace("\"value\":\"2\"", "\"value\":\"8\""));
    p.recheck(&quantity, &mut Control::unlimited()).unwrap();
    let missing = inputs(&remove(A, "x-quantity"));
    assert!(matches!(
        p.recheck(&missing, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let owner = inputs(&A.replace("\"value\":[\"v\",\"A\"]", "\"value\":[\"v\",\"B\"]"));
    assert!(p.recheck(&owner, &mut Control::unlimited()).is_err());
    let alternative =
        construct_profiles(&i, "Alternative", "v", "A", &mut Control::unlimited()).unwrap();
    assert_ne!(p.profiles()[0].object(), alternative.profiles()[0].object());
    assert_eq!(
        p.profiles()[0].pattern(),
        alternative.profiles()[0].pattern()
    );
}
#[test]
fn source_array_order_does_not_change_known_or_conditional_profile_order() {
    for a in [A.to_owned(), remove(&remove(A, "p-owner"), "q-owner")] {
        let changed = reverse_array(&reverse_array(&a, "subjects"), "atoms");
        assert_eq!(profiles(&inputs(&a)), profiles(&inputs(&changed)));
    }
    let p = profiles(&inputs(&remove(&remove(A, "p-owner"), "q-owner")));
    assert_eq!(
        p.profiles()[0]
            .domain()
            .conditional()
            .iter()
            .map(|c| c.subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["p", "q"]
    );
}
#[test]
fn invalid_selections_return_concrete_errors() {
    let i = inputs(A);
    for (reading, snapshot, root) in [
        ("absent", "v", "A"),
        ("ProfileRead", "absent", "A"),
        ("ProfileRead", "v", "absent"),
        ("ProfileRead", "v", "p"),
    ] {
        assert!(
            matches!(construct_profiles(&i,reading,snapshot,root,&mut Control::unlimited()),Err(ConstructionFailure::InvalidSelection(message))if !message.is_empty())
        );
    }
}
#[test]
fn every_fixed_profile_stop_rejects_unfinished_results_and_latches() {
    let i = inputs(A);
    let original = profiles(&i);
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::ConfigurationProfile {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    construct_profiles(&i, "ProfileRead", "v", "A", &mut c).unwrap();
    let total = count.get();
    assert!(total > 210);
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
                    if p == Checkpoint::ConfigurationProfile {
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
            let failure = construct_profiles(&i, "ProfileRead", "v", "A", &mut c).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(c.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(original.recheck(&i, &mut c).unwrap_err(), failure);
            assert_eq!(count.get(), at);
        }
    }
}
