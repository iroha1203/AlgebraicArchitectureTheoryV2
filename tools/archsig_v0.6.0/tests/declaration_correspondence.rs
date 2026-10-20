use archsig::{
    construction::{
        ConstructionFailure,
        maps::{
            DeclarationConditionFailure as Failure, DeclarationCorrespondence, correspondence,
            declaration_correspondence, identity,
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
const L: &str = include_str!("fixtures/declaration-correspondence.law");
fn sources(law: &str) -> InputSources {
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
    let a = include_str!("fixtures/configuration-map-bridge.archmap.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd)
        .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest);
    InputSources::from_bytes(
        vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
        law.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .into_bytes(),
        a.into_bytes(),
    )
}
fn inputs(law: &str) -> CheckedInputs {
    check_inputs(sources(law), &mut Control::unlimited())
        .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn result(i: &CheckedInputs) -> DeclarationCorrespondence {
    let m = correspondence(
        i,
        "v",
        "m",
        "Before",
        Some("After"),
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(m.missing().is_empty());
    assert!(m.counterexamples().is_empty());
    declaration_correspondence(i, m.map().unwrap(), &mut Control::unlimited()).unwrap()
}
#[test]
fn all_five_kinds_match_only_selected_readings_with_positional_owner_and_compound_types() {
    let i = inputs(L);
    let r = result(&i);
    assert!(r.all_signatures_compatible());
    assert_eq!(
        r.types(),
        [
            ("Left.Child".into(), "Right.Child".into()),
            ("Left.Root".into(), "Right.Root".into())
        ]
    );
    assert_eq!(r.candidates().len(), 9);
    assert_eq!(
        r.candidates()
            .iter()
            .map(|c| c.source().name.as_str())
            .collect::<Vec<_>>(),
        [
            "Before.Amount",
            "Before.again",
            "Before.amount",
            "Before.bounded",
            "Before.bump",
            "Before.owned",
            "Before.packed",
            "Before.paths",
            "Before.procedure"
        ]
    );
    for c in r.candidates() {
        assert!(c.failures().is_empty());
        let p = c.pair().unwrap();
        assert_eq!(p.source(), c.source().name);
        assert_eq!(p.target(), c.target().unwrap().name);
        assert_eq!(p.parameters().len(), c.source().parameters.len());
        for ((s, t), ((sn, _), (tn, _))) in p.parameters().iter().zip(
            c.source()
                .parameters
                .iter()
                .zip(&c.target().unwrap().parameters),
        ) {
            assert_eq!((s, t), (sn, tn));
        }
    }
    let owned = r
        .candidates()
        .iter()
        .find(|c| c.source().name == "Before.owned")
        .unwrap();
    assert_eq!(
        owned.pair().unwrap().parameters(),
        [
            ("a".into(), "x".into()),
            ("b".into(), "y".into()),
            ("c".into(), "k".into())
        ]
    );
    assert_eq!(
        owned.source().parameters[2].1,
        Type::Owned("Left.Child".into(), "a".into())
    );
    assert_eq!(
        owned.target().unwrap().parameters[2].1,
        Type::Owned("Right.Child".into(), "x".into())
    );
    let amount = r
        .candidates()
        .iter()
        .find(|c| c.source().name == "Before.amount")
        .unwrap();
    assert!(
        amount
            .source()
            .dependencies
            .contains(&"Helper.external".into())
    );
    assert!(
        amount
            .source()
            .references
            .iter()
            .any(|(_, n)| n == "Helper.external")
    );
    assert_ne!(
        amount.source().expressions,
        amount.target().unwrap().expressions
    );
    let bounded = r
        .candidates()
        .iter()
        .find(|c| c.source().name == "Before.bounded")
        .unwrap();
    assert_ne!(bounded.source().role, bounded.target().unwrap().role);
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
fn candidate<'a>(
    r: &'a DeclarationCorrespondence,
    name: &str,
) -> &'a archsig::construction::maps::DeclarationCandidate {
    r.candidates()
        .iter()
        .find(|c| c.source().name == format!("Before.{name}"))
        .unwrap()
}
fn edit(before: &str, after: &str) -> String {
    assert_eq!(L.matches(before).count(), 1);
    L.replace(before, after)
}
#[test]
fn missing_wrong_kind_and_different_short_name_do_not_use_aliases_or_other_readings() {
    let line = "  view amount(k: Child): Z = 9;";
    for (law, kind) in [
        (edit(line, ""), 0),
        (edit(line, "  view renamed(k: Child): Z = 9;"), 0),
        (edit(line, "  law optional amount(k: Child): true;"), 1),
    ] {
        let i = inputs(&law);
        let r = result(&i);
        assert!(!r.all_signatures_compatible());
        assert_eq!(r.candidates().len(), 9);
        assert_eq!(
            r.candidates().iter().filter(|c| c.pair().is_some()).count(),
            8
        );
        let c = candidate(&r, "amount");
        assert!(c.pair().is_none());
        if kind == 0 {
            assert!(c.target().is_none());
            assert_eq!(
                c.failures(),
                [Failure::Missing {
                    name: "After.amount".into()
                }]
            );
        } else {
            assert_eq!(c.target().unwrap().name, "After.amount");
            assert_eq!(
                c.failures(),
                [Failure::Kind {
                    expected: "view",
                    actual: "law"
                }]
            );
        }
        assert!(i.law().declarations.contains_key("Decoy.amount"));
        r.operation()
            .recheck(&i, &mut Control::unlimited())
            .unwrap();
        r.recheck(&i, &mut Control::unlimited()).unwrap();
    }
}
#[test]
fn arity_and_owner_positions_are_checked_without_erasing_dependencies() {
    let original = "view owned(x: Root, y: Root, k: Child[x])";
    let i = inputs(&edit(original, "view owned(x: Root, y: Root)"));
    let r = result(&i);
    let c = candidate(&r, "owned");
    assert_eq!(
        c.failures(),
        [Failure::Arity {
            source: 3,
            target: 2
        }]
    );
    assert!(c.pair().is_none());
    assert_eq!(c.source().parameters.len(), 3);
    assert_eq!(c.target().unwrap().parameters.len(), 2);
    let i = inputs(&edit(original, "view owned(x: Root, y: Root, k: Child[y])"));
    let r = result(&i);
    let c = candidate(&r, "owned");
    assert_eq!(
        c.failures(),
        [Failure::Parameter {
            position: 2,
            expected: Type::Owned("Right.Child".into(), "x".into()),
            actual: Type::Owned("Right.Child".into(), "y".into())
        }]
    );
    assert!(c.pair().is_none());
    assert_eq!(
        r.candidates().iter().filter(|c| c.pair().is_some()).count(),
        8
    );
}
#[test]
fn compound_parameter_scalar_and_view_return_mismatches_keep_exact_types() {
    let law = edit(
        "values: List<Option<(Child[x], Z)>>",
        "values: List<Option<(Child[x], Bool)>>",
    );
    let r = result(&inputs(&law));
    let c = candidate(&r, "packed");
    let ty = |t| {
        Type::List(Box::new(Type::Option(Box::new(Type::Tuple(vec![
            Type::Owned("Right.Child".into(), "x".into()),
            t,
        ])))))
    };
    assert_eq!(
        c.failures(),
        [Failure::Parameter {
            position: 1,
            expected: ty(Type::Z),
            actual: ty(Type::Bool)
        }]
    );
    assert!(c.pair().is_none());
    let r = result(&inputs(&edit(
        "law optional bounded(x: Root, k: Child[x], shift: Z)",
        "law optional bounded(x: Root, k: Child[x], shift: Q)",
    )));
    assert_eq!(
        candidate(&r, "bounded").failures(),
        [Failure::Parameter {
            position: 2,
            expected: Type::Z,
            actual: Type::Q
        }]
    );
    let r = result(&inputs(&edit(
        "view amount(k: Child): Z = 9;",
        "view amount(k: Child): Bool = false;",
    )));
    assert_eq!(
        candidate(&r, "amount").failures(),
        [Failure::Return {
            expected: Type::Z,
            actual: Some(Type::Bool)
        }]
    );
}
#[test]
fn term_value_types_are_preserved_and_path_endpoints_are_transported() {
    let i = inputs(L);
    let r = result(&i);
    let term = Type::Term(
        vec![Type::Z, Type::Bool],
        Box::new(Type::Option(Box::new(Type::Z))),
    );
    let c = candidate(&r, "procedure");
    assert_eq!(c.source().parameters[1].1, term);
    assert_eq!(c.target().unwrap().parameters[1].1, term);
    assert!(c.pair().is_some());
    let paths = candidate(&r, "paths");
    assert_eq!(
        paths.target().unwrap().parameters[0].1,
        Type::Path("Right.Child".into(), "Right.Child".into())
    );
    let law = edit(
        "view paths(w: Path<Child, Child>): Path<Child, Child> = w;",
        "view paths(w: Path<Child, Root>): Path<Child, Root> = w;",
    );
    let r = result(&inputs(&law));
    let p = candidate(&r, "paths");
    assert_eq!(
        p.failures(),
        [
            Failure::Parameter {
                position: 0,
                expected: Type::Path("Right.Child".into(), "Right.Child".into()),
                actual: Type::Path("Right.Child".into(), "Right.Root".into())
            },
            Failure::Return {
                expected: Type::Path("Right.Child".into(), "Right.Child".into()),
                actual: Some(Type::Path("Right.Child".into(), "Right.Root".into()))
            }
        ]
    );
    let law = L.replacen(
        "Term<(Z, Bool) -> Option<Z>>",
        "Term<(Child, Bool) -> Option<Z>>",
        1,
    );
    let failure = check_inputs(sources(&law), &mut Control::unlimited()).unwrap_err();
    assert!(
        failure
            .issues()
            .iter()
            .any(|issue| issue.canonical().contains("Term の引数・戻り型は参照"))
    );
}
#[test]
fn current_declaration_metadata_is_rechecked_and_quantity_changes_do_not_define_signatures() {
    let i = inputs(L);
    let r = result(&i);
    let changed = inputs(&edit(
        "view owned(x: Root, y: Root, k: Child[x])",
        "view owned(x: Root, y: Root, k: Child[y])",
    ));
    r.operation()
        .map()
        .recheck(&changed, &mut Control::unlimited())
        .unwrap();
    assert!(r.recheck(&changed, &mut Control::unlimited()).is_err());
    let s = sources(L);
    let map = std::str::from_utf8(s.archmap().bytes())
        .unwrap()
        .replace("\"value\": \"2\"", "\"value\": \"17\"");
    let changed = check_inputs(
        InputSources::from_bytes(
            s.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
            s.law().bytes().to_vec(),
            map.into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    r.recheck(&changed, &mut Control::unlimited()).unwrap();
}
#[test]
fn declaration_input_order_keeps_pairs_and_updates_original_positions() {
    let start = L.find("  view amount(k:").unwrap();
    let end = start + L[start..].find("\n}").unwrap();
    let mut lines: Vec<_> = L[start..end].lines().collect();
    lines.reverse();
    let changed = format!("{}{}{}", &L[..start], lines.join("\n"), &L[end..]);
    let a = result(&inputs(L));
    let b = result(&inputs(&changed));
    assert_eq!(
        a.candidates().iter().map(|c| c.pair()).collect::<Vec<_>>(),
        b.candidates().iter().map(|c| c.pair()).collect::<Vec<_>>()
    );
    assert_ne!(
        candidate(&a, "amount").target().unwrap().span,
        candidate(&b, "amount").target().unwrap().span
    );
    assert!(
        a.recheck(&inputs(&changed), &mut Control::unlimited())
            .is_err()
    );
}
#[test]
fn internal_identity_and_composite_maps_cannot_supply_declaration_correspondence() {
    let i = inputs(L);
    let id = identity(&i, "Before", "v", "a", None, &mut Control::unlimited())
        .unwrap()
        .operation()
        .unwrap()
        .clone();
    let composed = id.compose(&i, &id, &mut Control::unlimited()).unwrap();
    for map in [id.map(), composed.map()] {
        assert!(
            matches!(declaration_correspondence(&i,map,&mut Control::unlimited()),Err(ConstructionFailure::InvalidSelection(message))if !message.is_empty())
        );
    }
    let i = check_inputs(
        InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
            include_bytes!("fixtures/reservations.law").to_vec(),
            include_bytes!("fixtures/reservations.archmap.json").to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let e = archsig::construction::maps::internal_arrow(
        &i,
        "Reservations",
        "v",
        "A",
        "v",
        "e",
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(matches!(
        declaration_correspondence(&i, e.map().unwrap(), &mut Control::unlimited()),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
}
#[test]
fn every_fixed_declaration_stop_latches_without_new_probes() {
    let i = inputs(L);
    let r = result(&i);
    let map = r.operation().map();
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut c = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::DeclarationCorrespondence {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    declaration_correspondence(&i, map, &mut c).unwrap();
    let total = count.get();
    assert!(total > 100);
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
                    if p == Checkpoint::DeclarationCorrespondence {
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
            let failure = declaration_correspondence(&i, map, &mut c).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(c.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(r.recheck(&i, &mut c).unwrap_err(), failure);
            assert_eq!(count.get(), at);
        }
    }
}
