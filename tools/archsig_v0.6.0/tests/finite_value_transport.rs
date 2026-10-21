use archsig::{
    construction::{
        ConstructionFailure,
        maps::{
            DeclarationCorrespondence, DeclarationValuePosition as Position,
            FiniteValueConditionFailure as Failure, FiniteValueTransport, correspondence,
            declaration_correspondence, finite_declaration_value_transport,
        },
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
const L: &str = include_str!("fixtures/finite-value-transport.law");
const A: &str = include_str!("fixtures/reference-type.archmap.json");
fn inputs(a: &str) -> CheckedInputs {
    with_left(include_bytes!("fixtures/finite-value-left.atoms.json"), a)
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
                .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
                .into_bytes(),
            a.into_bytes(),
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
fn result(i: &CheckedInputs, p: usize) -> FiniteValueTransport {
    finite_declaration_value_transport(
        i,
        &declarations(i),
        "Before.axes",
        Position::Parameter(p),
        &mut Control::unlimited(),
    )
    .unwrap()
}
fn wires(values: &[archsig::construction::maps::FiniteTransportValue]) -> Vec<String> {
    values.iter().map(|v| v.wire().canonical()).collect()
}
fn expected(r: &FiniteValueTransport, source: &[&str], target: &[&str], images: &[&str]) {
    assert_eq!(wires(r.source()), source);
    assert_eq!(wires(r.target()), target);
    assert_eq!(wires(r.images()), images);
}
fn add(a: &str, subject: &str, ty: &str) -> String {
    a.replace(
        "\"subjects\": [",
        &format!(
            "\"subjects\": [\n{{\"id\":\"{subject}\",\"type\":\"{ty}\",\"origin\":\"model\"}},"
        ),
    )
}
fn many_to_one() -> String {
    add(A,"r","Left.Child").replace("\"atoms\": [", "\"atoms\": [\n{\"id\":\"r-owner\",\"subject\":\"r\",\"field\":\"Left.Child.owner\",\"value\":[\"v\",\"a\"],\"origin\":\"model\"},{\"id\":\"r-count\",\"subject\":\"r\",\"field\":\"Left.Child.count\",\"value\":\"20\",\"origin\":\"model\"},")
 .replace("[[[\"v\",\"p\"],[\"v\",\"q\"]]]", "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]")
}
#[test]
fn scalar_domains_are_complete_and_parameter_selection_is_typed() {
    let i = inputs(A);
    for (p, expected_values) in [
        (0, vec!["[]"]),
        (1, vec!["false", "true"]),
        (2, vec!["\"0\"", "\"1\"", "\"2\""]),
    ] {
        let r = result(&i, p);
        expected(&r, &expected_values, &expected_values, &expected_values);
        assert!(r.failures().is_empty());
        assert_eq!(
            r.bijection().unwrap().forward(),
            (0..expected_values.len()).collect::<Vec<_>>()
        );
        assert_eq!(
            r.bijection().unwrap().inverse(),
            r.bijection().unwrap().forward()
        );
        r.recheck(&i, &mut Control::unlimited()).unwrap();
    }
}
#[test]
fn tuple_option_and_return_domains_are_all_values_with_structural_transport() {
    let i = inputs(A);
    let r = result(&i, 5);
    expected(
        &r,
        &[
            "[{\"none\":true},false]",
            "[{\"none\":true},true]",
            "[{\"some\":[\"v\",\"p\"]},false]",
            "[{\"some\":[\"v\",\"p\"]},true]",
        ],
        &[
            "[{\"none\":true},false]",
            "[{\"none\":true},true]",
            "[{\"some\":[\"v\",\"q\"]},false]",
            "[{\"some\":[\"v\",\"q\"]},true]",
        ],
        &[
            "[{\"none\":true},false]",
            "[{\"none\":true},true]",
            "[{\"some\":[\"v\",\"q\"]},false]",
            "[{\"some\":[\"v\",\"q\"]},true]",
        ],
    );
    assert_eq!(r.bijection().unwrap().forward(), [0, 1, 2, 3]);
    let r = finite_declaration_value_transport(
        &i,
        &declarations(&i),
        "Before.returned",
        Position::Return,
        &mut Control::unlimited(),
    )
    .unwrap();
    expected(
        &r,
        &["{\"none\":true}", "{\"some\":[\"v\",\"p\"]}"],
        &["{\"none\":true}", "{\"some\":[\"v\",\"q\"]}"],
        &["{\"none\":true}", "{\"some\":[\"v\",\"q\"]}"],
    );
    assert!(r.bijection().is_some());
    assert_eq!(r.position(), Position::Return);
    assert_eq!(r.declaration(), "Before.returned");
}
#[test]
fn set_images_deduplicate_while_whole_value_domain_collisions_remain() {
    let i = inputs(&many_to_one());
    let r = result(&i, 6);
    expected(
        &r,
        &[
            "[]",
            "[[\"v\",\"p\"]]",
            "[[\"v\",\"r\"]]",
            "[[\"v\",\"p\"],[\"v\",\"r\"]]",
        ],
        &["[]", "[[\"v\",\"q\"]]"],
        &[
            "[]",
            "[[\"v\",\"q\"]]",
            "[[\"v\",\"q\"]]",
            "[[\"v\",\"q\"]]",
        ],
    );
    assert_eq!(
        r.failures(),
        [Failure::Collision {
            image: r.images()[1].clone(),
            target: Some(1),
            sources: vec![1, 2, 3]
        }]
    );
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn map_domain_is_the_complete_function_space_and_conflicting_keys_are_retained() {
    let i = inputs(&add(&many_to_one(), "n", "Bridge.Move"));
    let r = result(&i, 8);
    assert_eq!(r.source().len(), 4);
    assert_eq!(r.target().len(), 2);
    assert_eq!(
        wires(r.images()),
        [
            "[[[\"v\",\"q\"],[\"v\",\"m\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"m\"]],[[\"v\",\"q\"],[\"v\",\"n\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"n\"]],[[\"v\",\"q\"],[\"v\",\"m\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"n\"]]]"
        ]
    );
    assert!(matches!(
        r.failures(),
        [
            Failure::OutsideTarget { source: 1, .. },
            Failure::OutsideTarget { source: 2, .. },
            Failure::Collision { target: None, sources, .. }
        ] if sources == &[1,2]
    ));
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn finite_data_uses_its_real_constructors_and_does_not_erase_nested_reference_types() {
    let i = inputs(A);
    let r = result(&i, 9);
    let values = [
        "{\"args\":[],\"tag\":\"No\"}",
        "{\"args\":[false],\"tag\":\"Yes\"}",
        "{\"args\":[true],\"tag\":\"Yes\"}",
    ];
    expected(&r, &values, &values, &values);
    assert_eq!(r.bijection().unwrap().forward(), [0, 1, 2]);
    let r = result(&i, 10);
    expected(
        &r,
        &["{\"args\":[[\"v\",\"p\"]],\"tag\":\"Put\"}"],
        &["{\"args\":[[\"v\",\"p\"]],\"tag\":\"Put\"}"],
        &["{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}"],
    );
    assert!(matches!(
        r.failures(),
        [
            Failure::OutsideTarget { source: 0, .. },
            Failure::Unreached { target: 0 }
        ]
    ));
    assert!(r.bijection().is_none());
}
#[test]
fn empty_products_and_empty_map_domains_can_be_bijective_even_with_nonbijective_leaf() {
    let i = inputs(&many_to_one());
    let leaf = result(&i, 4);
    assert!(leaf.bijection().is_none());
    let r = result(&i, 12);
    assert!(r.source().is_empty());
    assert!(r.target().is_empty());
    assert!(r.bijection().unwrap().forward().is_empty());
    let r = result(&i, 11);
    expected(&r, &["[]"], &["[]"], &["[]"]);
    assert_eq!(r.bijection().unwrap().forward(), [0]);
    assert_eq!(r.bijection().unwrap().inverse(), [0]);
}
#[test]
fn unselected_and_nonfinite_positions_are_native_selection_errors() {
    let i = inputs(A);
    let d = declarations(&i);
    for (name, pos) in [
        ("Before.absent", Position::Return),
        ("Before.axes", Position::Parameter(99)),
        ("Before.stated", Position::Return),
        ("Before.recursive", Position::Return),
    ] {
        assert!(matches!(
            finite_declaration_value_transport(&i, &d, name, pos, &mut Control::unlimited()),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
    for p in [13, 14, 15, 16, 17] {
        assert!(matches!(
            finite_declaration_value_transport(
                &i,
                &d,
                "Before.axes",
                Position::Parameter(p),
                &mut Control::unlimited()
            ),
            Err(ConstructionFailure::InvalidSelection(_))
        ));
    }
}
#[test]
fn current_input_recheck_and_support_use_the_whole_frozen_roster() {
    let i = inputs(A);
    let r = result(&i, 5);
    assert_eq!(r.support().len(), 2);
    assert_eq!(
        r.snapshots().iter().map(String::as_str).collect::<Vec<_>>(),
        ["v"]
    );
    assert_eq!(
        r.modes().iter().map(String::as_str).collect::<Vec<_>>(),
        ["specification"]
    );
    let changed = inputs(&A.replace("\"value\":\"2\"", "\"value\":\"19\""));
    r.recheck(&changed, &mut Control::unlimited()).unwrap();
    let changed = inputs(&many_to_one());
    assert!(r.recheck(&changed, &mut Control::unlimited()).is_err());
}
#[test]
fn finite_value_stops_latch_across_enumeration_and_final_bijection_check() {
    let i = inputs(A);
    let d = declarations(&i);
    for point in [
        Checkpoint::FiniteValueTransport,
        Checkpoint::FiniteIteration,
    ] {
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut c = Control::new(Limits::default(), move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        finite_declaration_value_transport(&i, &d, "Before.axes", Position::Parameter(5), &mut c)
            .unwrap();
        let total = count.get();
        assert!(total > 30);
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
                let f = finite_declaration_value_transport(
                    &i,
                    &d,
                    "Before.axes",
                    Position::Parameter(5),
                    &mut c,
                )
                .unwrap_err();
                assert_eq!(f, ConstructionFailure::Stopped(c.stop_reason().unwrap()));
                assert_eq!(count.get(), at);
                assert_eq!(
                    finite_declaration_value_transport(
                        &i,
                        &d,
                        "Before.axes",
                        Position::Parameter(5),
                        &mut c
                    )
                    .unwrap_err(),
                    f
                );
                assert_eq!(count.get(), at);
            }
        }
    }
}

#[test]
fn map_bijection_enumerates_every_function_on_two_element_domains() {
    let a=add(&many_to_one(),"s","Right.Child")
        .replace("\"atoms\": [", "\"atoms\": [\n{\"id\":\"s-owner\",\"subject\":\"s\",\"field\":\"Right.Child.owner\",\"value\":[\"v\",\"b\"],\"origin\":\"model\"},{\"id\":\"s-amount\",\"subject\":\"s\",\"field\":\"Right.Child.amount\",\"value\":[\"1\",\"1\"],\"origin\":\"model\"},")
        .replace("[[\"v\",\"r\"],[\"v\",\"q\"]]","[[\"v\",\"r\"],[\"v\",\"s\"]]");
    let i = inputs(&a);
    let r = result(&i, 7);
    expected(
        &r,
        &[
            "[[[\"v\",\"p\"],[\"v\",\"p\"]],[[\"v\",\"r\"],[\"v\",\"p\"]]]",
            "[[[\"v\",\"p\"],[\"v\",\"p\"]],[[\"v\",\"r\"],[\"v\",\"r\"]]]",
            "[[[\"v\",\"p\"],[\"v\",\"r\"]],[[\"v\",\"r\"],[\"v\",\"p\"]]]",
            "[[[\"v\",\"p\"],[\"v\",\"r\"]],[[\"v\",\"r\"],[\"v\",\"r\"]]]",
        ],
        &[
            "[[[\"v\",\"q\"],[\"v\",\"q\"]],[[\"v\",\"s\"],[\"v\",\"q\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"q\"]],[[\"v\",\"s\"],[\"v\",\"s\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"s\"]],[[\"v\",\"s\"],[\"v\",\"q\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"s\"]],[[\"v\",\"s\"],[\"v\",\"s\"]]]",
        ],
        &[
            "[[[\"v\",\"q\"],[\"v\",\"q\"]],[[\"v\",\"s\"],[\"v\",\"q\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"q\"]],[[\"v\",\"s\"],[\"v\",\"s\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"s\"]],[[\"v\",\"s\"],[\"v\",\"q\"]]]",
            "[[[\"v\",\"q\"],[\"v\",\"s\"]],[[\"v\",\"s\"],[\"v\",\"s\"]]]",
        ],
    );
    assert_eq!(r.bijection().unwrap().forward(), [0, 1, 2, 3]);
    assert_eq!(r.bijection().unwrap().inverse(), [0, 1, 2, 3]);
}
#[test]
fn map_images_missing_target_keys_are_not_accepted_as_partial_functions() {
    let a=A.replace("\"snapshots\":[", "\"snapshots\":[{\"id\":\"w\",\"origin\":\"model\",\"subjects\":[{\"id\":\"root\",\"type\":\"Right.Root\",\"origin\":\"model\"},{\"id\":\"r\",\"type\":\"Right.Child\",\"origin\":\"model\"}],\"atoms\":[{\"id\":\"r-owner\",\"subject\":\"r\",\"field\":\"Right.Child.owner\",\"value\":[\"w\",\"root\"],\"origin\":\"model\"}]},");
    let i = inputs(&a);
    let r = result(&i, 7);
    assert_eq!(r.source().len(), 1);
    assert_eq!(r.target().len(), 4);
    assert!(matches!(
        r.failures(),
        [
            Failure::OutsideTarget { source: 0, .. },
            Failure::Unreached { target: 0 },
            Failure::Unreached { target: 1 },
            Failure::Unreached { target: 2 },
            Failure::Unreached { target: 3 }
        ]
    ));
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn external_references_keep_snapshot_identity_and_both_origin_modes() {
    let a=A.replace("\"origins\": [", "\"origins\": [{\"id\":\"proposal\",\"mode\":\"proposed\",\"method\":\"別snapshotの参照域。\",\"locations\":[],\"note\":\"別snapshotの固定参照。\"},")
        .replace("\"snapshots\":[", "\"snapshots\":[{\"id\":\"w\",\"origin\":\"proposal\",\"subjects\":[{\"id\":\"m\",\"type\":\"Bridge.Move\",\"origin\":\"proposal\"}],\"atoms\":[]},");
    let i = inputs(&a);
    let r = result(&i, 8);
    expected(
        &r,
        &[
            "[[[\"v\",\"p\"],[\"v\",\"m\"]]]",
            "[[[\"v\",\"p\"],[\"w\",\"m\"]]]",
        ],
        &[
            "[[[\"v\",\"q\"],[\"v\",\"m\"]]]",
            "[[[\"v\",\"q\"],[\"w\",\"m\"]]]",
        ],
        &[
            "[[[\"v\",\"q\"],[\"v\",\"m\"]]]",
            "[[[\"v\",\"q\"],[\"w\",\"m\"]]]",
        ],
    );
    assert_eq!(r.bijection().unwrap().forward(), [0, 1]);
    assert_eq!(r.support().len(), 4);
    assert_eq!(
        r.snapshots().iter().map(String::as_str).collect::<Vec<_>>(),
        ["v", "w"]
    );
    assert_eq!(
        r.modes().iter().map(String::as_str).collect::<Vec<_>>(),
        ["proposed", "specification"]
    );
}

#[test]
fn incompatible_declaration_signatures_cannot_supply_a_value_certificate() {
    let i = inputs(A);
    let s = i.sources();
    let law = std::str::from_utf8(s.law().bytes()).unwrap();
    let (before, after) = law.split_once("reading After").unwrap();
    let law = format!(
        "{before}reading After{}",
        after.replacen("u: Unit", "u: Bool", 1)
    );
    let changed = check_inputs(
        InputSources::from_bytes(
            s.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
            law.into_bytes(),
            s.archmap().bytes().to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let d = declarations(&changed);
    assert!(!d.all_signatures_compatible());
    assert!(matches!(
        finite_declaration_value_transport(
            &changed,
            &d,
            "Before.axes",
            Position::Parameter(0),
            &mut Control::unlimited()
        ),
        Err(ConstructionFailure::InvalidSelection(_))
    ));
    d.operation()
        .recheck(&changed, &mut Control::unlimited())
        .unwrap();
}
#[test]
fn subject_array_order_keeps_canonical_value_domains_and_support() {
    let a = many_to_one();
    let mut rows: Vec<_> = a.lines().collect();
    let p = rows
        .iter()
        .position(|r| r.contains("\"id\":\"p\""))
        .unwrap();
    let r = rows
        .iter()
        .position(|r| r.contains("\"id\":\"r\""))
        .unwrap();
    rows.swap(p, r);
    let b = rows.join("\n");
    let ia = inputs(&a);
    let ib = inputs(&b);
    let ra = result(&ia, 7);
    let rb = result(&ib, 7);
    assert_eq!(ra.source(), rb.source());
    assert_eq!(ra.target(), rb.target());
    assert_eq!(ra.images(), rb.images());
    assert_eq!(ra.failures(), rb.failures());
    assert_eq!(ra.support(), rb.support());
    assert_eq!(ra.bijection(), rb.bijection());
    ra.recheck(&ib, &mut Control::unlimited()).unwrap();
}

#[test]
fn nontrivial_reference_permutation_transports_maps_by_both_domain_and_codomain() {
    let base = inputs(A);
    let original = base.sources();
    let left = original.definitions()[0].bytes();
    let right = original.definitions()[1].bytes();
    let bridge = std::str::from_utf8(original.definitions()[2].bytes())
        .unwrap()
        .replace("Right.Root", "Left.Root")
        .replace("Right.Child.amount", "Left.Child.count")
        .replace("Right.Child", "Left.Child");
    let definitions = archsig::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let old_bridge = &base.definitions().vocabularies["Bridge"].digest;
    let new_bridge = &definitions.vocabularies["Bridge"].digest;
    let law = std::str::from_utf8(original.law().bytes())
        .unwrap()
        .replace(old_bridge, new_bridge);
    let (before, after) = law.split_once("reading After").unwrap();
    let law = format!(
        "{before}reading After{}",
        after
            .replace("Right.Root", "Left.Root")
            .replace("Right.Child", "Left.Child")
    );
    let a = many_to_one()
        .replace(
            "\"field\":\"Bridge.Move.to\",\"value\":[\"v\",\"b\"]",
            "\"field\":\"Bridge.Move.to\",\"value\":[\"v\",\"a\"]",
        )
        .replace(
            "[[[\"v\",\"p\"],[\"v\",\"q\"]],[[\"v\",\"r\"],[\"v\",\"q\"]]]",
            "[[[\"v\",\"p\"],[\"v\",\"r\"]],[[\"v\",\"r\"],[\"v\",\"p\"]]]",
        )
        .replace("@LEFT_DIGEST@", &definitions.vocabularies["Left"].digest)
        .replace("@RIGHT_DIGEST@", &definitions.vocabularies["Right"].digest)
        .replace("@BRIDGE_DIGEST@", new_bridge);
    let i = check_inputs(
        InputSources::from_bytes(
            vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
            law.into_bytes(),
            a.into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let r = result(&i, 7);
    assert!(r.failures().is_empty());
    assert_eq!(r.source().len(), 4);
    assert_eq!(r.source(), r.target());
    assert_eq!(r.bijection().unwrap().forward(), [3, 1, 2, 0]);
    assert_eq!(r.bijection().unwrap().inverse(), [3, 1, 2, 0]);
    for (a, b) in r.bijection().unwrap().forward().iter().enumerate() {
        assert_eq!(r.bijection().unwrap().inverse()[*b], a);
    }
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}

#[test]
fn equal_outside_target_data_images_keep_their_complete_collision_fiber() {
    let i = inputs(&many_to_one());
    let r = result(&i, 10);
    assert_eq!(
        wires(r.source()),
        [
            "{\"args\":[[\"v\",\"p\"]],\"tag\":\"Put\"}",
            "{\"args\":[[\"v\",\"r\"]],\"tag\":\"Put\"}"
        ]
    );
    assert_eq!(
        wires(r.images()),
        [
            "{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}",
            "{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}"
        ]
    );
    assert!(matches!(r.failures(),[
        Failure::OutsideTarget{source:0,..},Failure::OutsideTarget{source:1,..},
        Failure::Collision{target:None,sources,image},
        Failure::Unreached{target:0},Failure::Unreached{target:1}
    ] if sources == &[0,1] && image == &r.images()[0]));
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn outside_target_data_set_images_are_sets_before_membership_and_collision_checks() {
    let base = inputs(&many_to_one());
    let s = base.sources();
    let law = std::str::from_utf8(s.law().bytes())
        .unwrap()
        .replace("members: Set<Left.Child>", "members: Set<Left.Box>")
        .replace("members: Set<Right.Child>", "members: Set<Left.Box>");
    let i = check_inputs(
        InputSources::from_bytes(
            s.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
            law.into_bytes(),
            s.archmap().bytes().to_vec(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap();
    let r = result(&i, 6);
    assert_eq!(
        wires(r.images()),
        [
            "[]",
            "[{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}]",
            "[{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}]",
            "[{\"args\":[[\"v\",\"q\"]],\"tag\":\"Put\"}]"
        ]
    );
    assert!(matches!(r.failures(),[
        Failure::OutsideTarget{source:1,detail:a},Failure::OutsideTarget{source:2,detail:b},Failure::OutsideTarget{source:3,detail:c},
        Failure::Collision{target:None,sources,image},
        Failure::Unreached{target:1},Failure::Unreached{target:2},Failure::Unreached{target:3}
    ] if sources == &[1,2,3] && image == &r.images()[1] && [a,b,c].iter().all(|s| s.contains("payload型") && !s.contains("重複"))));
    assert!(r.bijection().is_none());
    r.operation()
        .recheck(&i, &mut Control::unlimited())
        .unwrap();
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
