use super::super::super::finite_law_valuations::{FiniteLawState, finite_law_family_valuations};
use super::*;
use crate::{canonical::Json, input::InputSources, json::parse};

fn quantity_input(mark_type: Json, extra: &str) -> Arc<CheckedInputs> {
    typed_input(mark_type, None, vec![], extra)
}
fn typed_input(
    mark_type: Json,
    value: Option<Json>,
    additions: Vec<Json>,
    extra: &str,
) -> Arc<CheckedInputs> {
    let original = arrow_fixture::input("normal", "path-quantity");
    let mut defs = map_fixture::convert(&parse(original.definitions()[0].bytes()).unwrap());
    let Json::Obj(root) = &mut defs else { panic!() };
    let Json::Arr(vocabs) = root.get_mut("vocabularies").unwrap() else {
        panic!()
    };
    let Json::Obj(vocab) = &mut vocabs[0] else {
        panic!()
    };
    let Json::Arr(declarations) = vocab.get_mut("declarations").unwrap() else {
        panic!()
    };
    for d in declarations.iter_mut() {
        let Json::Obj(d) = d else { panic!() };
        if d["name"] == Json::str("Paths.Node") {
            let Json::Arr(fields) = d.get_mut("fields").unwrap() else {
                panic!()
            };
            fields.retain(|f| matches!(f,Json::Obj(f)if f["name"]==Json::str("mark")));
            let Json::Obj(mark) = &mut fields[0] else {
                panic!()
            };
            mark.insert("type".into(), mark_type.clone());
        }
    }
    declarations.extend(additions);
    let defs = defs.canonical();
    let checked_defs =
        crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &checked_defs.vocabularies["Paths"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Walk{{use vocabulary Paths version \"1\" digest \"{digest}\";view step(e:Hop):Path<Node,Node> =path(e);law required exact(e:Hop):path(e)=path(e);{extra}}}"
    );
    let mut map = map_fixture::convert(&parse(original.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(vocabs) = root.get_mut("vocabularies").unwrap() else {
        panic!()
    };
    let Json::Obj(vocab) = &mut vocabs[0] else {
        panic!()
    };
    vocab.insert("digest".into(), Json::str(digest));
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    snapshots.retain(|s| matches!(s,Json::Obj(s)if s["id"]==Json::str("v")));
    let Json::Obj(snapshot) = &mut snapshots[0] else {
        panic!()
    };
    let Json::Arr(atoms) = snapshot.get_mut("atoms").unwrap() else {
        panic!()
    };
    atoms.retain(|a| {
        let Json::Obj(a) = a else { panic!() };
        let Json::Str(field) = &a["field"] else {
            panic!()
        };
        !field.starts_with("Paths.Node.")
            || matches!(field.as_str(), "Paths.Node.owner" | "Paths.Node.mark")
    });
    if let Some(value) = value {
        for a in atoms {
            let Json::Obj(a) = a else { panic!() };
            if a["field"] == Json::str("Paths.Node.mark") {
                a.insert("value".into(), value.clone());
            }
        }
    }
    checked(InputSources::from_bytes(
        vec![defs.into_bytes()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    ))
}
#[test]
fn integer_quantities_do_not_make_finite_path_endpoints_infinite() {
    let i = quantity_input(Json::str("Z"), "");
    let bytes = i.sources().clone();
    let selected = [(
        "Walk.exact".into(),
        vec![("e".into(), reference("Paths.Hop", "e"))],
    )];
    let r = finite_law_family_valuations(&i, &selected, &mut quiet()).unwrap();
    assert_eq!(r.state(), &FiniteLawState::Ready);
    assert!(r.domain_complete());
    assert_eq!(r.domain().len(), 9);
    assert_eq!(r.columns()[0].rows().len(), 9);
    assert!(
        !r.positions()
            .iter()
            .any(|f| f.field.as_deref() == Some("Paths.Node.mark"))
    );
    let mut counts = BTreeMap::<(String, String), usize>::new();
    for row in r.columns()[0].rows() {
        assert_eq!(row.indicator, Some(0.into()));
        let (_, Some(Scalar::Path(a)), Some(Scalar::Path(b))) = row.operands.as_ref().unwrap()
        else {
            panic!()
        };
        assert_eq!(a, b);
        let target = a.target();
        let Scalar::Subject { subject, .. } = &target else {
            panic!()
        };
        *counts
            .entry((a.subject.clone(), subject.clone()))
            .or_default() += 1;
        assert_eq!(subject_image(a, "v", &a.subject).subject, *subject);
        assert!(
            row.support
                .iter()
                .any(|f| f.field.as_deref() == Some("Paths.Node.mark") && f.atom.is_some())
        );
    }
    assert_eq!(counts.len(), 9);
    assert!(counts.values().all(|n| *n == 1));
    assert_eq!(
        r.required_zero(),
        Some((0..9).collect::<Vec<_>>().as_slice())
    );
    r.recheck(&i, &mut quiet()).unwrap();
    assert_eq!(i.sources(), &bytes);
}

fn trace(
    e: &Environment<'_>,
    map_case: bool,
) -> (
    super::super::super::internal_path::PathResult,
    BTreeSet<Fact>,
) {
    *e.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
    let result = if map_case {
        correspondence(e)
    } else {
        arrow(e)
    }
    .unwrap();
    let reads = e.state.primitive_reads.borrow_mut().take().unwrap();
    (result, reads)
}
#[test]
fn both_path_routes_keep_quantity_atoms_but_trace_only_structural_values() {
    for map_case in [false, true] {
        let i = if map_case {
            checked(map_fixture::input("normal", "quantity-trace"))
        } else {
            checked(arrow_fixture::input("normal", "quantity-trace"))
        };
        let position = if map_case {
            fact("Reservations.State", "p", "free")
        } else {
            fact("Paths.Node", "p", "mark")
        };
        let normal = Environment::new(&i, &mut quiet()).unwrap();
        let (before, reads) = trace(&normal, map_case);
        assert!(before.value.is_some());
        assert!(!reads.contains(&position));
        let endpoint = if map_case {
            fact("Reservations.Migration", "m", "to")
        } else {
            fact("Paths.Hop", "e", "to")
        };
        assert!(reads.contains(&endpoint));
        let owner = if map_case {
            fact("Reservations.State", "p", "owner")
        } else {
            fact("Paths.Node", "q", "owner")
        };
        assert!(reads.contains(&owner));
        assert!(
            before
                .support
                .iter()
                .any(|f| f.snapshot == position.snapshot
                    && f.subject == position.subject
                    && f.field == position.field
                    && f.atom.is_some())
        );
        let candidate = Environment::with_primitive_valuation(
            &i,
            &[(position.clone(), Scalar::Z((-999).into()))],
            &mut quiet(),
        )
        .unwrap();
        let (after, reads) = trace(&candidate, map_case);
        assert_eq!(path(&before), path(&after));
        assert!(!reads.contains(&position));
        assert!(after.scope.assignments);
        assert!(after.support.contains(&position));
        assert!(
            !after.support.iter().any(|f| f.snapshot == position.snapshot
                && f.subject == position.subject
                && f.field == position.field
                && f.atom.is_some())
        );
    }
}
#[test]
fn a_direct_quantity_read_remains_a_nonfinite_original_position() {
    let i = quantity_input(
        Json::str("Z"),
        "law required quantity(n:Node):n.mark=n.mark;",
    );
    let r = finite_law_family_valuations(
        &i,
        &[
            (
                "Walk.exact".into(),
                vec![("e".into(), reference("Paths.Hop", "e"))],
            ),
            (
                "Walk.quantity".into(),
                vec![("n".into(), reference("Paths.Node", "p"))],
            ),
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(
        r.state(),
        &FiniteLawState::OutsideFinite {
            position: fact("Paths.Node", "p", "mark"),
            ty: Type::Z
        }
    );
    assert!(!r.domain_complete());
    assert!(r.columns().iter().all(|c| c.rows().is_empty()));
    r.recheck(&i, &mut quiet()).unwrap();
}
#[test]
fn an_empty_option_still_tracks_its_possible_reference_shape() {
    let i = typed_input(
        Json::Arr(vec![
            Json::str("Option"),
            Json::Arr(vec![Json::str("Ref"), Json::str("Paths.Node")]),
        ]),
        Some(Json::obj([("none", Json::Bool(true))])),
        vec![],
        "",
    );
    let normal = Environment::new(&i, &mut quiet()).unwrap();
    let (out, reads) = trace(&normal, false);
    assert!(out.value.is_some());
    for n in ["p", "q"] {
        assert!(reads.contains(&fact("Paths.Node", n, "mark")));
    }
    let e = Environment::with_primitive_valuation(
        &i,
        &[(
            fact("Paths.Node", "q", "mark"),
            Scalar::Option {
                element: Type::Ref("Paths.Node".into()),
                value: Some(Box::new(reference("Paths.Node", "p"))),
            },
        )],
        &mut quiet(),
    )
    .unwrap();
    let (out, reads) = trace(&e, false);
    assert!(out.value.is_none());
    assert!(out.failure.is_some());
    assert!(reads.contains(&fact("Paths.Node", "q", "mark")));
}
fn recursive_definition(reference: bool) -> Json {
    Json::obj([
        ("kind", Json::str("data")),
        ("name", Json::str("Paths.Tree")),
        ("meaning", Json::str("再帰する値。")),
        (
            "constructors",
            Json::Arr(vec![
                Json::obj([
                    ("name", Json::str("End")),
                    ("meaning", Json::str("終端。")),
                    ("arguments", Json::Arr(vec![])),
                ]),
                Json::obj([
                    ("name", Json::str("Next")),
                    ("meaning", Json::str("次の値。")),
                    (
                        "arguments",
                        Json::Arr(vec![
                            Json::Arr(vec![Json::str("Data"), Json::str("Paths.Tree")]),
                            if reference {
                                Json::Arr(vec![Json::str("Ref"), Json::str("Paths.Node")])
                            } else {
                                Json::str("Z")
                            },
                        ]),
                    ),
                ]),
            ]),
        ),
    ])
}
#[test]
fn recursive_data_uses_all_constructors_for_value_dependency() {
    for has_reference in [false, true] {
        let i = typed_input(
            Json::Arr(vec![Json::str("Data"), Json::str("Paths.Tree")]),
            Some(Json::obj([
                ("tag", Json::str("End")),
                ("args", Json::Arr(vec![])),
            ])),
            vec![recursive_definition(has_reference)],
            "",
        );
        let normal = Environment::new(&i, &mut quiet()).unwrap();
        let (out, reads) = trace(&normal, false);
        assert!(out.value.is_some());
        for n in ["p", "q"] {
            assert_eq!(
                reads.contains(&fact("Paths.Node", n, "mark")),
                has_reference
            );
        }
        if !has_reference {
            let r = finite_law_family_valuations(
                &i,
                &[(
                    "Walk.exact".into(),
                    vec![("e".into(), reference("Paths.Hop", "e"))],
                )],
                &mut quiet(),
            )
            .unwrap();
            assert!(r.is_complete());
            assert_eq!(r.domain().len(), 9);
            r.recheck(&i, &mut quiet()).unwrap();
        }
    }
}
#[test]
fn a_quantity_in_a_mixed_slot_does_not_erase_the_whole_slot_dependency() {
    let i = typed_input(
        Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Z"),
            Json::Arr(vec![
                Json::str("Option"),
                Json::Arr(vec![Json::str("Ref"), Json::str("Paths.Node")]),
            ]),
        ]),
        Some(Json::Arr(vec![
            Json::str("7"),
            Json::obj([("none", Json::Bool(true))]),
        ])),
        vec![],
        "",
    );
    let e = Environment::new(&i, &mut quiet()).unwrap();
    let (out, reads) = trace(&e, false);
    assert!(out.value.is_some());
    assert!(reads.contains(&fact("Paths.Node", "p", "mark")));
    let r = finite_law_family_valuations(
        &i,
        &[(
            "Walk.exact".into(),
            vec![("e".into(), reference("Paths.Hop", "e"))],
        )],
        &mut quiet(),
    )
    .unwrap();
    assert!(
        matches!(r.state(),FiniteLawState::OutsideFinite{position,ty:Type::Tuple(..)} if position.field.as_deref()==Some("Paths.Node.mark"))
    );
    assert!(!r.domain_complete());
    assert!(r.columns()[0].rows().is_empty());
}
