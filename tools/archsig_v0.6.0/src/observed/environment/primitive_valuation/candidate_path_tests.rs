use super::*;
use crate::{law::model::Signature, result::Signal};
use std::{cell::Cell, rc::Rc, sync::Arc};
#[allow(dead_code)]
mod arrow_fixture {
    use crate as archsig;
    include!("../../../../tests/common/internal_paths.rs");
}
#[allow(dead_code)]
mod map_fixture {
    use crate as archsig;
    include!("../../../../tests/common/correspondence_paths.rs");
}
use crate::control::quiet;
fn checked(s: crate::input::InputSources) -> Arc<CheckedInputs> {
    Arc::new(crate::input::check_inputs(s, &mut quiet()).unwrap())
}
fn fact(namespace: &str, subject: &str, field: &str) -> Fact {
    Fact {
        snapshot: "v".into(),
        subject: subject.into(),
        field: Some(format!("{namespace}.{field}")),
        atom: None,
    }
}
fn reference(ty: &str, subject: &str) -> Scalar {
    Scalar::Subject {
        snapshot: "v".into(),
        subject: subject.into(),
        entity: ty.into(),
    }
}
fn body(i: &CheckedInputs, name: &str) -> usize {
    match i.law().declarations[name].signature {
        Signature::View { body, .. } => body,
        _ => panic!(),
    }
}
fn arrow(
    e: &Environment<'_>,
) -> Result<super::super::internal_path::PathResult, ValidationFailure> {
    e.internal_path(body(e.inputs, "Walk.step"), &[reference("Paths.Hop", "e")])
}
fn correspondence(
    e: &Environment<'_>,
) -> Result<super::super::internal_path::PathResult, ValidationFailure> {
    e.internal_path(
        body(e.inputs, "Reservations.step"),
        &[reference("Reservations.Migration", "m")],
    )
}
fn path(out: &super::super::internal_path::PathResult) -> &crate::observed::path_value::PathValue {
    let Some(Scalar::Path(p)) = &out.value else {
        panic!("Pathなし")
    };
    p
}
fn subject_image(
    p: &crate::observed::path_value::PathValue,
    snapshot: &str,
    subject: &str,
) -> Fact {
    let step = p.step.as_ref().unwrap();
    let at = step
        .carrier
        .iter()
        .position(|f| f.snapshot == snapshot && f.subject == subject && f.field.is_none())
        .unwrap();
    step.images[at].clone()
}
fn list(values: &[&str]) -> Scalar {
    Scalar::List {
        element: Type::Ref("Paths.Node".into()),
        items: values.iter().map(|s| reference("Paths.Node", s)).collect(),
    }
}
fn map(ty: &str, rows: &[(&str, &str)]) -> Scalar {
    Scalar::Map {
        domain: Type::Ref(ty.into()),
        codomain: Type::Ref(ty.into()),
        pairs: rows
            .iter()
            .map(|(a, b)| (reference(ty, a), reference(ty, b)))
            .collect(),
    }
}
#[test]
fn candidate_internal_path_keeps_original_carrier_word_and_exact_complement() {
    let i = checked(arrow_fixture::input("normal", "candidate"));
    let bytes = i.sources().clone();
    let normal = Environment::new(&i, &mut quiet()).unwrap();
    let before = arrow(&normal).unwrap();
    let assignments = vec![
        (fact("Paths.Node", "p", "mark"), Scalar::Z(123.into())),
        (fact("Paths.Node", "q", "mark"), Scalar::Z((-9).into())),
    ];
    let e = Environment::with_primitive_valuation(&i, &assignments, &mut quiet()).unwrap();
    let out = arrow(&e).unwrap();
    assert!(out.failure.is_none());
    assert!(out.missing.is_empty());
    assert!(out.scope.assignments);
    assert_eq!(
        path(&out).step.as_ref().unwrap().carrier,
        path(&before).step.as_ref().unwrap().carrier
    );
    assert_eq!(
        path(&out).step.as_ref().unwrap().images,
        path(&before).step.as_ref().unwrap().images
    );
    assert_eq!(
        path(&out).step.as_ref().unwrap().generator,
        reference("Paths.Hop", "e")
    );
    assert!(path(&out).step.as_ref().unwrap().word_tail.is_empty());
    assert_eq!(subject_image(path(&out), "v", "p").subject, "q");
    let external = subject_image(path(&out), "w", "p");
    assert_eq!(
        (external.snapshot.as_str(), external.subject.as_str()),
        ("w", "p")
    );
    for (position, _) in &assignments {
        assert!(out.support.contains(position));
        assert!(!out.support.iter().any(|f| f.snapshot == position.snapshot
            && f.subject == position.subject
            && f.field == position.field
            && f.atom.is_some()));
    }
    assert!(!before.scope.assignments);
    assert_eq!(i.sources(), &bytes);
    assert!(
        validation_identity::scalar(
            before.value.as_ref().unwrap(),
            arrow(&normal).unwrap().value.as_ref().unwrap(),
            &quiet()
        )
        .unwrap()
    );
}
#[test]
fn changed_target_reference_refutes_original_preserved_action() {
    let i = checked(arrow_fixture::input("normal", "candidate"));
    let e = Environment::with_primitive_valuation(
        &i,
        &[(
            fact("Paths.Node", "q", "link"),
            reference("Paths.Node", "p"),
        )],
        &mut quiet(),
    )
    .unwrap();
    let out = arrow(&e).unwrap();
    assert!(out.value.is_none());
    assert!(out.failure.is_some());
    assert!(out.missing.is_empty());
    assert!(out.scope.assignments);
    assert!(out.support.contains(&fact("Paths.Node", "q", "link")));
    assert!(
        arrow(&Environment::new(&i, &mut quiet()).unwrap())
            .unwrap()
            .value
            .is_some()
    );
}
#[test]
fn candidate_reference_can_restore_original_refutation_and_candidate_caches_are_separate() {
    let i = checked(arrow_fixture::input("mismatch", "candidate"));
    assert!(
        arrow(&Environment::new(&i, &mut quiet()).unwrap())
            .unwrap()
            .failure
            .is_some()
    );
    for target in ["q", "p", "q"] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(
                fact("Paths.Node", "q", "link"),
                reference("Paths.Node", target),
            )],
            &mut quiet(),
        )
        .unwrap();
        for _ in 0..2 {
            let out = arrow(&e).unwrap();
            assert_eq!(out.value.is_some(), target == "q");
            assert_eq!(out.failure.is_some(), target != "q");
        }
    }
}
#[test]
fn candidate_list_reference_order_and_duplicates_are_rechecked() {
    let i = checked(arrow_fixture::input("normal", "candidate"));
    for (values, valid) in [(["q", "q", "q"], true), (["q", "p", "q"], false)] {
        let e = Environment::with_primitive_valuation(
            &i,
            &[(fact("Paths.Node", "q", "links"), list(&values))],
            &mut quiet(),
        )
        .unwrap();
        let out = arrow(&e).unwrap();
        assert_eq!(out.value.is_some(), valid);
        assert_eq!(out.failure.is_none(), valid);
    }
}
#[test]
fn changed_arrow_endpoint_builds_the_actual_new_action() {
    let i = checked(arrow_fixture::input("normal", "candidate"));
    let e = Environment::with_primitive_valuation(
        &i,
        &[(fact("Paths.Hop", "e", "to"), reference("Paths.Node", "r"))],
        &mut quiet(),
    )
    .unwrap();
    let out = arrow(&e).unwrap();
    assert!(out.failure.is_none());
    assert_eq!(path(&out).target(), reference("Paths.Node", "r"));
    assert_eq!(subject_image(path(&out), "v", "p").subject, "r");
    let baseline = arrow(&Environment::new(&i, &mut quiet()).unwrap()).unwrap();
    assert_eq!(path(&baseline).target(), reference("Paths.Node", "q"));
    assert!(
        !validation_identity::scalar(
            out.value.as_ref().unwrap(),
            baseline.value.as_ref().unwrap(),
            &quiet()
        )
        .unwrap()
    );
}
#[test]
fn candidate_quantity_does_not_create_a_missing_target_atom() {
    let i = checked(arrow_fixture::input("missing_tag", "candidate"));
    let position = fact("Paths.Node", "q", "mark");
    let e = Environment::with_primitive_valuation(
        &i,
        &[(position.clone(), Scalar::Z(7.into()))],
        &mut quiet(),
    )
    .unwrap();
    let out = arrow(&e).unwrap();
    assert!(out.value.is_none());
    assert!(out.failure.is_none());
    assert!(out.missing.contains(&position));
    assert!(out.scope.assignments);
    assert!(out.scope.completions);
    assert!(
        !i.archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .flat_map(|s| &s.fields)
            .any(|f| matches!(&f.slot,Slot::Known{atom,..}if atom=="q-mark"))
    );
}
#[test]
fn candidate_correspondence_rebuilds_tables_roots_and_full_universe_action() {
    let i = checked(map_fixture::input("normal", "r1"));
    let bytes = i.sources().clone();
    let assignments = vec![
        (
            fact("Reservations.Migration", "m", "to"),
            reference("Reservations.System", "A"),
        ),
        (
            fact("Reservations.Migration", "m", "states"),
            map("Reservations.State", &[("p", "p"), ("q", "q")]),
        ),
        (
            fact("Reservations.Migration", "m", "reserves"),
            map("Reservations.Reserve", &[("e", "e")]),
        ),
    ];
    let e = Environment::with_primitive_valuation(&i, &assignments, &mut quiet()).unwrap();
    let out = correspondence(&e).unwrap();
    assert!(out.failure.is_none());
    assert!(out.missing.is_empty());
    assert!(out.scope.assignments);
    assert_eq!(path(&out).target(), reference("Reservations.System", "A"));
    assert_eq!(subject_image(path(&out), "v", "p").subject, "p");
    assert_eq!(subject_image(path(&out), "v", "e").subject, "e");
    assert_eq!(subject_image(path(&out), "v", "r").subject, "A");
    assert_eq!(
        path(&out).step.as_ref().unwrap().generator,
        reference("Reservations.Migration", "m")
    );
    let before = correspondence(&Environment::new(&i, &mut quiet()).unwrap()).unwrap();
    assert_eq!(
        path(&out).step.as_ref().unwrap().carrier,
        path(&before).step.as_ref().unwrap().carrier
    );
    assert_eq!(subject_image(path(&before), "v", "p").subject, "r");
    for (position, _) in assignments {
        assert!(out.support.contains(&position));
        assert!(!out.support.iter().any(|f| f.snapshot == position.snapshot
            && f.subject == position.subject
            && f.field == position.field
            && f.atom.is_some()));
    }
    assert_eq!(i.sources(), &bytes);
}
#[test]
fn candidate_correspondence_table_refutes_endpoint_preservation() {
    let i = checked(map_fixture::input("normal", "r1"));
    let e = Environment::with_primitive_valuation(
        &i,
        &[(
            fact("Reservations.Migration", "m", "states"),
            map("Reservations.State", &[("p", "s"), ("q", "r")]),
        )],
        &mut quiet(),
    )
    .unwrap();
    let out = correspondence(&e).unwrap();
    assert!(out.value.is_none());
    assert!(out.failure.is_some());
    assert!(out.missing.is_empty());
    assert!(
        correspondence(&Environment::new(&i, &mut quiet()).unwrap())
            .unwrap()
            .value
            .is_some()
    );
}
#[test]
fn candidate_correspondence_does_not_create_missing_target_field_atom() {
    let i = checked(map_fixture::input("missing_field", "r1"));
    let position = fact("Reservations.State", "r", "free");
    let e = Environment::with_primitive_valuation(
        &i,
        &[(position.clone(), Scalar::Z(2.into()))],
        &mut quiet(),
    )
    .unwrap();
    let out = correspondence(&e).unwrap();
    assert!(out.value.is_none());
    assert!(out.failure.is_none());
    assert!(out.missing.contains(&position));
}
#[test]
fn bad_candidate_type_and_incomplete_correspondence_map_are_not_path_refutations() {
    let i = checked(map_fixture::input("normal", "r1"));
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(
                fact("Reservations.Migration", "m", "to"),
                Scalar::Z(0.into())
            )],
            &mut quiet()
        )
        .is_err()
    );
    assert!(
        Environment::with_primitive_valuation(
            &i,
            &[(
                fact("Reservations.Migration", "m", "states"),
                map("Reservations.State", &[("p", "r")])
            )],
            &mut quiet()
        )
        .is_err()
    );
}
#[test]
fn candidate_paths_reconstruct_from_same_inputs_and_freeze_each_fixed_stop() {
    for correspondence_case in [false, true] {
        let i = if correspondence_case {
            checked(map_fixture::input("normal", "r1"))
        } else {
            checked(arrow_fixture::input("normal", "candidate"))
        };
        let assignments = if correspondence_case {
            vec![(
                fact("Reservations.State", "p", "free"),
                Scalar::Z(123.into()),
            )]
        } else {
            vec![(fact("Paths.Hop", "e", "to"), reference("Paths.Node", "r"))]
        };
        let calculate: fn(
            &Environment<'_>,
        )
            -> Result<super::super::internal_path::PathResult, ValidationFailure> =
            if correspondence_case {
                correspondence
            } else {
                arrow
            };
        let original = calculate(
            &Environment::with_primitive_valuation(&i, &assignments, &mut quiet()).unwrap(),
        )
        .unwrap();
        let control = |at: usize, signal: Signal| {
            let active = Rc::new(Cell::new(false));
            let enabled = active.clone();
            let visits = Rc::new(Cell::new(0));
            let seen = visits.clone();
            let calls = Rc::new(Cell::new(0));
            let samples = calls.clone();
            (
                Control::new(move |cp| {
                    samples.set(samples.get() + 1);
                    if enabled.get() && cp == Checkpoint::FiniteIteration {
                        seen.set(seen.get() + 1);
                    }
                    (enabled.get() && seen.get() >= at).then_some(signal)
                }),
                active,
                visits,
                calls,
            )
        };
        let (mut c, active, visits, _) = control(usize::MAX, Signal::Int);
        let e = Environment::with_primitive_valuation(&i, &assignments, &mut c).unwrap();
        active.set(true);
        calculate(&e).unwrap();
        let total = visits.get();
        assert!(total > 3);
        for at in [1, total / 2, total] {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, active, _, calls) = control(at, signal);
                let e = Environment::with_primitive_valuation(&i, &assignments, &mut c).unwrap();
                active.set(true);
                let error = match calculate(&e) {
                    Err(e) => e,
                    Ok(_) => panic!("停止が成功"),
                };
                assert!(matches!(error,ValidationFailure::Stop(ref s)if s==&signal));
                let before = calls.get();
                assert_eq!(c.checkpoint(Checkpoint::FiniteIteration), Err(signal));
                assert_eq!(before, calls.get());
                let rebuilt = calculate(
                    &Environment::with_primitive_valuation(&i, &assignments, &mut quiet()).unwrap(),
                )
                .unwrap();
                assert!(
                    validation_identity::scalar(
                        original.value.as_ref().unwrap(),
                        rebuilt.value.as_ref().unwrap(),
                        &quiet()
                    )
                    .unwrap()
                );
            }
        }
    }
}

#[test]
fn finite_path_law_evaluates_all_seventy_two_original_primitive_assignments() {
    use super::super::finite_law_valuations::finite_law_family_valuations;
    use crate::{canonical::Json, input::InputSources, json::parse};
    let original = arrow_fixture::input("normal", "finite-path");
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
    for d in declarations {
        let Json::Obj(d) = d else { panic!() };
        if d["name"] == Json::str("Paths.Node") {
            let Json::Arr(fields) = d.get_mut("fields").unwrap() else {
                panic!()
            };
            fields.retain(|f| matches!(f,Json::Obj(f)if f["name"]==Json::str("mark")));
            let Json::Obj(mark) = &mut fields[0] else {
                panic!()
            };
            mark.insert(
                "type".into(),
                Json::Arr(vec![Json::str("Fp"), Json::str("2")]),
            );
        }
    }
    let defs = defs.canonical();
    let checked_defs =
        crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &checked_defs.vocabularies["Paths"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Walk{{use vocabulary Paths version \"1\" digest \"{digest}\";view step(e:Hop):Path<Node,Node> =path(e);law required exact(e:Hop) when (forall n:Node . n.mark=n.mark):path(e)=path(e);}}"
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
    for a in atoms {
        let Json::Obj(a) = a else { panic!() };
        if a["field"] == Json::str("Paths.Node.mark") {
            let value = if a["subject"] == Json::str("p") {
                "0"
            } else {
                "1"
            };
            a.insert("value".into(), Json::str(value));
        }
    }
    let i = checked(InputSources::from_bytes(
        vec![defs.into_bytes()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    ));
    let bytes = i.sources().clone();
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
    assert!(r.domain_complete());
    assert_eq!(r.domain().len(), 72);
    assert_eq!(r.columns()[0].rows().len(), 72);
    assert_eq!(
        r.required_zero(),
        Some((0..72).collect::<Vec<_>>().as_slice())
    );
    assert!(r.observed_point().is_some());
    let mut targets = BTreeMap::<String, usize>::new();
    let mut sources = BTreeMap::<String, usize>::new();
    for row in r.columns()[0].rows() {
        assert_eq!(row.indicator, Some(0.into()));
        assert!(row.scope.assignments);
        let (_, Some(Scalar::Path(left)), Some(Scalar::Path(right))) =
            row.operands.as_ref().unwrap()
        else {
            panic!()
        };
        assert!(
            validation_identity::scalar(
                &Scalar::Path(left.clone()),
                &Scalar::Path(right.clone()),
                &quiet()
            )
            .unwrap()
        );
        let target_value = left.target();
        let Scalar::Subject {
            subject: target, ..
        } = &target_value
        else {
            panic!()
        };
        *targets.entry(target.clone()).or_default() += 1;
        *sources.entry(left.subject.clone()).or_default() += 1;
        assert_eq!(
            subject_image(left, "v", &left.subject),
            Fact {
                snapshot: "v".into(),
                subject: target.clone(),
                field: None,
                atom: None
            }
        );
    }
    assert_eq!(
        targets,
        BTreeMap::from([("p".into(), 24), ("q".into(), 24), ("r".into(), 24)])
    );
    assert_eq!(sources, targets);
    let q = r.required_quotient(&mut quiet()).unwrap();
    assert_eq!(q.points().len(), 72);
    q.recheck(&i, &mut quiet()).unwrap();
    r.recheck(&i, &mut quiet()).unwrap();
    assert_eq!(i.sources(), &bytes);
}

mod structure;
