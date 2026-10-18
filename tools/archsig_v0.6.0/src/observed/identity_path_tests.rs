use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/identity_paths.rs");
}
fn example() -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        fixture::input(false),
        &[
            "other=evaluate(Walk.id,x=@w/a)",
            "target=evaluate(Walk.maybe_value,x=@v/a)",
            "nested=evaluate(Walk.nested,x=@v/b)",
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete");
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn path_mut(node: &mut Node) -> &mut super::super::super::path_value::Identity {
    let Some(Payload::Scalar(Scalar::Path(path))) = &mut node.payload else {
        panic!("Path")
    };
    path
}
fn mutated_path(kinds: &[usize]) {
    let r = example();
    let index = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 1
                && matches!(n.payload, Some(Payload::Scalar(Scalar::Path(_))))
        })
        .unwrap()
        .0;
    let original = &r.nodes[index];
    let foreign = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 0
                && matches!(n.payload, Some(Payload::Scalar(Scalar::Subject { .. })))
        })
        .unwrap()
        .0;
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..index]).unwrap();
    graph.active = r.contexts[index];
    let e = environment(&r);
    e.validate(&graph, original).unwrap();
    for &kind in kinds {
        let mut bad = original.clone();
        match kind {
            0 => path_mut(&mut bad).reading = "Other".into(),
            1 => path_mut(&mut bad).subject = "b".into(),
            2 => path_mut(&mut bad).snapshot = "w".into(),
            3 => path_mut(&mut bad).entity = "Paths.Ghost".into(),
            4 => bad.arguments.clear(),
            5 => bad.arguments[0] = NodeRef(foreign),
            6 => bad.support.clear(),
            7 => bad.scope.snapshots.clear(),
            8 => bad.ty = NodeType::Value(Type::Ref("Paths.Node".into())),
            9 => path_mut(&mut bad).snapshot.clear(),
            _ => panic!(),
        }
        assert_ne!(&bad, original, "mutation {kind}");
        assert!(
            matches!(
                e.validate(&graph, &bad),
                Err(ValidationFailure::Internal(_))
            ),
            "cached {kind}"
        );
        assert!(
            matches!(
                environment(&r).validate(&graph, &bad),
                Err(ValidationFailure::Internal(_))
            ),
            "fresh {kind}"
        );
        e.validate(&graph, original).unwrap();
        let mut all = r.nodes.clone();
        all[index] = bad;
        assert!(
            matches!(
                rebuild_for_origin_and_support_recheck(&r, &all),
                Err(ValidationFailure::Internal(_))
            ),
            "full {kind}"
        );
    }
}
#[test]
fn identity_path_recheck_rejects_reading_subject_snapshot_and_entity_substitution() {
    mutated_path(&[0, 1, 2, 3, 9]);
}
#[test]
fn identity_path_recheck_rejects_missing_foreign_arguments_support_scope_and_type() {
    mutated_path(&[4, 5, 6, 7, 8]);
}
#[test]
fn identity_recheck_rejects_another_valid_reading_despite_same_action() {
    let r = evaluate_observed_bytes(
        fixture::cross_reading(),
        &["same=evaluate(Other.mixed,x=@v/a,y=@v/a)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let index = r
        .nodes
        .iter()
        .position(|n| {
            matches!(
                &n.payload, Some(Payload::Scalar(Scalar::Path(p))) if p.reading=="Walk"
            )
        })
        .unwrap();
    let original = &r.nodes[index];
    let mut bad = original.clone();
    path_mut(&mut bad).reading = "Other".into();
    let (Some(Payload::Scalar(a)), Some(Payload::Scalar(b))) = (&original.payload, &bad.payload)
    else {
        panic!()
    };
    assert_ne!(a, b);
    assert!(super::super::super::data::equal(a, b, &named_call_quiet()).unwrap());
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..index]).unwrap();
    graph.active = r.contexts[index];
    let e = environment(&r);
    e.validate(&graph, original).unwrap();
    assert!(matches!(
        e.validate(&graph, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        environment(&r).validate(&graph, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&graph, original).unwrap();
    let mut all = r.nodes.clone();
    all[index] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &all),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn nonprimitive_container_requires_the_same_typed_prior_value() {
    let r = example();
    let index = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 1
                && matches!(
                    n.payload,
                    Some(Payload::Scalar(Scalar::Option { value: Some(_), .. }))
                )
        })
        .unwrap()
        .0;
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..index]).unwrap();
    graph.active = r.contexts[index];
    let original = &r.nodes[index];
    graph.push(original.clone()).unwrap();
    let mut empty = Graph::new(&named_call_quiet());
    let mut bad = original.clone();
    bad.arguments.clear();
    assert!(matches!(
        empty.push(bad.clone()),
        Err(ValidationFailure::Internal(_))
    ));
    // foreign の同型 Path だけを残しても、別 snapshot の値で代用できない。
    let p = r
        .nodes
        .iter()
        .find(|n| matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p))) if p.snapshot=="w"))
        .unwrap()
        .clone();
    empty.nodes.push(p);
    assert!(matches!(
        empty.push(bad.clone()),
        Err(ValidationFailure::Internal(_))
    ));
    // 数学的にも同じ値があっても、実 arguments の外にある値は借用しない。
    let same=r.nodes.iter().find(|n| matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p))) if p.snapshot=="v" && p.subject=="a")).unwrap().clone();
    empty.nodes.push(same);
    assert!(matches!(
        empty.push(bad),
        Err(ValidationFailure::Internal(_))
    ));
    let mut changed = r.nodes.clone();
    let Some(Payload::Scalar(Scalar::Option { value: Some(p), .. })) = &mut changed[index].payload
    else {
        panic!()
    };
    let Scalar::Path(p) = p.as_mut() else {
        panic!()
    };
    p.snapshot = "w".into();
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &changed),
        Err(ValidationFailure::Internal(_))
    ));
}
fn stop(stage: &'static str, kind: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "current=evaluate(Walk.nested,x=@v/a)",
        "later=evaluate(Walk.seed)",
    ];
    let inputs = fixture::input(false);
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            super::super::super::control::Usage::default()
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            super::super::super::path_value::observe(move |actual, _| {
                if actual == stage && !s.replace(true) {
                    a.set(true)
                }
            });
        }
        Ok(())
    })
    .unwrap();
    super::super::super::path_value::clear_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert!(stopped.nodes.len() < normal.nodes.len());
    assert_eq!(
        stopped.nodes.as_slice(),
        &normal.nodes[..stopped.nodes.len()]
    );
    assert_eq!(
        stopped.contexts.as_slice(),
        &normal.contexts[..stopped.contexts.len()]
    );
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    for answer in &stopped.answers[2..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty());
        assert!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason) if reason==&expected))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    stopped.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn identity_value_cancel_preserves_verified_prefix_and_probe_freeze() {
    stop("identity", 0)
}
#[test]
fn identity_reference_time_stop_preserves_verified_prefix_and_probe_freeze() {
    stop("reference", 1)
}
#[test]
fn nonprimitive_component_memory_stop_preserves_verified_prefix_and_probe_freeze() {
    stop("component", 2)
}
