use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_containers.rs");
}
fn example() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(true, "r1"),
        &[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
            "target=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)",
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    assert_eq!(r.answers[1].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn reject(r: &ObservedEvaluation, index: usize, bad: Node) {
    let original = &r.nodes[index];
    assert_ne!(&bad, original);
    let mut g = rebuild_for_origin_and_support_recheck(r, &r.nodes[..index]).unwrap();
    g.active = r.contexts[index];
    let e = environment(r);
    e.validate(&g, original).unwrap();
    assert!(matches!(
        e.validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        environment(r).validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&g, original).unwrap();
    let mut all = r.nodes.clone();
    all[index] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(r, &all),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn owned_call_missing_rejects_removed_fabricated_and_foreign_source_reasons() {
    let r = example();
    let i = r
        .nodes
        .iter()
        .enumerate()
        .position(|(i, n)| {
            r.contexts[i].request == 2
                && r.contexts[i].case.is_none()
                && matches!(n.payload, Some(Payload::Evaluation { .. }))
                && n.arguments.len() == 3
                && n.arguments[1..]
                    .iter()
                    .all(|a| matches!(r.nodes[a.0].ty, NodeType::Evaluation(_)))
                && n.reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Missing))
        })
        .unwrap();
    let foreign = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 0 && matches!(n.payload, Some(Payload::Expression { .. }))
        })
        .unwrap()
        .0;
    for kind in 0..3 {
        let mut bad = r.nodes[i].clone();
        if kind == 0 {
            bad.reasons.clear();
        } else {
            let reason = bad
                .reasons
                .iter_mut()
                .find(|r| matches!(r.kind, ReasonKind::Missing))
                .unwrap();
            if kind == 1 {
                reason.missing[0].field = Some("Reservations.State.free".into());
            } else {
                reason.dependencies = vec![NodeRef(foreign)];
            }
        }
        reject(&r, i, bad);
    }
}
#[test]
fn owned_call_case_rejects_other_owner_value_and_scope() {
    let r = example();
    let case = r
        .cases
        .iter()
        .find(|c| {
            r.nodes[c.values[0].0].payload
                == Some(Payload::Scalar(Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "A".into(),
                    entity: "Reservations.System".into(),
                }))
        })
        .unwrap();
    let i = case.values[0].0;
    let mut bad = r.nodes[i].clone();
    bad.payload = Some(Payload::Scalar(Scalar::Subject {
        snapshot: "v".into(),
        subject: "B".into(),
        entity: "Reservations.System".into(),
    }));
    reject(&r, i, bad);
    let mut bad = r.nodes[i].clone();
    bad.scope.snapshots.clear();
    reject(&r, i, bad);
}
#[test]
fn owned_call_case_frame_rejects_missing_and_extra_arguments_without_panic() {
    let mut r = example();
    let frame = r
        .frames
        .iter()
        .position(|f| f.caller.request == 2 && f.caller.case.is_some() && f.arguments.len() == 2)
        .unwrap();
    let original = r.frames[frame].clone();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = environment(&r);
    e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
        .unwrap();
    for extra in [false, true] {
        let mut bad = original.clone();
        if extra {
            bad.arguments.push(bad.arguments[0]);
        } else {
            bad.arguments.clear();
        }
        assert_ne!(bad.arguments, original.arguments);
        g.frames[frame] = bad;
        assert!(matches!(
            e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2]),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            environment(&r).validate_answer(
                &g,
                &r.prepared.requests().requests()[2],
                &r.answers[2]
            ),
            Err(ValidationFailure::Internal(_))
        ));
        g.frames[frame] = original.clone();
        e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
            .unwrap();
    }
    drop(e);
    r.frames[frame].arguments.clear();
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    r.frames[frame] = original;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
fn stop(stage: &'static str, kind: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "target=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)",
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = fixture::input(true, "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
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
            super::super::super::data::observe_iterations(move |_, _, actual, _| {
                if actual == stage && !s.replace(true) {
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    super::super::super::data::clear_iteration_observer();
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
    assert_eq!(
        stopped.frames.as_slice(),
        &normal.frames[..stopped.frames.len()]
    );
    assert_eq!(
        stopped.iterations.as_slice(),
        &normal.iterations[..stopped.iterations.len()]
    );
    assert_eq!(
        stopped.instances.as_slice(),
        &normal.instances[..stopped.instances.len()]
    );
    assert_eq!(
        stopped.cases.as_slice(),
        &normal.cases[..stopped.cases.len()]
    );
    assert_eq!(
        stopped.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..stopped.universal_witnesses.len()]
    );
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    for (i, answer) in stopped.answers.iter().enumerate().skip(2) {
        assert_eq!(answer.status, Decision::Undetermined);
        if stage == "owned_call_missing_source" && i == 2 {
            // 全補完の収集前には、既に検査済みの元body評価だけを保持する。
            assert_eq!(answer.outputs.len(), 1);
            let evaluation = answer.outputs["evaluation"];
            assert!(matches!(
                stopped.nodes[evaluation.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
            assert_eq!(stopped.nodes[evaluation.0], normal.nodes[evaluation.0]);
        } else {
            assert!(answer.outputs.is_empty());
        }
        assert!(answer.claim.is_none() && answer.evidence.is_empty());
        assert!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason)if reason==&expected))
        );
    }
    if stage != "owned_call_missing" {
        assert!(
            stopped.answers[2]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.subject == "p"
                        && f.field.as_deref() == Some("Reservations.State.owner")))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    stopped.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_call_missing_cancel_keeps_verified_prefix_and_probe_freeze() {
    stop("owned_call_missing", 0)
}
#[test]
fn owned_call_missing_source_time_stop_keeps_verified_prefix_and_probe_freeze() {
    stop("owned_call_missing_source", 1)
}
#[test]
fn owned_call_case_memory_stop_keeps_verified_prefix_and_probe_freeze() {
    stop("owned_call_case", 2)
}

#[test]
fn owned_call_skipped_branch_rejects_changed_selector_and_lost_missing() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &["x=evaluate(Reservations.pcSkipIf,a=@v/B,e=@v/e)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(r.answers[0].status, Decision::Established);
    assert!(
        r.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert!(
        !r.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let (selector, _) = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].case.is_some() && n.payload == Some(Payload::Scalar(Scalar::Bool(false)))
        })
        .unwrap();
    let mut bad = r.nodes[selector].clone();
    bad.payload = Some(Payload::Scalar(Scalar::Bool(true)));
    reject(&r, selector, bad);
    let (evaluation, _) = r.nodes.iter().enumerate().find(|(i, n)|
        r.contexts[*i].case.is_some() && matches!(n.payload, Some(Payload::Evaluation { value: Some(_), ref parts, .. }) if parts.len()==1 && parts[0].children.len()==3)
        && n.reasons.iter().any(|r| matches!(r.kind, ReasonKind::Missing))
    ).unwrap();
    let mut bad = r.nodes[evaluation].clone();
    bad.reasons
        .retain(|r| !matches!(r.kind, ReasonKind::Missing));
    reject(&r, evaluation, bad);
}
