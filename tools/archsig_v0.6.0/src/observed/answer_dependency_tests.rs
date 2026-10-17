use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_dependencies.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.abSeed)",
    "prior=check(Applications.abPrior)",
    "raw=evaluate(Applications.adMissing,p=@v/p)",
    "opaque=evaluate(Applications.adOpaque)",
    "both=evaluate(Applications.adBoth,x=$raw.value,b=$opaque.evaluation.value)",
    "later=evaluate(Applications.abSeed)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, request, answer).unwrap();
    }
    r
}
fn reject_answer(r: &ObservedEvaluation, change: impl Fn(&mut Answer)) {
    let cutoff = r.contexts.iter().position(|c| c.request == 5).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let g = rebuild_for_origin_and_support_recheck(r, nodes).unwrap();
        let e = Environment::with_requests(
            r.prepared.inputs(),
            r.prepared.requests().requests(),
            &mut named_call_quiet(),
        )
        .unwrap();
        let request = &r.prepared.requests().requests()[4];
        let original = &r.answers[4];
        e.validate_answer(&g, request, original).unwrap();
        let mut altered = original.clone();
        change(&mut altered);
        assert_ne!(&altered, original);
        assert!(matches!(
            e.validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        let fresh = Environment::with_requests(
            r.prepared.inputs(),
            r.prepared.requests().requests(),
            &mut named_call_quiet(),
        )
        .unwrap();
        assert!(matches!(
            fresh.validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        e.validate_answer(&g, request, original).unwrap();
    }
}
#[test]
fn dependency_answer_rechecks_ids_status_outputs_scope_and_each_original_reason() {
    let r = result();
    reject_answer(&r, |a| a.id = "other".into());
    reject_answer(&r, |a| a.status = Decision::Established);
    reject_answer(&r, |a| {
        a.outputs
            .insert("value".into(), r.answers[0].outputs["value"]);
    });
    reject_answer(&r, |a| a.claim = r.answers[1].claim);
    reject_answer(&r, |a| a.evidence = r.answers[1].evidence.clone());
    reject_answer(&r, |a| a.scope.snapshots.clear());
    reject_answer(&r, |a| {
        a.reasons
            .retain(|r| !matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
    });
    reject_answer(&r, |a| {
        let d = a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
            .unwrap();
        d.kind = ReasonKind::DependencyBlocked {
            request: "seed".into(),
        };
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
            .unwrap()
            .dependencies
            .clear()
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap()
            .missing
            .clear()
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap()
            .location = None
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap()
            .request = "both".into()
    });
    reject_answer(&r, |a| {
        let ReasonKind::UnsupportedAlgorithm { method, .. } = &mut a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
            .unwrap()
            .kind
        else {
            panic!()
        };
        *method = "foreign".into();
    });
    reject_answer(&r, |a| {
        let ReasonKind::UnsupportedAlgorithm { operand_types, .. } = &mut a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
            .unwrap()
            .kind
        else {
            panic!()
        };
        operand_types[0] = Type::Bool;
    });
}
#[test]
fn dependency_answer_rejects_coherent_request_and_producer_registry_changes() {
    let r = result();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let request = &r.prepared.requests().requests()[4];
    let original = &r.answers[4];
    e.validate_answer(&g, request, original).unwrap();
    let old = g.requests[4].clone();
    let Selector::Answer { id, .. } = &mut g.requests[4].arguments[0].value else {
        panic!()
    };
    *id = "seed".into();
    g.requests[4].dependencies = vec!["seed".into(), "opaque".into()];
    let mut changed = original.clone();
    let reason = changed
        .reasons
        .iter_mut()
        .find(|r| matches!(&r.kind,ReasonKind::DependencyBlocked{request}if request=="raw"))
        .unwrap();
    reason.kind = ReasonKind::DependencyBlocked {
        request: "seed".into(),
    };
    reason.dependencies = vec![r.answers[0].outputs["value"]];
    assert!(matches!(
        e.validate_answer(&g, &g.requests[4], &changed),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[4] = old;
    e.validate_answer(&g, request, original).unwrap();
    let at = g.checked_answers.iter().position(|(i, _)| *i == 2).unwrap();
    let producer = g.checked_answers[at].1.clone();
    g.checked_answers[at].1 = r.answers[0].clone();
    g.checked_answers[at].1.id = "raw".into();
    assert!(matches!(
        e.validate_answer(&g, request, original),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = producer.clone();
    e.validate_answer(&g, request, original).unwrap();
    g.checked_answers[at]
        .1
        .reasons
        .iter_mut()
        .find(|r| matches!(r.kind, ReasonKind::Missing))
        .unwrap()
        .missing
        .clear();
    assert!(matches!(
        e.validate_answer(&g, request, original),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = producer;
    e.validate_answer(&g, request, original).unwrap();
    let at = g.checked_answers.iter().position(|(i, _)| *i == 3).unwrap();
    let producer = g.checked_answers[at].1.clone();
    let ReasonKind::UnsupportedAlgorithm { method, .. } = &mut g.checked_answers[at]
        .1
        .reasons
        .iter_mut()
        .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        .unwrap()
        .kind
    else {
        panic!()
    };
    *method = "other".into();
    assert!(matches!(
        e.validate_answer(&g, request, original),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = producer;
    e.validate_answer(&g, request, original).unwrap();
}
fn dependency_stop(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let normal = result();
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations["Applications.adBoth"].signature
    else {
        panic!()
    };
    let span = params[0].span;
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(fixture::input("stop", "r1"), ASK, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "opaque" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span
                    && ctx.request == 4
                    && operation == "answer_binding_scan"
                    && (!recheck || ph.get())
                {
                    let old = s.get();
                    s.set(old + 1);
                    if old == 1 {
                        a.set(true)
                    }
                }
            });
        }
        if request.id == "both" && recheck {
            let fresh = Environment::with_requests(
                normal.prepared.inputs(),
                normal.prepared.requests().requests(),
                &mut cc,
            )?;
            phase.set(true);
            let r = fresh.validate_answer(g, request, answer);
            phase.set(false);
            r?;
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 2);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for index in 4..stopped.answers.len() {
        let answer = &stopped.answers[index];
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty());
        if recheck && index == 4 {
            for reason in &normal.answers[4].reasons {
                assert!(answer.reasons.contains(reason));
            }
            assert_eq!(answer.scope, normal.answers[4].scope);
        }
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, answer.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn dependency_answer_actual_scan_stop_keeps_prior_values_refutations_and_reasons() {
    dependency_stop(false)
}
#[test]
fn dependency_answer_fresh_recheck_stop_keeps_verified_blocked_answer_and_freezes() {
    dependency_stop(true)
}
