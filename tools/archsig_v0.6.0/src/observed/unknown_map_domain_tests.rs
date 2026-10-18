use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/unknown_map_domain.rs");
}
fn example(mode: &str) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(mode, "r1"),
        &[
            "seed=evaluate(MapCall.seed)",
            "prior=check(MapCall.prior)",
            "target=evaluate(MapCall.call,a=@v/A,h=@v/h)",
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    assert_eq!(r.answers[1].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn reject(r: &ObservedEvaluation, i: usize, bad: Node) {
    let original = &r.nodes[i];
    assert_ne!(&bad, original);
    let mut g = rebuild_for_origin_and_support_recheck(r, &r.nodes[..i]).unwrap();
    g.active = r.contexts[i];
    let e = env(r);
    e.validate(&g, original).unwrap();
    assert!(matches!(
        e.validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(r).validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&g, original).unwrap();
    let mut all = r.nodes.clone();
    all[i] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(r, &all),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn map_owner_cases_reject_changed_assignment_domain_and_scope() {
    let r = example("empty_varying");
    let c=r.cases.iter().find(|c| matches!(&r.nodes[c.values[0].0].payload,Some(Payload::Scalar(Scalar::Subject{subject,..}))if subject=="A")).unwrap();
    let i = c.values[0].0;
    let mut bad = r.nodes[i].clone();
    let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut bad.payload else {
        panic!()
    };
    *subject = "B".into();
    reject(&r, i, bad);
    let mut bad = r.nodes[i].clone();
    bad.scope.snapshots.clear();
    reject(&r, i, bad);
    let domain = r
        .nodes
        .iter()
        .position(|n| matches!(&n.payload,Some(Payload::Domain{elements,..})if elements.len()==2))
        .unwrap();
    let mut bad = r.nodes[domain].clone();
    let Some(Payload::Domain { elements, .. }) = &mut bad.payload else {
        panic!()
    };
    elements.pop();
    reject(&r, domain, bad);
}
#[test]
fn map_full_roster_rejects_lost_nonkey_missing_and_changed_expected_set() {
    let r = example("empty_varying");
    let source = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 2
                && r.contexts[*i].case.is_none()
                && matches!(n.payload, Some(Payload::Evaluation { .. }))
                && n.reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Missing))
        })
        .map(|(i, _)| i)
        .unwrap();
    let mut bad = r.nodes[source].clone();
    bad.reasons
        .retain(|r| !matches!(r.kind, ReasonKind::Missing));
    reject(&r, source, bad);
    let mut bad = r.nodes[source].clone();
    bad.reasons
        .iter_mut()
        .find(|r| matches!(r.kind, ReasonKind::Missing))
        .unwrap()
        .missing[0]
        .field = Some("MapCall.Holder.owner".into());
    reject(&r, source, bad);
    let condition = owned_condition(&r, 2);
    let edges = &r.nodes[condition].arguments;
    let actual = edges[edges.len() - 3];
    let required = edges[edges.len() - 2];
    assert!(
        matches!(&r.nodes[actual.0].payload,Some(Payload::Scalar(Scalar::Set{items,..}))if items.is_empty())
    );
    assert!(
        matches!(&r.nodes[required.0].payload,Some(Payload::Scalar(Scalar::Set{items,..}))if items.len()==1)
    );
    let mut bad = r.nodes[required.0].clone();
    let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut bad.payload else {
        panic!()
    };
    items.clear();
    reject(&r, required.0, bad);
    for change_scope in [false, true] {
        let mut bad = r.nodes[condition].clone();
        if change_scope {
            bad.scope.snapshots.clear();
        } else {
            bad.support.clear();
        }
        reject(&r, condition, bad);
    }
}
fn stop(stage: &'static str, kind: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(MapCall.seed)",
        "prior=check(MapCall.prior)",
        "target=evaluate(MapCall.call,a=@v/A,h=@v/h)",
        "later=evaluate(MapCall.seed)",
    ];
    let inputs = fixture::input("empty_varying", "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
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
    macro_rules! prefix {
        ($field:ident) => {
            assert_eq!(
                stopped.$field.as_slice(),
                &normal.$field[..stopped.$field.len()]
            );
        };
    }
    prefix!(nodes);
    prefix!(contexts);
    prefix!(frames);
    prefix!(iterations);
    prefix!(instances);
    prefix!(cases);
    prefix!(universal_witnesses);
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason)if reason==&expected))
        );
        if i == 3 {
            assert!(a.outputs.is_empty());
        }
        for r in a.outputs.values() {
            assert!(matches!(
                stopped.nodes[r.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
        }
    }
    if stage != "owned_call_map_domain_missing" {
        assert!(stopped.answers[2].reasons.iter().any(|r| {
            matches!(r.kind, ReasonKind::Missing)
                && r.missing
                    .iter()
                    .any(|f| f.subject == "p" && f.field.as_deref() == Some("MapCall.Item.owner"))
        }));
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    stopped.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn map_domain_missing_cancel_retains_verified_prefix_and_stops_probes() {
    stop("owned_call_map_domain_missing", 0)
}
#[test]
fn map_domain_comparison_time_stop_retains_original_missing_and_prefix() {
    stop("owned_call_map_domain", 1)
}
#[test]
fn map_domain_case_memory_stop_retains_original_missing_and_prefix() {
    stop("owned_call_case", 2)
}
