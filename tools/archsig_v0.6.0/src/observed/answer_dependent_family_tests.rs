use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_dependent_family.rs");
}
const ASK: &[&str] = &[
    "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "other=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "flag=evaluate(Reservations.adFlag)",
    "take=check(Reservations.adFixed,a=$owner.value,flag=$flag.value)",
    "later=evaluate(Reservations.seed)",
];
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, false, "r1"),
        ASK,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, request, answer).unwrap();
    }
    r
}
fn source(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==3 && r.contexts[i].instance.is_none() && matches!(&n.payload,Some(Payload::Expression{parameters,..})if !parameters.is_empty())).then_some(i)).unwrap()
}
fn fiber(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==3 && r.contexts[i].instance.is_none() && matches!(&n.payload,Some(Payload::Domain{ty:Type::Option(_),elements})if elements.len()==3)).then_some(i)).unwrap()
}
#[test]
fn dependent_answer_fibers_recheck_source_identity_free_axes_domains_rows_and_support() {
    let r = result();
    let source = source(&r);
    let domain = fiber(&r);
    let root = r.answers[0].outputs["value"];
    let foreign = r.answers[1].outputs["value"];
    assert_ne!(root, foreign);
    assert_eq!(r.nodes[root.0].payload, r.nodes[foreign.0].payload);
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source].payload else {
            panic!()
        };
        parameters.clear();
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        bindings[0].name = "f".into();
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        bindings[0].value = foreign;
        for a in &mut ns[source].arguments {
            if *a == root {
                *a = foreign;
            }
        }
    });
    completion_mutation(&r, source, |ns| ns[source].scope.quantifiers.clear());
    completion_mutation(&r, source, |ns| ns[source].scope.assignments = false);
    completion_mutation(&r, domain, |ns| {
        let Some(Payload::Domain { elements, .. }) = &mut ns[domain].payload else {
            panic!()
        };
        elements.pop();
        ns[domain].arguments.pop();
    });
    completion_mutation(&r, domain, |ns| {
        let Some(Payload::Domain { elements, .. }) = &mut ns[domain].payload else {
            panic!()
        };
        elements.push(elements[0]);
        let r = elements[0];
        ns[domain].arguments.push(r);
    });
    completion_mutation(&r, domain, |ns| ns[domain].support.clear());
    completion_mutation(&r, domain, |ns| ns[domain].scope.quantifiers.clear());
    completion_mutation(&r, domain, |ns| ns[domain].scope.snapshots.clear());
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    let member = elements
        .iter()
        .find(|n| {
            matches!(
                &r.nodes[n.0].payload,
                Some(Payload::Scalar(Scalar::Option { value: Some(_), .. }))
            )
        })
        .unwrap()
        .0;
    for (snapshot, subject) in [("v", "r"), ("empty", "p")] {
        completion_mutation(&r, member, |ns| {
            let Some(Payload::Scalar(Scalar::Option { value: Some(v), .. })) =
                &mut ns[member].payload
            else {
                panic!()
            };
            **v = Scalar::Subject {
                snapshot: snapshot.into(),
                subject: subject.into(),
                entity: "Reservations.State".into(),
            };
        });
    }
    completion_mutation(&r, member, |ns| ns[member].arguments.clear());
}
#[test]
fn dependent_answer_rechecks_request_producer_registry_and_successful_environment_changes() {
    let r = result();
    let cutoff = r.contexts.iter().position(|c| c.request == 4).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let request = &r.prepared.requests().requests()[3];
        let answer = &r.answers[3];
        e.validate_answer(&g, request, answer).unwrap();
        let source = source(&r);
        let original = g.nodes[source].clone();
        g.nodes[source].scope.quantifiers.clear();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.nodes[source] = original;
        e.validate_answer(&g, request, answer).unwrap();
        let original = g.requests[3].clone();
        g.requests[3].arguments[0].value = Selector::Answer {
            id: "other".into(),
            path: vec![crate::observed::projection::ProjectionStep::Field(
                "value".into(),
            )],
        };
        g.requests[3].dependencies = vec!["other".into(), "flag".into()];
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.requests[3] = original;
        e.validate_answer(&g, request, answer).unwrap();
        let position = g.checked_answers.iter().position(|(i, _)| *i == 0).unwrap();
        let original = g.checked_answers[position].1.clone();
        g.checked_answers[position].1.outputs = r.answers[1].outputs.clone();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.checked_answers[position].1 = original;
        e.validate_answer(&g, request, answer).unwrap();
        let mut altered = answer.clone();
        altered.scope.quantifiers.clear();
        assert!(matches!(
            e.validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        e.validate_answer(&g, request, answer).unwrap();
    }
}
fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "missing=evaluate(Reservations.adMissing,p=@v/p)",
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        "take=check(Reservations.option_values,a=$owner.value)",
        "later=evaluate(Reservations.seed)",
    ];
    let input = fixture::input(false, false, "r1");
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let declaration = &normal.prepared.inputs().law().declarations["Reservations.option_values"];
    let span = if mode == 0 {
        declaration.span
    } else {
        match &declaration.signature {
            Signature::Law { params, .. } => params[0].span,
            _ => panic!(),
        }
    };
    let (limits, usage, expected) = reservations_private_stop_usage(if mode == 1 { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
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
            Default::default()
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "owner" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = if mode == 0 {
                    operation == "dependent_domain_done" && index == 1
                } else {
                    operation == "answer_binding_scan" && index == 2
                };
                if at == span && ctx.request == 4 && target && (mode == 0 || ph.get()) {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 1 {
            let fresh = Environment::with_requests(
                normal.prepared.inputs(),
                normal.prepared.requests().requests(),
                &mut cc,
            )?;
            phase.set(true);
            let result = fresh.validate_answer(g, request, answer);
            phase.set(false);
            result?;
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    for (index, a) in stopped.answers.iter().enumerate().skip(4) {
        if mode == 1 && index == 4 {
            let original = &normal.answers[4];
            assert_eq!(a.status, original.status);
            assert_eq!(a.outputs, original.outputs);
            assert_eq!(a.claim, original.claim);
            assert_eq!(a.evidence, original.evidence);
            assert_eq!(a.scope, original.scope);
            for reason in &original.reasons {
                assert!(a.reasons.contains(reason));
            }
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn dependent_answer_fiber_stop_preserves_prior_values_refutation_missing_and_prefix() {
    stop(0)
}
#[test]
fn dependent_answer_fresh_recheck_stop_preserves_verified_claim_prefix_details_and_probe_freeze() {
    stop(1)
}
