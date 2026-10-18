use super::*;
use crate::law::model::Signature;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/free_compound_answer_binding.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "missing=evaluate(Applications.cbMissing,p=@v/p)",
    "v=evaluate(Applications.fcMapAll,m=@v/m)",
    "other=evaluate(Applications.fcMapAll,m=@v/m)",
    "take=check(Applications.fcMap,x=$v.value)",
    "later=evaluate(Applications.seed)",
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
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial");
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (q, a) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, q, a).unwrap();
    }
    r
}
fn source(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==5 && r.contexts[i].instance.is_none() && matches!(&n.payload,Some(Payload::Expression{parameters,..})if !parameters.is_empty())).then_some(i)).unwrap()
}
fn fixed_domain(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==5 && matches!(&n.payload,Some(Payload::Domain{ty:Type::Map(..),elements})if elements.len()==1)).then_some(i)).unwrap()
}
#[test]
fn free_compound_answer_fibers_recheck_original_fixed_ref_owner_domains_rows_support_and_scope() {
    let r = result();
    let source = source(&r);
    let domain = fixed_domain(&r);
    let original = r.answers[3].outputs["value"];
    let foreign = r.answers[4].outputs["value"];
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0].payload, r.nodes[foreign.0].payload);
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].value, original);
        bindings[0].value = foreign;
        for a in &mut ns[source].arguments {
            if *a == original {
                *a = foreign;
            }
        }
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source].payload else {
            panic!()
        };
        parameters.pop();
    });
    completion_mutation(&r, source, |ns| ns[source].scope.quantifiers.clear());
    completion_mutation(&r, domain, |ns| {
        let Some(Payload::Domain { elements, .. }) = &mut ns[domain].payload else {
            panic!()
        };
        elements.clear();
        ns[domain].arguments.pop();
    });
    completion_mutation(&r, domain, |ns| {
        ns[domain]
            .support
            .retain(|f| f.atom.as_deref() != Some("p-owner"))
    });
    completion_mutation(&r, domain, |ns| ns[domain].scope.quantifiers.clear());
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    let member = elements[0].0;
    completion_mutation(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[member].payload else {
            panic!()
        };
        assert_eq!(pairs.len(), 2);
        pairs.pop();
    });
    let row = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 5 && matches!(&n.payload, Some(Payload::LawInstance { .. })))
                .then_some(i)
        })
        .unwrap();
    completion_mutation(&r, row, |ns| ns[row].scope.quantifiers.clear());
}
#[test]
fn free_compound_answer_successful_rechecks_reject_request_registry_and_changed_source_restore_same_and_fresh()
 {
    let r = result();
    let cutoff = r.contexts.iter().position(|c| c.request == 6).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let request = &r.prepared.requests().requests()[5];
        let answer = &r.answers[5];
        e.validate_answer(&g, request, answer).unwrap();
        let i = source(&r);
        let saved = g.nodes[i].clone();
        g.nodes[i].scope.quantifiers.clear();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.nodes[i] = saved;
        e.validate_answer(&g, request, answer).unwrap();
        let saved = g.requests[5].clone();
        g.requests[5].arguments[0].value = Selector::Answer {
            id: "other".into(),
            path: vec![crate::observed::projection::ProjectionStep::Field(
                "value".into(),
            )],
        };
        g.requests[5].dependencies = vec!["other".into()];
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.requests[5] = saved;
        e.validate_answer(&g, request, answer).unwrap();
        let i = g.checked_answers.iter().position(|(i, _)| *i == 3).unwrap();
        let saved = g.checked_answers[i].1.clone();
        g.checked_answers[i].1.outputs = r.answers[4].outputs.clone();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.checked_answers[i].1 = saved;
        e.validate_answer(&g, request, answer).unwrap();
    }
}

fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = ASK;
    let input = fixture::input("stop", "r1");
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let declaration = &normal.prepared.inputs().law().declarations["Applications.fcMap"];
    assert!(normal.answers[5].claim.is_some());
    assert!(!normal.answers[5].evidence.is_empty());
    let span = match &declaration.signature {
        Signature::Law { params, .. } => params[2].span,
        _ => panic!(),
    };
    let (limits, usage, expected) = reservations_private_stop_usage(mode);
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
        if request.id == "other" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = match mode {
                    0 => operation == "owned_call_constraint" && index == 0,
                    1 => operation == "owned_call_map_domain_roster" && index == 3,
                    _ => operation == "owned_call_map_domain" && index == 0,
                };
                if at == span && ctx.request == 5 && target && (mode != 2 || ph.get()) {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 2 {
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
    assert_eq!(&stopped.answers[..5], &normal.answers[..5]);
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
    for (index, a) in stopped.answers.iter().enumerate().skip(5) {
        if mode == 2 && index == 5 {
            let original = &normal.answers[5];
            assert!(a.claim.is_some());
            assert!(!a.evidence.is_empty());
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
fn free_compound_answer_member_cancel_keeps_prior_answers_prefix_and_probe_freeze() {
    stop(0)
}
#[test]
fn free_compound_answer_map_domain_budget_keeps_values_refutation_missing_and_prefix() {
    stop(1)
}
#[test]
fn free_compound_answer_fresh_recheck_stop_keeps_nonempty_claim_evidence_and_probe_freeze() {
    stop(2)
}
