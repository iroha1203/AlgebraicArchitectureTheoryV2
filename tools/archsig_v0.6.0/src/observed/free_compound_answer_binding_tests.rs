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

#[test]
fn free_compound_unknown_owner_recheck_preserves_completion_scope_and_rejects_finite_scope() {
    for (law, producer) in [
        ("fcList", "cbList,p=@v/p,q=@v/q"),
        ("fcDomain", "cbMap,m=@v/m"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let take = format!("take=check(Applications.{law},x=$v.value)");
        let other = format!("other=evaluate(Applications.{producer})");
        let r = evaluate_observed_bytes(
            fixture::input("unknown_owner", "r1"),
            &[&make, &other, &take, "later=evaluate(Applications.seed)"],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "complete", "{law}: {:?}", r.answers);
        assert_eq!(r.answers[0].status, Decision::Established);
        let original = &r.answers[2];
        assert!(original.scope.completions);
        assert_eq!(original.status, Decision::Established);
        assert!(original.outputs.contains_key("evaluation"));
        assert!(original.claim.is_some());
        assert!(!original.evidence.is_empty());
        assert!(
            original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.subject == "p"
                        && f.field.as_deref() == Some("Reservations.State.owner")
                        && f.atom.is_none()))
        );
        assert!(
            !original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        );
        let value = r.answers[0].outputs["value"];
        let foreign = r.answers[1].outputs["value"];
        assert_ne!(value, foreign);
        assert_eq!(r.nodes[value.0].payload, r.nodes[foreign.0].payload);
        let seed = r
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                (r.contexts[i].request == 2
                    && matches!(&n.payload, Some(Payload::CompletionSeed { .. })))
                .then_some(i)
            })
            .unwrap();
        completion_mutation(&r, seed, |nodes| {
            let Some(Payload::CompletionSeed { bindings, .. }) = &mut nodes[seed].payload else {
                panic!()
            };
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].value, value);
            bindings[0].value = foreign;
            for argument in &mut nodes[seed].arguments {
                if *argument == value {
                    *argument = foreign;
                }
            }
        });
        let case_source = r.nodes.iter().enumerate().find_map(|(i, n)| {
            (r.contexts[i].request == 2 && r.contexts[i].case.is_some()
                && matches!(&n.payload, Some(Payload::Expression { bindings, .. }) if bindings.iter().any(|b| b.value == value))).then_some(i)
        }).unwrap();
        completion_mutation(&r, case_source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[case_source].payload else {
                panic!()
            };
            bindings
                .iter_mut()
                .find(|b| b.value == value)
                .unwrap()
                .value = foreign;
            for argument in &mut nodes[case_source].arguments {
                if *argument == value {
                    *argument = foreign;
                }
            }
        });
        let cutoff = r.contexts.iter().position(|c| c.request == 3).unwrap();
        for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
            let g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
            let e = env(&r);
            let req = &r.prepared.requests().requests()[2];
            e.validate_answer(&g, req, original).unwrap();
            let mut wrong = original.clone();
            wrong.scope.completions = false;
            assert_ne!(&wrong, original);
            assert!(matches!(
                e.validate_answer(&g, req, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, req, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
            e.validate_answer(&g, req, original).unwrap();
            env(&r).validate_answer(&g, req, original).unwrap();
        }
    }
}
#[test]
fn free_compound_dynamic_projection_conditions_recheck_original_root_scope_and_direct_reasons() {
    let asks = [
        "seed=evaluate(Applications.seed)",
        "prior=check(Applications.prior)",
        "missing=evaluate(Applications.cbMissing,p=@v/p)",
        "v=evaluate(Applications.cbMapWrapped,m=@v/m)",
        "other=evaluate(Applications.cbMapWrapped,m=@v/m)",
        "take=check(Applications.fcMap,x=$v.value.some[99])",
        "later=evaluate(Applications.seed)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial");
    let original = r.answers[3].outputs["value"];
    let foreign = r.answers[4].outputs["value"];
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0].payload, r.nodes[foreign.0].payload);
    let parts: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            (r.contexts[i].request == 5
                && matches!(&n.rule,Rule::ProjectionCheck{parameter,..}if parameter=="x"))
            .then_some(i)
        })
        .collect();
    assert_eq!(parts.len(), 5);
    for &i in &parts {
        assert_eq!(r.nodes[i].arguments[0], original);
        completion_mutation(&r, i, |ns| ns[i].arguments[0] = foreign);
        completion_mutation(&r, i, |ns| ns[i].support.clear());
        completion_mutation(&r, i, |ns| ns[i].scope.snapshots.clear());
    }
    let cutoff = r.contexts.iter().position(|c| c.request == 6).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let req = &r.prepared.requests().requests()[5];
        let original = &r.answers[5];
        e.validate_answer(&g, req, original).unwrap();
        let mut wrong = original.clone();
        wrong
            .reasons
            .retain(|reason| !matches!(&reason.kind, ReasonKind::DependencyBlocked { .. }));
        assert_ne!(&wrong, original);
        assert!(matches!(
            e.validate_answer(&g, req, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, req, &wrong),
            Err(ValidationFailure::Internal(_))
        ));
        e.validate_answer(&g, req, original).unwrap();
        env(&r).validate_answer(&g, req, original).unwrap();
    }
}
