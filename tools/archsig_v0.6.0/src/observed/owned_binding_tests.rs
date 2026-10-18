use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/owned_binding.rs");
}
const GOOD: &[&str] = &[
    "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "otherOwner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "child=evaluate(Reservations.obChild,p=@v/p)",
    "otherChild=evaluate(Reservations.obChild,p=@v/p)",
    "take=check(Reservations.obFamily,a=$owner.value,p=$child.value)",
    "later=evaluate(Reservations.seed)",
];
const BAD: &[&str] = &[
    "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "otherOwner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "child=evaluate(Reservations.obChild,p=@v/r)",
    "otherChild=evaluate(Reservations.obChild,p=@v/r)",
    "take=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)",
    "later=evaluate(Reservations.seed)",
];
#[test]
fn owned_subject_binding_cannot_reuse_a_prior_requests_equal_membership_check() {
    let r = run(&[
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        "child=evaluate(Reservations.obChild,p=@v/p)",
        "first=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)",
        "take=evaluate(Reservations.obUse,a=$owner.value,p=@v/p)",
        "later=evaluate(Reservations.seed)",
    ]);
    assert_eq!(r.status(), "complete");
    let prior = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 2 && matches!(n.rule, Rule::OwnedBinding(_)))
                .then_some(NodeRef(i))
        })
        .unwrap();
    assert_eq!(r.answers[2].outputs["value"], r.answers[1].outputs["value"]);
    let own = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 3 && matches!(n.rule, Rule::OwnedBinding(_)))
                .then_some(NodeRef(i))
        })
        .unwrap();
    assert_ne!(own, prior);
    assert_eq!(r.nodes[own.0].payload, r.nodes[prior.0].payload);
    let source = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 3 && matches!(n.payload, Some(Payload::Expression { .. })))
                .then_some(i)
        })
        .unwrap();
    completion_mutation(&r, source, |ns| {
        for edge in &mut ns[source].arguments {
            if *edge == own {
                *edge = prior;
            }
        }
    });
}
fn run(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| {
        panic!(
            "{:?}",
            e.wire().map(|w| match &w {
                Json::Obj(m) => m.get("issues").cloned(),
                _ => None,
            })
        )
    });
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (req, a) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, req, a).unwrap();
    }
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
#[test]
fn owned_binding_recheck_rejects_changed_value_owner_support_scope_and_bypassed_check() {
    let r = run(GOOD);
    assert_eq!(r.status(), "complete");
    let i = r
        .nodes
        .iter()
        .position(|n| matches!(&n.rule,Rule::OwnedBinding(p) if p=="p"))
        .unwrap();
    let original = r.nodes[i].arguments[0];
    let foreign = r.answers[3].outputs["value"];
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0].payload, r.nodes[foreign.0].payload);
    completion_mutation(&r, i, |ns| ns[i].arguments[0] = foreign);
    completion_mutation(&r, i, |ns| {
        ns[i].arguments.pop();
    });
    completion_mutation(&r, i, |ns| ns[i].support.clear());
    completion_mutation(&r, i, |ns| ns[i].scope.quantifiers.clear());
    completion_mutation(&r, i, |ns| ns[i].scope.assignments = false);
    completion_mutation(&r, i, |ns| {
        ns[i].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    completion_mutation(&r, i, |ns| ns[i].rule = Rule::OwnedBinding("a".into()));
    let source=r.nodes.iter().enumerate().find_map(|(j,n)|(r.contexts[j].request==4 && matches!(&n.payload,Some(Payload::Expression{parameters,..})if !parameters.is_empty())).then_some(j)).unwrap();
    completion_mutation(&r, source, |ns| {
        for edge in &mut ns[source].arguments {
            if *edge == NodeRef(i) {
                *edge = original;
            }
        }
    });
    completion_mutation(&r, source, |ns| {
        ns[source].arguments.retain(|r| *r != NodeRef(i))
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        bindings.iter_mut().find(|b| b.name == "p").unwrap().value = foreign;
        for edge in &mut ns[source].arguments {
            if *edge == original {
                *edge = foreign;
            }
        }
    });
}
#[test]
fn owned_binding_conditions_recheck_all_inputs_typed_parts_scope_support_and_reasons() {
    let r = run(BAD);
    assert_eq!(r.status(), "partial");
    let parts: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            matches!(&n.rule,Rule::ProjectionCheck{parameter,..}if parameter=="p").then_some(i)
        })
        .collect();
    assert_eq!(parts.len(), 5);
    for &i in &parts {
        completion_mutation(&r, i, |ns| ns[i].support.clear());
        completion_mutation(&r, i, |ns| ns[i].scope.quantifiers.clear());
        completion_mutation(&r, i, |ns| {
            ns[i].arguments.remove(1);
        });
    }
    let [name, actual, required, evidence, condition] = parts.as_slice() else {
        panic!()
    };
    completion_mutation(&r, *name, |ns| {
        ns[*name].payload = Some(Payload::Scalar(Scalar::Text("other".into())))
    });
    completion_mutation(&r, *actual, |ns| {
        ns[*actual].payload = Some(Payload::Scalar(Scalar::Bool(true)))
    });
    completion_mutation(&r, *required, |ns| {
        ns[*required].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    completion_mutation(&r, *evidence, |ns| {
        ns[*evidence].ty = NodeType::Value(Type::Bool)
    });
    completion_mutation(&r, *condition, |ns| {
        ns[*condition].judgment.as_mut().unwrap().status = Decision::Established
    });
    completion_mutation(&r, *condition, |ns| ns[*condition].evidence.clear());
    let mut answer = r.answers[4].clone();
    let e = env(&r);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for reason in &mut answer.reasons {
        if matches!(reason.kind, ReasonKind::ConditionFailed { .. }) {
            reason.dependencies.pop();
        }
    }
    assert!(matches!(
        e.validate_answer(&g, &r.prepared.requests().requests()[4], &answer),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn owned_binding_success_then_changed_request_registry_and_nodes_rejects_same_and_fresh_restores() {
    for asks in [GOOD, BAD] {
        let r = run(asks);
        let cutoff = r.contexts.iter().position(|c| c.request == 5).unwrap();
        for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
            let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
            let e = env(&r);
            let request = &r.prepared.requests().requests()[4];
            let answer = &r.answers[4];
            e.validate_answer(&g, request, answer).unwrap();
            let target = g
                .nodes
                .iter()
                .position(|n| {
                    matches!(
                        n.rule,
                        Rule::OwnedBinding(_)
                            | Rule::ProjectionCheck {
                                part: ProjectionCheckPart::Condition,
                                ..
                            }
                    )
                })
                .unwrap();
            let saved = g.nodes[target].clone();
            g.nodes[target].support.clear();
            assert!(matches!(
                e.validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            g.nodes[target] = saved;
            e.validate_answer(&g, request, answer).unwrap();
            if let Some((source, span, bindings)) = g.nodes.iter().enumerate().find_map(|(i, n)| {
                if r.contexts[i].request != 4 {
                    return None;
                }
                match &n.payload {
                    Some(Payload::Expression {
                        location: Location::Law { span },
                        bindings,
                        ..
                    }) => Some((i, *span, bindings.clone())),
                    _ => None,
                }
            }) {
                let source_context = g.context_at(source);
                let previous = std::mem::replace(&mut g.active, source_context);
                e.source_arguments(&g, span, &bindings).unwrap();
                for invalid in [
                    Selector::Declaration {
                        name: "Reservations.absent".into(),
                    },
                    Selector::Subject {
                        snapshot: "v".into(),
                        subject: "A".into(),
                    },
                ] {
                    let original = std::mem::replace(&mut g.requests[4].head, invalid);
                    assert!(matches!(
                        e.source_arguments(&g, span, &bindings),
                        Err(ValidationFailure::Internal(_))
                    ));
                    g.requests[4].head = original;
                    e.source_arguments(&g, span, &bindings).unwrap();
                }
                g.active = previous;
                e.validate_answer(&g, request, answer).unwrap();
            }
            let saved = g.requests[4].clone();
            g.requests[4]
                .arguments
                .iter_mut()
                .find(|a| a.name == "bind.p")
                .unwrap()
                .value = Selector::Answer {
                id: "otherChild".into(),
                path: vec![crate::observed::projection::ProjectionStep::Field(
                    "value".into(),
                )],
            };
            g.requests[4].dependencies = vec!["owner".into(), "otherChild".into()];
            assert!(matches!(
                e.validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            g.requests[4] = saved;
            e.validate_answer(&g, request, answer).unwrap();
            let saved = g.requests[4].clone();
            g.requests[4]
                .constraints
                .iter_mut()
                .find(|c| c.parameter == "p")
                .unwrap()
                .dynamic = false;
            assert!(matches!(
                e.validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            g.requests[4] = saved;
            e.validate_answer(&g, request, answer).unwrap();
            let k = g.checked_answers.iter().position(|(k, _)| *k == 2).unwrap();
            let saved = g.checked_answers[k].1.clone();
            g.checked_answers[k].1.outputs = r.answers[3].outputs.clone();
            assert!(matches!(
                e.validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, request, answer),
                Err(ValidationFailure::Internal(_))
            ));
            g.checked_answers[k].1 = saved;
            e.validate_answer(&g, request, answer).unwrap();
        }
    }
}
fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let child = if mode == 1 {
        "child=evaluate(Reservations.obChild,p=@v/r)"
    } else {
        "child=evaluate(Reservations.obChild,p=@v/p)"
    };
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "missing=evaluate(Reservations.adMissing,p=@v/p)",
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        child,
        if mode == 2 {
            "take=check(Reservations.obEq,a=$owner.value,p=$child.value)"
        } else {
            "take=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)"
        },
        "later=evaluate(Reservations.seed)",
    ];
    let input = fixture::input(false, false, "r1");
    let normal = run(&asks);
    assert_eq!(normal.status(), "partial");
    let declaration = if mode == 2 {
        "Reservations.obEq"
    } else {
        "Reservations.obUse"
    };
    let params = match &normal.prepared.inputs().law().declarations[declaration].signature {
        Signature::View { params, .. } | Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    if mode == 2 {
        assert!(normal.answers[5].claim.is_some());
        assert!(!normal.answers[5].evidence.is_empty());
    }
    let span = params[1].span;
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
        if request.id == "child" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = match mode {
                    0 => operation == "owned_binding_checked",
                    1 => operation == "answer_projection_condition" && index == 5,
                    _ => operation == "owned_binding_checked" && ph.get(),
                };
                if at == span && ctx.request == 5 && target {
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
    for (i, a) in stopped.answers.iter().enumerate().skip(5) {
        if mode == 2 && i == 5 {
            let original = &normal.answers[5];
            assert!(a.claim.is_some());
            assert!(!a.evidence.is_empty());
            assert_eq!(a.status, original.status);
            assert_eq!(a.outputs, original.outputs);
            assert_eq!(a.claim, original.claim);
            assert_eq!(a.evidence, original.evidence);
            assert_eq!(a.scope, original.scope);
            for r in &original.reasons {
                assert!(a.reasons.contains(r));
            }
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(actual), Json::Obj(wanted)) = (&reason.wire(), &expected.wire()) else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_binding_actual_membership_stop_preserves_prior_values_refutation_missing_and_prefix() {
    stop(0)
}
#[test]
fn owned_binding_condition_generation_stop_preserves_prior_results_and_probe_freeze() {
    stop(1)
}
#[test]
fn owned_binding_fresh_recheck_stop_preserves_verified_claim_details_and_probe_freeze() {
    stop(2)
}
