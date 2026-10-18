use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/compound_owned_binding.rs");
}
const GOOD: &[&str] = &[
    "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "b=evaluate(Applications.cbOwner,a=@v/B)",
    "v=evaluate(Applications.cbMap,m=@v/m)",
    "other=evaluate(Applications.cbMap,m=@v/m)",
    "otherB=evaluate(Applications.cbOwner,a=@v/B)",
    "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
const BAD: &[&str] = &[
    "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "b=evaluate(Applications.cbOwner,a=@v/A)",
    "v=evaluate(Applications.cbMap,m=@v/m)",
    "other=evaluate(Applications.cbMap,m=@v/m)",
    "otherB=evaluate(Applications.cbOwner,a=@v/A)",
    "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)",
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
fn run(asks: &[&str]) -> ObservedEvaluation {
    run_with("known", asks)
}
fn run_with(mode: &str, asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input(mode, "r1"), asks, &mut named_call_quiet())
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
#[test]
fn compound_owned_binding_recheck_rejects_all_owner_edges_value_check_and_source_bypass() {
    let r = run(GOOD);
    assert_eq!(r.status(), "complete");
    let i = r
        .nodes
        .iter()
        .position(|n| matches!(&n.rule,Rule::OwnedBinding(p)if p=="x"))
        .unwrap();
    assert_eq!(r.nodes[i].arguments.len(), 3);
    assert_eq!(
        r.nodes[i].arguments,
        [
            r.answers[2].outputs["value"],
            r.answers[0].outputs["value"],
            r.answers[1].outputs["value"]
        ]
    );
    let foreign = r.answers[3].outputs["value"];
    assert_ne!(foreign, r.nodes[i].arguments[0]);
    assert_eq!(
        r.nodes[foreign.0].payload,
        r.nodes[r.nodes[i].arguments[0].0].payload
    );
    completion_mutation(&r, i, |ns| ns[i].arguments[0] = foreign);
    let foreign_owner = r.answers[4].outputs["value"];
    assert_ne!(foreign_owner, r.nodes[i].arguments[2]);
    assert_eq!(
        r.nodes[foreign_owner.0].payload,
        r.nodes[r.nodes[i].arguments[2].0].payload
    );
    completion_mutation(&r, i, |ns| ns[i].arguments[2] = foreign_owner);
    completion_mutation(&r, i, |ns| {
        ns[i].arguments.remove(1);
    });
    completion_mutation(&r, i, |ns| {
        ns[i]
            .support
            .retain(|f| f.atom.as_deref() != Some("q-owner"));
    });
    completion_mutation(&r, i, |ns| ns[i].scope.quantifiers.clear());
    completion_mutation(&r, i, |ns| {
        ns[i].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    let source = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(j, n)| {
            (r.contexts[j].request == 5 && matches!(n.payload, Some(Payload::Expression { .. })))
                .then_some(j)
        })
        .unwrap();
    completion_mutation(&r, source, |ns| {
        ns[source].arguments.retain(|r| *r != NodeRef(i))
    });
    completion_mutation(&r, source, |ns| {
        for edge in &mut ns[source].arguments {
            if *edge == NodeRef(i) {
                *edge = r.nodes[i].arguments[0];
            }
        }
    });
}
#[test]
fn compound_owned_conditions_recheck_three_inputs_all_typed_parts_and_roster_support() {
    let r = run(BAD);
    assert_eq!(r.status(), "partial");
    let parts: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            matches!(&n.rule,Rule::ProjectionCheck{parameter,..}if parameter=="x").then_some(i)
        })
        .collect();
    assert_eq!(parts.len(), 5);
    for &i in &parts {
        completion_mutation(&r, i, |ns| ns[i].support.clear());
        completion_mutation(&r, i, |ns| ns[i].scope.quantifiers.clear());
        completion_mutation(&r, i, |ns| {
            ns[i].arguments.remove(2);
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
    let Some(Payload::ProjectionCondition { inputs, .. }) = &r.nodes[*condition].payload else {
        panic!()
    };
    assert_eq!(inputs.len(), 3);
    assert_eq!(
        inputs,
        &vec![
            r.answers[2].outputs["value"],
            r.answers[0].outputs["value"],
            r.answers[1].outputs["value"]
        ]
    );
    for kind in 0..5 {
        completion_mutation(&r, *condition, |ns| {
            let Some(Payload::ProjectionCondition { inputs, .. }) = &mut ns[*condition].payload
            else {
                panic!()
            };
            match kind {
                0 => {
                    inputs.pop();
                }
                1 => inputs.clear(),
                2 => inputs.swap(1, 2),
                3 => inputs.push(inputs[1]),
                _ => inputs[0] = r.answers[3].outputs["value"],
            }
        });
    }
    let mut answer = r.answers[5].clone();
    for reason in &mut answer.reasons {
        if matches!(reason.kind, ReasonKind::ConditionFailed { .. }) {
            reason.dependencies.pop();
        }
    }
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert!(matches!(
        env(&r).validate_answer(&g, &r.prepared.requests().requests()[5], &answer),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn compound_owned_same_and_fresh_recheck_detects_mutation_after_success_and_accepts_restoration() {
    for asks in [GOOD, BAD] {
        let r = run(asks);
        let cutoff = r.contexts.iter().position(|c| c.request == 6).unwrap();
        for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
            let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
            let e = env(&r);
            let request = &r.prepared.requests().requests()[5];
            let answer = &r.answers[5];
            e.validate_answer(&g, request, answer).unwrap();
            let i = g
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
            let saved = g.nodes[i].clone();
            g.nodes[i].support.clear();
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
            g.requests[5]
                .arguments
                .iter_mut()
                .find(|a| a.name == "bind.b")
                .unwrap()
                .value = Selector::Answer {
                id: "otherB".into(),
                path: vec![crate::observed::projection::ProjectionStep::Field(
                    "value".into(),
                )],
            };
            g.requests[5].dependencies = vec!["a".into(), "otherB".into(), "v".into()];
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
            let saved = g.requests[5].clone();
            g.requests[5]
                .constraints
                .iter_mut()
                .find(|c| c.parameter == "x")
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
            g.requests[5] = saved;
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
    let producer = if mode == 0 {
        "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)"
    } else {
        "v=evaluate(Applications.cbMap,m=@v/m)"
    };
    let b = if mode == 2 {
        "b=evaluate(Applications.cbOwner,a=@v/A)"
    } else {
        "b=evaluate(Applications.cbOwner,a=@v/B)"
    };
    let take = if mode == 0 {
        "take=check(Applications.cbFamily,a=$a.value,x=$v.value)"
    } else {
        "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)"
    };
    let asks = [
        "seed=evaluate(Applications.seed)",
        "prior=check(Applications.prior)",
        "missing=evaluate(Applications.cbMissing,p=@v/p)",
        "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
        b,
        producer,
        take,
        "later=evaluate(Applications.seed)",
    ];
    let input = fixture::input("stop", "r1");
    let normal = run_with("stop", &asks);
    assert_eq!(normal.status(), "partial");
    let declaration = if mode == 0 {
        "Applications.cbFamily"
    } else {
        "Applications.cbEq"
    };
    let params = match &normal.prepared.inputs().law().declarations[declaration].signature {
        Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    if mode == 3 {
        assert!(normal.answers[6].claim.is_some());
        assert!(!normal.answers[6].evidence.is_empty());
    }
    let span = params[if mode == 0 { 1 } else { 2 }].span;
    let (limits, usage, expected) = reservations_private_stop_usage(mode.min(2));
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
        if request.id == "v" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = match mode {
                    0 => operation == "owned_call_constraint",
                    1 => operation == "owned_call_map_domain_roster" && index == 1,
                    2 => operation == "answer_projection_condition" && index == 5,
                    _ => operation == "owned_binding_checked" && ph.get(),
                };
                if at == span && ctx.request == 6 && target {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 3 {
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
    assert_eq!(&stopped.answers[..6], &normal.answers[..6]);
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
    for (i, a) in stopped.answers.iter().enumerate().skip(6) {
        if mode == 3 && i == 6 {
            let original = &normal.answers[6];
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
fn compound_owned_member_stop_preserves_prior_values_refutation_missing_and_prefix() {
    stop(0)
}
#[test]
fn compound_owned_map_domain_stop_preserves_exact_budget_and_prefix() {
    stop(1)
}
#[test]
fn compound_owned_condition_stop_preserves_prior_results_and_probe_freeze() {
    stop(2)
}
#[test]
fn compound_owned_fresh_recheck_stop_preserves_nonempty_claim_and_evidence() {
    stop(3)
}
