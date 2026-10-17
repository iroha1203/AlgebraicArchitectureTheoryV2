#[allow(dead_code)]
mod application_fixture {
    use crate as archsig;
    include!("../../tests/common/map_application.rs");
}
fn application_result(asks: &[&str], mode: &str) -> ObservedEvaluation {
    let mut c = named_call_quiet();
    let p = prepare_observed(application_fixture::owned(mode), asks, &mut c).unwrap();
    evaluate_observed(p, &mut c).unwrap()
}
fn application_condition(r: &ObservedEvaluation, request: usize) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == request
                && matches!(n.payload, Some(Payload::MapDomainCondition { .. })))
            .then_some(i)
        })
        .unwrap()
}
#[test]
fn map_application_rechecks_value_key_image_type_support_scope_and_source() {
    let r = application_result(&["a=evaluate(Applications.apply,m=@v/m,x=@v/p)"], "known");
    assert_eq!(r.status(), "complete");
    let t = r.answers[0].outputs["value"].0;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=t]).unwrap();
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut nodes[t].payload else {
            panic!("ref")
        };
        *subject = "s".into();
    });
    completion_mutation(&r, t, |nodes| {
        nodes[t].ty = NodeType::Value(Type::Ref("Reservations.System".into()));
        let Some(Payload::Scalar(Scalar::Subject { entity, .. })) = &mut nodes[t].payload else {
            panic!("ref")
        };
        *entity = "Reservations.System".into();
    });
    completion_mutation(&r, t, |nodes| nodes[t].support.clear());
    completion_mutation(&r, t, |nodes| {
        nodes[t].scope.snapshots.remove("v");
    });
    completion_mutation(&r, t, |nodes| {
        let Rule::Input {
            location: Location::Law { span },
            ..
        } = &mut nodes[t].rule
        else {
            panic!("location")
        };
        span.0 += 1;
    });
    let key = r.nodes[t].arguments[1].0;
    completion_mutation(&r, key, |nodes| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut nodes[key].payload else {
            panic!("key")
        };
        *subject = "q".into();
    });
    let map = r.nodes[t].arguments[0].0;
    completion_mutation(&r, map, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[map].payload else {
            panic!("map")
        };
        let Scalar::Subject { subject, .. } = &mut pairs[0].1 else {
            panic!("image")
        };
        *subject = "s".into();
    });
}
#[test]
fn map_application_rejects_equal_other_request_value_and_condition_producers() {
    let r = application_result(
        &[
            "first=evaluate(Applications.apply,m=@v/m,x=@v/p)",
            "again=evaluate(Applications.apply,m=@v/m,x=@v/p)",
        ],
        "known",
    );
    let first = r.answers[0].outputs["value"].0;
    let current = r.answers[1].outputs["value"].0;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for index in [0, 1] {
        let donor = r.nodes[first].arguments[index];
        let actual = r.nodes[current].arguments[index];
        assert_ne!(donor, actual);
        assert_eq!(data_scalar_at(&r, donor.0), data_scalar_at(&r, actual.0));
        completion_mutation(&r, current, |nodes| nodes[current].arguments[index] = donor);
    }
    let r = application_result(
        &[
            "first=evaluate(Applications.apply,m=@v/m,x=@v/r)",
            "again=evaluate(Applications.apply,m=@v/m,x=@v/r)",
        ],
        "known",
    );
    let first = application_condition(&r, 0);
    let current = application_condition(&r, 1);
    let t = r.nodes[current].arguments[3].0;
    for i in [0, 1, 2] {
        let donor = r.nodes[first].arguments[i];
        assert_ne!(r.nodes[current].arguments[i], donor);
        completion_mutation(&r, t, |nodes| nodes[t].arguments[i] = donor);
    }
    let evaluation = r.answers[1].outputs["evaluation"].0;
    completion_mutation(&r, evaluation, |nodes| {
        let reason = nodes[evaluation]
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap();
        let ReasonKind::ConditionFailed { condition, .. } = &mut reason.kind else {
            panic!("reason")
        };
        *condition = NodeRef(first);
    });
}
#[test]
fn map_application_rechecks_condition_sets_counterexample_and_exact_failure_reason() {
    let r = application_result(&["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"], "known");
    assert_eq!(r.status(), "partial");
    let p = application_condition(&r, 0);
    let (left, right, evidence) = (
        r.nodes[p].arguments[3],
        r.nodes[p].arguments[4],
        r.nodes[p].arguments[5],
    );
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for t in [left.0, right.0] {
        let other = if t == left.0 { right.0 } else { left.0 };
        let replacement = r.nodes[other].payload.clone();
        completion_mutation(&r, t, |nodes| {
            nodes[t].payload = replacement.clone();
        });
        completion_mutation(&r, t, |nodes| nodes[t].support.clear());
        completion_mutation(&r, t, |nodes| {
            nodes[t].scope.snapshots.clear();
        });
    }
    completion_mutation(&r, evidence.0, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[evidence.0].payload else {
            panic!("evidence")
        };
        facts.clear();
    });
    completion_mutation(&r, evidence.0, |nodes| {
        let Some(Payload::Counterexample { left: actual, .. }) = &mut nodes[evidence.0].payload
        else {
            panic!("evidence")
        };
        *actual = right;
        nodes[evidence.0].arguments[3] = right;
    });
    completion_mutation(&r, p, |nodes| {
        nodes[p].judgment.as_mut().unwrap().status = Decision::Established;
    });
    completion_mutation(&r, p, |nodes| {
        let Some(Payload::MapDomainCondition { left: actual, .. }) = &mut nodes[p].payload else {
            panic!("condition")
        };
        *actual = right;
        nodes[p].arguments[3] = right;
    });
    completion_mutation(&r, p, |nodes| {
        nodes[p].evidence.clear();
        nodes[p].judgment.as_mut().unwrap().evidence.clear();
    });
    let evaluation = r.answers[0].outputs["evaluation"].0;
    for variant in 0..4 {
        completion_mutation(&r, evaluation, |nodes| match variant {
            0 => nodes[evaluation].reasons.clear(),
            1 => {
                let ReasonKind::ConditionFailed { construction, .. } =
                    &mut nodes[evaluation].reasons[0].kind
                else {
                    panic!("kind")
                };
                *construction = "domain";
            }
            2 => {
                nodes[evaluation].reasons[0].dependencies.clear();
            }
            _ => {
                let Some(Location::Law { span }) = &mut nodes[evaluation].reasons[0].location
                else {
                    panic!("location")
                };
                span.0 += 1;
            }
        });
    }
}
#[test]
fn map_application_normal_validation_does_not_authorize_later_condition_changes() {
    let r = application_result(&["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"], "known");
    let p = application_condition(&r, 0);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..p]).unwrap();
    g.active = r.contexts[p];
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.validate(&g, &r.nodes[p]).unwrap();
    let mut changed = r.nodes[p].clone();
    changed.judgment.as_mut().unwrap().status = Decision::Established;
    assert!(matches!(
        e.validate(&g, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&g, &r.nodes[p]).unwrap();
}
fn application_stop(kind: usize, phase: &'static str, at: usize, after_answer: bool) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Applications.prior)",
        "current=evaluate(Applications.apply,m=@v/m,x=@v/r)",
        "later=evaluate(Applications.seed)",
    ];
    let normal = application_result(&asks, "known");
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Usage::default()
        }
    });
    let prepared =
        prepare_observed(application_fixture::owned("known"), &asks, &mut control).unwrap();
    let law = prepared.inputs().sources().law().bytes().to_vec();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "prior" && !after_answer {
                let (arm, seen, law) = (armed.clone(), seen.clone(), law.clone());
                data::observe_iterations(move |span, context, operation, index| {
                    if context.request == 1
                        && operation == phase
                        && index == at
                        && &law[span.0..span.1] == b"m.states(x)"
                    {
                        assert!(!seen.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && after_answer {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(
        stopped.contexts.as_slice(),
        &normal.contexts[..stopped.contexts.len()]
    );
    assert_eq!(stopped.answers[0].status, Decision::Refuted);
    assert_eq!(
        format!("{:?}", stopped.answers[0]),
        format!("{:?}", normal.answers[0])
    );
    if after_answer {
        assert_eq!(stopped.answers[1].status, Decision::Undetermined);
        assert_eq!(
            format!("{:?}", stopped.answers[1]),
            format!("{:?}", normal.answers[1])
        );
    }
    for answer in &stopped.answers[if after_answer { 2 } else { 1 }..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty() && answer.evidence.is_empty() && answer.claim.is_none());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if s==&expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected) = expected.wire() else {
            unreachable!()
        };
        assert_eq!(actual["details"], expected["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}

#[test]
fn map_application_lookup_cancel_keeps_verified_prefix_and_prior_refutation() {
    application_stop(0, "map_lookup", 0, false);
}
#[test]
fn map_application_condition_time_stop_keeps_verified_prefix_and_prior_refutation() {
    application_stop(1, "map_condition", 0, false);
}
#[test]
fn map_application_condition_memory_stop_keeps_verified_prefix_and_prior_refutation() {
    application_stop(2, "map_condition", 1, false);
}
#[test]
fn map_application_answer_stop_retains_completed_condition_and_verified_answer() {
    application_stop(0, "answer", 0, true);
}

#[test]
fn map_application_recheck_stops_freeze_the_shared_control() {
    use std::{cell::Cell, rc::Rc};
    let r = application_result(&["a=evaluate(Applications.apply,m=@v/m,x=@v/r)"], "known");
    let target = application_condition(&r, 0);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..target]).unwrap();
    graph.active = r.contexts[target];
    for kind in [0, 1, 2] {
        let (limits, usage, expected) = reservations_private_stop_usage(kind);
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let mut control = Control::new(limits, move |_| {
            count.set(count.get() + 1);
            if arm.get() {
                usage
            } else {
                super::super::control::Usage::default()
            }
        });
        let environment = Environment::new(r.prepared.inputs(), &mut control).unwrap();
        environment.validate(&graph, &r.nodes[target]).unwrap();
        armed.set(true);
        assert!(
            matches!(environment.validate(&graph,&r.nodes[target]),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        let frozen = probes.get();
        assert!(
            matches!(environment.validate(&graph,&r.nodes[target]),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        assert_eq!(probes.get(), frozen);
    }
}
