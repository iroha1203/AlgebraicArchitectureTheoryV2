mod finite_map_fixture {
    include!("../../tests/common/finite_map.rs");
}
fn finite_map_private_inputs() -> InputSources {
    let definitions = finite_map_fixture::DEFINITIONS.as_bytes();
    let d = crate::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        finite_map_fixture::law(digest).into_bytes(),
        finite_map_fixture::archmap(digest, "r1").into_bytes(),
    )
}
fn finite_map_private_owned_inputs() -> InputSources {
    let definitions = finite_map_fixture::OWNED_DEFINITIONS.as_bytes();
    let d = crate::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        finite_map_fixture::owned_law(digest).into_bytes(),
        finite_map_fixture::owned_archmap(false).into_bytes(),
    )
}
fn finite_map_private_result(asks: &[&str]) -> ObservedEvaluation {
    let mut control = named_call_quiet();
    let p = prepare_observed(finite_map_private_inputs(), asks, &mut control).unwrap();
    evaluate_observed(p, &mut control).unwrap()
}
fn finite_map_private_domain(r: &ObservedEvaluation, request: usize) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == request
                && matches!(
                    n.payload,
                    Some(Payload::Domain {
                        ty: Type::Map(..),
                        ..
                    })
                ))
            .then_some(i)
        })
        .unwrap()
}
fn finite_map_private_members(r: &ObservedEvaluation, d: usize) -> Vec<NodeRef> {
    let Some(Payload::Domain { elements, .. }) = &r.nodes[d].payload else {
        panic!("domain")
    };
    elements.clone()
}
#[test]
fn finite_map_domains_recheck_totality_membership_type_support_and_scope() {
    let r = finite_map_private_result(&["a=evaluate(Maps.every)"]);
    assert_eq!(r.status(), "complete");
    let d = finite_map_private_domain(&r, 0);
    let es = finite_map_private_members(&r, d);
    assert_eq!(es.len(), 4);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=d]).unwrap();
    completion_mutation(&r, d, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[d].payload else {
            unreachable!()
        };
        elements.pop();
        nodes[d].arguments.pop();
    });
    completion_mutation(&r, d, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[d].payload else {
            unreachable!()
        };
        elements[1] = elements[0];
        nodes[d].arguments[2] = nodes[d].arguments[1];
    });
    let t = es[0].0;
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[t].payload else {
            unreachable!()
        };
        pairs.pop();
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[t].payload else {
            unreachable!()
        };
        let Scalar::Subject { subject, .. } = &mut pairs[0].1 else {
            unreachable!()
        };
        *subject = "absent".into();
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { codomain, .. })) = &mut nodes[t].payload else {
            unreachable!()
        };
        *codomain = Type::Ref("Maps.Void".into());
    });
    completion_mutation(&r, t, |nodes| {
        nodes[t].support.clear();
    });
    completion_mutation(&r, d, |nodes| {
        nodes[d].scope.snapshots.remove("w");
    });
}
#[test]
fn finite_owned_map_domains_reject_equal_other_request_owner_producers() {
    let mut c = named_call_quiet();
    let p = prepare_observed(
        finite_map_private_owned_inputs(),
        &[
            "first=evaluate(Reservations.every,a=@v/A,b=@v/B)",
            "again=evaluate(Reservations.every,a=@v/A,b=@v/B)",
        ],
        &mut c,
    )
    .unwrap();
    let r = evaluate_observed(p, &mut c).unwrap();
    assert_eq!(r.status(), "complete");
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let first = finite_map_private_domain(&r, 0);
    let current = finite_map_private_domain(&r, 1);
    let donor = r.nodes[first].arguments[1];
    let actual = r.nodes[current].arguments[1];
    assert_ne!(donor, actual);
    assert_eq!(data_scalar_at(&r, donor.0), data_scalar_at(&r, actual.0));
    completion_mutation(&r, current, |nodes| {
        nodes[current].arguments[1] = donor;
    });
    let source = r.nodes[current].arguments[0].0;
    completion_mutation(&r, source, |nodes| {
        let i = nodes[source].arguments.len() - 2;
        assert_eq!(nodes[source].arguments[i], actual);
        nodes[source].arguments[i] = donor;
    });
    completion_mutation(&r, source, |nodes| {
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &mut nodes[source].payload
        else {
            unreachable!()
        };
        span.0 += 1;
    });
}
#[test]
fn finite_map_domain_success_does_not_authorize_later_missing_function() {
    let r = finite_map_private_result(&["a=evaluate(Maps.every)"]);
    let t = finite_map_private_domain(&r, 0);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..t]).unwrap();
    graph.active = r.contexts[t];
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.validate(&graph, &r.nodes[t]).unwrap();
    let mut changed = r.nodes[t].clone();
    let Some(Payload::Domain { elements, .. }) = &mut changed.payload else {
        unreachable!()
    };
    elements.pop();
    changed.arguments.pop();
    assert_ne!(format!("{changed:?}"), format!("{:?}", r.nodes[t]));
    assert!(matches!(
        e.validate(&graph, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&graph, &r.nodes[t]).unwrap();
}
fn finite_map_private_stop(kind: usize, after_answer: bool) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Maps.prior)",
        "current=evaluate(Maps.every)",
        "later=evaluate(Maps.seed)",
    ];
    let normal = finite_map_private_result(&asks);
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
    let prepared = prepare_observed(finite_map_private_inputs(), &asks, &mut control).unwrap();
    let law = prepared.inputs().sources().law().bytes().to_vec();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "prior" && !after_answer {
                let (arm, seen, law) = (armed.clone(), seen.clone(), law.clone());
                data::observe_iterations(move |span, context, operation, _| {
                    if context.request == 1
                        && operation == "type_enum"
                        && &law[span.0..span.1] == b"forall f:Map<Key,Image> . f=f"
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
        assert_eq!(stopped.answers[1].status, Decision::Established);
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
fn finite_map_enumeration_cancel_keeps_verified_prefix_and_prior_refutation() {
    finite_map_private_stop(0, false);
}
#[test]
fn finite_map_enumeration_time_stop_keeps_verified_prefix_and_prior_refutation() {
    finite_map_private_stop(1, false);
}
#[test]
fn finite_map_enumeration_memory_stop_keeps_verified_prefix_and_prior_refutation() {
    finite_map_private_stop(2, false);
}
#[test]
fn finite_map_answer_stop_retains_completed_domain_and_verified_answer() {
    finite_map_private_stop(0, true);
}

#[test]
fn finite_map_recheck_stops_freeze_the_shared_control() {
    use std::{cell::Cell, rc::Rc};
    let r = finite_map_private_result(&["a=evaluate(Maps.every)"]);
    let target = finite_map_private_domain(&r, 0);
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
