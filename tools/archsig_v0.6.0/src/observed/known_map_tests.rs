mod known_map_fixture {
    include!("../../tests/common/known_map.rs");
}
fn known_map_private_inputs() -> InputSources {
    let definitions = known_map_fixture::DEFINITIONS.as_bytes();
    let d = crate::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        known_map_fixture::law(digest).into_bytes(),
        known_map_fixture::archmap(digest, "r1").into_bytes(),
    )
}
fn known_map_private_result(asks: &[&str]) -> ObservedEvaluation {
    let mut control = named_call_quiet();
    let p = prepare_observed(known_map_private_inputs(), asks, &mut control).unwrap();
    evaluate_observed(p, &mut control).unwrap()
}
fn known_map_private_atom(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().position(|n|matches!((&n.payload,&n.rule),(Some(Payload::Scalar(Scalar::Map{pairs,..})),Rule::Input{kind:"atom",..}) if !pairs.is_empty())).unwrap()
}
fn known_map_private_change(value: &mut Scalar) {
    let Scalar::Map { pairs, .. } = value else {
        panic!("map")
    };
    let Scalar::Subject { subject, .. } = &mut pairs[0].1 else {
        panic!("ref")
    };
    assert_eq!(subject, "a");
    *subject = "b".into();
}
#[test]
fn known_map_rechecks_original_pairs_types_support_and_scope() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    assert_eq!(r.status(), "complete");
    let t = known_map_private_atom(&r);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=t]).unwrap();
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(value)) = &mut nodes[t].payload else {
            unreachable!()
        };
        known_map_private_change(value);
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[t].payload else {
            unreachable!()
        };
        pairs[0].0 = pairs[1].0.clone();
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
    completion_mutation(&r, t, |nodes| {
        nodes[t].scope.modes.clear();
    });
}
#[test]
fn known_map_normal_validation_does_not_authorize_later_changes() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    let t = known_map_private_atom(&r);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..t]).unwrap();
    graph.active = r.contexts[t];
    let mut control = named_call_quiet();
    let environment = Environment::new(r.prepared.inputs(), &mut control).unwrap();
    environment.validate(&graph, &r.nodes[t]).unwrap();
    let mut changed = r.nodes[t].clone();
    let Some(Payload::Scalar(value)) = &mut changed.payload else {
        unreachable!()
    };
    known_map_private_change(value);
    assert_ne!(format!("{changed:?}"), format!("{:?}", r.nodes[t]));
    assert!(matches!(
        environment.validate(&graph, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    environment.validate(&graph, &r.nodes[t]).unwrap();
}
#[test]
fn known_map_row_permutation_is_accepted_as_the_same_original_function() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    let t = known_map_private_atom(&r);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let mut nodes = r.nodes.clone();
    let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[t].payload else {
        unreachable!()
    };
    pairs.reverse();
    assert_ne!(format!("{:?}", nodes[t]), format!("{:?}", r.nodes[t]));
    rebuild_for_origin_and_support_recheck(&r, &nodes[..=t]).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &nodes).unwrap();
}
#[test]
fn known_map_walk_equality_and_recheck_stops_freeze_shared_control() {
    use std::{cell::Cell, rc::Rc};
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    let t = known_map_private_atom(&r);
    let Some(Payload::Scalar(value)) = &r.nodes[t].payload else {
        unreachable!()
    };
    for equality in [false, true] {
        for kind in [0, 1, 2] {
            let (limits, usage, expected) = reservations_private_stop_usage(kind);
            let probes = Rc::new(Cell::new(0));
            let count = probes.clone();
            let control = Control::new(limits, move |_| {
                count.set(count.get() + 1);
                if count.get() == 5 {
                    usage
                } else {
                    super::super::control::Usage::default()
                }
            });
            let operation = || {
                if equality {
                    data::equal(value, value, &control).map(|_| ())
                } else {
                    data::check(value, r.prepared.inputs().law(), &control)
                }
            };
            assert!(matches!(operation(),Err(ValidationFailure::Stop(s)) if s==expected));
            assert_eq!(probes.get(), 5);
            assert!(matches!(operation(),Err(ValidationFailure::Stop(s)) if s==expected));
            assert_eq!(probes.get(), 5);
        }
    }
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..t]).unwrap();
    graph.active = r.contexts[t];
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let (arm, count) = (armed.clone(), probes.clone());
    let (limits, usage, expected) = reservations_private_stop_usage(0);
    let mut control = Control::new(limits, move |_| {
        count.set(count.get() + 1);
        if arm.get() {
            usage
        } else {
            super::super::control::Usage::default()
        }
    });
    let environment = Environment::new(r.prepared.inputs(), &mut control).unwrap();
    environment.validate(&graph, &r.nodes[t]).unwrap();
    armed.set(true);
    assert!(
        matches!(environment.validate(&graph,&r.nodes[t]),Err(ValidationFailure::Stop(s)) if s==expected)
    );
    let frozen = probes.get();
    assert!(
        matches!(environment.validate(&graph,&r.nodes[t]),Err(ValidationFailure::Stop(s)) if s==expected)
    );
    assert_eq!(probes.get(), frozen);
}
fn known_map_private_stop(kind: usize, after_answer: bool) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Maps.prior)",
        "current=evaluate(Maps.equal,s=@v/s)",
        "later=evaluate(Maps.seed)",
    ];
    let normal = known_map_private_result(&asks);
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
    let prepared = prepare_observed(known_map_private_inputs(), &asks, &mut control).unwrap();
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
                        && operation == "expression"
                        && &law[span.0..span.1] == b"s.m=s.n"
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
fn known_map_stops_preserve_prefix_prior_refutation_and_verified_answer() {
    for kind in [0, 1, 2] {
        known_map_private_stop(kind, false);
    }
    known_map_private_stop(0, true);
}
