mod recursive_tree_fixture {
    include!("../../tests/common/recursive_tree.rs");
}

fn recursive_tree_private_inputs() -> super::super::input::InputSources {
    let definitions = recursive_tree_fixture::DEFINITIONS.as_bytes();
    let checked = crate::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &checked.vocabularies["Trees"].digest;
    super::super::input::InputSources::from_bytes(
        vec![definitions.to_vec()],
        recursive_tree_fixture::law(digest, "view seed():Z=1;law required prior():false;")
            .into_bytes(),
        recursive_tree_fixture::archmap(digest, false, "r1").into_bytes(),
    )
}
fn recursive_tree_private_result(asks: &[&str]) -> ObservedEvaluation {
    let mut control = named_call_quiet();
    let prepared = prepare_observed(recursive_tree_private_inputs(), asks, &mut control).unwrap();
    evaluate_observed(prepared, &mut control).unwrap()
}
fn recursive_tree_private_atom(result: &ObservedEvaluation) -> usize {
    result
        .nodes
        .iter()
        .position(|n| {
            matches!(
                (&n.payload, &n.rule),
                (
                    Some(Payload::Scalar(Scalar::Data { .. })),
                    Rule::Input { kind: "atom", .. }
                )
            )
        })
        .unwrap()
}
fn recursive_tree_private_change_leaf(value: &mut Scalar) {
    let Scalar::Data { args, .. } = value else {
        panic!("tree")
    };
    let Scalar::Data { args, .. } = &mut args[0] else {
        panic!("leaf")
    };
    assert_eq!(args[0], Scalar::Z(2.into()));
    args[0] = Scalar::Z(3.into());
}

#[test]
fn recursive_tree_rechecks_original_constructor_payload_support_and_scope() {
    let result = recursive_tree_private_result(&["a=evaluate(Trees.read,s=@v/sample)"]);
    assert_eq!(result.status(), "complete");
    let target = recursive_tree_private_atom(&result);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    completion_mutation(&result, target, |nodes| {
        let Some(Payload::Scalar(Scalar::Data { constructor, .. })) = &mut nodes[target].payload
        else {
            unreachable!()
        };
        *constructor = "Trees.Tree.Empty".into();
    });
    completion_mutation(&result, target, |nodes| {
        let Some(Payload::Scalar(value)) = &mut nodes[target].payload else {
            unreachable!()
        };
        recursive_tree_private_change_leaf(value);
    });
    completion_mutation(&result, target, |nodes| {
        nodes[target].support.clear();
    });
    completion_mutation(&result, target, |nodes| {
        nodes[target].scope.modes.clear();
    });
}

#[test]
fn recursive_tree_rejects_equal_sibling_and_other_request_call_arguments() {
    let mut result = recursive_tree_private_result(&[
        "a=evaluate(Trees.read,s=@v/sample)",
        "b=evaluate(Trees.read,s=@v/sample)",
    ]);
    let leaf = Scalar::Data {
        family: "Trees.Tree".into(),
        constructor: "Trees.Tree.Leaf".into(),
        args: vec![Scalar::Z(2.into())],
    };
    let arguments: Vec<_> = result
        .frames
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            let &r = f.arguments.first()?;
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &result.nodes[r.0].payload
            else {
                return None;
            };
            matches!(&result.nodes[value.0].payload,Some(Payload::Scalar(v)) if v==&leaf)
                .then_some((i, r))
        })
        .collect();
    assert_eq!(arguments.len(), 4);
    assert_ne!(arguments[0].1, arguments[1].1);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    for (target, donor) in [(arguments[1], arguments[0]), (arguments[2], arguments[0])] {
        let prefix = result
            .contexts
            .iter()
            .enumerate()
            .find(|(i, c)| {
                c.frame == Some(target.0)
                    && matches!(result.nodes[*i].payload, Some(Payload::Expression { .. }))
            })
            .unwrap()
            .0;
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=prefix]).unwrap();
        let original = result.frames[target.0].arguments.clone();
        result.frames[target.0].arguments[0] = donor.1;
        assert_ne!(result.frames[target.0].arguments, original);
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=prefix]),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            rebuild_for_origin_and_support_recheck(&result, &result.nodes),
            Err(ValidationFailure::Internal(_))
        ));
        result.frames[target.0].arguments = original;
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

#[test]
fn recursive_tree_pattern_source_rejects_equal_sibling_producer_and_value() {
    let result = recursive_tree_private_result(&["a=evaluate(Trees.read,s=@v/sample)"]);
    let law = result.prepared.inputs().sources().law().bytes();
    let sources: Vec<_> = result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| match &n.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) if &law[span.0..span.1] == b"n" => Some(i),
            _ => None,
        })
        .collect();
    assert_eq!(sources.len(), 2);
    let (donor, target) = (sources[0], sources[1]);
    assert_ne!(result.contexts[donor], result.contexts[target]);
    assert_ne!(
        result.nodes[donor].arguments,
        result.nodes[target].arguments
    );
    completion_mutation(&result, target, |nodes| {
        nodes[target].arguments = result.nodes[donor].arguments.clone();
    });
    let scalar = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| match &n.payload {
            Some(Payload::Scalar(Scalar::Z(v)))
                if v == &2.into() && result.contexts[i] == result.contexts[target] =>
            {
                Some(i)
            }
            _ => None,
        })
        .unwrap();
    completion_mutation(&result, scalar, |nodes| {
        nodes[scalar].payload = Some(Payload::Scalar(Scalar::Z(3.into())));
    });
}

#[test]
fn recursive_tree_validation_success_does_not_authorize_later_payload_changes() {
    let result = recursive_tree_private_result(&["a=evaluate(Trees.read,s=@v/sample)"]);
    let target = recursive_tree_private_atom(&result);
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..target]).unwrap();
    graph.active = result.contexts[target];
    let mut control = named_call_quiet();
    let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
    environment.validate(&graph, &result.nodes[target]).unwrap();
    let mut changed = result.nodes[target].clone();
    let Some(Payload::Scalar(v)) = &mut changed.payload else {
        unreachable!()
    };
    recursive_tree_private_change_leaf(v);
    assert_ne!(
        format!("{changed:?}"),
        format!("{:?}", result.nodes[target])
    );
    assert!(matches!(
        environment.validate(&graph, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    environment.validate(&graph, &result.nodes[target]).unwrap();
}

fn recursive_tree_private_stop(kind: usize, after_answer: bool) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Trees.prior)",
        "current=evaluate(Trees.read,s=@v/sample)",
        "later=evaluate(Trees.seed)",
    ];
    let normal = recursive_tree_private_result(&asks);
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
    let prepared = prepare_observed(recursive_tree_private_inputs(), &asks, &mut control).unwrap();
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
                        && context.frame.is_some()
                        && operation == "expression"
                        && &law[span.0..span.1] == b"total(l)"
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
fn recursive_tree_recursive_call_cancel_keeps_prefix_and_prior_refutation() {
    recursive_tree_private_stop(0, false);
}
#[test]
fn recursive_tree_recursive_call_time_stop_keeps_prefix_and_prior_refutation() {
    recursive_tree_private_stop(1, false);
}
#[test]
fn recursive_tree_recursive_call_memory_stop_keeps_prefix_and_prior_refutation() {
    recursive_tree_private_stop(2, false);
}
#[test]
fn recursive_tree_answer_cancel_retains_verified_value() {
    recursive_tree_private_stop(0, true);
}

#[test]
fn recursive_tree_value_walk_and_recheck_stops_freeze_the_shared_control() {
    use std::{cell::Cell, rc::Rc};
    let result = recursive_tree_private_result(&["a=evaluate(Trees.raw,s=@v/sample)"]);
    let target = recursive_tree_private_atom(&result);
    let Some(Payload::Scalar(value)) = &result.nodes[target].payload else {
        unreachable!()
    };
    for kind in [0, 1, 2] {
        let (limits, usage, expected) = reservations_private_stop_usage(kind);
        let probes = Rc::new(Cell::new(0));
        let count = probes.clone();
        let control = Control::new(limits, move |_| {
            count.set(count.get() + 1);
            if count.get() == 9 {
                usage
            } else {
                super::super::control::Usage::default()
            }
        });
        assert!(
            matches!(data::check(value,result.prepared.inputs().law(),&control),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        assert_eq!(probes.get(), 9);
        assert!(
            matches!(data::check(value,result.prepared.inputs().law(),&control),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        assert_eq!(probes.get(), 9);
    }
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..target]).unwrap();
    graph.active = result.contexts[target];
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
    let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
    environment.validate(&graph, &result.nodes[target]).unwrap();
    armed.set(true);
    assert!(
        matches!(environment.validate(&graph,&result.nodes[target]),Err(ValidationFailure::Stop(s)) if s==expected)
    );
    let frozen = probes.get();
    assert!(
        matches!(environment.validate(&graph,&result.nodes[target]),Err(ValidationFailure::Stop(s)) if s==expected)
    );
    assert_eq!(probes.get(), frozen);
}
