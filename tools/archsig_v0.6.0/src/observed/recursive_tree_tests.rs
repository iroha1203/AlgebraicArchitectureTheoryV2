mod recursive_tree_fixture {
    include!("../../tests/common/recursive_tree.rs");
}

fn recursive_tree_private_inputs() -> crate::input::InputSources {
    let definitions = recursive_tree_fixture::DEFINITIONS.as_bytes();
    let checked = crate::definition::check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &checked.vocabularies["Trees"].digest;
    crate::input::InputSources::from_bytes(
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

fn recursive_tree_private_stop(kind: usize, after_answer: bool) {
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
            None
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
}
#[test]
fn recursive_tree_recursive_call_cancel_keeps_prefix_and_prior_refutation() {
    recursive_tree_private_stop(0, false);
}
