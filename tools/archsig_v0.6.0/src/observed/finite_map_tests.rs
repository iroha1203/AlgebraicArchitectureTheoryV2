#[allow(dead_code)]
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
fn finite_map_private_result(asks: &[&str]) -> ObservedEvaluation {
    let mut control = named_call_quiet();
    let p = prepare_observed(finite_map_private_inputs(), asks, &mut control).unwrap();
    evaluate_observed(p, &mut control).unwrap()
}
fn finite_map_private_domain(r: &ObservedEvaluation) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 0
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
    let d = finite_map_private_domain(&r);
    let es = finite_map_private_members(&r, d);
    assert_eq!(es.len(), 4);
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
fn finite_map_private_stop(after_answer: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Maps.prior)",
        "current=evaluate(Maps.every)",
        "later=evaluate(Maps.seed)",
    ];
    let normal = finite_map_private_result(&asks);
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
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
    assert_eq!(control.stop_reason(), Some(expected));
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
        let Json::Obj(ref expected) = expected.issue() else {
            unreachable!()
        };
        assert_eq!(actual["details"], expected["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn finite_map_enumeration_cancel_keeps_verified_prefix_and_prior_refutation() {
    finite_map_private_stop(false);
}
#[test]
fn finite_map_answer_stop_retains_completed_domain_and_verified_answer() {
    finite_map_private_stop(true);
}
