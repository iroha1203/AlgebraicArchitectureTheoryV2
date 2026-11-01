mod compound_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_compound_family.rs");
}
fn compound_result(asks: &[&str]) -> ObservedEvaluation {
    let mut c = named_call_quiet();
    let p = prepare_observed(compound_fixture::input(false, false, "r1"), asks, &mut c).unwrap();
    evaluate_observed(p, &mut c).unwrap()
}
fn compound_domain(r: &ObservedEvaluation, request: usize) -> usize {
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
fn compound_elements(r: &ObservedEvaluation, d: usize) -> Vec<NodeRef> {
    let Some(Payload::Domain { elements, .. }) = &r.nodes[d].payload else {
        panic!("domain")
    };
    elements.clone()
}
#[test]
fn owned_compound_domains_recheck_original_fibers_members_types_support_and_scope() {
    let r = compound_result(&["c=check(Reservations.maps,a=@v/A,b=@v/B)"]);
    assert_eq!(r.status(), "complete");
    let d = compound_domain(&r, 0);
    let es = compound_elements(&r, d);
    assert_eq!(es.len(), 4);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=d]).unwrap();
    completion_mutation(&r, d, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[d].payload else {
            panic!("domain")
        };
        elements.pop();
        nodes[d].arguments.pop();
    });
    completion_mutation(&r, d, |nodes| {
        let Some(Payload::Domain { elements, .. }) = &mut nodes[d].payload else {
            panic!("domain")
        };
        elements[1] = elements[0];
        let len = nodes[d].arguments.len();
        nodes[d].arguments[len - 3] = nodes[d].arguments[len - 4];
    });
    let t = es[0].0;
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut nodes[t].payload else {
            panic!("map")
        };
        let Scalar::Subject { subject, .. } = &mut pairs[0].1 else {
            panic!("ref")
        };
        *subject = "p".into();
    });
    completion_mutation(&r, t, |nodes| {
        let Some(Payload::Scalar(Scalar::Map { codomain, .. })) = &mut nodes[t].payload else {
            panic!("map")
        };
        *codomain = Type::Ref("Reservations.System".into());
    });
    completion_mutation(&r, t, |nodes| nodes[t].support.clear());
    completion_mutation(&r, d, |nodes| {
        nodes[d].scope.snapshots.remove("v");
    });
    completion_mutation(&r, d, |nodes| {
        let Rule::Input {
            location: Location::Law { span },
            ..
        } = &mut nodes[d].rule
        else {
            panic!("rule")
        };
        span.0 += 1;
    });
}
fn compound_stop(kind: usize, after_answer: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "prior=check(Reservations.prior)",
        "current=check(Reservations.maps,a=@v/A,b=@v/B)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = compound_result(&asks);
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
    let prepared = prepare_observed(
        compound_fixture::input(false, false, "r1"),
        &asks,
        &mut control,
    )
    .unwrap();
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
                        && operation == "dependent_enum"
                        && std::str::from_utf8(&law[span.0..span.1])
                            .unwrap()
                            .starts_with("law required maps(")
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
fn owned_compound_enumeration_cancel_keeps_verified_prefix_and_prior_refutation() {
    compound_stop(0, false);
}
