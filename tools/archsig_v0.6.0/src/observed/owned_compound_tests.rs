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
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
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
#[test]
fn owned_compound_domains_reject_equal_foreign_owner_and_prefix_producers() {
    let r = compound_result(&[
        "first=check(Reservations.maps,a=@v/A,b=@v/B)",
        "again=check(Reservations.maps,a=@v/A,b=@v/B)",
    ]);
    let first = compound_domain(&r, 0);
    let d = compound_domain(&r, 1);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for index in [1, 2, 3, 4] {
        let donor = r.nodes[first].arguments[index];
        let actual = r.nodes[d].arguments[index];
        assert_ne!(donor, actual);
        if index == 2 || index == 4 {
            assert_eq!(data_scalar_at(&r, donor.0), data_scalar_at(&r, actual.0));
        }
        completion_mutation(&r, d, |nodes| nodes[d].arguments[index] = donor);
    }
    let t = compound_elements(&r, d)[0].0;
    let donor = compound_elements(&r, first)[0];
    assert_eq!(data_scalar_at(&r, t), data_scalar_at(&r, donor.0));
    completion_mutation(&r, t, |nodes| {
        nodes[t].arguments[2] = r.nodes[donor.0].arguments[2]
    });
}
#[test]
fn owned_compound_success_does_not_authorize_later_changed_domain() {
    let r = compound_result(&["c=check(Reservations.maps,a=@v/A,b=@v/B)"]);
    let d = compound_domain(&r, 0);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..d]).unwrap();
    g.active = r.contexts[d];
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.validate(&g, &r.nodes[d]).unwrap();
    let mut changed = r.nodes[d].clone();
    let Some(Payload::Domain { elements, .. }) = &mut changed.payload else {
        panic!("domain")
    };
    elements.pop();
    changed.arguments.pop();
    assert_ne!(format!("{changed:?}"), format!("{:?}", r.nodes[d]));
    assert!(matches!(
        e.validate(&g, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&g, &r.nodes[d]).unwrap();
}
fn compound_stop(kind: usize, after_answer: bool) {
    use super::super::control::Usage;
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
            Usage::default()
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
fn owned_compound_enumeration_cancel_keeps_verified_prefix_and_prior_refutation() {
    compound_stop(0, false);
}
#[test]
fn owned_compound_enumeration_time_stop_keeps_verified_prefix_and_prior_refutation() {
    compound_stop(1, false);
}
#[test]
fn owned_compound_enumeration_memory_stop_keeps_verified_prefix_and_prior_refutation() {
    compound_stop(2, false);
}
#[test]
fn owned_compound_answer_stop_retains_completed_domain_and_verified_answer() {
    compound_stop(0, true);
}

#[test]
fn owned_compound_recheck_stops_freeze_the_shared_control() {
    use std::{cell::Cell, rc::Rc};
    let r = compound_result(&["a=check(Reservations.maps,a=@v/A,b=@v/B)"]);
    let target = compound_domain(&r, 0);
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

#[test]
fn owned_compound_domains_reject_other_prefix_and_wrapped_owner_member_changes() {
    let r = compound_result(&["c=check(Reservations.maps)"]);
    let Signature::Law { params, .. } =
        &r.prepared.inputs().law().declarations["Reservations.maps"].signature
    else {
        panic!("law")
    };
    let target = params[2].span;
    let ds: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            (matches!(
                n.payload,
                Some(Payload::Domain {
                    ty: Type::Map(..),
                    ..
                })
            ) && n.arguments.len() >= 5
                && matches!(n.rule,Rule::Input{location:Location::Law{span},..} if span==target))
            .then_some(i)
        })
        .collect();
    let first = ds[0];
    let other = ds[1];
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_ne!(r.nodes[first].arguments[4], r.nodes[other].arguments[4]);
    completion_mutation(&r, other, |nodes| {
        nodes[other].arguments[4] = r.nodes[first].arguments[4]
    });
    for name in ["option_values", "tupled", "subset"] {
        let ask = format!("c=check(Reservations.{name},a=@v/A)");
        let r = compound_result(&[&ask]);
        let d = r
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                (matches!(
                    n.payload,
                    Some(Payload::Domain {
                        ty: Type::Option(_) | Type::Tuple(_) | Type::Set(_),
                        ..
                    })
                ))
                .then_some(i)
            })
            .unwrap();
        let es = compound_elements(&r, d);
        rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=d]).unwrap();
        completion_mutation(&r, d, |nodes| {
            let Some(Payload::Domain { elements, .. }) = &mut nodes[d].payload else {
                panic!("domain")
            };
            elements.pop();
            nodes[d].arguments.pop();
        });
        let t = es
            .iter()
            .find_map(|r0| match &r.nodes[r0.0].payload {
                Some(Payload::Scalar(Scalar::Option { value: Some(_), .. })) => Some(r0.0),
                Some(Payload::Scalar(Scalar::Tuple(_))) => Some(r0.0),
                Some(Payload::Scalar(Scalar::Set { items, .. })) if !items.is_empty() => Some(r0.0),
                _ => None,
            })
            .unwrap();
        completion_mutation(&r, t, |nodes| {
            let Some(Payload::Scalar(value)) = &mut nodes[t].payload else {
                panic!("scalar")
            };
            let leaf = match value {
                Scalar::Option { value: Some(v), .. } => v.as_mut(),
                Scalar::Tuple(v) => &mut v[1],
                Scalar::Set { items, .. } => &mut items[0],
                _ => panic!("wrapped"),
            };
            let Scalar::Subject { subject, .. } = leaf else {
                panic!("subject")
            };
            *subject = "r".into();
        });
    }
}
