use super::*;
mod partial_container_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_containers.rs");
}
fn partial_container_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        partial_container_fixture::input(false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
const PARTIAL_CONTAINER_BAD: &str = "x=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/r)";
#[test]
fn partial_container_calls_reject_original_binder_member_and_condition_mutations() {
    let r = partial_container_result(&[PARTIAL_CONTAINER_BAD]);
    assert_eq!(r.status(), "partial");
    let target = owned_condition(&r, 0);
    let edges = r.nodes[target].arguments.clone();
    let n = edges.len();
    let source = edges[0];
    completion_mutation(&r, source.0, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source.0].payload else {
            panic!("source")
        };
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters[0].1, Type::Z);
        parameters.clear();
    });
    let replacement = r.nodes[edges[n - 2].0].payload.clone();
    completion_mutation(&r, edges[n - 3].0, |ns| {
        ns[edges[n - 3].0].payload = replacement.clone()
    });
    let proof = edges[n - 1];
    completion_mutation(&r, proof.0, |ns| {
        ns[proof.0].ty = NodeType::Value(Type::Bool)
    });
    completion_mutation(&r, target, |ns| ns[target].support.clear());
    completion_mutation(&r, target, |ns| ns[target].scope.snapshots.clear());
    completion_mutation(&r, target, |ns| ns[target].scope.quantifiers.clear());
    let container = edges[2];
    let Some(Payload::Evaluation { value, .. }) = &r.nodes[container.0].payload else {
        panic!("container")
    };
    assert!(value.is_none());
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[container.0].payload else {
            panic!("container")
        };
        assert_eq!(parts[0].children.len(), 3);
        parts[0].children.swap(0, 1);
    });
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[container.0].payload else {
            panic!("container")
        };
        parts[0].children.pop();
    });
    let member = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, node)| match &node.payload {
            Some(Payload::Scalar(Scalar::Subject { subject, .. }))
                if subject == "r" && i < container.0 =>
            {
                Some(i)
            }
            _ => None,
        })
        .unwrap();
    completion_mutation(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[member].payload else {
            panic!("member")
        };
        *subject = "q".into();
    });
    assert!(!r.frames.iter().any(|f| f.source == source));
}
#[test]
fn partial_container_calls_reject_equal_foreign_producers_and_same_environment_changes() {
    for ask in [
        "x=evaluate(Reservations.ocMissingSet,a=@v/B,p=@v/p,q=@v/q)",
        PARTIAL_CONTAINER_BAD,
        "x=evaluate(Reservations.ocMissing,a=@v/B,p=@v/p,q=@v/q)",
        "x=check(Reservations.ocSomeGood,a=@v/B,p=@v/p)",
    ] {
        let first = ask.replacen("x=", "first=", 1);
        let second = ask.replacen("x=", "second=", 1);
        let r = partial_container_result(&[&first, &second]);
        let donor = owned_condition(&r, 0);
        let target = owned_condition(&r, 1);
        let own = r.nodes[target].arguments.clone();
        let other = r.nodes[donor].arguments.clone();
        let n = own.len();
        for p in [own[2], other[2]] {
            let Some(Payload::Evaluation { value, .. }) = &r.nodes[p.0].payload else {
                panic!("container")
            };
            assert!(value.is_none());
        }
        assert_ne!(own[2], other[2]);
        let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        let env = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
        let actual = env.owned_call_argument(&graph, own[2]).unwrap();
        let foreign = env.owned_call_argument(&graph, other[2]).unwrap();
        if ask.contains("=check(") {
            assert_ne!(actual, foreign, "別Requestの全域軸は別の束縛");
        } else {
            assert_eq!(actual, foreign, "共有する元slotと既知memberは同じ部分値");
        }
        completion_mutation(&r, target, |ns| {
            for p in [own[n - 3], own[n - 2], own[n - 1], NodeRef(target)] {
                ns[p.0].arguments[2] = other[2];
            }
        });
        let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
        e.recheck_node(&g, &g.nodes[target], target).unwrap();
        let old = g.nodes[own[n - 3].0].clone();
        g.nodes[own[n - 3].0].payload = g.nodes[own[n - 2].0].payload.clone();
        assert_ne!(format!("{:?}", g.nodes[own[n - 3].0]), format!("{old:?}"));
        assert!(matches!(
            e.recheck_node(&g, &g.nodes[target], target),
            Err(ValidationFailure::Internal(_))
        ));
        g.nodes[own[n - 3].0] = old;
        e.recheck_node(&g, &g.nodes[target], target).unwrap();
    }
}

fn partial_container_member_stop(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "current=evaluate(Reservations.ocStop,a=@v/A,p=@v/p,q=@v/q)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = partial_container_result(&asks);
    let bytes = normal.prepared.inputs().sources().law().bytes();
    let span = normal
        .prepared
        .inputs()
        .law()
        .exprs
        .iter()
        .find(|x| {
            &bytes[x.span.0..x.span.1]
                == b"ocStopAccept(a,some(set<(State,Z)>{(p,q.free),(p,q.free+1),(p,q.free)}))"
        })
        .unwrap()
        .span;
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let traversing = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
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
    let prepared =
        prepare_observed(partial_container_fixture::input(false, "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, ph, t, s) = (
                armed.clone(),
                phase.clone(),
                traversing.clone(),
                seen.clone(),
            );
            data::observe_iterations(move |at, ctx, operation, _| {
                if at != span {
                    return;
                }
                if !recheck && ctx.request == 2 && operation == "call_arguments_complete" {
                    t.set(true);
                }
                if operation == "owned_call_constraint"
                    && (if recheck {
                        ph.get() && ctx.request == 2
                    } else {
                        t.get()
                    })
                {
                    let i = s.get();
                    s.set(i + 1);
                    if i == 2 {
                        a.set(true);
                    }
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::new(normal.prepared.inputs(), &mut cc)?;
            phase.set(true);
            let result = fresh.validate_answer(g, request, answer);
            phase.set(false);
            result?;
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 3);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        if recheck && i == 2 {
            // 欠測のobserved回答はcomplete_answerで独立検査済み。
            assert_eq!(a.status, normal.answers[i].status);
            assert_eq!(a.status, Decision::Established);
            assert_eq!(a.outputs, normal.answers[i].outputs);
            assert_eq!(a.claim, normal.answers[i].claim);
            assert_eq!(a.evidence, normal.answers[i].evidence);
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn partial_container_actual_member_stop_keeps_values_refutation_and_prefix() {
    partial_container_member_stop(false)
}
#[test]
fn partial_container_original_input_recheck_stop_keeps_verified_outputs_and_prefix() {
    partial_container_member_stop(true)
}

#[test]
fn partial_option_actual_constructor_and_tuple_value_recheck_original_source() {
    let r = partial_container_result(&["x=check(Reservations.ocSomeGood,a=@v/B,p=@v/p)"]);
    let target = owned_condition(&r, 0);
    let edges = r.nodes[target].arguments.clone();
    let container = edges[2];
    let Some(Payload::Evaluation { value, parts, .. }) = &r.nodes[container.0].payload else {
        panic!("option")
    };
    assert!(value.is_none());
    assert_eq!(parts[0].children.len(), 1);
    let tuple = parts[0].children[0];
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[container.0].payload else {
            panic!()
        };
        parts[0].children.clear();
    });
    completion_mutation(&r, tuple.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[tuple.0].payload else {
            panic!()
        };
        assert_eq!(parts[0].children.len(), 2);
        parts[0].children.swap(0, 1);
    });
    let replacement = r.nodes[edges[edges.len() - 3].0].payload.clone();
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Scalar(_)) = &replacement else {
            panic!()
        };
        ns[container.0].payload = replacement.clone();
    });
}

#[test]
fn partial_option_set_return_whole_keeps_call_body_and_universal_template_distinct() {
    let r = partial_container_result(&["bad=check(Reservations.ocReturnedSet,a=@v/B,p=@v/p)"]);
    assert_eq!(r.status(), "partial");
    let whole = r.answers[0].outputs["evaluation"].0;
    let Some(Payload::Evaluation {
        expression, parts, ..
    }) = &r.nodes[whole].payload
    else {
        panic!("whole")
    };
    let source = *expression;
    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0].children.len(), 1);
    let child = parts[0].children[0];
    let Some(Payload::Evaluation {
        expression: pointwise,
        ..
    }) = r.nodes[child.0].payload
    else {
        panic!("pointwise")
    };
    assert_ne!(source, pointwise);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    assert_eq!(e.universal_source_root(&g, source).unwrap(), Some(source));
    assert_eq!(
        e.universal_source_root(&g, pointwise).unwrap(),
        Some(source)
    );
    completion_mutation(&r, whole, |ns| {
        let Some(Payload::Evaluation { expression, .. }) = &mut ns[whole].payload else {
            panic!("whole")
        };
        *expression = pointwise;
    });
    completion_mutation(&r, whole, |ns| ns[whole].arguments.retain(|r| *r != source));
}
