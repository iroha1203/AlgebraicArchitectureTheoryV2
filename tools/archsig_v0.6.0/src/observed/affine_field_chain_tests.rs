use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/affine_field_chains.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Walk.seed)",
    "prior=check(Walk.prior)",
    "first=check(Walk.chain,n=@v/p)",
    "second=check(Walk.chain,n=@v/p)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(fixture::SCRIPT, "Z", &[], "r1"),
        ASK,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn field(r: &ObservedEvaluation, request: usize) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            if n.ty != NodeType::Evaluation(Type::Z) || r.contexts[i].request != request {
                return None;
            }
            let Some(Payload::Evaluation { expression, .. }) = &n.payload else {
                return None;
            };
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &r.nodes[expression.0].payload
            else {
                return None;
            };
            (&r.prepared.inputs().sources().law().bytes()[span.0..span.1] == b"n.link.mark")
                .then_some(i)
        })
        .unwrap()
}
fn child(n: &Node) -> NodeRef {
    let Some(Payload::Evaluation { parts, .. }) = &n.payload else {
        panic!()
    };
    assert_eq!(parts[0].children.len(), 1);
    parts[0].children[0]
}
fn replace(n: &mut Node, old: NodeRef, new: NodeRef) {
    let Some(Payload::Evaluation { parts, .. }) = &mut n.payload else {
        panic!()
    };
    assert_eq!(parts[0].children, vec![old]);
    parts[0].children[0] = new;
    for r in &mut n.arguments {
        if *r == old {
            *r = new
        }
    }
}
#[test]
fn all_assignment_field_rejects_equal_value_from_a_different_prefix_or_request() {
    let r = result();
    let at = field(&r, 3);
    let owner = child(&r.nodes[at]);
    let first = child(&r.nodes[owner.0]);
    let foreign = child(&r.nodes[field(&r, 2)]);
    for substitute in [first, foreign] {
        assert_ne!(owner, substitute);
        assert_eq!(r.nodes[owner.0].ty, r.nodes[substitute.0].ty);
        let value = |i: NodeRef| {
            let Some(Payload::Evaluation { value, .. }) = &r.nodes[i.0].payload else {
                panic!()
            };
            *value
        };
        let shape = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        assert_eq!(
            shape.scalar(value(owner).unwrap()).unwrap(),
            shape.scalar(value(substitute).unwrap()).unwrap()
        );
        let change = |ns: &mut [Node]| replace(&mut ns[at], owner, substitute);
        let mut before = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..at]).unwrap();
        before.active = r.contexts[at];
        let mut changed = r.nodes[at].clone();
        replace(&mut changed, owner, substitute);
        before
            .push(changed)
            .expect("同値・同型の既出子は形検査だけでは拒否しない");
        completion_mutation(&r, at, change);
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn all_assignment_field_warm_environment_rechecks_prefix_context_type_scope_and_restoration() {
    let r = result();
    let at = field(&r, 3);
    let owner = child(&r.nodes[at]);
    let other = child(&r.nodes[field(&r, 2)]);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let environment = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let saved = graph.nodes.clone();
    for variant in 0..4 {
        environment
            .recheck_node(&graph, &graph.nodes[at], at)
            .unwrap();
        match variant {
            0 => replace(&mut graph.nodes[at], owner, other),
            1 => graph.nodes[owner.0].ty = NodeType::Evaluation(Type::Ref("Paths.Root".into())),
            2 => graph.nodes[at].scope.quantifiers.clear(),
            3 => graph.nodes[owner.0].support.clear(),
            _ => unreachable!(),
        }
        assert!(
            environment
                .recheck_node(&graph, &graph.nodes[at], at)
                .is_err(),
            "variant {variant}"
        );
        graph.nodes.clone_from(&saved);
        environment
            .recheck_node(&graph, &graph.nodes[at], at)
            .unwrap();
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
fn stop(fresh: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = &[
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "v=evaluate(Walk.current,n=@v/p)",
        "later=evaluate(Walk.seed)",
    ];
    let inputs = fixture::input(fixture::SCRIPT, "Z", &[], "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let at = field(&normal, 2);
    let Some(Payload::Evaluation { expression, .. }) = &normal.nodes[at].payload else {
        panic!()
    };
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &normal.nodes[expression.0].payload
    else {
        panic!()
    };
    let span = *span;
    let (limits, usage, expected) = reservations_private_stop_usage(if fresh { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(inputs, asks, &mut control).unwrap();
    let mut copy = control.clone();
    let stopped =
        evaluate_observed_with_validator(prepared, &mut control, |env, graph, request, answer| {
            env.validate_answer(graph, request, answer)?;
            if request.id == "prior" {
                let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, index| {
                    if at == span
                        && context.request == 2
                        && ((!fresh && operation == "universal_field" && index == 1)
                            || (fresh
                                && ph.get()
                                && operation == "universal_field_recheck"
                                && index == 2))
                    {
                        assert_eq!(s.get(), 0);
                        s.set(1);
                        a.set(true)
                    }
                });
            }
            if fresh && request.id == "v" {
                let independent = Environment::with_requests(
                    normal.prepared.inputs(),
                    normal.prepared.requests().requests(),
                    &mut copy,
                )?;
                phase.set(true);
                let checked = independent.validate_answer(graph, request, answer);
                phase.set(false);
                checked?;
            }
            Ok(())
        })
        .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 1);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, normal.contexts[..stopped.contexts.len()]);
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for i in 2..4 {
        if fresh && i == 2 {
            assert_eq!(stopped.answers[i].status, normal.answers[i].status);
            assert_eq!(stopped.answers[i].outputs, normal.answers[i].outputs);
            assert_eq!(stopped.answers[i].claim, normal.answers[i].claim);
            assert_eq!(stopped.answers[i].evidence, normal.answers[i].evidence)
        } else {
            assert_eq!(stopped.answers[i].status, Decision::Undetermined);
            assert!(stopped.answers[i].outputs.is_empty())
        }
        let reason = stopped.answers[i]
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(actual)if actual==&expected))
            .unwrap();
        assert_eq!(reason.request, stopped.answers[i].id);
        let (Json::Obj(ref a), Json::Obj(ref b)) = (reason.wire(), expected.wire()) else {
            panic!()
        };
        assert_eq!(a["details"], b["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn all_assignment_field_actual_prefix_stop_keeps_verified_results_and_freezes() {
    stop(false)
}
#[test]
fn all_assignment_field_fresh_recheck_stop_keeps_current_and_freezes() {
    stop(true)
}
