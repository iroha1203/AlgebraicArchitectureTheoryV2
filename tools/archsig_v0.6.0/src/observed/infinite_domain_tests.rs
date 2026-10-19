use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/infinite_domains.rs");
}
const SCRIPT: &str = "view inner(n:Node):Bool=forall item:Text.(item=item) and n.mark=2; view caller(n:Node):Bool=let use_inner=true in if use_inner then inner(n) else false; view keep(x:Bool):Bool=x;";
const ASKS: &[&str] = &[
    "seed=evaluate(Walk.seed)",
    "prior=check(Walk.prior)",
    "v=evaluate(Walk.caller,n=@v/p)",
    "two=evaluate(Walk.caller,n=@v/p)",
    "later=evaluate(Walk.keep,x=$two.value)",
];
fn result() -> ObservedEvaluation {
    let input = fixture::input(SCRIPT, "Z", &[], "r1");
    let r = evaluate_observed_bytes(input.clone(), ASKS, &mut named_call_quiet()).unwrap();
    assert_eq!(r.prepared.inputs().sources(), &input);
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    assert_eq!(r.answers[0].status, Decision::Established);
    assert_eq!(
        data_scalar_at(&r, r.answers[0].outputs["value"].0),
        &Scalar::Z(1.into())
    );
    assert_eq!(r.answers[1].status, Decision::Refuted);
    assert!(r.answers[1].claim.is_some() && !r.answers[1].evidence.is_empty());
    for i in [2, 3] {
        assert_eq!(r.answers[i].status, Decision::Undetermined);
        assert!(!r.answers[i].outputs.contains_key("value"));
        assert!(r.answers[i].reasons.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm{operand_types,..} if operand_types.contains(&Type::Text))));
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn domains(r: &ObservedEvaluation) -> Vec<usize> {
    r.nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            matches!(&n.payload, Some(Payload::TypeDomain { ty: Type::Text })).then_some(i)
        })
        .collect()
}
#[test]
fn infinite_type_domain_source_and_binder_mutations_are_rejected() {
    let r = result();
    let ds = domains(&r);
    assert_eq!(ds.len(), 2);
    let at = ds[1];
    let source = r.nodes[at].arguments[0];
    assert_eq!(r.contexts[at], r.contexts[source.0]);
    assert!(r.contexts[at].frame.is_some());
    for kind in 0..3 {
        completion_mutation(&r, at, |ns| match kind {
            0 => {
                if let Some(Payload::TypeDomain { ty }) = &mut ns[at].payload {
                    *ty = Type::Z;
                }
            }
            1 => ns[at].arguments[0] = r.nodes[ds[0]].arguments[0],
            _ => {
                if let Rule::Input {
                    location: Location::Law { span },
                    ..
                } = &mut ns[at].rule
                {
                    span.0 += 1;
                }
            }
        });
    }
    let law = r.prepared.inputs().law();
    let span = law
        .exprs
        .iter()
        .find_map(|e| matches!(&e.kind, ExprKind::Binary { op: BinOp::Eq, .. }).then_some(e.span))
        .unwrap();
    completion_mutation(&r, source.0, |ns| {
        if let Some(Payload::Expression { location, .. }) = &mut ns[source.0].payload {
            *location = Location::Law { span };
        }
        if let Rule::Input { location, .. } = &mut ns[source.0].rule {
            *location = Location::Law { span };
        }
    });
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn infinite_warm_recheck_rejects_foreign_context_scope_and_algorithm_reasons() {
    let r = result();
    let ds = domains(&r);
    let d = ds[1];
    let at = r.answers[3].outputs["evaluation"].0;
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let env = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let saved = graph.nodes.clone();
    let contexts = graph.contexts.clone();
    for kind in 0..5 {
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
        match kind {
            0 => graph.contexts[d].frame = graph.contexts[ds[0]].frame,
            1 => graph.nodes[at].scope.quantifiers[0].kind = crate::law::ast::QuantKind::Exists,
            2 => {
                let reason = graph.nodes[at]
                    .reasons
                    .iter_mut()
                    .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                    .unwrap();
                if let ReasonKind::UnsupportedAlgorithm { operand_types, .. } = &mut reason.kind {
                    *operand_types = vec![Type::Z];
                }
            }
            3 => {
                let reason = graph.nodes[at]
                    .reasons
                    .iter_mut()
                    .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                    .unwrap();
                reason.location = Some(Location::Law { span: (0, 1) });
            }
            _ => {
                let reason = graph.nodes[at]
                    .reasons
                    .iter_mut()
                    .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                    .unwrap();
                if let ReasonKind::UnsupportedAlgorithm { method, .. } = &mut reason.kind {
                    *method = "different decision".into();
                }
            }
        }
        assert!(
            env.recheck_node(&graph, &graph.nodes[at], at).is_err(),
            "mutation {kind}"
        );
        graph.nodes.clone_from(&saved);
        graph.contexts.clone_from(&contexts);
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn infinite_unbound_mixed_family_claims_recheck_original_domains() {
    let r = evaluate_observed_bytes(
        fixture::input(
            "law required current(b:Bool,item:Text):item=item;",
            "Z",
            &[],
            "r1",
        ),
        &["v=check(Walk.current)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    assert_eq!(r.answers[0].status, Decision::Undetermined);
    let claim = r.answers[0].claim.unwrap();
    assert_eq!(
        r.nodes[claim.0].judgment.as_ref().unwrap().status,
        Decision::Undetermined
    );
    assert_eq!(r.nodes[claim.0].scope, r.answers[0].scope);
    let ds = domains(&r);
    assert_eq!(ds.len(), 2);
    for at in ds {
        completion_mutation(&r, at, |ns| {
            if let Some(Payload::TypeDomain { ty }) = &mut ns[at].payload {
                *ty = Type::Bool;
            }
        });
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
fn stop(fresh_recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = ASKS;
    let inputs = fixture::input(SCRIPT, "Z", &[], "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), asks, &mut named_call_quiet()).unwrap();
    let d = domains(&normal)[0];
    let source = normal.nodes[d].arguments[0];
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &normal.nodes[source.0].payload
    else {
        panic!()
    };
    let span = *span;
    let (limits, usage, expected) =
        reservations_private_stop_usage(if fresh_recheck { 2 } else { 0 });
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
    let prepared = prepare_observed(inputs, ASKS, &mut control).unwrap();
    let mut copy = control.clone();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "prior" {
                let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, index| {
                    if at == span
                        && context.request == 2
                        && ((!fresh_recheck && operation == "universal" && index == 2)
                            || (fresh_recheck && ph.get() && operation == "quantifier_kind"))
                    {
                        assert_eq!(s.get(), 0);
                        s.set(1);
                        a.set(true);
                    }
                });
            }
            if fresh_recheck && request.id == "v" {
                let fresh = Environment::with_requests(
                    normal.prepared.inputs(),
                    normal.prepared.requests().requests(),
                    &mut copy,
                )?;
                phase.set(true);
                let result = fresh.validate_answer(graph, request, answer);
                phase.set(false);
                result?;
            }
            Ok(())
        },
    )
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
    for i in 2..5 {
        assert_eq!(stopped.answers[i].status, Decision::Undetermined);
        if fresh_recheck && i == 2 {
            assert_eq!(stopped.answers[i].outputs, normal.answers[i].outputs);
            assert_eq!(stopped.answers[i].claim, normal.answers[i].claim);
            assert_eq!(stopped.answers[i].evidence, normal.answers[i].evidence);
        } else {
            assert!(stopped.answers[i].outputs.is_empty());
        }
        assert!(
            stopped.answers[i]
                .reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(actual) if actual==&expected))
        );
    }
    assert!(stopped.answers[2].reasons.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm{operand_types,..} if operand_types.contains(&Type::Text))));
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn infinite_actual_type_answer_stop_retains_original_algorithm_reason_and_prior_results() {
    stop(false)
}
#[test]
fn infinite_fresh_recheck_stop_retains_verified_answer_and_freezes() {
    stop(true)
}

#[test]
fn generic_outer_domain_finite_decisions_recheck_before_and_after_false_mutation() {
    for (script, ask) in [
        (
            "view current():Bool=forall t:(Text,Unused).forall b:Bool.false;",
            "v=evaluate(Walk.current)",
        ),
        (
            "law required current(t:(Text,Unused)):forall b:Bool.false;",
            "v=check(Walk.current)",
        ),
    ] {
        let r = evaluate_observed_bytes(
            fixture::input(script, "Z", &[], "r1"),
            &[ask],
            &mut named_call_quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "partial");
        assert_eq!(r.answers[0].status, Decision::Undetermined);
        let at = r.answers[0].outputs["evaluation"].0;
        let Some(Payload::Evaluation {
            expression,
            bindings,
            value,
            ..
        }) = &r.nodes[at].payload
        else {
            panic!()
        };
        assert!(value.is_none());
        let domain = r.nodes[at]
            .scope
            .quantifiers
            .iter()
            .find(|q| q.name == "t")
            .unwrap()
            .domain
            .unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
        let env = Environment::with_requests(
            r.prepared.inputs(),
            r.prepared.requests().requests(),
            &mut named_call_quiet(),
        )
        .unwrap();
        for _ in 0..2 {
            env.validate_answer(&graph, &r.prepared.requests().requests()[0], &r.answers[0])
                .unwrap();
            let analyzed = env
                .universal_analysis(&graph, *expression, &[domain], bindings)
                .unwrap();
            assert_eq!(analyzed.value, None);
            assert_eq!(analyzed.finite_dependency, None);
        }
        let false_value = r
            .nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                matches!(&n.payload, Some(Payload::Scalar(Scalar::Bool(false))))
                    .then_some(NodeRef(i))
            })
            .unwrap();
        let saved = graph.nodes[at].clone();
        let Some(Payload::Evaluation { value, parts, .. }) = &mut graph.nodes[at].payload else {
            panic!()
        };
        *value = Some(false_value);
        parts[0].value = Some(false_value);
        assert!(env.recheck_node(&graph, &graph.nodes[at], at).is_err());
        graph.nodes[at] = saved;
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
        env.validate_answer(&graph, &r.prepared.requests().requests()[0], &r.answers[0])
            .unwrap();
        rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    }
}

fn committed_reason_stop(kind: usize) {
    use std::{cell::Cell, rc::Rc};
    let inputs = fixture::input(SCRIPT, "Z", &[], "r1");
    let phase = Rc::new(Cell::new(false));
    let count = Rc::new(Cell::new(0));
    let (p, c) = (phase.clone(), count.clone());
    let mut control = Control::new(Default::default(), move |_| {
        if p.get() {
            c.set(c.get() + 1);
        }
        Default::default()
    });
    let prepared = prepare_observed(inputs.clone(), ASKS, &mut control).unwrap();
    phase.set(true);
    let normal = evaluate_observed(prepared, &mut control).unwrap();
    assert_eq!(normal.status(), "partial");
    let total = count.get();
    let target = normal
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (normal.contexts[i].request == 2
                && matches!(n.ty, NodeType::Evaluation(Type::Bool))
                && n.reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. })))
            .then_some(i)
        })
        .unwrap();
    let original = normal.nodes[target]
        .reasons
        .iter()
        .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        .unwrap()
        .clone();
    assert!(
        matches!(&original.kind, ReasonKind::UnsupportedAlgorithm{operand_types,..} if operand_types == &[Type::Text])
    );
    assert_eq!(original.request, "v");
    assert!(matches!(original.location, Some(Location::Law { .. })));
    assert_eq!(original.dependencies.len(), 1);
    assert!(original.dependencies[0].0 < target);
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let run_at = |position| {
        let phase = Rc::new(Cell::new(false));
        let seen = Rc::new(Cell::new(0));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let point = Rc::new(Cell::new(None));
        let (ph, s, p, f, at) = (
            phase.clone(),
            seen.clone(),
            probes.clone(),
            frozen.clone(),
            point.clone(),
        );
        let mut control = Control::new(limits, move |checkpoint| {
            p.set(p.get() + 1);
            if ph.get() {
                s.set(s.get() + 1);
                if s.get() == position {
                    assert!(f.replace(Some(p.get())).is_none());
                    at.set(Some(checkpoint));
                    return usage;
                }
            }
            Default::default()
        });
        let prepared = prepare_observed(inputs.clone(), ASKS, &mut control).unwrap();
        phase.set(true);
        let stopped = evaluate_observed(prepared, &mut control).unwrap();
        assert_eq!(stopped.status(), "interrupted");
        assert_eq!(seen.get(), position);
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(
            control.checkpoint(Checkpoint::Expression),
            Err(expected.clone())
        );
        assert_eq!(Some(probes.get()), frozen.get());
        (stopped, point.get().unwrap())
    };
    // Find the first checkpoint after this exact Evaluation was committed.
    // No fixed checkpoint count or additional production observer is needed.
    let (mut low, mut high) = (1, total);
    assert!(run_at(high).0.nodes.len() > target);
    while low < high {
        let mid = low + (high - low) / 2;
        if run_at(mid).0.nodes.len() > target {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    assert!(low > 1);
    let before = run_at(low - 1).0;
    assert!(before.nodes.len() <= target);
    assert!(!before.answers[2].reasons.contains(&original));
    assert!(!before.issues.contains(&original));
    let (stopped, point) = run_at(low);
    assert_eq!(point, Checkpoint::FiniteIteration);
    assert_eq!(stopped.nodes.len(), target + 1);
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..=target])
    );
    assert_eq!(stopped.contexts, normal.contexts[..=target]);
    assert_eq!(stopped.nodes[target].reasons, normal.nodes[target].reasons);
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    assert!(
        stopped.answers[2].reasons.contains(&original),
        "挿入後停止でも元算法理由をAnswerへ残す"
    );
    assert!(stopped.issues.contains(&original));
    for a in &stopped.answers[2..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind, ReasonKind::Stop(reason) if reason == &expected))
        );
    }
    assert_eq!(stopped.prepared.inputs().sources(), &inputs);
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn infinite_committed_evaluation_post_cancel_retains_original_algorithm_reason() {
    committed_reason_stop(0)
}

#[test]
fn infinite_committed_evaluation_post_budgets_retain_original_algorithm_reason() {
    for kind in [1, 2] {
        committed_reason_stop(kind);
    }
}
