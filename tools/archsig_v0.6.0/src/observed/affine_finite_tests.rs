use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/affine_field_chains.rs");
}
const SCRIPT: &str = "view current(n:Node):Bool=forall z:Z . z+count(set{x|x in list<Z>[1,1,2]})=z+2; view quantified(n:Node):Bool=forall z:Z . z+(if (forall x in list<Z>[1,2] . x>0) then 2 else 3)=z+2;";
const ASK: &[&str] = &[
    "seed=evaluate(Walk.seed)",
    "prior=check(Walk.prior)",
    "one=evaluate(Walk.current,n=@v/p)",
    "two=evaluate(Walk.current,n=@v/p)",
    "quant=evaluate(Walk.quantified,n=@v/p)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(SCRIPT, "Z", &[], "r1"),
        ASK,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn evaluation(r: &ObservedEvaluation, request: usize, text: &str) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            if r.contexts[i].request != request {
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
            (&r.prepared.inputs().sources().law().bytes()[span.0..span.1] == text.as_bytes())
                .then_some(i)
        })
        .unwrap()
}
fn children(n: &Node) -> Vec<NodeRef> {
    let Some(Payload::Evaluation { parts, .. }) = &n.payload else {
        panic!()
    };
    parts[0].children.clone()
}
fn value(n: &Node) -> NodeRef {
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &n.payload
    else {
        panic!()
    };
    *value
}
fn replace_children(ns: &mut [Node], at: usize, children: Vec<NodeRef>) {
    let (source, v) = match &mut ns[at].payload {
        Some(Payload::Evaluation {
            expression,
            parts,
            value,
            ..
        }) => {
            parts[0].children = children.clone();
            (*expression, *value)
        }
        _ => panic!(),
    };
    ns[at].arguments = std::iter::once(source)
        .chain(children.iter().copied())
        .chain(v)
        .collect();
    if let Some(v) = v {
        ns[v.0].arguments = children;
    }
}
#[test]
fn affine_comprehension_rejects_equal_duplicate_iteration_and_incomplete_coverage() {
    let mut r = result();
    let at = evaluation(&r, 2, "set{x|x in list<Z>[1,1,2]}");
    let cs = children(&r.nodes[at]);
    assert_eq!(cs.len(), 4);
    assert_ne!(cs[1], cs[2]);
    assert_eq!(
        data_scalar_at(&r, value(&r.nodes[cs[1].0]).0),
        data_scalar_at(&r, value(&r.nodes[cs[2].0]).0)
    );
    let scalar = value(&r.nodes[at]).0;
    let mut changed = r.nodes[..=at].to_vec();
    let mut duplicate = cs.clone();
    duplicate[1] = cs[2];
    replace_children(&mut changed, at, duplicate);
    let mut shape = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..scalar]).unwrap();
    shape.active = r.contexts[scalar];
    shape
        .push(changed[scalar].clone())
        .expect("同値の別反復子は形検査だけでは拒否しない");
    for kind in 0..3 {
        completion_mutation(&r, at, |ns| {
            let mut altered = cs.clone();
            match kind {
                0 => altered[1] = cs[2],
                1 => {
                    altered.remove(1);
                }
                _ => altered.swap(1, 2),
            }
            replace_children(ns, at, altered);
        });
    }
    let index = r.contexts[cs[1].0].iteration.unwrap();
    let saved = r.iterations[index].member.clone();
    assert!(matches!(
        saved,
        crate::observed::call::Member::ListPosition(0)
    ));
    r.iterations[index].member = crate::observed::call::Member::ListPosition(1);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=cs[1].0]).unwrap();
    rejects_named_prefix(&r, &r.nodes[..=scalar]);
    rejects_named_prefix(&r, &r.nodes);
    r.iterations[index].member = saved;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn affine_finite_warm_environment_rejects_foreign_cases_scope_and_restores() {
    let r = result();
    let at = evaluation(&r, 3, "set{x|x in list<Z>[1,1,2]}");
    let foreign = children(&r.nodes[evaluation(&r, 2, "set{x|x in list<Z>[1,1,2]}")])[1];
    let original = children(&r.nodes[at]);
    assert_eq!(
        data_scalar_at(&r, value(&r.nodes[original[1].0]).0),
        data_scalar_at(&r, value(&r.nodes[foreign.0]).0)
    );
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let env = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let saved = graph.nodes.clone();
    for kind in 0..3 {
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
        match kind {
            0 => {
                let mut cs = original.clone();
                cs[1] = foreign;
                replace_children(&mut graph.nodes, at, cs)
            }
            1 => graph.nodes[at].scope.quantifiers.clear(),
            _ => {
                let Some(Payload::Evaluation { expression, .. }) = graph.nodes[at].payload else {
                    panic!()
                };
                graph.nodes[expression.0].arguments.swap(0, 1)
            }
        }
        assert!(env.recheck_node(&graph, &graph.nodes[at], at).is_err());
        graph.nodes.clone_from(&saved);
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn affine_finite_quantifier_rechecks_members_binders_and_exhaustion() {
    let r = result();
    let at = evaluation(&r, 4, "forall x in list<Z>[1,2] . x>0");
    let cs = children(&r.nodes[at]);
    assert_eq!(cs.len(), 3);
    assert_ne!(cs[1], cs[2]);
    assert_eq!(
        data_scalar_at(&r, value(&r.nodes[cs[1].0]).0),
        &Scalar::Bool(true)
    );
    assert_eq!(
        data_scalar_at(&r, value(&r.nodes[cs[2].0]).0),
        &Scalar::Bool(true)
    );
    completion_mutation(&r, at, |ns| {
        let mut altered = cs.clone();
        altered[2] = cs[1];
        replace_children(ns, at, altered);
    });
    let domain = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            if r.contexts[i].request == 4
                && matches!(n.payload,Some(Payload::Domain{ref ty,..})if *ty==Type::Z)
            {
                Some(i)
            } else {
                None
            }
        })
        .unwrap();
    completion_mutation(&r, domain, |ns| {
        let Some(Payload::Domain { elements, .. }) = &mut ns[domain].payload else {
            panic!()
        };
        assert_eq!(elements.len(), 2);
        elements.pop();
        ns[domain].arguments.pop();
    });
    let evidence = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            if r.contexts[i].request == 4
                && matches!(n.payload, Some(Payload::FiniteExhaustion { .. }))
            {
                Some(i)
            } else {
                None
            }
        })
        .unwrap();
    completion_mutation(&r, evidence, |ns| {
        let Some(Payload::FiniteExhaustion {
            checked, instances, ..
        }) = &mut ns[evidence].payload
        else {
            panic!()
        };
        assert_eq!(*checked, 2);
        *checked = 1;
        instances.pop();
        ns[evidence].arguments.pop();
    });
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
fn stop(fresh: bool, quant: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = &[
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        if quant {
            "v=evaluate(Walk.quantified,n=@v/p)"
        } else {
            "v=evaluate(Walk.current,n=@v/p)"
        },
        "later=evaluate(Walk.seed)",
    ];
    let input = fixture::input(SCRIPT, "Z", &[], "r1");
    let normal = evaluate_observed_bytes(input.clone(), asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let text = if quant {
        "forall x in list<Z>[1,2] . x>0"
    } else {
        "set{x|x in list<Z>[1,1,2]}"
    };
    let at = evaluation(&normal, 2, text);
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
    let prepared = prepare_observed(input, asks, &mut control).unwrap();
    let mut copy = control.clone();
    let stopped =
        evaluate_observed_with_validator(prepared, &mut control, |env, graph, request, answer| {
            env.validate_answer(graph, request, answer)?;
            if request.id == "prior" {
                let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, index| {
                    let actual = if quant {
                        "quant_body"
                    } else {
                        "comprehension_iteration"
                    };
                    let recheck = if quant {
                        "universal_quant_recheck"
                    } else {
                        "universal_finite_recheck"
                    };
                    if at == span
                        && context.request == 2
                        && index == 1
                        && ((!fresh && operation == actual)
                            || (fresh && ph.get() && operation == recheck))
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
            assert_eq!(stopped.answers[i].evidence, normal.answers[i].evidence);
        } else {
            assert_eq!(stopped.answers[i].status, Decision::Undetermined);
            assert!(stopped.answers[i].outputs.is_empty());
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
fn affine_comprehension_actual_iteration_stop_keeps_verified_results() {
    stop(false, false)
}
#[test]
fn affine_comprehension_fresh_recheck_stop_keeps_verified_current() {
    stop(true, false)
}
#[test]
fn affine_finite_quantifier_actual_body_stop_keeps_verified_results() {
    stop(false, true)
}
#[test]
fn affine_finite_quantifier_fresh_recheck_stop_keeps_verified_current() {
    stop(true, true)
}

#[test]
fn affine_finite_symbolic_whole_rechecks_source_steps_domain_and_coverage() {
    let script = "view inner(x:Q):Bool=forall y:Q . x+y=y; law required finite(z:Q):forall b in list<Bool>[true,false] . inner(z);";
    let r = evaluate_observed_bytes(
        fixture::input(script, "Z", &[], "r1"),
        &["one=check(Walk.finite)", "two=check(Walk.finite)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let proofs: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.payload, Some(Payload::Normalization { .. })).then_some(i))
        .collect();
    assert_eq!(proofs.len(), 2);
    let at = proofs[1];
    let Some(Payload::Normalization {
        before,
        after,
        steps,
    }) = &r.nodes[at].payload
    else {
        panic!()
    };
    assert_eq!(steps.len(), 1);
    let (before, after, source) = (*before, *after, steps[0]);
    let Some(Payload::Normalization { steps: old, .. }) = &r.nodes[proofs[0]].payload else {
        panic!()
    };
    let foreign = old[0];
    assert_eq!(
        graph.get(source).unwrap().ty,
        graph.get(foreign).unwrap().ty
    );
    let env = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap();
    let saved = graph.nodes.clone();
    for replacement in [vec![], vec![foreign]] {
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
        if let Some(Payload::Normalization { steps, .. }) = &mut graph.nodes[at].payload {
            *steps = replacement.clone();
        }
        graph.nodes[at].arguments = [before, after]
            .into_iter()
            .chain(replacement.iter().copied())
            .collect();
        graph.nodes[after.0].arguments = std::iter::once(before).chain(replacement).collect();
        assert!(env.recheck_node(&graph, &graph.nodes[at], at).is_err());
        graph.nodes.clone_from(&saved);
        env.recheck_node(&graph, &graph.nodes[at], at).unwrap();
    }
    let finite = evaluation(&r, 1, "forall b in list<Bool>[true,false] . inner(z)");
    let cs = children(&r.nodes[finite]);
    assert_eq!(cs.len(), 3);
    for replacement in [vec![cs[0], cs[1]], vec![cs[0], cs[1], cs[1]]] {
        let mut nodes = r.nodes.clone();
        replace_children(&mut nodes, finite, replacement);
        rejects_named_prefix(&r, &nodes);
    }
    let domain = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 1
                && n.arguments.first() == Some(&source)
                && matches!(n.payload, Some(Payload::Domain { .. })))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&r, at, |nodes| {
        if let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload {
            elements.pop();
        }
        nodes[domain].arguments.pop();
    });
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
