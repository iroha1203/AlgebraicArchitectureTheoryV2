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
}
#[test]
fn affine_comprehension_actual_iteration_stop_keeps_verified_results() {
    stop(false, false)
}
