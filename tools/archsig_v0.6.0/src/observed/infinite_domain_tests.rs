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
fn infinite_unbound_mixed_family_claims_recheck_original_domains() {
    let r = evaluate_observed_bytes(
        fixture::input(
            "law required current(b:Bool,item:Text):item=item;",
            "Z",
            &[],
            "r1",
        ),
        &["v=check(Walk.current)"],
        &quiet(),
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
        let r =
            evaluate_observed_bytes(fixture::input(script, "Z", &[], "r1"), &[ask], &quiet())
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
            &quiet(),
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

fn committed_reason_stop() {
    use std::{cell::Cell, rc::Rc};
    let inputs = fixture::input(SCRIPT, "Z", &[], "r1");
    let phase = Rc::new(Cell::new(false));
    let count = Rc::new(Cell::new(0));
    let (p, c) = (phase.clone(), count.clone());
    let control = Control::new(move |_| {
        if p.get() {
            c.set(c.get() + 1);
        }
        None
    });
    let prepared = prepare_observed(inputs.clone(), ASKS, &control).unwrap();
    phase.set(true);
    let normal = evaluate_observed(prepared, &control).unwrap();
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
    let expected = crate::result::Signal::Term;
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
        let control = Control::new(move |checkpoint| {
            p.set(p.get() + 1);
            if ph.get() {
                s.set(s.get() + 1);
                if s.get() == position {
                    assert!(f.replace(Some(p.get())).is_none());
                    at.set(Some(checkpoint));
                    return Some(crate::result::Signal::Term);
                }
            }
            None
        });
        let prepared = prepare_observed(inputs.clone(), ASKS, &control).unwrap();
        phase.set(true);
        let stopped = evaluate_observed(prepared, &control).unwrap();
        assert_eq!(stopped.status(), "interrupted");
        assert_eq!(seen.get(), position);
        assert_eq!(control.stop_reason(), Some(expected));
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
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
    committed_reason_stop()
}
