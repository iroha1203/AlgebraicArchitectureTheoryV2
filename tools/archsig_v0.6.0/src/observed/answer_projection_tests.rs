use super::*;
use crate::observed::projection::ProjectionStep;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_projections.rs");
}
const ASK: &[&str] = &[
    "first=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    "other=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    "foreign=evaluate(Applications.abIdentity,x=$other.evaluation.value[6][0])",
    "take=evaluate(Applications.abIdentity,x=$first.evaluation.value[6][0])",
    "nested=evaluate(Applications.apNested)",
    "deep=evaluate(Applications.abIdentity,x=$nested.value[0].some[1][1])",
    "universal=check(Applications.abUniversal,x=$first.value[0])",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn projection(r: &ObservedEvaluation, request: usize) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == request && matches!(n.rule, Rule::Projection(_))).then_some(i)
        })
        .unwrap()
}
fn env<'a>(r: &'a ObservedEvaluation) -> Environment<'a> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
#[test]
fn answer_projection_rechecks_original_root_path_value_type_scope_support_and_arity() {
    let r = result();
    let at = projection(&r, 3);
    completion_mutation(&r, at, |ns| {
        ns[at].payload = Some(Payload::Scalar(Scalar::Z(7.into())))
    });
    completion_mutation(&r, at, |ns| ns[at].ty = NodeType::Value(Type::Bool));
    completion_mutation(&r, at, |ns| {
        assert!(!ns[at].support.is_empty());
        ns[at].support.clear();
    });
    completion_mutation(&r, at, |ns| ns[at].scope.snapshots.clear());
    completion_mutation(&r, at, |ns| ns[at].arguments.clear());
    completion_mutation(&r, at, |ns| {
        ns[at].arguments.push(r.answers[1].outputs["evaluation"])
    });
    completion_mutation(&r, at, |ns| {
        ns[at].arguments[0] = r.answers[1].outputs["evaluation"]
    });
    completion_mutation(&r, at, |ns| ns[at].rule = Rule::Projection(vec![]));
    completion_mutation(&r, at, |ns| {
        let Rule::Projection(path) = &mut ns[at].rule else {
            panic!()
        };
        *path.last_mut().unwrap() = ProjectionStep::Index(1);
    });
    completion_mutation(&r, at, |ns| {
        let Rule::Projection(path) = &mut ns[at].rule else {
            panic!()
        };
        path.remove(0);
    });
    completion_mutation(&r, at, |ns| ns[at].rule = Rule::Construction("projection"));
    let deep = projection(&r, 5);
    completion_mutation(&r, deep, |ns| {
        let Rule::Projection(path) = &mut ns[deep].rule else {
            panic!()
        };
        path[1] = ProjectionStep::Index(0);
    });
    let universal = projection(&r, 6);
    completion_mutation(&r, universal, |ns| {
        ns[universal].arguments[0] = r.answers[1].outputs["value"]
    });
}
#[test]
fn answer_projection_equal_foreign_binding_and_context_are_not_original_selection() {
    let r = result();
    let at = projection(&r, 3);
    let foreign = projection(&r, 2);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_ne!(at, foreign);
    assert_eq!(
        g.scalar(NodeRef(at)).unwrap(),
        g.scalar(NodeRef(foreign)).unwrap()
    );
    assert!(foreign < at);
    let evaluation = r.answers[3].outputs["evaluation"].0;
    let Some(Payload::Evaluation { expression, .. }) = &r.nodes[evaluation].payload else {
        panic!()
    };
    let source = expression.0;
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        assert_eq!(bindings[0].value, NodeRef(at));
        bindings[0].value = NodeRef(foreign);
        for reference in &mut ns[source].arguments {
            if *reference == NodeRef(at) {
                *reference = NodeRef(foreign);
            }
        }
    });
    let mut g = g;
    let e = env(&r);
    e.recheck_node(&g, &g.nodes[evaluation], evaluation)
        .unwrap();
    let old = g.contexts[at];
    g.contexts[at].request = 2;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[evaluation], evaluation),
        Err(ValidationFailure::Internal(_))
    ));
    g.contexts[at] = old;
    e.recheck_node(&g, &g.nodes[evaluation], evaluation)
        .unwrap();
}
#[test]
fn answer_projection_whole_existing_ref_cannot_be_repackaged_as_inline_projection() {
    let r = result();
    let at = projection(&r, 3);
    let root = r.answers[0].outputs["evaluation"];
    let value = r.answers[0].outputs["value"];
    let original = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let scalar = original.scalar(value).unwrap().clone();
    let mut repackaged = r.nodes[at].clone();
    repackaged.ty = NodeType::Value(scalar.ty());
    repackaged.payload = Some(Payload::Scalar(scalar));
    repackaged.rule = Rule::Projection(vec![ProjectionStep::Field("value".into())]);
    repackaged.arguments = vec![root];
    repackaged.scope = r.nodes[root.0].scope.clone();
    repackaged.support = r.nodes[root.0].support.clone();
    let mut shape = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..at]).unwrap();
    shape.active = r.contexts[at];
    shape
        .push(repackaged.clone())
        .expect("形だけでは合法な通常値だが、既出Refの再包装は元Request射影でない");
    completion_mutation(&r, at, |ns| ns[at] = repackaged.clone());
}
#[test]
fn answer_projection_same_environment_rejects_changed_nodes_requests_and_producer_outputs() {
    let r = result();
    let at = projection(&r, 3);
    let target = r.answers[3].outputs["evaluation"].0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let original = g.nodes[at].clone();
    g.nodes[at].payload = Some(Payload::Scalar(Scalar::Z(7.into())));
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[at] = original.clone();
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let old = g.requests[3].clone();
    let Selector::Answer { id, .. } = &mut g.requests[3].arguments[0].value else {
        panic!()
    };
    *id = "other".into();
    g.requests[3].dependencies = vec!["other".into()];
    g.nodes[at].arguments[0] = r.answers[1].outputs["evaluation"];
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[3] = old;
    g.nodes[at] = original;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let registry = g.checked_answers.iter().position(|(i, _)| *i == 0).unwrap();
    let old = g.checked_answers[registry].1.clone();
    g.checked_answers[registry].1.outputs = r.answers[1].outputs.clone();
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[registry].1 = old;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
}
fn projection_stop(recheck: bool, law: bool) {
    use std::{cell::Cell, rc::Rc};
    let current = if law {
        "current=check(Applications.abFour,x=$packed.evaluation.value[6][1])"
    } else {
        "current=evaluate(Applications.abIdentity,x=$nested.value[0].some[1][1])"
    };
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
        "nested=evaluate(Applications.apNested)",
        current,
        "later=evaluate(Applications.abSeed)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut named_call_quiet())
            .unwrap();
    assert_eq!(normal.status(), "partial");
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let declaration = if law {
        "Applications.abFour"
    } else {
        "Applications.abIdentity"
    };
    let params = match &normal.prepared.inputs().law().declarations[declaration].signature {
        Signature::View { params, .. } | Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    let span = params[0].span;
    assert_eq!(
        normal.answers[5].status,
        if law {
            Decision::Refuted
        } else {
            Decision::Established
        }
    );
    if law {
        assert!(normal.answers[5].claim.is_some());
        assert!(!normal.answers[5].evidence.is_empty());
    }
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
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
    let prepared = prepare_observed(fixture::input("stop", "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "nested" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span
                    && ctx.request == 5
                    && operation == "answer_projection_step"
                    && (!recheck || ph.get())
                {
                    let old = s.get();
                    s.set(old + 1);
                    if old == if law { 1 } else { 2 } {
                        a.set(true)
                    }
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::with_requests(
                normal.prepared.inputs(),
                normal.prepared.requests().requests(),
                &mut cc,
            )?;
            phase.set(true);
            let result = fresh.validate_answer(g, request, answer);
            phase.set(false);
            result?;
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), if law { 2 } else { 3 });
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    assert_eq!(&stopped.answers[..5], &normal.answers[..5]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for (index, a) in stopped.answers.iter().enumerate().skip(5) {
        if recheck && index == 5 {
            assert_eq!(a.status, normal.answers[index].status);
            assert_eq!(a.outputs, normal.answers[index].outputs);
            assert_eq!(a.claim, normal.answers[index].claim);
            assert_eq!(a.evidence, normal.answers[index].evidence);
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
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn answer_projection_actual_path_stop_keeps_prior_values_refutation_missing_and_prefix() {
    projection_stop(false, false)
}
#[test]
fn answer_projection_fresh_path_recheck_stop_keeps_verified_current_and_freezes() {
    projection_stop(true, false)
}

#[test]
fn answer_projection_fresh_recheck_stop_keeps_verified_current_refutation_claim_and_evidence() {
    projection_stop(true, true)
}
