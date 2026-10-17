use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_bindings.rs");
}
fn result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("r1"), asks, &mut named_call_quiet()).unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn env<'a>(r: &'a ObservedEvaluation, c: &mut Control) -> Environment<'a> {
    Environment::with_requests(r.prepared.inputs(), r.prepared.requests().requests(), c).unwrap()
}
const ASK: &[&str] = &[
    "first=evaluate(Applications.abSeed)",
    "other=evaluate(Applications.abSeed)",
    "take=evaluate(Applications.abDouble,x=$first.value)",
];
#[test]
fn answer_binding_rechecks_original_values_types_support_scope_and_context() {
    let r = result(&[
        "used=evaluate(Applications.abUse,x=$copied.value)",
        "copied=evaluate(Applications.abCopy,x=$packed.evaluation.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ]);
    let value = r.answers[2].outputs["value"].0;
    completion_mutation(&r, value, |ns| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut ns[value].payload else {
            panic!()
        };
        items[0] = Scalar::Z(7.into());
    });
    completion_mutation(&r, value, |ns| ns[value].ty = NodeType::Value(Type::Bool));
    completion_mutation(&r, value, |ns| {
        assert!(!ns[value].support.is_empty());
        ns[value].support.clear()
    });
    completion_mutation(&r, value, |ns| ns[value].scope.snapshots.clear());
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r, &mut named_call_quiet());
    let target = r.answers[0].outputs["evaluation"].0;
    let old = g.contexts[value];
    g.contexts[value].request = 0;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.contexts[value] = old;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let u = result(&[
        "universal=check(Applications.abUniversal,x=$first.value)",
        "first=evaluate(Applications.abSeed)",
        "other=evaluate(Applications.abSeed)",
    ]);
    let first = u.answers[1].outputs["value"];
    let other = u.answers[2].outputs["value"];
    let target=u.nodes.iter().enumerate().find_map(|(i,n)|matches!(&n.payload,Some(Payload::Expression{bindings,..})if bindings.iter().any(|b|b.name=="x"&&b.value==first)).then_some(i)).unwrap();
    completion_mutation(&u, target, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[target].payload else {
            panic!()
        };
        let binding = bindings.iter_mut().find(|b| b.name == "x").unwrap();
        binding.value = other;
    });
}
#[test]
fn answer_binding_equal_foreign_value_and_output_registry_are_not_authorized() {
    let r = result(ASK);
    let first = r.answers[0].outputs["value"];
    let other = r.answers[1].outputs["value"];
    assert_ne!(first, other);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_eq!(g.scalar(first).unwrap(), g.scalar(other).unwrap());
    let target = r.answers[2].outputs["evaluation"].0;
    let source = match &r.nodes[target].payload {
        Some(Payload::Evaluation { expression, .. }) => expression.0,
        _ => panic!(),
    };
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        assert_eq!(bindings[0].value, first);
        bindings[0].value = other;
        for x in &mut ns[source].arguments {
            if *x == first {
                *x = other
            }
        }
    });
    let e = env(&r, &mut named_call_quiet());
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let at = g.checked_answers.iter().position(|(i, _)| *i == 0).unwrap();
    let original = g.checked_answers[at].1.clone();
    g.checked_answers[at].1.outputs = r.answers[1].outputs.clone();
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = original;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
}
#[test]
fn answer_binding_original_request_anchor_rejects_coherent_selector_changes() {
    let r = result(ASK);
    let target = r.answers[2].outputs["evaluation"].0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r, &mut named_call_quiet());
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let old = g.requests[2].clone();
    let Selector::Answer { id, .. } = &mut g.requests[2].arguments[0].value else {
        panic!()
    };
    *id = "other".into();
    g.requests[2].dependencies = vec!["other".into()];
    let first = r.answers[0].outputs["value"];
    let other = r.answers[1].outputs["value"];
    let mut changed = g.nodes.clone();
    for (i, n) in changed.iter_mut().enumerate() {
        if g.contexts[i].request == 2 {
            for x in &mut n.arguments {
                if *x == first {
                    *x = other
                }
            }
            match &mut n.payload {
                Some(
                    Payload::Expression { bindings, .. } | Payload::Evaluation { bindings, .. },
                ) => {
                    for b in bindings {
                        if b.value == first {
                            b.value = other
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let original_nodes = std::mem::replace(&mut g.nodes, changed);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[2] = old;
    g.nodes = original_nodes;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
}
#[test]
fn answer_binding_same_environment_rejects_answer_status_and_registered_output_changes() {
    let r = result(ASK);
    let target = r.answers[2].outputs["evaluation"].0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r, &mut named_call_quiet());
    let at = g.checked_answers.iter().position(|(i, _)| *i == 0).unwrap();
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    let original = g.checked_answers[at].1.clone();
    g.checked_answers[at].1.status = Decision::Undetermined;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = original.clone();
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
    g.checked_answers[at].1.outputs.remove("value");
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[at].1 = original;
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
}
fn answer_binding_stop(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "current=evaluate(Applications.abKeep,x=$seed.value,p=@v/p)",
        "later=evaluate(Applications.abSeed)",
    ];
    let normal = evaluate_observed_bytes(
        fixture::input_mode("stop", "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(normal.status(), "complete");
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations["Applications.abKeep"].signature
    else {
        panic!()
    };
    let span = params[0].span;
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
    let prepared = prepare_observed(fixture::input_mode("stop", "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span
                    && ctx.request == 2
                    && operation == "answer_binding_scan"
                    && (!recheck || ph.get())
                {
                    let old = s.get();
                    s.set(old + 1);
                    if old == 1 {
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
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 2);
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
    for (index, a) in stopped.answers.iter().enumerate().skip(2) {
        if recheck && index == 2 {
            assert_eq!(a.status, Decision::Established);
            assert_eq!(a.outputs, normal.answers[index].outputs);
            assert_eq!(a.claim, normal.answers[index].claim);
            assert_eq!(a.evidence, normal.answers[index].evidence);
            assert!(a.reasons.iter().any(|r| {
                matches!(r.kind, ReasonKind::Missing)
                    && r.missing
                        .iter()
                        .any(|f| f.field.as_deref() == Some("Reservations.State.free"))
            }));
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
fn answer_binding_actual_scan_stop_keeps_prior_value_refutation_and_prefix() {
    answer_binding_stop(false)
}
#[test]
fn answer_binding_fresh_recheck_stop_keeps_verified_current_value_reasons_and_prefix() {
    answer_binding_stop(true)
}
