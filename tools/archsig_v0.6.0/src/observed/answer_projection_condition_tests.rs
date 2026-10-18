use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_projection_conditions.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.abSeed)",
    "prior=check(Applications.abPrior)",
    "empty=evaluate(Applications.apEmpty)",
    "other=evaluate(Applications.apEmpty)",
    "take=evaluate(Applications.abIdentity,x=$empty.value[0])",
    "later=evaluate(Applications.abSeed)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, request, answer).unwrap();
    }
    r
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn at(r: &ObservedEvaluation, part: ProjectionCheckPart) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            matches!(&n.rule,Rule::ProjectionCheck{part:p,..}if *p==part).then_some(i)
        })
        .unwrap()
}
#[test]
fn projection_condition_nodes_recheck_original_root_values_types_edges_support_scope_and_evidence()
{
    let r = result();
    for part in [
        ProjectionCheckPart::Name,
        ProjectionCheckPart::Actual,
        ProjectionCheckPart::Required,
        ProjectionCheckPart::Evidence,
        ProjectionCheckPart::Condition,
    ] {
        let i = at(&r, part);
        completion_mutation(&r, i, |ns| ns[i].arguments.clear());
        completion_mutation(&r, i, |ns| {
            ns[i].arguments.push(r.answers[0].outputs["value"])
        });
        completion_mutation(&r, i, |ns| {
            ns[i].arguments[0] = r.answers[3].outputs["value"]
        });
        completion_mutation(&r, i, |ns| ns[i].scope.readings.clear());
        completion_mutation(&r, i, |ns| {
            ns[i].support.push(Fact {
                snapshot: "v".into(),
                subject: "p".into(),
                field: None,
                atom: None,
            })
        });
        completion_mutation(&r, i, |ns| ns[i].ty = NodeType::Value(Type::Z));
        completion_mutation(&r, i, |ns| {
            let Rule::ProjectionCheck { parameter, .. } = &mut ns[i].rule else {
                panic!()
            };
            *parameter = "foreign".into();
        });
    }
    let actual = at(&r, ProjectionCheckPart::Actual);
    completion_mutation(&r, actual, |ns| {
        ns[actual].payload = Some(Payload::Scalar(Scalar::Bool(true)))
    });
    let required = at(&r, ProjectionCheckPart::Required);
    completion_mutation(&r, required, |ns| {
        ns[required].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    let condition = at(&r, ProjectionCheckPart::Condition);
    completion_mutation(&r, condition, |ns| {
        ns[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
    completion_mutation(&r, condition, |ns| ns[condition].evidence.clear());
    let proof = at(&r, ProjectionCheckPart::Evidence);
    completion_mutation(&r, proof, |ns| {
        let Some(Payload::ProjectionCounterexample { left, right, .. }) = &mut ns[proof].payload
        else {
            panic!()
        };
        std::mem::swap(left, right);
    });
}
fn reject_answer(r: &ObservedEvaluation, change: impl Fn(&mut Answer)) {
    let cutoff = r.contexts.iter().position(|c| c.request == 5).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let g = rebuild_for_origin_and_support_recheck(r, nodes).unwrap();
        let e = env(r);
        let request = &r.prepared.requests().requests()[4];
        let original = &r.answers[4];
        e.validate_answer(&g, request, original).unwrap();
        let mut altered = original.clone();
        change(&mut altered);
        assert_ne!(&altered, original);
        assert!(matches!(
            e.validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(r).validate_answer(&g, request, &altered),
            Err(ValidationFailure::Internal(_))
        ));
        e.validate_answer(&g, request, original).unwrap();
    }
}
#[test]
fn projection_condition_answer_rejects_forged_decisions_condition_reasons_refs_and_scope() {
    let r = result();
    reject_answer(&r, |a| a.status = Decision::Refuted);
    reject_answer(&r, |a| a.claim = r.answers[1].claim);
    reject_answer(&r, |a| a.evidence = r.answers[1].evidence.clone());
    reject_answer(&r, |a| {
        a.outputs
            .insert("value".into(), r.answers[0].outputs["value"]);
    });
    reject_answer(&r, |a| a.scope.readings.clear());
    reject_answer(&r, |a| {
        a.reasons
            .retain(|r| !matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    });
    reject_answer(&r, |a| {
        a.reasons
            .retain(|r| !matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
    });
    reject_answer(&r, |a| {
        let reason = a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap();
        reason.dependencies.clear();
    });
    reject_answer(&r, |a| {
        let reason = a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap();
        let ReasonKind::ConditionFailed { construction, .. } = &mut reason.kind else {
            panic!()
        };
        *construction = "evaluation";
    });
    reject_answer(&r, |a| {
        let reason = a
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap();
        reason.location = None;
    });
}
#[test]
fn projection_condition_same_environment_rechecks_selector_path_producer_context_and_coherent_transfers()
 {
    let r = result();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    let request = &r.prepared.requests().requests()[4];
    let answer = &r.answers[4];
    e.validate_answer(&g, request, answer).unwrap();
    let condition = at(&r, ProjectionCheckPart::Condition);
    let old = g.contexts[condition];
    g.contexts[condition].request = 3;
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.contexts[condition] = old;
    e.validate_answer(&g, request, answer).unwrap();
    let actual = at(&r, ProjectionCheckPart::Actual);
    let old = g.nodes[actual].clone();
    g.nodes[actual].payload = Some(Payload::Scalar(Scalar::Bool(true)));
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[actual] = old;
    e.validate_answer(&g, request, answer).unwrap();
    let old = g.requests[4].clone();
    let Selector::Answer { id, .. } = &mut g.requests[4].arguments[0].value else {
        panic!()
    };
    *id = "other".into();
    g.requests[4].dependencies = vec!["other".into()];
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[4] = old;
    e.validate_answer(&g, request, answer).unwrap();
    let old = g.requests[4].clone();
    let Selector::Answer { path, .. } = &mut g.requests[4].arguments[0].value else {
        panic!()
    };
    *path.last_mut().unwrap() = crate::observed::projection::ProjectionStep::Index(1);
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[4] = old;
    e.validate_answer(&g, request, answer).unwrap();
    let position = g.checked_answers.iter().position(|(i, _)| *i == 2).unwrap();
    let old = g.checked_answers[position].1.clone();
    g.checked_answers[position].1.outputs = r.answers[3].outputs.clone();
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[position].1 = old;
    e.validate_answer(&g, request, answer).unwrap();
    // 同値の別producerへ、全条件nodeをまとめて差し替えても元selectorは変えられない。
    assert_ne!(r.answers[2].outputs["value"], r.answers[3].outputs["value"]);
    assert_eq!(
        g.scalar(r.answers[2].outputs["value"]).unwrap(),
        g.scalar(r.answers[3].outputs["value"]).unwrap()
    );
    let nodes = g.nodes.clone();
    for n in &mut g.nodes {
        if matches!(n.rule, Rule::ProjectionCheck { .. }) {
            n.arguments[0] = r.answers[3].outputs["value"];
            if let Some(Payload::ProjectionCondition { root, .. }) = &mut n.payload {
                *root = r.answers[3].outputs["value"];
            }
        }
    }
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes = nodes;
    e.validate_answer(&g, request, answer).unwrap();
}
fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "empty=evaluate(Applications.acNestedNone)",
        "take=evaluate(Applications.abIdentity,x=$empty.value[0].some[0])",
        "later=evaluate(Applications.abSeed)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut named_call_quiet())
            .unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[4].status, Decision::Undetermined);
    assert!(
        normal.answers[4]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let span =
        match &normal.prepared.inputs().law().declarations["Applications.abIdentity"].signature {
            Signature::View { params, .. } => params[0].span,
            _ => panic!(),
        };
    let (limits, usage, expected) = reservations_private_stop_usage(if mode == 2 { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
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
        if request.id == "empty" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = if mode == 1 {
                    operation == "answer_projection_condition" && index == 3
                } else {
                    operation == "answer_projection_check_step" && index == 1
                };
                if at == span && ctx.request == 4 && target && (mode != 2 || ph.get()) {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 2 {
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
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    for (index, a) in stopped.answers.iter().enumerate().skip(4) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        if index == 4 && mode == 2 {
            for reason in &normal.answers[4].reasons {
                assert!(a.reasons.contains(reason));
            }
            assert_eq!(a.scope, normal.answers[4].scope);
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn projection_condition_actual_inapplicable_walk_stop_keeps_prior_values_refutation_missing_and_prefix()
 {
    stop(0)
}
#[test]
fn projection_condition_actual_construction_stop_keeps_checked_prefix_and_freezes() {
    stop(1)
}
#[test]
fn projection_condition_fresh_recheck_stop_keeps_verified_blocked_answer_and_original_reasons() {
    stop(2)
}
