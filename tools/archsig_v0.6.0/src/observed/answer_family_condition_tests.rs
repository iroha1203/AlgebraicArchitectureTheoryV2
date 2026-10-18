use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_family_conditions.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.abSeed)",
    "prior=check(Applications.abPrior)",
    "empty=evaluate(Applications.apEmpty)",
    "other=evaluate(Applications.apEmpty)",
    "take=check(Applications.afFinite,x=$empty.value[0])",
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
fn answer_family_failed_conditions_recheck_free_partition_parts_and_original_reasons() {
    let r = result();
    assert_eq!(r.prepared.requests().requests()[4].arguments.len(), 1);
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
        completion_mutation(&r, i, |ns| ns[i].ty = NodeType::Value(Type::Z));
        completion_mutation(&r, i, |ns| ns[i].scope.readings.clear());
        completion_mutation(&r, i, |ns| {
            ns[i].support.push(Fact {
                snapshot: "v".into(),
                subject: "p".into(),
                field: None,
                atom: None,
            });
        });
        completion_mutation(&r, i, |ns| {
            let Rule::ProjectionCheck { parameter, .. } = &mut ns[i].rule else {
                panic!()
            };
            *parameter = "b".into();
        });
    }
    let actual = at(&r, ProjectionCheckPart::Actual);
    completion_mutation(&r, actual, |ns| {
        ns[actual].payload = Some(Payload::Scalar(Scalar::Bool(true)))
    });
    let proof = at(&r, ProjectionCheckPart::Evidence);
    completion_mutation(&r, proof, |ns| {
        let Some(Payload::ProjectionCounterexample { left, right, .. }) = &mut ns[proof].payload
        else {
            panic!()
        };
        std::mem::swap(left, right);
    });
    let condition = at(&r, ProjectionCheckPart::Condition);
    completion_mutation(&r, condition, |ns| ns[condition].evidence.clear());
    completion_mutation(&r, condition, |ns| {
        ns[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
    reject_answer(&r, |a| a.status = Decision::Refuted);
    reject_answer(&r, |a| a.claim = r.answers[1].claim);
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
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap()
            .dependencies
            .clear()
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap()
            .location = None
    });
}
#[test]
fn answer_family_same_environment_rejects_request_partition_and_coherent_condition_transfers() {
    let r = result();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    let request = &r.prepared.requests().requests()[4];
    let answer = &r.answers[4];
    e.validate_answer(&g, request, answer).unwrap();
    let saved = g.requests[4].clone();
    for variant in 0..3 {
        g.requests[4] = saved.clone();
        match variant {
            0 => {
                g.requests[4].arguments.clear();
                g.requests[4].dependencies.clear();
            }
            1 => g.requests[4].arguments[0].name = "bind.b".into(),
            _ => {
                let Selector::Answer { id, .. } = &mut g.requests[4].arguments[0].value else {
                    panic!()
                };
                *id = "other".into();
                g.requests[4].dependencies = vec!["other".into()];
            }
        }
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.requests[4] = saved.clone();
        e.validate_answer(&g, request, answer).unwrap();
    }
    let root = r.answers[2].outputs["value"];
    let foreign = r.answers[3].outputs["value"];
    assert_ne!(root, foreign);
    assert_eq!(g.scalar(root).unwrap(), g.scalar(foreign).unwrap());
    let nodes = g.nodes.clone();
    for n in &mut g.nodes {
        if matches!(n.rule, Rule::ProjectionCheck { .. }) {
            n.arguments[0] = foreign;
            if let Some(Payload::ProjectionCondition { root, .. }) = &mut n.payload {
                *root = foreign;
            }
        }
    }
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes = nodes;
    e.validate_answer(&g, request, answer).unwrap();
    let position = g.checked_answers.iter().position(|(i, _)| *i == 2).unwrap();
    let saved = g.checked_answers[position].1.clone();
    g.checked_answers[position].1.outputs = r.answers[3].outputs.clone();
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[position].1 = saved;
    e.validate_answer(&g, request, answer).unwrap();
}
#[test]
fn answer_family_fixed_source_rechecks_original_binding_free_axis_scope_and_cached_success() {
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "other=evaluate(Applications.afTruth)",
        "zero=evaluate(Applications.mcMissingZero,p=@v/p)",
        "universal=check(Applications.abUniversal,x=$seed.value)",
        "take=check(Applications.afBool,c=$universal.evaluation.value)",
        "later=evaluate(Applications.abSeed)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, request, answer).unwrap();
    }
    let source=r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==4&&r.contexts[i].instance.is_none()&&matches!(&n.payload,Some(Payload::Expression{parameters,..})if parameters==&vec![("b".into(),Type::Bool)])).then_some(i)).unwrap();
    let Some(Payload::Evaluation {
        value: Some(root), ..
    }) = &g.get(r.answers[3].outputs["evaluation"]).unwrap().payload
    else {
        panic!()
    };
    let root = *root;
    let foreign = r.answers[1].outputs["value"];
    assert_ne!(root, foreign);
    assert_eq!(g.scalar(root).unwrap(), g.scalar(foreign).unwrap());
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source].payload else {
            panic!()
        };
        parameters.clear();
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        bindings[0].name = "b".into();
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        bindings[0].value = foreign;
        for a in &mut ns[source].arguments {
            if *a == root {
                *a = foreign;
            }
        }
    });
    completion_mutation(&r, source, |ns| ns[source].scope.quantifiers.clear());
    completion_mutation(&r, source, |ns| ns[source].scope.assignments = false);
    let request = &r.prepared.requests().requests()[4];
    let answer = &r.answers[4];
    let saved = g.nodes[source].clone();
    g.nodes[source].scope.quantifiers.clear();
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[source] = saved;
    e.validate_answer(&g, request, answer).unwrap();
    let saved = g.requests[4].clone();
    g.requests[4].arguments[0].name = "bind.b".into();
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[4] = saved;
    e.validate_answer(&g, request, answer).unwrap();
    let position = g.checked_answers.iter().position(|(i, _)| *i == 3).unwrap();
    let saved = g.checked_answers[position].1.clone();
    g.checked_answers[position].1.outputs = r.answers[1].outputs.clone();
    assert!(matches!(
        e.validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).validate_answer(&g, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[position].1 = saved;
    e.validate_answer(&g, request, answer).unwrap();
}

fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "empty=evaluate(Applications.apEmpty)",
        "opaque=evaluate(Applications.adOpaque)",
        "take=check(Applications.afMany,a=$missing.evaluation.environment.root,x=$empty.value[0],y=$missing.value,c=$opaque.value)",
        "later=evaluate(Applications.abBool,x=$take.evaluation.value)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut named_call_quiet())
            .unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[5].status, Decision::Undetermined);
    assert!(
        normal.answers[5]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let span = match &normal.prepared.inputs().law().declarations["Applications.afMany"].signature {
        Signature::Law { params, .. } => params[0].span,
        _ => panic!(),
    };
    let (limits, usage, expected) = reservations_private_stop_usage(if mode == 1 { 2 } else { 0 });
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
        if request.id == "opaque" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = if mode == 0 {
                    operation == "answer_projection_condition" && index == 3
                } else {
                    operation == "answer_binding_scan" && index == 2
                };
                if at == span && ctx.request == 5 && target && (mode == 0 || ph.get()) {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 1 {
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
    assert_eq!(&stopped.answers[..5], &normal.answers[..5]);
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
    for (index, a) in stopped.answers.iter().enumerate().skip(5) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        if index == 5 && mode == 1 {
            for reason in &normal.answers[5].reasons {
                assert!(a.reasons.contains(reason));
            }
            assert_eq!(a.scope, normal.answers[5].scope);
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
fn answer_family_condition_construction_stop_keeps_values_refutation_original_reasons_and_prefix() {
    stop(0)
}
#[test]
fn answer_family_fresh_recheck_stop_preserves_verified_blocked_answer_scope_and_probe_freeze() {
    stop(1)
}
