use super::*;
#[allow(dead_code)]
mod fixture {

    include!("../../../../tests/common/answer_projection_conditions.rs");
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &quiet(),
    )
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
fn projection_condition_undetermined_environment_rechecks_original_reasons_and_producer() {
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "other=evaluate(Applications.adMissing,p=@v/p)",
        "take=evaluate(Applications.acRoot,a=$missing.evaluation.environment.root)",
        "later=evaluate(Applications.abSeed)",
    ];
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &quiet()).unwrap();
    assert_eq!(r.status(), "partial");
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, request, answer).unwrap();
    }
    assert_eq!(r.answers[2].status, Decision::Undetermined);
    assert!(r.answers[2].outputs.get("value").is_none());
    assert!(r.answers[4].outputs.is_empty());
    for reason in &r.answers[2].reasons {
        assert!(r.answers[4].reasons.contains(reason));
    }
    reject_answer(&r, |a| {
        a.reasons.retain(|r| !matches!(r.kind, ReasonKind::Missing))
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap()
            .location = None;
    });
    reject_answer(&r, |a| {
        a.reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            .unwrap()
            .dependencies
            .clear();
    });
    reject_answer(&r, |a| a.scope.readings.clear());
    let original = r.answers[2].outputs["evaluation"];
    let foreign = r.answers[3].outputs["evaluation"];
    assert_ne!(original, foreign);
    let saved = g.nodes.clone();
    for n in &mut g.nodes {
        if matches!(n.rule, Rule::ProjectionCheck { .. }) {
            assert_eq!(n.arguments[0], original);
            n.arguments[0] = foreign;
            if let Some(Payload::ProjectionCondition { inputs, .. }) = &mut n.payload {
                assert_eq!(inputs.len(), 1);
                inputs[0] = foreign;
            }
        }
    }
    let request = &r.prepared.requests().requests()[4];
    for environment in [e, env(&r)] {
        assert!(matches!(
            environment.validate_answer(&g, request, &r.answers[4]),
            Err(ValidationFailure::Internal(_))
        ));
    }
    assert!(rebuild_for_origin_and_support_recheck(&r, &g.nodes).is_err());
    g.nodes = saved;
    let e = env(&r);
    e.validate_answer(&g, request, &r.answers[4]).unwrap();
    let position = g.checked_answers.iter().position(|(i, _)| *i == 2).unwrap();
    let saved = g.checked_answers[position].1.clone();
    g.checked_answers[position].1.outputs = r.answers[3].outputs.clone();
    assert!(matches!(
        e.validate_answer(&g, request, &r.answers[4]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).validate_answer(&g, request, &r.answers[4]),
        Err(ValidationFailure::Internal(_))
    ));
    g.checked_answers[position].1 = saved;
    e.validate_answer(&g, request, &r.answers[4]).unwrap();
}
#[test]
fn projection_condition_actual_inapplicable_walk_stop_keeps_prior_values_refutation_missing_and_prefix()
 {
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
        evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[4].status, Decision::Undetermined);
    assert!(
        normal.answers[4]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    let span =
        match &normal.prepared.inputs().law().declarations()["Applications.abIdentity"].signature {
            Signature::View { params, .. } => params[0].span,
            _ => panic!(),
        };
    let expected = archsig_input::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(archsig_input::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(fixture::input("stop", "r1"), &asks, &c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "empty" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                if at == span
                    && ctx.request == 4
                    && operation == "answer_projection_check_step"
                    && index == 1
                {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for a in stopped.answers.iter().skip(4) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
