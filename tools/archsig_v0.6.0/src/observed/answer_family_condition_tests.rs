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
    r
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
fn answer_family_failed_conditions_recheck_free_partition_parts_and_original_reasons() {
    let r = result();
    // 条件の失敗した回答は、その失敗を理由に残す。
    assert!(
        r.answers[4]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    // 判断の再検査の代表: 条件の判断を反転すると核が拒否する。
    let condition = at(&r, ProjectionCheckPart::Condition);
    rejects_mutated_prefix(&r, condition, |ns| {
        ns[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
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
    let span = match &normal.prepared.inputs().law().declarations["Applications.afMany"].signature {
        Signature::Law { params, .. } => params[0].span,
        _ => panic!(),
    };
    let expected = StopReason::Cancelled(crate::result::Signal::Term);
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
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
}
#[test]
fn answer_family_condition_construction_stop_keeps_values_refutation_original_reasons_and_prefix() {
    stop(0)
}
