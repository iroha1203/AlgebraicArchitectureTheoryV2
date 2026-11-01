use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_containers.rs");
}
fn stop(stage: &'static str) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "target=check(Reservations.ocSomeGood,a=@v/A,p=@v/p)",
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = fixture::input(true, "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    let expected = StopReason::Cancelled(crate::result::Signal::Term);
    let armed = Rc::new(Cell::new(false));
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
    let prepared = prepare_observed(inputs, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            super::super::super::data::observe_iterations(move |_, _, actual, _| {
                if actual == stage && !s.replace(true) {
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    super::super::super::data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert!(stopped.nodes.len() < normal.nodes.len());
    assert_eq!(
        stopped.frames.as_slice(),
        &normal.frames[..stopped.frames.len()]
    );
    assert_eq!(
        stopped.iterations.as_slice(),
        &normal.iterations[..stopped.iterations.len()]
    );
    assert_eq!(
        stopped.instances.as_slice(),
        &normal.instances[..stopped.instances.len()]
    );
    assert_eq!(
        stopped.cases.as_slice(),
        &normal.cases[..stopped.cases.len()]
    );
    assert_eq!(
        stopped.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..stopped.universal_witnesses.len()]
    );
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    for (i, answer) in stopped.answers.iter().enumerate().skip(2) {
        assert_eq!(answer.status, Decision::Undetermined);
        if stage == "owned_call_missing_source" && i == 2 {
            // 全補完の収集前には、既に検査済みの元body評価だけを保持する。
            assert_eq!(answer.outputs.len(), 1);
            let evaluation = answer.outputs["evaluation"];
            assert!(matches!(
                stopped.nodes[evaluation.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
            assert_eq!(stopped.nodes[evaluation.0], normal.nodes[evaluation.0]);
        } else {
            assert!(answer.outputs.is_empty());
        }
        assert!(answer.claim.is_none() && answer.evidence.is_empty());
        assert!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason)if reason==&expected))
        );
    }
    if stage != "owned_call_missing" {
        assert!(
            stopped.answers[2]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.subject == "p"
                        && f.field.as_deref() == Some("Reservations.State.owner")))
        );
    }
    // 停止後の全体の再検査は所有callの停止(owned_partial_call_tests)が代表する。
    stopped.wire();
}
#[test]
fn owned_call_missing_source_stop_keeps_verified_prefix_and_probe_freeze() {
    stop("owned_call_missing_source")
}

#[test]
fn owned_call_skipped_branch_rejects_changed_selector_and_lost_missing() {
    let r = evaluate_observed_bytes(
        fixture::missing_reference_input(),
        &["x=evaluate(Reservations.pcSkipIf,a=@v/B,e=@v/e)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(r.answers[0].status, Decision::Established);
    assert!(
        r.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert!(
        !r.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
}
