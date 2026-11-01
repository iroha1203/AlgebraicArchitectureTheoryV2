use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_dependencies.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.abSeed)",
    "prior=check(Applications.abPrior)",
    "raw=evaluate(Applications.adMissing,p=@v/p)",
    "opaque=evaluate(Applications.adOpaque)",
    "both=evaluate(Applications.adBoth,x=$raw.value,b=$opaque.evaluation.value)",
    "later=evaluate(Applications.abSeed)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), ASK, &mut quiet()).unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    r
}
#[test]
fn dependency_answer_rechecks_ids_status_outputs_scope_and_each_original_reason() {
    let r = result();
    // 依存先が未決の回答は未決のまま、依存の停止と元の欠測を理由に残す。
    let answer = &r.answers[4];
    assert_ne!(answer.status, Decision::Established);
    assert!(
        answer
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
    );
    assert!(
        answer
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    // 判断の再検査の代表: 回答の判断を確定へ書き換えると核が拒否する。
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap();
    let mut altered = answer.clone();
    altered.status = Decision::Established;
    assert!(matches!(
        e.validate_answer(&g, &r.prepared.requests().requests()[4], &altered),
        Err(ValidationFailure::Internal(_))
    ));
}
fn dependency_stop() {
    use std::{cell::Cell, rc::Rc};
    let normal = result();
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations()["Applications.adBoth"].signature
    else {
        panic!()
    };
    let span = params[0].span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
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
    let prepared = prepare_observed(fixture::input("stop", "r1"), ASK, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "opaque" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span && ctx.request == 4 && operation == "answer_binding_scan" {
                    let old = s.get();
                    s.set(old + 1);
                    if old == 1 {
                        a.set(true)
                    }
                }
            });
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 2);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for index in 4..stopped.answers.len() {
        let answer = &stopped.answers[index];
        assert_ne!(answer.status, Decision::Established);
        assert!(answer.outputs.is_empty());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, answer.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn dependency_answer_actual_scan_stop_keeps_prior_values_refutations_and_reasons() {
    dependency_stop()
}
