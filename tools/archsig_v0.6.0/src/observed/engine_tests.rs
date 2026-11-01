#[allow(dead_code)]
mod engine_fixture {
    include!("../../tests/common/engine.rs");
}
fn engine_private_inputs(missing: bool) -> InputSources {
    InputSources::from_bytes(
        vec![engine_fixture::DEFINITIONS.to_vec()],
        engine_fixture::law(true),
        engine_fixture::smaller(missing, Some("r1")),
    )
}
fn engine_private_result(asks: &[&str], missing: bool) -> ObservedEvaluation {
    let c = quiet();
    let p = prepare_observed(engine_private_inputs(missing), asks, &c).unwrap();
    evaluate_observed(p, &c).unwrap()
}
#[test]
fn engine_rechecks_all_z_coefficients_counterexample_assignment_and_original_sides() {
    let r = engine_private_result(&["a=check(Engine.preserves,c=@engine/subtract)"], false);
    assert_eq!(r.answers[0].status, Decision::Refuted);
    // 反例の再検査の代表: 反例の代入値を書き換えると核が拒否する。
    let Some(Payload::Counterexample { bindings, .. }) = r
        .nodes
        .iter()
        .map(|n| &n.payload)
        .find(|p| matches!(p, Some(Payload::Counterexample { .. })))
        .unwrap()
    else {
        panic!("counterexample")
    };
    let x = bindings.iter().find(|b| b.name == "x").unwrap().value.0;
    rejects_mutated_prefix(&r, x, |ns| {
        ns[x].payload = Some(Payload::Scalar(Scalar::Z(99.into())));
    });
}

// 停止の代表: 反例を確定した回答の直後に取消され、確定済みの反例と前の回答を残す。
// 反例の再検査は上のテストが代表するので、停止後の全体の再検査は重ねない。
#[test]
fn engine_answer_cancel_keeps_completed_engine_counterexample_and_prior_answer() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Engine.seed)",
        "prior=check(Engine.prior)",
        "current=check(Engine.preserves,c=@engine/subtract)",
        "later=evaluate(Engine.seed)",
    ];
    let normal = engine_private_result(&asks, false);
    assert_eq!(normal.answers[0].status, Decision::Established);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let c = Control::new(move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(engine_private_inputs(false), &asks, &c).unwrap();
    let stopped =
        evaluate_observed_with_validator(prepared, &c, |environment, g, request, answer| {
            environment.validate_answer(g, request, answer)?;
            if request.id == "current" {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        })
        .unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[2].status, Decision::Refuted);
    assert_eq!(
        format!("{:?}", stopped.answers[2]),
        format!("{:?}", normal.answers[2])
    );
    for a in &stopped.answers[3..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if s==&expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            panic!("reason")
        };
        let Json::Obj(ref wanted) = expected.issue() else {
            panic!("details")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
}
