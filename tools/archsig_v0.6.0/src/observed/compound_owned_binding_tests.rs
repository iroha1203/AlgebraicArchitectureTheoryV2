use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/compound_owned_binding.rs");
}
const BAD: &[&str] = &[
    "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "b=evaluate(Applications.cbOwner,a=@v/A)",
    "v=evaluate(Applications.cbMap,m=@v/m)",
    "other=evaluate(Applications.cbMap,m=@v/m)",
    "otherB=evaluate(Applications.cbOwner,a=@v/A)",
    "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
fn run(asks: &[&str]) -> ObservedEvaluation {
    run_with("known", asks)
}
fn run_with(mode: &str, asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input(mode, "r1"), asks, &mut quiet()).unwrap_or_else(
        |e| {
            panic!(
                "{:?}",
                e.wire().map(|w| match &w {
                    Json::Obj(m) => m.get("issues").cloned(),
                    _ => None,
                })
            )
        },
    );
    r
}
#[test]
fn compound_owned_conditions_recheck_three_inputs_all_typed_parts_and_roster_support() {
    let r = run(BAD);
    assert_eq!(r.status(), "partial");
    // 判断の再検査の代表: 3入力のowner条件の判断を反転すると核が拒否する。
    let condition = r
        .nodes
        .iter()
        .position(|n| matches!(&n.rule,Rule::ProjectionCheck{parameter,part:ProjectionCheckPart::Condition}if parameter=="x"))
        .unwrap();
    rejects_mutated_prefix(&r, condition, |ns| {
        ns[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
}
#[test]
fn compound_owned_condition_stop_preserves_prior_results_and_probe_freeze() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.seed)",
        "prior=check(Applications.prior)",
        "missing=evaluate(Applications.cbMissing,p=@v/p)",
        "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
        "b=evaluate(Applications.cbOwner,a=@v/A)",
        "v=evaluate(Applications.cbMap,m=@v/m)",
        "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)",
        "later=evaluate(Applications.seed)",
    ];
    let input = fixture::input("stop", "r1");
    let normal = run_with("stop", &asks);
    assert_eq!(normal.status(), "partial");
    let params = match &normal.prepared.inputs().law().declarations()["Applications.cbEq"].signature {
        Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    let span = params[2].span;
    let expected = crate::result::Signal::Term;
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
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "v" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = operation == "answer_projection_condition" && index == 5;
                if at == span && ctx.request == 6 && target {
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
    assert_eq!(&stopped.answers[..6], &normal.answers[..6]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for a in stopped.answers.iter().skip(6) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(actual), Json::Obj(wanted)) = (&reason.wire(), &expected.issue()) else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
