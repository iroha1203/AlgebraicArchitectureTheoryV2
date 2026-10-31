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
    let r = evaluate_observed_bytes(fixture::input(mode, "r1"), asks, &mut named_call_quiet())
        .unwrap_or_else(|e| {
            panic!(
                "{:?}",
                e.wire().map(|w| match &w {
                    Json::Obj(m) => m.get("issues").cloned(),
                    _ => None,
                })
            )
        });
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
fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let producer = if mode == 0 {
        "v=evaluate(Applications.cbList,p=@v/p,q=@v/q)"
    } else {
        "v=evaluate(Applications.cbMap,m=@v/m)"
    };
    let b = if mode == 2 {
        "b=evaluate(Applications.cbOwner,a=@v/A)"
    } else {
        "b=evaluate(Applications.cbOwner,a=@v/B)"
    };
    let take = if mode == 0 {
        "take=check(Applications.cbFamily,a=$a.value,x=$v.value)"
    } else {
        "take=check(Applications.cbEq,a=$a.value,b=$b.value,x=$v.value)"
    };
    let asks = [
        "seed=evaluate(Applications.seed)",
        "prior=check(Applications.prior)",
        "missing=evaluate(Applications.cbMissing,p=@v/p)",
        "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
        b,
        producer,
        take,
        "later=evaluate(Applications.seed)",
    ];
    let input = fixture::input("stop", "r1");
    let normal = run_with("stop", &asks);
    assert_eq!(normal.status(), "partial");
    let declaration = if mode == 0 {
        "Applications.cbFamily"
    } else {
        "Applications.cbEq"
    };
    let params = match &normal.prepared.inputs().law().declarations[declaration].signature {
        Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    if mode == 3 {
        assert!(normal.answers[6].claim.is_some());
        assert!(!normal.answers[6].evidence.is_empty());
    }
    let span = params[if mode == 0 { 1 } else { 2 }].span;
    let (limits, usage, expected) = reservations_private_stop_usage(match mode {
        4 => 0,
        5 => 1,
        _ => mode.min(2),
    });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let later_member = Rc::new(Cell::new(false));
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
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "v" {
            let (a, ph, s, member) = (
                armed.clone(),
                phase.clone(),
                seen.clone(),
                later_member.clone(),
            );
            data::observe_iterations(move |at, ctx, operation, index| {
                if mode >= 4
                    && at == span
                    && ctx.request == 6
                    && s.get()
                    && operation == "owned_call_constraint"
                {
                    member.set(true);
                }
                let target = match mode {
                    0 => operation == "owned_call_constraint",
                    1 => operation == "owned_call_map_domain_roster" && index == 1,
                    2 => operation == "answer_projection_condition" && index == 5,
                    4 => operation == "owned_binding_type" && index == 1,
                    5 => operation == "owned_binding_owner" && index == 1,
                    _ => operation == "owned_binding_checked" && ph.get(),
                };
                if at == span && ctx.request == 6 && target {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "take" && mode == 3 {
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
    assert!(!later_member.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(&stopped.answers[..6], &normal.answers[..6]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for (i, a) in stopped.answers.iter().enumerate().skip(6) {
        if mode == 3 && i == 6 {
            let original = &normal.answers[6];
            assert!(a.claim.is_some());
            assert!(!a.evidence.is_empty());
            assert_eq!(a.status, original.status);
            assert_eq!(a.outputs, original.outputs);
            assert_eq!(a.claim, original.claim);
            assert_eq!(a.evidence, original.evidence);
            assert_eq!(a.scope, original.scope);
            for r in &original.reasons {
                assert!(a.reasons.contains(r));
            }
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(actual), Json::Obj(wanted)) = (&reason.wire(), &expected.wire()) else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn compound_owned_condition_stop_preserves_prior_results_and_probe_freeze() {
    stop(2)
}

