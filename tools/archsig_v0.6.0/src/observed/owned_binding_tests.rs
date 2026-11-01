use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/owned_binding.rs");
}
const BAD: &[&str] = &[
    "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "otherOwner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
    "child=evaluate(Reservations.obChild,p=@v/r)",
    "otherChild=evaluate(Reservations.obChild,p=@v/r)",
    "take=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)",
    "later=evaluate(Reservations.seed)",
];
fn run(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
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
fn owned_binding_conditions_recheck_all_inputs_typed_parts_scope_support_and_reasons() {
    let r = run(BAD);
    assert_eq!(r.status(), "partial");
    // 判断の再検査の代表: owner条件の判断を反転すると核が拒否する。
    let condition = r
        .nodes
        .iter()
        .position(|n| matches!(&n.rule,Rule::ProjectionCheck{parameter,part:ProjectionCheckPart::Condition}if parameter=="p"))
        .unwrap();
    rejects_mutated_prefix(&r, condition, |ns| {
        ns[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
}
fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let child = if mode == 1 {
        "child=evaluate(Reservations.obChild,p=@v/r)"
    } else {
        "child=evaluate(Reservations.obChild,p=@v/p)"
    };
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "missing=evaluate(Reservations.adMissing,p=@v/p)",
        "owner=evaluate(Reservations.adUniversalOwner,a=@v/A)",
        child,
        if mode == 2 {
            "take=check(Reservations.obEq,a=$owner.value,p=$child.value)"
        } else {
            "take=evaluate(Reservations.obUse,a=$owner.value,p=$child.value)"
        },
        "later=evaluate(Reservations.seed)",
    ];
    let input = fixture::input(false, false, "r1");
    let normal = run(&asks);
    assert_eq!(normal.status(), "partial");
    let declaration = if mode == 2 {
        "Reservations.obEq"
    } else {
        "Reservations.obUse"
    };
    let params = match &normal.prepared.inputs().law().declarations[declaration].signature {
        Signature::View { params, .. } | Signature::Law { params, .. } => params,
        _ => panic!(),
    };
    if mode == 2 {
        assert!(normal.answers[5].claim.is_some());
        assert!(!normal.answers[5].evidence.is_empty());
    }
    let span = params[1].span;
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
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "child" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = match mode {
                    0 => operation == "owned_binding_checked",
                    1 => operation == "answer_projection_condition" && index == 5,
                    _ => operation == "owned_binding_checked" && ph.get(),
                };
                if at == span && ctx.request == 5 && target {
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
    assert_eq!(&stopped.answers[..5], &normal.answers[..5]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for (i, a) in stopped.answers.iter().enumerate().skip(5) {
        if mode == 2 && i == 5 {
            let original = &normal.answers[5];
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
fn owned_binding_actual_membership_stop_preserves_prior_values_refutation_missing_and_prefix() {
    stop(0)
}

const COMPLETION_ASKS: &[&str] = &[
    "seed=evaluate(Reservations.adZero)",
    "prior=check(Reservations.prior)",
    "child=evaluate(Reservations.obChild,p=@v/p)",
    "take=check(Reservations.obEq,a=@v/A,p=$child.value)",
    "again=check(Reservations.adBool,a=@v/A,flag=$take.evaluation.value)",
    "later=evaluate(Reservations.adFlag)",
];
fn completion_run(mode: &str) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::completion_input(mode, "r1"),
        COMPLETION_ASKS,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error");
    r
}
#[test]
fn owned_binding_completion_visits_all_admissible_shared_assignments() {
    use std::{cell::RefCell, rc::Rc};
    for (mode, count) in [
        ("ambiguous", 3),
        ("single", 1),
        ("forceA", 1),
        ("forceB", 1),
    ] {
        let seen = Rc::new(RefCell::new(std::collections::BTreeSet::new()));
        let recorded = seen.clone();
        data::observe_iterations(move |_, context, operation, index| {
            if context.request == 3 && operation == "owned_binding_completion_case" {
                recorded.borrow_mut().insert(index);
            }
        });
        let r = completion_run(mode);
        data::clear_iteration_observer();
        assert_eq!(*seen.borrow(), (0..count).collect());
        assert_eq!(
            r.answers[3].status,
            if mode == "forceB" || mode == "ambiguous" {
                Decision::Undetermined
            } else {
                Decision::Established
            }
        );
        assert!(r.answers[3].scope.completions);
        let p = r.prepared.inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .find(|s| s.id == "p")
            .unwrap();
        assert!(matches!(
            p.fields
                .iter()
                .find(|f| f.name == "Reservations.State.owner")
                .unwrap()
                .slot,
            crate::archmap::Slot::Missing
        ));
    }
}
fn completion_stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let normal = completion_run("ambiguous");
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
    let prepared = prepare_observed(
        fixture::completion_input("ambiguous", "r1"),
        COMPLETION_ASKS,
        &mut c,
    )
    .unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "child" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                let target = if mode == 0 {
                    operation == "owned_binding_completion_enum"
                } else {
                    operation == "owned_binding_completion_case"
                };
                if ctx.request == 3 && target && index == 1 && !s.replace(true) {
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
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(&stopped.answers[..3], &normal.answers[..3]);
    for answer in &stopped.answers[3..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty());
        assert!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn owned_binding_completion_enumeration_cancel_preserves_prefix_and_independent_answers() {
    completion_stop(0)
}
