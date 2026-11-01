use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_bindings.rs");
}
fn result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("r1"), asks, &mut quiet()).unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    r
}
#[test]
fn answer_binding_rechecks_original_values_types_support_scope_and_context() {
    let r = result(&[
        "used=evaluate(Applications.abUse,x=$copied.value)",
        "copied=evaluate(Applications.abCopy,x=$packed.evaluation.value)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    ]);
    // 束縛値の再検査の代表: 回答から束縛した値を書き換えると核が拒否する。
    let value = r.answers[2].outputs["value"].0;
    rejects_mutated_prefix(&r, value, |ns| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut ns[value].payload else {
            panic!()
        };
        items[0] = Scalar::Z(7.into());
    });
}
#[test]
fn answer_binding_actual_scan_stop_keeps_prior_value_refutation_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "current=evaluate(Applications.abKeep,x=$seed.value,p=@v/p)",
        "later=evaluate(Applications.abSeed)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::input_mode("stop", "r1"), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations()["Applications.abKeep"].signature
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
    let prepared = prepare_observed(fixture::input_mode("stop", "r1"), &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span && ctx.request == 2 && operation == "answer_binding_scan" {
                    let old = s.get();
                    s.set(old + 1);
                    if old == 1 {
                        a.set(true)
                    }
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 2);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for a in stopped.answers.iter().skip(2) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
