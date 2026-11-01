use super::*;
mod fixture {
    use crate as archsig;
    include!("../../tests/common/answer_projections.rs");
}
const ASK: &[&str] = &[
    "first=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    "other=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
    "foreign=evaluate(Applications.abIdentity,x=$other.evaluation.value[6][0])",
    "take=evaluate(Applications.abIdentity,x=$first.evaluation.value[6][0])",
    "nested=evaluate(Applications.apNested)",
    "deep=evaluate(Applications.abIdentity,x=$nested.value[0].some[1][1])",
    "universal=check(Applications.abUniversal,x=$first.value[0])",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("known", "r1"), ASK, &mut quiet()).unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    r
}
fn projection(r: &ObservedEvaluation) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 3 && matches!(n.rule, Rule::Projection(_))).then_some(i)
        })
        .unwrap()
}
#[test]
fn answer_projection_rechecks_original_root_path_value_type_scope_support_and_arity() {
    let r = result();
    // 射影値の照合の代表: 射影した値を書き換えると核が拒否する。
    let at = projection(&r);
    rejects_mutated_prefix(&r, at, |ns| {
        ns[at].payload = Some(Payload::Scalar(Scalar::Z(7.into())))
    });
}
#[test]
fn answer_projection_actual_path_stop_keeps_prior_values_refutation_missing_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Applications.abSeed)",
        "prior=check(Applications.abPrior)",
        "missing=evaluate(Applications.adMissing,p=@v/p)",
        "packed=evaluate(Applications.abPack,p=@v/p,m=@v/m)",
        "nested=evaluate(Applications.apNested)",
        "current=evaluate(Applications.abIdentity,x=$nested.value[0].some[1][1])",
        "later=evaluate(Applications.abSeed)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::input("stop", "r1"), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    let params =
        match &normal.prepared.inputs().law().declarations()["Applications.abIdentity"].signature {
            Signature::View { params, .. } => params,
            _ => panic!(),
        };
    let span = params[0].span;
    assert_eq!(normal.answers[5].status, Decision::Established);
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
    let prepared = prepare_observed(fixture::input("stop", "r1"), &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "nested" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at == span && ctx.request == 5 && operation == "answer_projection_step" {
                    let old = s.get();
                    s.set(old + 1);
                    if old == 2 {
                        a.set(true)
                    }
                }
            });
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 3);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(&stopped.answers[..5], &normal.answers[..5]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    for a in stopped.answers.iter().skip(5) {
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
