use super::*;
use crate::law::model::Signature;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/free_owner_answer_binding.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Reservations.seed)",
    "prior=check(Reservations.prior)",
    "missing=evaluate(Reservations.adMissing,p=@v/p)",
    "v=evaluate(Reservations.foUniversal,p=@v/p)",
    "other=evaluate(Reservations.foUniversal,p=@v/p)",
    "take=check(Reservations.foMixed,p=$v.value)",
    "later=evaluate(Reservations.seed)",
];

fn stop() {
    use std::{cell::Cell, rc::Rc};
    let asks = ASK;
    let input = fixture::input(false, false, "r1");
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    let declaration = &normal.prepared.inputs().law().declarations["Reservations.foMixed"];
    assert!(normal.answers[5].claim.is_some());
    assert!(!normal.answers[5].evidence.is_empty());
    let span = match &declaration.signature {
        Signature::Law { params, .. } => params[1].span,
        _ => panic!(),
    };
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
        if request.id == "other" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                if at == span && ctx.request == 5 && operation == "dependent_subject" && index == 3
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
        assert_eq!(reason.request, a.id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn free_owner_answer_actual_fiber_stop_keeps_values_refutation_missing_and_prefix() {
    stop()
}
