use super::*;
use crate::law::model::Signature;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/free_compound_answer_binding.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "missing=evaluate(Applications.cbMissing,p=@v/p)",
    "v=evaluate(Applications.fcMapAll,m=@v/m)",
    "other=evaluate(Applications.fcMapAll,m=@v/m)",
    "take=check(Applications.fcMap,x=$v.value)",
    "later=evaluate(Applications.seed)",
];

#[test]
fn free_compound_answer_map_domain_stop_keeps_values_refutation_missing_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = ASK;
    let input = fixture::input("stop", "r1");
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    let declaration = &normal.prepared.inputs().law().declarations()["Applications.fcMap"];
    assert!(normal.answers[5].claim.is_some());
    assert!(!normal.answers[5].evidence.is_empty());
    let span = match &declaration.signature {
        Signature::Law { params, .. } => params[2].span,
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
                if at == span
                    && ctx.request == 5
                    && operation == "owned_call_map_domain_roster"
                    && index == 3
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
fn free_compound_unknown_owner_recheck_preserves_completion_scope_and_rejects_finite_scope() {
    for (law, producer) in [
        ("fcList", "cbList,p=@v/p,q=@v/q"),
        ("fcDomain", "cbMap,m=@v/m"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let take = format!("take=check(Applications.{law},x=$v.value)");
        let other = format!("other=evaluate(Applications.{producer})");
        let r = evaluate_observed_bytes(
            fixture::input("unknown_owner", "r1"),
            &[&make, &other, &take, "later=evaluate(Applications.seed)"],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "complete", "{law}: {:?}", r.answers);
        assert_eq!(r.answers[0].status, Decision::Established);
        let original = &r.answers[2];
        assert!(original.scope.completions);
        assert_eq!(original.status, Decision::Established);
        assert!(original.outputs.contains_key("evaluation"));
        assert!(original.claim.is_some());
        assert!(!original.evidence.is_empty());
        assert!(
            original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.subject == "p"
                        && f.field.as_deref() == Some("Reservations.State.owner")
                        && f.atom.is_none()))
        );
        assert!(
            !original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        );
    }
}
