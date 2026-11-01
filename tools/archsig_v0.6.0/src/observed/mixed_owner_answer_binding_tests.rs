use super::*;
use crate::law::model::Signature;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/mixed_owner_answer_binding.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "missing=evaluate(Applications.cbMissing,p=@v/p)",
    "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "othera=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "v=evaluate(Applications.fcMapAll,m=@v/m)",
    "other=evaluate(Applications.fcMapAll,m=@v/m)",
    "take=check(Applications.fcMap,a=$a.value,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
fn fixed_domain(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==7 && matches!(&n.payload,Some(Payload::Domain{ty:Type::Map(..),elements})if elements.len()==1)).then_some(i)).unwrap()
}
#[test]
fn mixed_owner_answer_fibers_recheck_original_fixed_ref_owner_domains_rows_support_and_scope() {
    // 完了しない問いは未決のまま、評価中の自己検査を通った回答だけを返す。
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), ASK, &mut quiet()).unwrap();
    assert_eq!(r.status(), "partial");
    assert!(r.answers[7].claim.is_some());
    assert!(!r.answers[7].evidence.is_empty());
    let original = r.answers[5].outputs["value"];
    let foreign = r.answers[6].outputs["value"];
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0].payload, r.nodes[foreign.0].payload);
    // 候補域の全域性の代表: 固定ownerの候補域から要素を落とすと核が拒否する。
    let domain = fixed_domain(&r);
    let mut prefix = r.nodes[..=domain].to_vec();
    let Some(Payload::Domain { elements, .. }) = &mut prefix[domain].payload else {
        panic!()
    };
    elements.clear();
    prefix[domain].arguments.pop();
    rejects_named_prefix(&r, &prefix);
}

// 停止の代表: 固定ownerの写像域の候補列挙で取消が届く。同じ問いの重複は外す。
const STOP_ASK: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "missing=evaluate(Applications.cbMissing,p=@v/p)",
    "a=evaluate(Applications.cbUniversalOwner,a=@v/A)",
    "v=evaluate(Applications.fcMapAll,m=@v/m)",
    "take=check(Applications.fcMap,a=$a.value,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
#[test]
fn mixed_owner_answer_map_domain_stop_keeps_values_refutation_missing_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input("stop", "r1");
    let normal = evaluate_observed_bytes(input.clone(), STOP_ASK, &mut quiet()).unwrap();
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
    let prepared = prepare_observed(input, STOP_ASK, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "v" {
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
    for a in &stopped.answers[5..] {
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
}

#[test]
fn mixed_unknown_free_owner_rechecks_completion_scope_with_same_and_fresh_environments() {
    for (law, producer, fixed, mode) in [
        (
            "mxTuple",
            "mxAll,p=@v/p,q=@v/r",
            "a=@v/A",
            "unknown_free_owner",
        ),
        ("fcMap", "cbMap,m=@v/m", "b=@v/B", "unknown_owner"),
    ] {
        let make = format!("v=evaluate(Applications.{producer})");
        let take = format!("take=check(Applications.{law},{fixed},x=$v.value)");
        let r = evaluate_observed_bytes(
            fixture::input(mode, "r1"),
            &[&make, &take, "later=evaluate(Applications.seed)"],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(r.status(), "complete", "{:?}", r.issues);
        assert_eq!(r.answers[0].status, Decision::Established);
        let original = &r.answers[1];
        assert!(original.scope.completions);
        assert_eq!(original.status, Decision::Established);
        assert!(original.outputs.contains_key("evaluation"));
        assert!(original.claim.is_some());
        assert!(!original.evidence.is_empty());
        assert!(
            original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing))
        );
        assert!(
            !original
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        );
    }
}

const COMPLETION_ASKS: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "v=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
    "take=check(Applications.mxTuple,a=@v/A,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
fn completed_result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input("ambiguous_free_owner", "r1"),
        COMPLETION_ASKS,
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    r
}
#[test]
fn mixed_completion_coverage_stop_preserves_cases_without_whole_claim() {
    use std::{cell::Cell, rc::Rc};
    let normal = completed_result();
    let target = normal.prepared.inputs().law().declarations()["Applications.mxTuple"].span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(
        fixture::input("ambiguous_free_owner", "r1"),
        COMPLETION_ASKS,
        &mut c,
    )
    .unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, a| {
        e.validate_answer(g, q, a)?;
        if q.id == "v" {
            let (arm, hit) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, context, operation, at| {
                if span == target
                    && context.request == 3
                    && context.case.is_none()
                    && operation == "completion_coverage"
                    && at == 0
                {
                    assert!(!hit.replace(true));
                    arm.set(true);
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
    assert_eq!(&stopped.answers[..3], &normal.answers[..3]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for a in &stopped.answers[3..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s == expected))
        );
    }
    assert!(
        stopped.answers[3]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
}
