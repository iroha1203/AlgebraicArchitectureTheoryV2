use super::*;
#[allow(dead_code)]
mod fixture {

    include!("../../../../tests/common/unknown_owned_type.rs");
}
fn example() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input("two", "r1"),
        &[
            "seed=evaluate(MapCall.seed)",
            "prior=check(MapCall.prior)",
            "target=evaluate(MapCall.typeEvery,a=@v/A,b=@v/B)",
        ],
        &quiet(),
    )
    .unwrap();
    assert!(matches!(r.status(), "complete" | "partial"));
    assert_eq!(r.answers[1].status, Decision::Refuted);
    r
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &quiet(),
    )
    .unwrap()
}
fn reject(r: &ObservedEvaluation, i: usize, bad: Node) {
    let original = &r.nodes[i];
    assert_ne!(original, &bad);
    let mut g = rebuild_for_origin_and_support_recheck(r, &r.nodes[..i]).unwrap();
    g.active = r.contexts[i];
    let e = env(r);
    e.validate(&g, original).unwrap();
    assert!(matches!(
        e.validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(r).validate(&g, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&g, original).unwrap();
    let mut all = r.nodes.clone();
    all[i] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(r, &all),
        Err(ValidationFailure::Internal(_))
    ));
}
fn map_domain(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find(|(i,n)|r.contexts[*i].request==2&&r.contexts[*i].case.is_some()&&matches!(&n.payload,Some(Payload::Domain{ty:Type::Map(..),elements})if !elements.is_empty())).map(|(i,_)|i).unwrap()
}
#[test]
fn owned_type_domain_rejects_missing_duplicate_foreign_members_and_scope() {
    let r = example();
    let i = map_domain(&r);
    for duplicate in [false, true] {
        let mut bad = r.nodes[i].clone();
        let Some(Payload::Domain { elements, .. }) = &mut bad.payload else {
            panic!()
        };
        if duplicate {
            elements.push(elements[0]);
        } else {
            elements.clear();
        }
        reject(&r, i, bad);
    }
    for scope in [false, true] {
        let mut bad = r.nodes[i].clone();
        if scope {
            bad.scope.quantifiers.clear();
        } else {
            bad.support.clear();
        }
        reject(&r, i, bad);
    }
    let later=r.nodes.iter().enumerate().find(|(j,n)|*j>i&&matches!(&n.payload,Some(Payload::Domain{ty:Type::Map(..),elements})if elements.len()==1&&matches!(&r.nodes[elements[0].0].payload,Some(Payload::Scalar(Scalar::Map{pairs,..}))if !pairs.is_empty()))).map(|(j,_)|j).unwrap();
    let Some(Payload::Domain { elements, .. }) = &r.nodes[i].payload else {
        panic!()
    };
    let foreign = elements[0];
    let mut bad = r.nodes[later].clone();
    let Some(Payload::Domain { elements, .. }) = &mut bad.payload else {
        panic!()
    };
    let old = elements[0];
    assert_ne!(old, foreign);
    elements[0] = foreign;
    for edge in &mut bad.arguments {
        if *edge == old {
            *edge = foreign;
        }
    }
    reject(&r, later, bad);
}
#[test]
fn owned_type_missing_cancel_keeps_verified_prefix_and_probe_freeze() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(MapCall.seed)",
        "prior=check(MapCall.prior)",
        "target=evaluate(MapCall.typeEvery,a=@v/A,b=@v/A)",
        "later=evaluate(MapCall.seed)",
    ];
    let inputs = fixture::input("plain", "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let expected = archsig_input::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(archsig_input::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(inputs, &asks, &c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &c, |e, g, q, a| {
        e.validate_answer(g, q, a)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            super::super::super::data::observe_iterations(move |_, _, actual, _| {
                if actual == "owned_type_missing" && !s.replace(true) {
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    super::super::super::data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert!(stopped.nodes.len() < normal.nodes.len());
    macro_rules! prefix {
        ($field:ident) => {
            assert_eq!(
                stopped.$field.as_slice(),
                &normal.$field[..stopped.$field.len()]
            );
        };
    }
    prefix!(nodes);
    prefix!(contexts);
    prefix!(frames);
    prefix!(iterations);
    prefix!(instances);
    prefix!(cases);
    prefix!(universal_witnesses);
    assert_eq!(&stopped.answers[..2], &normal.answers[..2]);
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(v)if v==&expected))
        );
        if i == 3 {
            assert!(a.outputs.is_empty());
        }
        for output in a.outputs.values() {
            assert!(matches!(
                stopped.nodes[output.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ));
        }
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    stopped.wire();
}
