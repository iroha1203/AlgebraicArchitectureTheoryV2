use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/unknown_owned_type.rs");
}
fn example(mode: &str, view: &str) -> ObservedEvaluation {
    let ask = if mode == "lexical" {
        format!("target=evaluate(MapCall.{view},h=@v/h)")
    } else {
        format!("target=evaluate(MapCall.{view},a=@v/A,b=@v/B)")
    };
    let r = evaluate_observed_bytes(
        fixture::input(mode, "r1"),
        &[
            "seed=evaluate(MapCall.seed)",
            "prior=check(MapCall.prior)",
            &ask,
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert!(matches!(r.status(), "complete" | "partial"));
    assert_eq!(r.answers[1].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
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
    let r = example("two", "typeEvery");
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
fn owned_type_original_missing_rejects_lost_fact_location_and_foreign_source() {
    let r = example("two", "typeEvery");
    let i = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 2
                && r.contexts[*i].case.is_none()
                && matches!(n.payload, Some(Payload::Evaluation { value: None, .. }))
                && n.reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Missing) && r.missing.len() == 2)
        })
        .map(|(i, _)| i)
        .unwrap();
    let foreign = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].request == 0 && matches!(n.payload, Some(Payload::Expression { .. }))
        })
        .map(|(i, _)| NodeRef(i))
        .unwrap();
    for kind in 0..3 {
        let mut bad = r.nodes[i].clone();
        let reason = bad
            .reasons
            .iter_mut()
            .find(|r| matches!(r.kind, ReasonKind::Missing))
            .unwrap();
        match kind {
            0 => {
                reason.missing.pop();
            }
            1 => reason.location = Some(Location::Law { span: (0, 1) }),
            _ => reason.dependencies = vec![foreign],
        };
        reject(&r, i, bad);
    }
}
#[test]
fn owned_type_owner_assignment_and_exhaustion_recheck_original_case_and_body() {
    let r = example("two", "typeEvery");
    let c = r.cases.iter().find(|c| c.caller.request == 2).unwrap();
    let i = c.values[0].0;
    let mut bad = r.nodes[i].clone();
    let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut bad.payload else {
        panic!()
    };
    *subject = if subject == "A" {
        "B".into()
    } else {
        "A".into()
    };
    reject(&r, i, bad);
    let i=r.nodes.iter().enumerate().find(|(i,n)|r.contexts[*i].case.is_some()&&matches!(&n.payload,Some(Payload::FiniteExhaustion{instances,..})if !instances.is_empty())).map(|(i,_)|i).unwrap();
    let mut bad = r.nodes[i].clone();
    let Some(Payload::FiniteExhaustion {
        checked, instances, ..
    }) = &mut bad.payload
    else {
        panic!()
    };
    *checked = 0;
    instances.clear();
    reject(&r, i, bad);
}
#[test]
fn owned_type_iteration_rejects_changed_map_binder_after_success() {
    let mut r = example("two", "typeEvery");
    let i=r.iterations.iter().position(|x|x.caller.request==2&&x.caller.case.is_some()&&matches!(&x.member,super::super::super::call::Member::SetElement(Scalar::Map{pairs,..})if !pairs.is_empty())).unwrap();
    let original = r.iterations[i].clone();
    let mut bad = original.clone();
    let super::super::super::call::Member::SetElement(Scalar::Map { pairs, .. }) = &mut bad.member
    else {
        panic!()
    };
    pairs.clear();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
        .unwrap();
    g.iterations[i] = bad.clone();
    assert!(matches!(
        e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2]),
        Err(ValidationFailure::Internal(_))
    ));
    g.iterations[i] = original.clone();
    e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
        .unwrap();
    drop(e);
    r.iterations[i] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    r.iterations[i] = original;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[test]
fn owned_type_call_owner_rejects_missing_extra_frame_arguments_without_panic() {
    let mut r = example("lexical", "typeCall");
    let i = r
        .frames
        .iter()
        .position(|f| f.caller.request == 2 && f.caller.case.is_some() && f.arguments.len() == 1)
        .unwrap();
    let original = r.frames[i].clone();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
        .unwrap();
    for extra in [false, true] {
        let mut bad = original.clone();
        if extra {
            bad.arguments.push(bad.arguments[0]);
        } else {
            bad.arguments.clear();
        }
        g.frames[i] = bad;
        assert!(matches!(
            e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2]),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2]),
            Err(ValidationFailure::Internal(_))
        ));
        g.frames[i] = original.clone();
        e.validate_answer(&g, &r.prepared.requests().requests()[2], &r.answers[2])
            .unwrap();
    }
    drop(e);
    r.frames[i].arguments.clear();
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    r.frames[i] = original;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
fn stop(stage: &'static str, kind: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(MapCall.seed)",
        "prior=check(MapCall.prior)",
        "target=evaluate(MapCall.typeEvery,a=@v/A,b=@v/A)",
        "later=evaluate(MapCall.seed)",
    ];
    let inputs = fixture::input("plain", "r1");
    let normal = evaluate_observed_bytes(inputs.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            super::super::super::control::Usage::default()
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, a| {
        e.validate_answer(g, q, a)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            super::super::super::data::observe_iterations(move |_, _, actual, _| {
                if actual == stage && !s.replace(true) {
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
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
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
    if stage != "owned_type_missing" {
        assert!(stopped.answers[2].reasons.iter().any(|r| {
            matches!(r.kind, ReasonKind::Missing)
                && r.missing
                    .iter()
                    .any(|f| f.subject == "p" && f.field.as_deref() == Some("MapCall.Item.owner"))
        }));
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    stopped.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_type_missing_cancel_keeps_verified_prefix_and_probe_freeze() {
    stop("owned_type_missing", 0)
}
#[test]
fn owned_type_missing_source_time_stop_keeps_original_missing_and_prefix() {
    stop("owned_type_missing_source", 1)
}
#[test]
fn owned_type_case_memory_stop_keeps_original_missing_and_prefix() {
    stop("owned_type_case", 2)
}
