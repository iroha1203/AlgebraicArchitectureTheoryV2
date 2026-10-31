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
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial");
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (q, a) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, q, a).unwrap();
    }
    r
}
fn source(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==7 && r.contexts[i].instance.is_none() && matches!(&n.payload,Some(Payload::Expression{parameters,..})if !parameters.is_empty())).then_some(i)).unwrap()
}
fn fixed_domain(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==7 && matches!(&n.payload,Some(Payload::Domain{ty:Type::Map(..),elements})if elements.len()==1)).then_some(i)).unwrap()
}
#[test]
fn mixed_owner_answer_fibers_recheck_original_fixed_ref_owner_domains_rows_support_and_scope() {
    let r = result();
    let source = source(&r);
    let domain = fixed_domain(&r);
    let original = r.answers[5].outputs["value"];
    let foreign = r.answers[6].outputs["value"];
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0].payload, r.nodes[foreign.0].payload);
    let binding = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 7
                && matches!(&n.rule,Rule::OwnedBinding(name) if name == "x"))
            .then_some(i)
        })
        .unwrap();
    assert!(
        r.nodes[binding]
            .arguments
            .contains(&r.answers[3].outputs["value"])
    );
    completion_mutation(&r, binding, |ns| {
        let edge = ns[binding]
            .arguments
            .iter_mut()
            .find(|r0| **r0 == r.answers[3].outputs["value"])
            .unwrap();
        *edge = r.answers[4].outputs["value"];
    });
    completion_mutation(&r, binding, |ns| ns[binding].scope.quantifiers.reverse());
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { bindings, .. }) = &mut ns[source].payload else {
            panic!()
        };
        assert_eq!(bindings.len(), 2);
        let binding = bindings.iter_mut().find(|b| b.name == "x").unwrap();
        assert_eq!(binding.value, original);
        binding.value = foreign;
        for a in &mut ns[source].arguments {
            if *a == original {
                *a = foreign;
            }
        }
    });
    completion_mutation(&r, source, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source].payload else {
            panic!()
        };
        parameters.pop();
    });
    completion_mutation(&r, source, |ns| ns[source].scope.quantifiers.clear());
    completion_mutation(&r, domain, |ns| {
        let Some(Payload::Domain { elements, .. }) = &mut ns[domain].payload else {
            panic!()
        };
        elements.clear();
        ns[domain].arguments.pop();
    });
    completion_mutation(&r, domain, |ns| {
        ns[domain]
            .support
            .retain(|f| f.atom.as_deref() != Some("p-owner"))
    });
    completion_mutation(&r, domain, |ns| ns[domain].scope.quantifiers.clear());
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    let member = elements[0].0;
    completion_mutation(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut ns[member].payload else {
            panic!()
        };
        assert_eq!(pairs.len(), 2);
        pairs.pop();
    });
    let row = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 7
                && r.contexts[i].instance.is_some()
                && matches!(&n.payload, Some(Payload::LawInstance { .. })))
            .then_some(i)
        })
        .unwrap();
    completion_mutation(&r, row, |ns| ns[row].scope.quantifiers.clear());
}

fn stop(mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let asks = ASK;
    let input = fixture::input("stop", "r1");
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let declaration = &normal.prepared.inputs().law().declarations["Applications.fcMap"];
    assert!(normal.answers[7].claim.is_some());
    assert!(!normal.answers[7].evidence.is_empty());
    let span = match &declaration.signature {
        Signature::Law { params, .. } => params[2].span,
        _ => panic!(),
    };
    let (limits, usage, expected) = reservations_private_stop_usage(mode);
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
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
            Default::default()
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "other" {
            let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, index| {
                let target = match mode {
                    0 => operation == "owned_binding_checked" && index == 0,
                    1 => operation == "owned_call_map_domain_roster" && index == 3,
                    _ => operation == "owned_call_map_domain" && index == 0,
                };
                if at == span && ctx.request == 7 && target && (mode != 2 || ph.get()) {
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
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(&stopped.answers[..7], &normal.answers[..7]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(
        stopped.answers[2]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    for (index, a) in stopped.answers.iter().enumerate().skip(7) {
        if mode == 2 && index == 7 {
            let original = &normal.answers[7];
            assert!(a.claim.is_some());
            assert!(!a.evidence.is_empty());
            assert_eq!(a.status, original.status);
            assert_eq!(a.outputs, original.outputs);
            assert_eq!(a.claim, original.claim);
            assert_eq!(a.evidence, original.evidence);
            assert_eq!(a.scope, original.scope);
            for reason in &original.reasons {
                assert!(a.reasons.contains(reason));
            }
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        assert_eq!(reason.request, a.id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}

#[test]
fn mixed_owner_answer_map_domain_budget_keeps_values_refutation_missing_and_prefix() {
    stop(1)
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
            &mut named_call_quiet(),
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
        let cutoff = r.contexts.iter().position(|c| c.request == 2).unwrap();
        for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
            let g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
            let e = env(&r);
            let req = &r.prepared.requests().requests()[1];
            e.validate_answer(&g, req, original).unwrap();
            let mut wrong = original.clone();
            wrong.scope.completions = false;
            assert_ne!(&wrong, original);
            assert!(matches!(
                e.validate_answer(&g, req, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
            assert!(matches!(
                env(&r).validate_answer(&g, req, &wrong),
                Err(ValidationFailure::Internal(_))
            ));
            e.validate_answer(&g, req, original).unwrap();
            env(&r).validate_answer(&g, req, original).unwrap();
        }
    }
}

const COMPLETION_ASKS: &[&str] = &[
    "seed=evaluate(Applications.seed)",
    "prior=check(Applications.prior)",
    "v=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
    "other=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
    "take=check(Applications.mxTuple,a=@v/A,x=$v.value)",
    "later=evaluate(Applications.seed)",
];
fn completed_result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input("ambiguous_free_owner", "r1"),
        COMPLETION_ASKS,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    for (q, a) in r.prepared.requests().requests().iter().zip(&r.answers) {
        e.validate_answer(&g, q, a).unwrap();
    }
    r
}
fn completion_stop(phase: &'static str, index: usize, mode: usize) {
    use std::{cell::Cell, rc::Rc};
    let normal = completed_result();
    let target = normal.prepared.inputs().law().declarations["Applications.mxTuple"].span;
    let (limits, usage, expected) = reservations_private_stop_usage(mode);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Default::default()
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
        if q.id == "other" {
            let (arm, hit) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, context, operation, at| {
                if span == target
                    && context.request == 4
                    && context.case.is_none()
                    && operation == phase
                    && at == index
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
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(&stopped.answers[..4], &normal.answers[..4]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert_eq!(stopped.nodes, &normal.nodes[..stopped.nodes.len()]);
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    assert_eq!(stopped.cases, &normal.cases[..stopped.cases.len()]);
    assert_eq!(
        stopped.instances,
        &normal.instances[..stopped.instances.len()]
    );
    for a in &stopped.answers[4..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s == expected))
        );
    }
    assert!(
        stopped.answers[4]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn mixed_completion_coverage_memory_stop_preserves_cases_without_whole_claim() {
    completion_stop("completion_coverage", 0, 2)
}

