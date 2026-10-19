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
#[test]
fn mixed_owner_answer_successful_rechecks_reject_request_registry_and_changed_source_restore_same_and_fresh()
 {
    let r = result();
    let cutoff = r.contexts.iter().position(|c| c.request == 8).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let request = &r.prepared.requests().requests()[7];
        let answer = &r.answers[7];
        e.validate_answer(&g, request, answer).unwrap();
        let i = source(&r);
        let saved = g.nodes[i].clone();
        g.nodes[i].scope.quantifiers.clear();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.nodes[i] = saved;
        e.validate_answer(&g, request, answer).unwrap();
        env(&r).validate_answer(&g, request, answer).unwrap();
        let saved = g.requests[7].clone();
        g.requests[7].arguments[0].value = Selector::Answer {
            id: "othera".into(),
            path: vec![crate::observed::projection::ProjectionStep::Field(
                "value".into(),
            )],
        };
        g.requests[7].dependencies = vec!["othera".into(), "v".into()];
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.requests[7] = saved;
        e.validate_answer(&g, request, answer).unwrap();
        env(&r).validate_answer(&g, request, answer).unwrap();
        let i = g.checked_answers.iter().position(|(i, _)| *i == 3).unwrap();
        let saved = g.checked_answers[i].1.clone();
        g.checked_answers[i].1.outputs = r.answers[4].outputs.clone();
        assert!(matches!(
            e.validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, request, answer),
            Err(ValidationFailure::Internal(_))
        ));
        g.checked_answers[i].1 = saved;
        e.validate_answer(&g, request, answer).unwrap();
        env(&r).validate_answer(&g, request, answer).unwrap();
    }
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
fn mixed_owner_answer_fixed_condition_cancel_keeps_prior_answers_prefix_and_probe_freeze() {
    stop(0)
}
#[test]
fn mixed_owner_answer_map_domain_budget_keeps_values_refutation_missing_and_prefix() {
    stop(1)
}
#[test]
fn mixed_owner_answer_fresh_recheck_stop_keeps_nonempty_claim_evidence_and_probe_freeze() {
    stop(2)
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
#[test]
fn mixed_fixed_condition_parts_reject_equal_foreign_owner_and_value_changes() {
    mixed_fixed_condition_parts_check(&[0, 1]);
}
#[test]
fn mixed_fixed_condition_parts_reject_support_and_scope_changes() {
    mixed_fixed_condition_parts_check(&[2, 3]);
}
#[test]
fn mixed_fixed_condition_direct_reason_changes_reject_same_and_fresh() {
    mixed_fixed_condition_parts_check(&[]);
}
fn mixed_fixed_condition_parts_check(kinds: &[usize]) {
    let asks: Vec<_> = ASK
        .iter()
        .map(|s| s.replace("cbUniversalOwner,a=@v/A", "cbUniversalOwner,a=@v/B"))
        .collect();
    let refs: Vec<_> = asks.iter().map(String::as_str).collect();
    let r = evaluate_observed_bytes(fixture::input("stop", "r1"), &refs, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "partial");
    let owner = r.answers[3].outputs["value"];
    let foreign_owner = r.answers[4].outputs["value"];
    let value = r.answers[5].outputs["value"];
    let foreign_value = r.answers[6].outputs["value"];
    assert_ne!(owner, foreign_owner);
    assert_ne!(value, foreign_value);
    assert_eq!(r.nodes[owner.0].payload, r.nodes[foreign_owner.0].payload);
    assert_eq!(r.nodes[value.0].payload, r.nodes[foreign_value.0].payload);
    let parts: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            (r.contexts[i].request == 7
                && matches!(&n.rule,Rule::ProjectionCheck{parameter,..}if parameter=="x"))
            .then_some(i)
        })
        .collect();
    assert_eq!(parts.len(), 5);
    for i in parts {
        assert_eq!(r.nodes[i].arguments[..2], [value, owner]);
        assert!(r.nodes[i].scope.quantifiers.len() >= 2);
        for &kind in kinds {
            completion_mutation(&r, i, |ns| match kind {
                0 => ns[i].arguments[0] = foreign_value,
                1 => ns[i].arguments[1] = foreign_owner,
                2 => ns[i].support.clear(),
                3 => ns[i].scope.quantifiers.reverse(),
                _ => unreachable!(),
            });
        }
    }
    if !kinds.is_empty() {
        return;
    }
    let cutoff = r.contexts.iter().position(|c| c.request == 8).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let req = &r.prepared.requests().requests()[7];
        let original = &r.answers[7];
        e.validate_answer(&g, req, original).unwrap();
        let mut wrong = original.clone();
        wrong
            .reasons
            .retain(|x| !matches!(&x.kind, ReasonKind::DependencyBlocked { .. }));
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

#[test]
fn mixed_direct_subject_condition_rechecks_operands_after_shape_acceptance_same_and_fresh() {
    let asks = [
        "seed=evaluate(Applications.seed)",
        "prior=check(Applications.prior)",
        "foreign=evaluate(Applications.cbOwner,a=@v/B)",
        "v=evaluate(Applications.mxAll,p=@v/p,q=@v/r)",
        "take=check(Applications.mxTuple,a=@v/B,x=$v.value)",
        "later=check(Applications.fcBool,x=$take.evaluation.value)",
        "last=evaluate(Applications.seed)",
    ];
    let r = evaluate_observed_bytes(
        fixture::input("known", "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    let all = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for (request, answer) in r.prepared.requests().requests().iter().zip(&r.answers) {
        env(&r).validate_answer(&all, request, answer).unwrap();
    }
    let parts: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            (r.contexts[i].request == 4
                && matches!(&n.rule,Rule::ProjectionCheck{parameter,..}if parameter=="x"))
            .then_some(i)
        })
        .collect();
    assert_eq!(parts.len(), 5);
    let value = r.answers[3].outputs["value"];
    let foreign = r.answers[2].outputs["value"];
    let owner = r.nodes[parts[0]].arguments[1];
    assert_ne!(owner, foreign);
    assert_eq!(r.nodes[owner.0].payload, r.nodes[foreign.0].payload);
    assert!(matches!(
        &r.nodes[owner.0].rule,
        Rule::Input {
            kind: "subject",
            ..
        }
    ));
    assert_eq!(r.contexts[owner.0].request, 4);
    assert_ne!(r.contexts[owner.0], r.contexts[foreign.0]);
    for &part in &parts {
        assert_eq!(r.nodes[part].arguments[..2], [value, owner]);
    }
    let Payload::ProjectionCondition { inputs, .. } =
        r.nodes[*parts.last().unwrap()].payload.as_ref().unwrap()
    else {
        panic!()
    };
    assert_eq!(inputs, &[value, owner]);
    let cutoff = r.contexts.iter().position(|c| c.request == 6).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let request = &r.prepared.requests().requests()[4];
        let answer = &r.answers[4];
        e.validate_answer(&g, request, answer).unwrap();
        let original_nodes = g.nodes.clone();
        let original_contexts = g.contexts.clone();
        let original_request = g.requests[4].clone();
        for kind in 0..5 {
            match kind {
                0 | 1 => {
                    for &part in &parts {
                        assert_eq!(g.nodes[part].arguments[1], owner);
                        if kind == 0 {
                            g.nodes[part].arguments.remove(1);
                        } else {
                            g.nodes[part].arguments[1] = foreign;
                        }
                        if let Some(Payload::ProjectionCondition { inputs, .. }) =
                            &mut g.nodes[part].payload
                        {
                            assert_eq!(inputs[1], owner);
                            if kind == 0 {
                                inputs.remove(1);
                            } else {
                                inputs[1] = foreign;
                            }
                        }
                    }
                    // 五部すべてを整合させても、shapeだけで元入力の資格を与えない。
                    for &part in &parts {
                        g.projection_check_shape(&g.nodes[part]).unwrap();
                    }
                }
                2 => {
                    g.contexts[owner.0] = r.contexts[foreign.0];
                    assert_ne!(g.contexts[owner.0], original_contexts[owner.0]);
                }
                3 => {
                    let arg = g.requests[4]
                        .arguments
                        .iter_mut()
                        .find(|a| a.name == "bind.a")
                        .unwrap();
                    arg.value = Selector::Subject {
                        snapshot: "v".into(),
                        subject: "A".into(),
                    };
                    assert_ne!(g.requests[4], original_request);
                }
                4 => {
                    assert!(!g.nodes[owner.0].support.is_empty());
                    g.nodes[owner.0].support.clear();
                }
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    e.validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "same kind {kind}"
            );
            assert!(
                matches!(
                    env(&r).validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh kind {kind}"
            );
            g.nodes = original_nodes.clone();
            g.contexts = original_contexts.clone();
            g.requests[4] = original_request.clone();
            e.validate_answer(&g, request, answer).unwrap();
            env(&r).validate_answer(&g, request, answer).unwrap();
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
#[test]
fn mixed_completion_seed_and_case_sources_reject_changed_scope_binding_and_membership_edges() {
    let r = completed_result();
    let seed = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 4
                && matches!(n.payload, Some(Payload::CompletionSeed { .. })))
            .then_some(i)
        })
        .unwrap();
    assert!(
        r.nodes[seed]
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "z")
    );
    completion_mutation(&r, seed, |ns| {
        ns[seed].scope.quantifiers.retain(|q| q.name != "z")
    });
    completion_mutation(&r, seed, |ns| {
        let Some(Payload::CompletionSeed { bindings, .. }) = &mut ns[seed].payload else {
            panic!()
        };
        let original = bindings.iter_mut().find(|b| b.name == "x").unwrap();
        assert_eq!(original.value, r.answers[2].outputs["value"]);
        original.value = r.answers[3].outputs["value"];
    });
    let checks: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            (r.contexts[i].request == 4
                && r.contexts[i].case.is_some()
                && matches!(&n.rule, Rule::OwnedBinding(p) if p == "x"))
            .then_some(i)
        })
        .collect();
    assert_eq!(checks.len(), 4);
    let own = checks[1];
    let foreign = checks[0];
    assert_ne!(r.contexts[own].case, r.contexts[foreign].case);
    assert_eq!(r.nodes[own], r.nodes[foreign]);
    completion_mutation(&r, own, |ns| {
        ns[own].arguments[0] = r.answers[3].outputs["value"]
    });
    completion_mutation(&r, own, |ns| ns[own].scope.quantifiers.clear());
    completion_mutation(&r, own, |ns| ns[own].support.clear());
    let source = r.nodes.iter().enumerate().find_map(|(i,n)| (r.contexts[i] == r.contexts[own] && matches!(&n.payload, Some(Payload::Expression { parameters, .. }) if !parameters.is_empty())).then_some(i)).unwrap();
    assert!(r.nodes[source].arguments.contains(&NodeRef(own)));
    completion_mutation(&r, source, |ns| {
        ns[source].arguments.retain(|r| *r != NodeRef(own))
    });
    completion_mutation(&r, source, |ns| {
        for r in &mut ns[source].arguments {
            if *r == NodeRef(own) {
                *r = NodeRef(foreign);
            }
        }
    });
}
#[test]
fn mixed_completion_cached_recheck_rejects_case_registry_and_context_mutations_and_restores() {
    let r = completed_result();
    let cutoff = r.contexts.iter().position(|c| c.request == 5).unwrap();
    let check = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 4
                && r.contexts[i].case.is_some()
                && matches!(n.rule, Rule::OwnedBinding(_)))
            .then_some(i)
        })
        .unwrap();
    let case = r.contexts[check].case.unwrap();
    let other = case + 1;
    assert_ne!(r.cases[case].member, r.cases[other].member);
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let q = &r.prepared.requests().requests()[4];
        let a = &r.answers[4];
        e.validate_answer(&g, q, a).unwrap();
        let original_contexts = g.contexts.clone();
        let original_cases = g.cases.clone();
        for kind in 0..3 {
            match kind {
                0 => g.contexts[check].case = Some(other),
                1 => g.cases[case].values = g.cases[other].values.clone(),
                2 => g.cases[case].caller.request = 3,
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    e.validate_answer(&g, q, a),
                    Err(ValidationFailure::Internal(_))
                ),
                "same {kind}"
            );
            assert!(
                matches!(
                    env(&r).validate_answer(&g, q, a),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh {kind}"
            );
            g.contexts = original_contexts.clone();
            g.cases = original_cases.clone();
            e.validate_answer(&g, q, a).unwrap();
            env(&r).validate_answer(&g, q, a).unwrap();
        }
    }
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
fn mixed_completion_enumeration_cancel_preserves_prior_answers_and_prefix() {
    completion_stop("completion_enum", 1, 0)
}
#[test]
fn mixed_completion_second_case_time_stop_preserves_first_case_and_prefix() {
    completion_stop("completion_case", 1, 1)
}
#[test]
fn mixed_completion_coverage_memory_stop_preserves_cases_without_whole_claim() {
    completion_stop("completion_coverage", 0, 2)
}

#[test]
fn mixed_completion_membership_cannot_use_another_requests_valid_case() {
    let mut asks = COMPLETION_ASKS[..5].to_vec();
    asks.push("again=check(Applications.mxTuple,a=@v/A,x=$v.value)");
    asks.push("last=evaluate(Applications.seed)");
    let r = evaluate_observed_bytes(
        fixture::input("ambiguous_free_owner", "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let check = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 5
                && r.contexts[i].case.is_some()
                && matches!(n.rule, Rule::OwnedBinding(_)))
            .then_some(i)
        })
        .unwrap();
    let foreign = r.cases.iter().position(|c| c.caller.request == 4).unwrap();
    let own = r.contexts[check].case.unwrap();
    assert_ne!(own, foreign);
    assert_eq!(
        r.nodes[r.cases[own].member.0].payload,
        r.nodes[r.cases[foreign].member.0].payload
    );
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = env(&r);
    e.recheck_node(&g, &g.nodes[check], check).unwrap();
    g.contexts[check].case = Some(foreign);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[check], check),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        env(&r).recheck_node(&g, &g.nodes[check], check),
        Err(ValidationFailure::Internal(_))
    ));
    g.contexts[check].case = Some(own);
    e.recheck_node(&g, &g.nodes[check], check).unwrap();
    env(&r).recheck_node(&g, &g.nodes[check], check).unwrap();
}

#[test]
fn mixed_completed_projection_refs_reject_equal_foreign_request_and_case_context_after_cache() {
    let asks = [
        "v=evaluate(Applications.mxWrapped,p=@v/p,q=@v/r)",
        "first=check(Applications.mxListLaw,a=@v/A,x=$v.value[1].some)",
        "take=check(Applications.mxListLaw,a=@v/A,x=$v.value[1].some)",
        "later=evaluate(Applications.seed)",
    ];
    let r = evaluate_observed_bytes(
        fixture::input("unknown_free_owner", "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    let binding = |request| {
        r.nodes
            .iter()
            .enumerate()
            .find_map(|(i, n)| {
                if r.contexts[i].request != request {
                    return None;
                }
                let Some(Payload::CompletionSeed { bindings, .. }) = &n.payload else {
                    return None;
                };
                Some((i, bindings.iter().find(|b| b.name == "x").unwrap().value))
            })
            .unwrap()
    };
    let (_, foreign) = binding(1);
    let (seed, original) = binding(2);
    assert_ne!(original, foreign);
    assert_eq!(r.nodes[original.0], r.nodes[foreign.0]);
    assert_eq!(r.contexts[original.0].request, 2);
    assert_eq!(r.contexts[original.0].case, None);
    let mut sources = Vec::new();
    for (i, n) in r.nodes.iter().enumerate() {
        if r.contexts[i].request != 2
            || r.contexts[i].case.is_none()
            || r.contexts[i].instance.is_some()
        {
            continue;
        }
        if let Some(Payload::Expression {
            parameters,
            bindings,
            ..
        }) = &n.payload
        {
            if !parameters.is_empty() {
                assert_eq!(
                    bindings.iter().find(|b| b.name == "x").unwrap().value,
                    original
                );
                sources.push(i);
            }
        }
    }
    assert!(!sources.is_empty());
    completion_mutation(&r, seed, |nodes| {
        let Some(Payload::CompletionSeed { bindings, .. }) = &mut nodes[seed].payload else {
            panic!()
        };
        bindings.iter_mut().find(|b| b.name == "x").unwrap().value = foreign;
        for edge in &mut nodes[seed].arguments {
            if *edge == original {
                *edge = foreign;
            }
        }
    });
    for source in sources {
        completion_mutation(&r, source, |nodes| {
            let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
                panic!()
            };
            bindings.iter_mut().find(|b| b.name == "x").unwrap().value = foreign;
            for edge in &mut nodes[source].arguments {
                if *edge == original {
                    *edge = foreign;
                }
            }
        });
    }
    let cutoff = r.contexts.iter().position(|c| c.request == 3).unwrap();
    let case = r.cases.iter().position(|c| c.caller.request == 2).unwrap();
    for nodes in [&r.nodes[..cutoff], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = env(&r);
        let q = &r.prepared.requests().requests()[2];
        let a = &r.answers[2];
        e.validate_answer(&g, q, a).unwrap();
        g.contexts[original.0].case = Some(case);
        assert!(matches!(
            e.validate_answer(&g, q, a),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            env(&r).validate_answer(&g, q, a),
            Err(ValidationFailure::Internal(_))
        ));
        g.contexts[original.0].case = None;
        e.validate_answer(&g, q, a).unwrap();
        env(&r).validate_answer(&g, q, a).unwrap();
    }
}
