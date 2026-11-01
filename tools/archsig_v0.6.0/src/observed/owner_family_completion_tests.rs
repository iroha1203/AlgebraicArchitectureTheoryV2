use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/owner_completions.rs");
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn example(stable: bool) -> ObservedEvaluation {
    let name = if stable { "total" } else { "pair" };
    let asks = [
        format!("first=evaluate(RefCalc.{name},a=@v/A,b=@v/B)"),
        format!("target=evaluate(RefCalc.{name},a=@v/A,b=@v/B)"),
        "later=evaluate(RefCalc.seed)".into(),
    ];
    let asks: Vec<_> = asks.iter().map(String::as_str).collect();
    let r = evaluate_observed_bytes(
        fixture::input(2, false, false, false),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
fn mutate(kinds: &[usize], stable: bool) {
    let r = example(stable);
    let root = r.answers[1].outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let seed = r.nodes[domain].arguments[0].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    assert_eq!(elements.len(), 4);
    let first = elements[0].0;
    let Some(Payload::CompletionSeed {
        fields, sources, ..
    }) = &r.nodes[seed].payload
    else {
        panic!()
    };
    assert_eq!(fields.len(), 2);
    assert_ne!(fields[0], fields[1]);
    assert_eq!(
        sources[0], sources[1],
        "one original Family reads both owner slots"
    );
    assert_eq!(
        fields
            .iter()
            .map(|f| f.subject.as_str())
            .collect::<Vec<_>>(),
        vec!["item", "other"]
    );
    let foreign_domain = r.nodes[r.answers[0].outputs["evaluation"].0].arguments[1];
    let foreign_seed = r.nodes[foreign_domain.0].arguments[0];
    let Some(Payload::CompletionSeed {
        sources: foreign_sources,
        ..
    }) = &r.nodes[foreign_seed.0].payload
    else {
        panic!()
    };
    let foreign_source = foreign_sources[0];
    assert_ne!(foreign_source, sources[0]);
    let proof = r.answers[1].evidence[0].0;
    let case = r
        .cases
        .iter()
        .position(|c| {
            c.domain == NodeRef(domain)
                && r.nodes[c.values[0].0].payload != r.nodes[c.values[1].0].payload
        })
        .unwrap();
    let projection = r.cases[case].values[0].0;
    let set=r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==1&&r.contexts[i].case.is_some()&&matches!(&n.rule,Rule::Input{kind:"law",..})&&matches!(&n.payload,Some(Payload::Scalar(Scalar::Set{items,..}))if !items.is_empty())).then_some(i)).unwrap();
    let original_missing = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == 1
                && r.contexts[i].case.is_none()
                && matches!(n.payload, Some(Payload::Evaluation { .. }))
                && n.reasons.iter().any(|reason| {
                    matches!(reason.kind, ReasonKind::Missing) && !reason.missing.is_empty()
                }))
            .then_some(i)
        })
        .unwrap();
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut g = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = environment(&r);
        e.validate_answer(&g, request, answer).unwrap();
        let original_nodes = g.nodes.clone();
        let original_cases = g.cases.clone();
        let original_request = g.requests[1].clone();
        for &kind in kinds {
            match kind {
                0 => {
                    let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements.pop();
                    g.nodes[domain].arguments.pop();
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut g.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements[1] = elements[0];
                    g.nodes[domain].arguments[2] = NodeRef(first);
                }
                2 => {
                    let Some(Payload::CompletionSeed { fields, .. }) = &mut g.nodes[seed].payload
                    else {
                        panic!()
                    };
                    fields.swap(0, 1);
                }
                3 => {
                    let Some(Payload::CompletionSeed { sources, .. }) = &mut g.nodes[seed].payload
                    else {
                        panic!()
                    };
                    sources[0] = foreign_source;
                }
                4 => {
                    assert!(!g.nodes[domain].support.is_empty());
                    g.nodes[domain].support.clear();
                }
                5 => g.nodes[domain].scope.snapshots.clear(),
                6 => {
                    assert_ne!(
                        g.nodes[g.cases[case].values[0].0].payload,
                        g.nodes[g.cases[case].values[1].0].payload
                    );
                    g.cases[case].values.swap(0, 1);
                }
                7 => {
                    assert!(!g.requests[1].defaults.is_empty());
                    g.requests[1].defaults.clear();
                }
                8 => {
                    let Some(Payload::CompletionPair { fields, .. }) = &mut g.nodes[proof].payload
                    else {
                        panic!()
                    };
                    fields.swap(0, 1);
                }
                9 => {
                    let Some(Payload::Scalar(Scalar::Tuple(values))) = &mut g.nodes[first].payload
                    else {
                        panic!()
                    };
                    values[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "ghost".into(),
                        entity: "Refs.Root".into(),
                    };
                }
                10 => g.nodes[root].arguments[1] = foreign_domain,
                11 => {
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut g.nodes[proof].payload
                    else {
                        panic!()
                    };
                    *checked += 1;
                }
                12 => {
                    let Some(Payload::Scalar(Scalar::Tuple(values))) = &mut g.nodes[first].payload
                    else {
                        panic!()
                    };
                    assert_eq!(values[0].ty(), Type::Ref("Refs.Root".into()));
                    values[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "item".into(),
                        entity: "Refs.Sample".into(),
                    };
                    g.nodes[first].ty = NodeType::Value(Type::Tuple(vec![
                        Type::Ref("Refs.Sample".into()),
                        Type::Ref("Refs.Root".into()),
                    ]));
                }
                13 => {
                    let Some(Payload::Domain { ty, .. }) = &mut g.nodes[domain].payload else {
                        panic!()
                    };
                    assert_eq!(
                        *ty,
                        Type::Tuple(vec![
                            Type::Ref("Refs.Root".into()),
                            Type::Ref("Refs.Root".into())
                        ])
                    );
                    *ty = Type::Tuple(vec![
                        Type::Ref("Refs.Sample".into()),
                        Type::Ref("Refs.Root".into()),
                    ]);
                }
                14 => {
                    assert_eq!(
                        g.nodes[projection].ty,
                        NodeType::Value(Type::Ref("Refs.Root".into()))
                    );
                    g.nodes[projection].ty = NodeType::Value(Type::Ref("Refs.Sample".into()));
                    g.nodes[projection].payload = Some(Payload::Scalar(Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "item".into(),
                        entity: "Refs.Sample".into(),
                    }));
                }
                15 => {
                    let Some(Payload::CompletionSeed { fields, .. }) = &mut g.nodes[seed].payload
                    else {
                        panic!()
                    };
                    assert_eq!(fields[0].field.as_deref(), Some("Refs.Sample.owner"));
                    fields[0].field = Some("Refs.Sample.left".into());
                }
                16 => {
                    let Some(Payload::Scalar(Scalar::Set { items, .. })) =
                        &mut g.nodes[set].payload
                    else {
                        panic!()
                    };
                    assert!(!items.is_empty());
                    items.pop();
                }
                17 => {
                    let reason = g.nodes[original_missing]
                        .reasons
                        .iter_mut()
                        .find(|reason| {
                            matches!(reason.kind, ReasonKind::Missing) && !reason.missing.is_empty()
                        })
                        .unwrap();
                    assert_eq!(
                        reason.missing[0].field.as_deref(),
                        Some("Refs.Sample.owner")
                    );
                    reason.missing[0].field = Some("Refs.Sample.left".into());
                }
                _ => panic!(),
            }
            assert!(
                g.nodes != original_nodes
                    || g.cases != original_cases
                    || g.requests[1] != original_request,
                "real mutation {kind}"
            );
            assert!(
                matches!(
                    e.validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "same {kind}"
            );
            assert!(
                matches!(
                    environment(&r).validate_answer(&g, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh {kind}"
            );
            g.nodes = original_nodes.clone();
            g.cases = original_cases.clone();
            g.requests[1] = original_request.clone();
            e.validate_answer(&g, request, answer).unwrap();
            environment(&r)
                .validate_answer(&g, request, answer)
                .unwrap();
        }
    }
}
#[test]
fn owner_completion_domains_reject_missing_duplicate_and_unregistered_members() {
    mutate(&[0, 1, 9], false)
}

fn stop(phase: &'static str, at: usize, kind: usize) {
    use crate::control::Control;
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(2, false, false, false);
    let asks = [
        "seed=evaluate(RefCalc.seed)",
        "prior=check(RefCalc.prior)",
        "hole=evaluate(RefCalc.size,a=@v/A)",
        "current=check(RefCalc.nonnegative,a=@v/A)",
        "later=evaluate(RefCalc.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    let target = normal.prepared.inputs().law().declarations["RefCalc.nonnegative"].span;
    let observed_span = if phase == "owned_family_enum" {
        normal
            .prepared
            .inputs()
            .law()
            .exprs
            .iter()
            .find(|e| {
                e.span.0 >= target.0
                    && e.span.1 <= target.1
                    && matches!(e.kind, ExprKind::Family { .. })
            })
            .unwrap()
            .span
    } else {
        target
    };
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut control, |e, g, q, a| {
        e.validate_answer(g, q, a)?;
        if q.id == "hole" && phase != "answer" {
            let (arm, hit) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, ctx, op, index| {
                if span == observed_span
                    && ctx.request == 3
                    && ((phase == "owned_family_enum" && ctx.case.is_some())
                        || (phase != "owned_family_enum" && ctx.case.is_none()))
                    && op == phase
                    && index == at
                {
                    assert!(!hit.replace(true));
                    arm.set(true);
                }
            });
        }
        if q.id == "current" && phase == "answer" {
            assert!(!seen.replace(true));
            armed.set(true);
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(
        stopped.frames.as_slice(),
        &normal.frames[..stopped.frames.len()]
    );
    assert_eq!(
        stopped.iterations.as_slice(),
        &normal.iterations[..stopped.iterations.len()]
    );
    assert_eq!(
        stopped.instances.as_slice(),
        &normal.instances[..stopped.instances.len()]
    );
    assert_eq!(
        stopped.cases.as_slice(),
        &normal.cases[..stopped.cases.len()]
    );
    assert_eq!(
        stopped.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..stopped.universal_witnesses.len()]
    );
    let Json::Obj(ref nw) = normal.wire() else {
        panic!()
    };
    let Json::Obj(ref sw) = stopped.wire() else {
        panic!()
    };
    let Json::Arr(na) = &nw["answers"] else {
        panic!()
    };
    let Json::Arr(sa) = &sw["answers"] else {
        panic!()
    };
    let retained = if phase == "answer" { 4 } else { 3 };
    assert_eq!(&sa[..retained], &na[..retained]);
    for a in &stopped.answers[retained..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(reason)if reason==&expected))
        );
    }
    if phase != "answer" {
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, n)| stopped.contexts[i].request == 3
                    && stopped.contexts[i].case.is_none()
                    && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn owner_completion_coverage_memory_stop_keeps_cases_without_whole_claim() {
    stop("completion_coverage", 0, 2)
}
