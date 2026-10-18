use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/finite_reference_fields.rs");
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn example(mode: usize) -> ObservedEvaluation {
    let question = match mode {
        0 => "evaluate(Inspect.chosen,h=@v/h)",
        1 => "evaluate(Inspect.mixed,h=@v/h)",
        2 => "evaluate(Inspect.members,h=@v/h)",
        3 => "evaluate(Inspect.choice,h=@v/h)",
        4 => "check(Inspect.valid,h=@v/h)",
        5 => "evaluate(Inspect.independent,h=@v/h)",
        _ => panic!(),
    };
    let first = format!("first={question}");
    let target = format!("target={question}");
    let r = evaluate_observed_bytes(
        fixture::input(false, false, mode == 4),
        &[&first, &target, "later=evaluate(Inspect.seed)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.answers);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn mutate(mode: usize, kinds: &[usize]) {
    let r = example(mode);
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let seed = r.nodes[domain].arguments[0].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    assert!(elements.len() > 1);
    let chosen = elements
        .iter()
        .copied()
        .find(|m| match r.nodes[m.0].payload.as_ref() {
            Some(Payload::Scalar(Scalar::Set { items, .. })) => !items.is_empty(),
            Some(Payload::Scalar(Scalar::Data { args, .. })) => !args.is_empty(),
            _ => true,
        })
        .unwrap();
    let first = chosen.0;
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
    let case = r
        .cases
        .iter()
        .position(|c| {
            c.domain == NodeRef(domain)
                && if mode == 5 {
                    r.nodes[c.values[0].0].payload != r.nodes[c.values[1].0].payload
                } else {
                    c.member == chosen
                }
        })
        .unwrap();
    let projection = r.cases[case].values[0].0;
    let proof = answer.evidence[0].0;
    let field_value=r.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==1&&r.contexts[i].case.is_some()&&n.arguments.len()==3&&matches!(&n.rule,Rule::Input{kind:"law",..})&&matches!(&n.payload,Some(Payload::Scalar(Scalar::Subject{entity,..}))if entity=="Fields.Sample")&&matches!(r.nodes[n.arguments[0].0].payload,Some(Payload::Expression{..}))).then_some(i));
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut graph = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = environment(&r);
        e.validate_answer(&graph, request, answer).unwrap();
        let original_nodes = graph.nodes.clone();
        let original_cases = graph.cases.clone();
        let original_request = graph.requests[1].clone();
        for &kind in kinds {
            match kind {
                0 => {
                    let Some(Payload::Domain { elements, .. }) = &mut graph.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements.pop();
                    graph.nodes[domain].arguments.pop();
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut graph.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements[1] = elements[0];
                    graph.nodes[domain].arguments[2] = elements[0];
                }
                2 => {
                    let Some(Payload::CompletionSeed { fields, .. }) =
                        &mut graph.nodes[seed].payload
                    else {
                        panic!()
                    };
                    assert_eq!(fields[0].field.as_deref(), Some("Fields.Holder.chosen"));
                    fields[0].field = Some("Fields.Holder.second".into());
                }
                3 => {
                    let Some(Payload::CompletionSeed { sources, .. }) =
                        &mut graph.nodes[seed].payload
                    else {
                        panic!()
                    };
                    assert_ne!(sources[0], foreign_source);
                    sources[0] = foreign_source;
                }
                4 => {
                    assert!(!graph.nodes[domain].support.is_empty());
                    graph.nodes[domain].support.clear();
                }
                5 => graph.nodes[domain].scope.snapshots.clear(),
                6 => {
                    assert_eq!(graph.cases[case].values.len(), 2);
                    assert_ne!(
                        graph.nodes[graph.cases[case].values[0].0].payload,
                        graph.nodes[graph.cases[case].values[1].0].payload
                    );
                    graph.cases[case].values.swap(0, 1);
                }
                7 => {
                    assert!(!graph.requests[1].defaults.is_empty());
                    graph.requests[1].defaults.clear();
                }
                8 => {
                    let Some(Payload::CompletionPair { fields, .. }) =
                        &mut graph.nodes[proof].payload
                    else {
                        panic!()
                    };
                    assert_eq!(fields.len(), 2);
                    fields.swap(0, 1);
                }
                9 | 11 => {
                    let index = if kind == 9 { first } else { projection };
                    assert_eq!(
                        graph.nodes[index].ty,
                        NodeType::Value(Type::Ref("Fields.Sample".into()))
                    );
                    graph.nodes[index].ty = NodeType::Value(Type::Ref("Fields.Root".into()));
                    graph.nodes[index].payload = Some(Payload::Scalar(Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "A".into(),
                        entity: "Fields.Root".into(),
                    }));
                }
                10 => {
                    let Some(Payload::Domain { ty, .. }) = &mut graph.nodes[domain].payload else {
                        panic!()
                    };
                    assert_eq!(*ty, Type::Ref("Fields.Sample".into()));
                    *ty = Type::Ref("Fields.Root".into());
                }
                12 | 16 => {
                    let index = if kind == 12 { first } else { projection };
                    let Some(Payload::Scalar(Scalar::Tuple(items))) =
                        &mut graph.nodes[index].payload
                    else {
                        panic!()
                    };
                    assert_eq!(items[0].ty(), Type::Ref("Fields.Sample".into()));
                    items[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "A".into(),
                        entity: "Fields.Root".into(),
                    };
                    graph.nodes[index].ty = NodeType::Value(Type::Tuple(vec![
                        Type::Ref("Fields.Root".into()),
                        Type::Bool,
                    ]));
                }
                13 => {
                    let Some(Payload::Scalar(Scalar::Set { element, items })) =
                        &mut graph.nodes[first].payload
                    else {
                        panic!()
                    };
                    assert_eq!(*element, Type::Ref("Fields.Sample".into()));
                    *element = Type::Ref("Fields.Root".into());
                    assert_eq!(items.len(), 1);
                    items[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "A".into(),
                        entity: "Fields.Root".into(),
                    };
                    graph.nodes[first].ty =
                        NodeType::Value(Type::Set(Box::new(Type::Ref("Fields.Root".into()))));
                }
                14 => {
                    let Some(Payload::Scalar(Scalar::Data { family, args, .. })) =
                        &mut graph.nodes[first].payload
                    else {
                        panic!()
                    };
                    assert_eq!(family, "Fields.Choice");
                    assert_eq!(args[0].ty(), Type::Ref("Fields.Root".into()));
                    args[0] = Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "p".into(),
                        entity: "Fields.Sample".into(),
                    };
                }
                15 => {
                    let Some(Payload::Domain { ty, .. }) = &mut graph.nodes[domain].payload else {
                        panic!()
                    };
                    assert_eq!(
                        *ty,
                        Type::Tuple(vec![Type::Ref("Fields.Sample".into()), Type::Bool])
                    );
                    *ty = Type::Tuple(vec![Type::Ref("Fields.Root".into()), Type::Bool]);
                }
                17 => {
                    let Some(Payload::CompletionSeed { sources, .. }) = &graph.nodes[seed].payload
                    else {
                        panic!()
                    };
                    let source = sources[0].0;
                    let Some(Payload::Expression { bindings, .. }) =
                        &mut graph.nodes[source].payload
                    else {
                        panic!()
                    };
                    assert_eq!(bindings[0].ty, Type::Ref("Fields.Holder".into()));
                    bindings[0].ty = Type::Ref("Fields.Root".into());
                }
                18 => {
                    let i = field_value.unwrap();
                    graph.nodes[i].arguments.remove(0);
                }
                19 => {
                    let i = field_value.unwrap();
                    assert_ne!(graph.nodes[i].arguments[0], foreign_source);
                    graph.nodes[i].arguments[0] = foreign_source;
                }
                20 => {
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut graph.nodes[proof].payload
                    else {
                        panic!()
                    };
                    *checked += 1;
                }
                21 => {
                    let i = field_value.unwrap();
                    assert!(graph.nodes[i].support.is_empty());
                    graph.nodes[i].support.push(Fact {
                        snapshot: "v".into(),
                        subject: "h".into(),
                        field: Some("Fields.Holder.chosen".into()),
                        atom: Some("fabricated".into()),
                    });
                }
                22 => {
                    assert_ne!(graph.nodes[root].arguments[1], foreign_domain);
                    graph.nodes[root].arguments[1] = foreign_domain;
                }
                23 => {
                    let reason = graph.nodes[seed]
                        .reasons
                        .iter_mut()
                        .find(|r| !r.missing.is_empty())
                        .unwrap();
                    reason.missing[0].field = Some("Fields.Holder.second".into());
                }
                24 => {
                    let reason = graph.nodes[seed]
                        .reasons
                        .iter_mut()
                        .find(|r| !r.dependencies.is_empty())
                        .unwrap();
                    assert_ne!(reason.dependencies[0], foreign_source);
                    reason.dependencies[0] = foreign_source;
                }
                _ => panic!(),
            }
            assert!(
                graph.nodes != original_nodes
                    || graph.cases != original_cases
                    || graph.requests[1] != original_request,
                "real {kind}"
            );
            assert!(
                matches!(
                    e.validate_answer(&graph, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "same {kind}"
            );
            assert!(
                matches!(
                    environment(&r).validate_answer(&graph, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh {kind}"
            );
            graph.nodes = original_nodes.clone();
            graph.cases = original_cases.clone();
            graph.requests[1] = original_request.clone();
            e.validate_answer(&graph, request, answer).unwrap();
            environment(&r)
                .validate_answer(&graph, request, answer)
                .unwrap();
        }
    }
}
#[test]
fn finite_reference_field_domains_reject_missing_duplicate_and_foreign_whole() {
    mutate(0, &[0, 1, 22]);
}
#[test]
fn finite_reference_field_sources_reject_unread_slot_foreign_source_and_missing_facts() {
    mutate(0, &[2, 3, 17, 23, 24]);
}
#[test]
fn finite_reference_field_support_scope_request_and_fake_atoms_are_rechecked() {
    mutate(0, &[4, 5, 7, 21]);
}
#[test]
fn finite_reference_field_actual_ref_member_domain_projection_types_are_rechecked() {
    mutate(0, &[9, 10, 11]);
}
#[test]
fn finite_reference_field_nested_tuple_member_domain_projection_types_are_rechecked() {
    mutate(1, &[12, 15, 16]);
}
#[test]
fn finite_reference_field_set_element_and_data_constructor_argument_types_are_rechecked() {
    mutate(2, &[13]);
    mutate(3, &[14]);
}
#[test]
fn finite_reference_field_shared_case_slots_and_pair_field_order_are_rechecked() {
    mutate(5, &[6, 8]);
}
#[test]
fn finite_reference_field_chain_prefix_original_source_edges_and_whole_count_are_rechecked() {
    mutate(4, &[18, 19, 20]);
}

#[test]
fn finite_reference_field_internal_pins_validate_original_shapes_refs_and_missing_identity() {
    use crate::archmap::{FieldAssignment, check_completion_with_values};
    use crate::observed::control::CheckFailure;
    let r = example(0);
    let input = r.prepared.inputs();
    let pin = |field: &str, value: Json| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("Fields.Holder.{field}"),
        value,
    };
    let ref_p = fixture::reference("v", "p");
    let root_a = fixture::reference("v", "A");
    for pins in [
        vec![pin("chosen", fixture::reference("v", "ghost"))],
        vec![pin("chosen", root_a.clone())],
        vec![pin("owner", root_a.clone())],
        vec![pin("chosen", ref_p.clone()), pin("chosen", ref_p.clone())],
        vec![pin(
            "mixed",
            Json::Arr(vec![root_a.clone(), Json::Bool(false)]),
        )],
        vec![pin("members", Json::Arr(vec![root_a.clone()]))],
        vec![pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![ref_p.clone(), Json::Bool(false)])),
            ]),
        )],
        vec![pin(
            "choice",
            Json::obj([("tag", Json::str("ghost")), ("args", Json::Arr(vec![]))]),
        )],
        vec![pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![root_a.clone()])),
            ]),
        )],
    ] {
        assert!(matches!(
            check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
                &input.archmap().snapshots,
                &input.law().definitions,
                &pins,
                &mut named_call_quiet()
            ),
            Err(CheckFailure::Input(_))
        ));
    }
    for p in [
        pin("chosen", ref_p.clone()),
        pin("mixed", Json::Arr(vec![ref_p.clone(), Json::Bool(false)])),
        pin("members", Json::Arr(vec![ref_p])),
        pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![root_a, Json::Bool(true)])),
            ]),
        ),
    ] {
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots,
            &input.law().definitions,
            &[p],
            &mut named_call_quiet(),
        )
        .unwrap();
    }
    assert!(
        matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots,&input.law().definitions,&[pin("chosen",fixture::reference("v","r"))],&mut named_call_quiet()),Err(CheckFailure::Input(issue))if issue.code==crate::issue::Code::InconsistentObservation)
    );
}

#[test]
fn finite_reference_field_set_member_display_order_keeps_extensional_proof_and_original_slots() {
    let r = example(2);
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1];
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain.0].payload else {
        panic!()
    };
    let member=elements.iter().find(|m|matches!(&r.nodes[m.0].payload,Some(Payload::Scalar(Scalar::Set{items,..}))if items.len()==2)).unwrap().0;
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut graph = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let original = graph.nodes[member].clone();
        let e = environment(&r);
        let q = &r.prepared.requests().requests()[1];
        e.validate_answer(&graph, q, answer).unwrap();
        let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut graph.nodes[member].payload
        else {
            panic!()
        };
        let first = items[0].clone();
        items.reverse();
        assert_ne!(items[0], first, "表示順の実変更");
        assert_eq!(graph.nodes[member], original, "Setの外延は同じ");
        e.validate_answer(&graph, q, answer).unwrap();
        environment(&r).validate_answer(&graph, q, answer).unwrap();
        graph.nodes[member] = original;
        e.validate_answer(&graph, q, answer).unwrap();
        environment(&r).validate_answer(&graph, q, answer).unwrap();
    }
}
fn stop(phase: &'static str, at: usize, kind: usize) {
    use crate::observed::control::{Checkpoint, Control, Usage};
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(false, false, false);
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.size,h=@v/h)",
        "current=evaluate(Inspect.stable,h=@v/h)",
        "later=evaluate(Inspect.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let target = normal.prepared.inputs().law().declarations["Inspect.stable"].span;
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let nested = Rc::new(Cell::new(0));
    let (a, p, f, n) = (
        armed.clone(),
        probes.clone(),
        frozen.clone(),
        nested.clone(),
    );
    let mut c = Control::new(limits, move |checkpoint| {
        p.set(p.get() + 1);
        let hit = if a.get() && phase == "pin_schema" && checkpoint == Checkpoint::ArchMapSchema {
            n.set(n.get() + 1);
            n.get() == 3
        } else {
            a.get() && phase != "pin_schema"
        };
        if hit {
            a.set(false);
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Usage::default()
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "hole" && phase != "answer" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, ctx, operation, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && operation
                        == if phase == "pin_schema" {
                            "completion_reference_constraints"
                        } else {
                            phase
                        }
                    && index == at
                {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if q.id == "current" && phase == "answer" {
            assert!(!seen.replace(true));
            armed.set(true);
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert!(seen.get());
    if phase == "pin_schema" {
        assert_eq!(nested.get(), 3);
    }
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        stopped.nodes.as_slice(),
        &normal.nodes[..stopped.nodes.len()]
    );
    assert_eq!(
        stopped.contexts.as_slice(),
        &normal.contexts[..stopped.contexts.len()]
    );
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
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
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
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn finite_reference_field_enumeration_cancel_keeps_values_refutation_and_missing_prefix() {
    stop("completion_enum", 1, 0);
}
#[test]
fn finite_reference_field_case_time_stop_keeps_completed_case_and_original_missing() {
    stop("completion_case", 1, 1);
}
#[test]
fn finite_reference_field_coverage_memory_stop_never_promotes_unfinished_whole() {
    stop("completion_coverage", 0, 2);
}
#[test]
fn finite_reference_field_nested_pin_shape_stop_keeps_original_tables_and_probe_freeze() {
    stop("pin_schema", 1, 2);
}
#[test]
fn finite_reference_field_post_validation_cancel_retains_verified_current_and_probe_freeze() {
    stop("answer", 0, 0);
}
