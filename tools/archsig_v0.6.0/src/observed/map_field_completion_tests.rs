use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/map_field_completions.rs");
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
        0 | 9 => "evaluate(Inspect.read,h=@v/h)",
        1 => "evaluate(Inspect.mixed,h=@v/h)",
        2 => "evaluate(Inspect.bag,h=@v/h)",
        3 => "evaluate(Inspect.choice,h=@v/h)",
        4 => "check(Inspect.valid,h=@v/h)",
        5 => "evaluate(Inspect.independent,h=@v/h)",
        6 => "evaluate(Inspect.partial,h=@v/h)",
        7 => "evaluate(Inspect.pending,h=@v/h,a=@v/B)",
        8 => "evaluate(Inspect.plain,h=@v/h)",
        _ => panic!(),
    };
    let first = format!("first={question}");
    let target = format!("target={question}");
    let r = evaluate_observed_bytes(
        fixture::input(mode == 8 || mode == 9, false, mode == 4 || mode == 6, false),
        &[&first, &target, "later=evaluate(Inspect.seed)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.answers);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn map_mut(value: &mut Scalar) -> (&mut Type, &mut Type, &mut Vec<(Scalar, Scalar)>) {
    match value {
        Scalar::Map {
            domain,
            codomain,
            pairs,
        } => (domain, codomain, pairs),
        _ => panic!("Map expected"),
    }
}
fn scalar_mut(node: &mut Node) -> &mut Scalar {
    match node.payload.as_mut().unwrap() {
        Payload::Scalar(s) => s,
        _ => panic!("Scalar expected"),
    }
}
fn subject(snapshot: &str, id: &str, entity: &str) -> Scalar {
    Scalar::Subject {
        snapshot: snapshot.into(),
        subject: id.into(),
        entity: format!("MapFields.{entity}"),
    }
}
fn wrong_map_image(value: &mut Scalar) {
    let (_, image, pairs) = map_mut(value);
    assert_eq!(*image, Type::Ref("MapFields.Image".into()));
    assert!(!pairs.is_empty());
    *image = Type::Ref("MapFields.Root".into());
    pairs[0].1 = subject("v", "A", "Root");
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
            Some(Payload::Scalar(Scalar::Set { items, .. })) => items
                .iter()
                .any(|x| matches!(x,Scalar::Map {pairs,..} if !pairs.is_empty())),
            Some(Payload::Scalar(Scalar::Data { args, .. })) => !args.is_empty(),
            Some(Payload::Scalar(Scalar::Tuple(items))) if mode == 1 => {
                matches!(&items[1],Scalar::Map {pairs,..} if !pairs.is_empty())
            }
            Some(Payload::Scalar(Scalar::Map { pairs, .. })) => !pairs.is_empty(),
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
    let proof = answer.evidence.first().map(|p| p.0);
    let field_value = r.nodes.iter().enumerate().find_map(|(i, n)| {
        (r.contexts[i].request == 1
            && r.contexts[i].case.is_some()
            && n.arguments.len() == 3
            && matches!(&n.rule, Rule::Input { kind: "law", .. })
            && matches!(&n.payload, Some(Payload::Scalar(Scalar::Map { .. })))
            && matches!(
                r.nodes[n.arguments[0].0].payload,
                Some(Payload::Expression { .. })
            ))
        .then_some(i)
    });
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
                    assert_eq!(fields[0].field.as_deref(), Some("MapFields.Holder.table"));
                    fields[0].field = Some("MapFields.Holder.other".into());
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
                    graph.cases[case].values.swap(0, 1);
                }
                7 => {
                    assert!(!graph.requests[1].defaults.is_empty());
                    graph.requests[1].defaults.clear();
                }
                8 => {
                    let Some(Payload::CompletionPair { fields, .. }) =
                        &mut graph.nodes[proof.expect("pair/exhaustion evidence")].payload
                    else {
                        panic!()
                    };
                    assert_eq!(fields.len(), 2);
                    fields.swap(0, 1);
                }
                9 | 11 => {
                    let index = if kind == 9 { first } else { projection };
                    wrong_map_image(scalar_mut(&mut graph.nodes[index]));
                    let t = scalar_mut(&mut graph.nodes[index]).ty();
                    graph.nodes[index].ty = NodeType::Value(t);
                }
                10 => {
                    let Some(Payload::Domain { ty, .. }) = &mut graph.nodes[domain].payload else {
                        panic!()
                    };
                    let Type::Map(_, image) = ty else { panic!() };
                    **image = Type::Ref("MapFields.Root".into());
                }
                12 | 16 => {
                    let index = if kind == 12 { first } else { projection };
                    let Scalar::Tuple(items) = scalar_mut(&mut graph.nodes[index]) else {
                        panic!()
                    };
                    wrong_map_image(&mut items[1]);
                    let t = scalar_mut(&mut graph.nodes[index]).ty();
                    graph.nodes[index].ty = NodeType::Value(t);
                }
                13 => {
                    let Scalar::Set { element, items } = scalar_mut(&mut graph.nodes[first]) else {
                        panic!()
                    };
                    let item = items
                        .iter_mut()
                        .find(|x| matches!(x,Scalar::Map {pairs,..} if !pairs.is_empty()))
                        .unwrap();
                    wrong_map_image(item);
                    *element = item.ty();
                    let t = scalar_mut(&mut graph.nodes[first]).ty();
                    graph.nodes[first].ty = NodeType::Value(t);
                }
                14 => {
                    let Scalar::Data { family, args, .. } = scalar_mut(&mut graph.nodes[first])
                    else {
                        panic!()
                    };
                    assert_eq!(family, "MapFields.Payload");
                    wrong_map_image(&mut args[0]);
                }
                15 => {
                    let Some(Payload::Domain { ty, .. }) = &mut graph.nodes[domain].payload else {
                        panic!()
                    };
                    let Type::Tuple(items) = ty else { panic!() };
                    items[1] = Type::Map(
                        Box::new(Type::Ref("MapFields.Key".into())),
                        Box::new(Type::Ref("MapFields.Root".into())),
                    );
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
                    assert_eq!(bindings[0].ty, Type::Ref("MapFields.Holder".into()));
                    bindings[0].ty = Type::Ref("MapFields.Root".into());
                }
                18 => {
                    graph.nodes[field_value.unwrap()].arguments.remove(0);
                }
                19 => {
                    let i = field_value.unwrap();
                    assert_ne!(graph.nodes[i].arguments[0], foreign_source);
                    graph.nodes[i].arguments[0] = foreign_source;
                }
                20 => {
                    let Some(Payload::FiniteExhaustion { checked, .. }) =
                        &mut graph.nodes[proof.expect("pair/exhaustion evidence")].payload
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
                        field: Some("MapFields.Holder.table".into()),
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
                    reason.missing[0].field = Some("MapFields.Holder.other".into());
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
                25..=30 => {
                    let (key, _, pairs) = map_mut(scalar_mut(&mut graph.nodes[first]));
                    assert!(!pairs.is_empty());
                    match kind {
                        25 => {
                            *key = Type::Ref("MapFields.Image".into());
                            pairs[0].0 = subject("v", "x", "Image");
                        }
                        26 => pairs[0].0 = subject("w", "k", "Key"),
                        27 => pairs[0].1 = subject("w", "x", "Image"),
                        28 => pairs.push(pairs[0].clone()),
                        29 => pairs.clear(),
                        30 => pairs.push((subject("w", "k", "Key"), subject("v", "x", "Image"))),
                        _ => unreachable!(),
                    }
                    let t = scalar_mut(&mut graph.nodes[first]).ty();
                    graph.nodes[first].ty = NodeType::Value(t);
                }
                31 => {
                    let i = field_value.unwrap();
                    let (_, _, pairs) = map_mut(scalar_mut(&mut graph.nodes[i]));
                    assert_eq!(pairs.len(), 1);
                    let old = pairs[0].1.clone();
                    pairs[0].1 = if old == subject("v", "x", "Image") {
                        subject("v", "y", "Image")
                    } else {
                        subject("v", "x", "Image")
                    };
                    assert_ne!(pairs[0].1, old);
                }
                32 => {
                    let old=graph.nodes.iter().enumerate().filter(|(i,_)|r.contexts[*i].request==1).flat_map(|(_,n)|n.reasons.iter()).find(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm {method,..} if method=="unresolved_owned_expression_family")).unwrap().clone();
                    assert!(!graph.nodes[seed].reasons.contains(&old));
                    graph.nodes[seed].reasons.push(old);
                }
                33 => {
                    let i=graph.nodes.iter().enumerate().find_map(|(i,n)|(r.contexts[i].request==1 && r.contexts[i].case.is_some() && n.reasons.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm {method,..} if method=="unresolved_owned_expression_family"))).then_some(i)).unwrap();
                    let old = graph.nodes[i].reasons.len();
                    graph.nodes[i].reasons.retain(|r|!matches!(&r.kind,ReasonKind::UnsupportedAlgorithm {method,..} if method=="unresolved_owned_expression_family"));
                    assert!(graph.nodes[i].reasons.len() < old);
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
fn map_field_domains_reject_missing_duplicate_and_foreign_whole() {
    mutate(0, &[0, 1, 22]);
}
#[test]
fn map_field_sources_reject_unread_slot_foreign_source_and_missing_facts() {
    mutate(0, &[2, 3, 17, 23, 24]);
}
#[test]
fn map_field_support_scope_request_and_fake_atoms_are_rechecked() {
    mutate(0, &[4, 5, 7, 21]);
}
#[test]
fn map_field_actual_map_member_domain_projection_types_are_rechecked() {
    mutate(0, &[9, 10, 11, 25]);
}
#[test]
fn map_field_nested_tuple_member_domain_projection_types_are_rechecked() {
    mutate(1, &[12, 15, 16]);
}
#[test]
fn map_field_set_element_and_data_constructor_map_types_are_rechecked() {
    mutate(2, &[13]);
    mutate(3, &[14]);
}
#[test]
fn map_field_shared_case_slots_and_pair_field_order_are_rechecked() {
    mutate(5, &[6, 8]);
}
#[test]
fn map_field_chain_prefix_source_edges_and_whole_count_are_rechecked() {
    mutate(4, &[18, 19, 20]);
}
#[test]
fn map_field_totality_owned_key_image_and_duplicate_rows_are_rechecked() {
    mutate(9, &[26, 27, 28, 29, 30]);
}
#[test]
fn map_field_actual_assigned_map_value_is_rechecked_against_case() {
    mutate(0, &[31]);
}
#[test]
fn map_field_resolved_family_rejects_stale_reason_and_pending_case_requires_actual_reason() {
    mutate(6, &[32]);
    mutate(7, &[33]);
}
#[test]
fn map_field_table_row_display_order_keeps_extensional_proof_and_original_slots() {
    let r = example(8);
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1];
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain.0].payload else {
        panic!()
    };
    let member=elements.iter().find(|m|matches!(&r.nodes[m.0].payload,Some(Payload::Scalar(Scalar::Map{pairs:items,..}))if items.len()==2)).unwrap().0;
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut graph = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let original = graph.nodes[member].clone();
        let e = environment(&r);
        let q = &r.prepared.requests().requests()[1];
        e.validate_answer(&graph, q, answer).unwrap();
        let Some(Payload::Scalar(Scalar::Map { pairs: items, .. })) =
            &mut graph.nodes[member].payload
        else {
            panic!()
        };
        let first = items[0].clone();
        items.reverse();
        assert_ne!(items[0], first, "表示順の実変更");
        assert_eq!(graph.nodes[member], original, "Mapの外延は同じ");
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
    let input = fixture::input(true, false, false, false);
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.partial,h=@v/h)",
        "current=evaluate(Inspect.same,h=@v/h)",
        "later=evaluate(Inspect.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let target = normal.prepared.inputs().law().declarations["Inspect.same"].span;
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let pin_gate = Rc::new(Cell::new(false));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Usage::default()
        }
    });
    if phase == "map_reader" || phase == "map_cover" {
        let (gate, a, s) = (pin_gate.clone(), armed.clone(), seen.clone());
        crate::archmap::observe_map_validation(move |operation, index| {
            if gate.get() && operation == phase && index == 0 {
                assert!(!s.replace(true));
                a.set(true);
                gate.set(false);
            }
        });
    }
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "hole" && phase != "answer" {
            let (a, s, gate) = (armed.clone(), seen.clone(), pin_gate.clone());
            data::observe_iterations(move |span, ctx, operation, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && operation
                        == if phase == "map_reader" || phase == "map_cover" {
                            "completion_reference_constraints"
                        } else {
                            phase
                        }
                    && index == at
                {
                    if phase == "map_reader" || phase == "map_cover" {
                        gate.set(true);
                    } else {
                        assert!(!s.replace(true));
                        a.set(true);
                    }
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
    crate::archmap::clear_map_validation_observer();
    assert!(seen.get());
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
fn map_field_enumeration_cancel_keeps_values_refutation_and_missing_prefix() {
    stop("completion_enum", 1, 0);
}
#[test]
fn map_field_case_time_stop_keeps_completed_case_and_original_missing() {
    stop("completion_case", 1, 1);
}
#[test]
fn map_field_coverage_memory_stop_never_promotes_unfinished_whole() {
    stop("completion_coverage", 0, 2);
}
#[test]
fn map_field_actual_reader_row_stop_keeps_original_tables_and_probe_freeze() {
    stop("map_reader", 1, 2);
}
#[test]
fn map_field_post_validation_cancel_retains_verified_current_and_probe_freeze() {
    stop("answer", 0, 0);
}

#[test]
fn map_field_actual_key_subset_construction_cancel_keeps_strict_prefix() {
    stop("map_field_key", 1, 0);
}
#[test]
fn map_field_actual_candidate_table_emission_time_stop_keeps_strict_prefix() {
    stop("map_field_candidate", 1, 1);
}

#[test]
fn map_field_actual_totality_cover_memory_stop_keeps_strict_prefix() {
    stop("map_cover", 1, 2);
}
#[test]
fn map_field_internal_pins_validate_original_map_shapes_refs_totality_and_missing_identity() {
    use crate::archmap::{FieldAssignment, check_completion_with_values};
    use crate::observed::control::CheckFailure;
    let pin = |field: &str, value: Json| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("MapFields.Holder.{field}"),
        value,
    };
    let r = example(9);
    let input = r.prepared.inputs();
    let kx = fixture::table("v", "k", "x");
    let row = |key: Json, image: Json| Json::Arr(vec![key, image]);
    let malformed = [
        ("table", fixture::table("v", "ghost", "x")),
        ("table", fixture::table("v", "x", "x")),
        ("table", fixture::table("v", "k", "A")),
        (
            "table",
            Json::Arr(vec![
                row(fixture::reference("v", "k"), fixture::reference("v", "x")),
                row(fixture::reference("v", "k"), fixture::reference("v", "y")),
            ]),
        ),
        (
            "table",
            Json::Arr(vec![Json::Arr(vec![fixture::reference("v", "k")])]),
        ),
        ("table", Json::Bool(true)),
        ("owner", fixture::reference("v", "A")),
        (
            "mixed",
            Json::Arr(vec![Json::Bool(false), fixture::table("v", "k", "A")]),
        ),
        ("bag", Json::Arr(vec![fixture::table("v", "x", "x")])),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("wrap")),
                ("args", Json::Arr(vec![fixture::table("v", "k", "A")])),
            ]),
        ),
    ];
    for (field, value) in malformed {
        assert!(
            matches!(
                check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
                    &input.archmap().snapshots,
                    &input.law().definitions,
                    &[pin(field, value)],
                    &mut named_call_quiet()
                ),
                Err(CheckFailure::Input(_))
            ),
            "malformed {field}"
        );
    }
    assert!(matches!(
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots,
            &input.law().definitions,
            &[pin("table", kx.clone()), pin("table", kx.clone())],
            &mut named_call_quiet()
        ),
        Err(CheckFailure::Input(_))
    ));
    for bad in [
        Json::Arr(vec![]),
        fixture::table("w", "k", "x"),
        Json::Arr(vec![row(
            fixture::reference("v", "k"),
            fixture::reference("w", "x"),
        )]),
        Json::Arr(vec![
            row(fixture::reference("v", "k"), fixture::reference("v", "x")),
            row(fixture::reference("w", "k"), fixture::reference("v", "y")),
        ]),
    ] {
        assert!(
            matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots,&input.law().definitions,&[pin("table",bad)],&mut named_call_quiet()),Err(CheckFailure::Input(issue)) if issue.code==crate::issue::Code::InconsistentObservation)
        );
    }
    for good in [kx, fixture::table("v", "k", "y")] {
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots,
            &input.law().definitions,
            &[pin("table", good)],
            &mut named_call_quiet(),
        )
        .unwrap();
    }
    let unknown = example(4);
    let input = unknown.prepared.inputs();
    check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
        &input.archmap().snapshots,
        &input.law().definitions,
        &[pin("table", Json::Arr(vec![]))],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert!(
        matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots,&input.law().definitions,&[pin("table",Json::Arr(vec![])),pin("owner",fixture::reference("v","A"))],&mut named_call_quiet()),Err(CheckFailure::Input(issue)) if issue.code==crate::issue::Code::InconsistentObservation)
    );
}
