// 小さい既知 Ref chain。全 fixture の byte API 接続は integration test が扱う。
fn reservations_private_fixture(body: &str, missing: bool) -> InputSources {
    let definition = include_bytes!("../../tests/fixtures/reservations.atoms.json");
    let digest = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; {body} }}"
    );
    let held = if missing {
        ""
    } else {
        r#",{"id":"q-held","subject":"q","field":"Reservations.State.held","value":"0","origin":"scan"}"#
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Reservations","version":"1","digest":"{digest}"}}],"sources":[{{"id":"source","uri":"urn:fixture:reservations-chain","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"scan","mode":"observed","method":"有限な参照と数値の観測。","locations":[{{"source":"source","path":"chain.model","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"scan","subjects":[{{"id":"A","type":"Reservations.System","origin":"scan"}},{{"id":"p","type":"Reservations.State","origin":"scan"}},{{"id":"q","type":"Reservations.State","origin":"scan"}},{{"id":"e","type":"Reservations.Reserve","origin":"scan"}}],"atoms":[{{"id":"p-owner","subject":"p","field":"Reservations.State.owner","value":["v","A"],"origin":"scan"}},{{"id":"q-owner","subject":"q","field":"Reservations.State.owner","value":["v","A"],"origin":"scan"}},{{"id":"e-owner","subject":"e","field":"Reservations.Reserve.owner","value":["v","A"],"origin":"scan"}},{{"id":"e-from","subject":"e","field":"Reservations.Reserve.from","value":["v","p"],"origin":"scan"}},{{"id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"],"origin":"scan"}},{{"id":"p-free","subject":"p","field":"Reservations.State.free","value":"1","origin":"scan"}},{{"id":"q-free","subject":"q","field":"Reservations.State.free","value":"1","origin":"scan"}}{held}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn reservations_private_example(body: &str, asks: &[&str], missing: bool) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        reservations_private_fixture(body, missing),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}

fn reservations_private_text<'a>(result: &'a ObservedEvaluation, expression: NodeRef) -> &'a str {
    let Some(Payload::Expression {
        location: Location::Law { span },
        ..
    }) = &result.nodes[expression.0].payload
    else {
        panic!("original Source")
    };
    std::str::from_utf8(&result.prepared.inputs().sources().law().bytes()[span.0..span.1]).unwrap()
}

fn reservations_private_evaluations(result: &ObservedEvaluation, text: &str) -> Vec<usize> {
    result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            let Some(Payload::Evaluation { expression, .. }) = &node.payload else {
                return None;
            };
            matches!(
                &result.nodes[expression.0].payload,
                Some(Payload::Expression { .. })
            )
            .then(|| reservations_private_text(result, *expression) == text)
            .unwrap_or(false)
            .then_some(index)
        })
        .collect()
}

fn reservations_private_parts(
    result: &ObservedEvaluation,
    evaluation: usize,
) -> (usize, usize, usize) {
    let Some(Payload::Evaluation {
        expression,
        value: Some(value),
        parts,
        ..
    }) = &result.nodes[evaluation].payload
    else {
        panic!("known field Evaluation")
    };
    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0].children.len(), 1);
    (expression.0, value.0, parts[0].children[0].0)
}

#[test]
fn reservations_chain_prefixes_recheck_original_tokens_types_owners_and_children() {
    let result = reservations_private_example(
        "view current(e:Reserve):Z=e.to.free; view alternate(e:Reserve):Z=e.from.free;",
        &[
            "current=evaluate(Reservations.current,e=@v/e)",
            "alternate=evaluate(Reservations.alternate,e=@v/e)",
        ],
        false,
    );
    assert_eq!(result.status(), "complete");
    let evaluation = reservations_private_evaluations(&result, "e.to.free")[0];
    let (source, scalar, child) = reservations_private_parts(&result, evaluation);
    let (owner_source, owner_scalar, root) = reservations_private_parts(&result, child);
    assert_eq!(
        reservations_private_text(&result, NodeRef(source)),
        "e.to.free"
    );
    assert_eq!(
        reservations_private_text(&result, NodeRef(owner_source)),
        "e.to"
    );
    assert_eq!(result.nodes[source].ty, NodeType::Expression(Type::Z));
    assert_eq!(
        result.nodes[owner_source].ty,
        NodeType::Expression(Type::Ref("Reservations.State".into()))
    );
    assert_eq!(data_scalar_at(&result, scalar), &Scalar::Z(1.into()));
    assert!(
        matches!(data_scalar_at(&result, owner_scalar), Scalar::Subject { snapshot, subject, entity } if snapshot=="v" && subject=="q" && entity=="Reservations.State")
    );
    assert_eq!(
        result.nodes[scalar].arguments,
        [NodeRef(owner_scalar), NodeRef(source)]
    );
    assert_eq!(result.nodes[evaluation].support.len(), 3);
    for target in [
        source,
        owner_source,
        scalar,
        owner_scalar,
        child,
        evaluation,
        root,
    ] {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    }
    completion_mutation(&result, source, |nodes| {
        nodes[source].ty = NodeType::Expression(Type::Bool);
    });
    completion_mutation(&result, owner_source, |nodes| {
        nodes[owner_source].ty = NodeType::Expression(Type::Ref("Reservations.Reserve".into()));
    });
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &mut nodes[source].payload
        else {
            unreachable!()
        };
        span.1 -= 1;
    });
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression { location, .. }) = &mut nodes[source].payload else {
            unreachable!()
        };
        let Some(Payload::Expression {
            location: other, ..
        }) = &result.nodes[owner_source].payload
        else {
            unreachable!()
        };
        *location = other.clone();
    });
    completion_mutation(&result, owner_scalar, |nodes| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) =
            &mut nodes[owner_scalar].payload
        else {
            unreachable!()
        };
        *subject = "p".into();
    });
    completion_mutation(&result, scalar, |nodes| {
        let Some(Payload::Scalar(Scalar::Z(value))) = &mut nodes[scalar].payload else {
            unreachable!()
        };
        *value += 1;
    });
    completion_mutation(&result, scalar, |nodes| {
        nodes[scalar].support[0].subject = "p".into();
    });
    completion_mutation(&result, scalar, |nodes| {
        nodes[scalar].support[0].field = Some("Reservations.State.held".into());
    });
    completion_mutation(&result, scalar, |nodes| {
        nodes[scalar].arguments[0] = result.nodes[owner_scalar].arguments[0];
    });
    completion_mutation(&result, evaluation, |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[evaluation].payload else {
            unreachable!()
        };
        parts[0].children[0] = NodeRef(root);
        nodes[evaluation].arguments[1] = NodeRef(root);
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation].scope.modes.clear();
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation].scope.snapshots.insert("foreign".into());
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation].scope.completions = true;
    });
    completion_mutation(&result, evaluation, |nodes| {
        nodes[evaluation].support.pop();
    });
}

#[test]
fn reservations_chain_rejects_equal_foreign_call_and_request_producers() {
    let result = reservations_private_example(
        "view current(e:Reserve):Z=e.to.free; view calls(e:Reserve):(Z,Z)=(current(e),current(e));",
        &[
            "first=evaluate(Reservations.calls,e=@v/e)",
            "again=evaluate(Reservations.calls,e=@v/e)",
        ],
        false,
    );
    assert_eq!(result.status(), "complete");
    let evaluations = reservations_private_evaluations(&result, "e.to.free");
    assert_eq!(evaluations.len(), 4);
    let target = evaluations[3];
    let (source, scalar, child) = reservations_private_parts(&result, target);
    let (_, _, earlier_call) = reservations_private_parts(&result, evaluations[2]);
    let (_, _, earlier_request) = reservations_private_parts(&result, evaluations[1]);
    for foreign in [earlier_call, earlier_request] {
        assert_ne!(foreign, child);
        let (_, foreign_scalar, _) = reservations_private_parts(&result, foreign);
        let (_, own_scalar, _) = reservations_private_parts(&result, child);
        assert_eq!(
            data_scalar_at(&result, own_scalar),
            data_scalar_at(&result, foreign_scalar)
        );
        completion_mutation(&result, target, |nodes| {
            let Some(Payload::Evaluation { parts, .. }) = &mut nodes[target].payload else {
                unreachable!()
            };
            parts[0].children[0] = NodeRef(foreign);
            nodes[target].arguments[1] = NodeRef(foreign);
        });
        completion_mutation(&result, scalar, |nodes| {
            nodes[scalar].arguments[0] = NodeRef(foreign_scalar);
        });
    }
    let (foreign_source, _, _) = reservations_private_parts(&result, evaluations[0]);
    completion_mutation(&result, target, |nodes| {
        let Some(Payload::Evaluation { expression, .. }) = &mut nodes[target].payload else {
            unreachable!()
        };
        *expression = NodeRef(foreign_source);
        nodes[target].arguments[0] = NodeRef(foreign_source);
    });
    completion_mutation(&result, source, |nodes| {
        let Some(Payload::Expression { bindings, .. }) = &mut nodes[source].payload else {
            unreachable!()
        };
        bindings[0].name = "other".into();
    });
}

#[test]
fn reservations_chain_rejects_equal_intermediate_reference_from_another_occurrence() {
    let result = reservations_private_example(
        "view calls(e:Reserve):(Z,Z)=(e.to.free,e.to.free);",
        &["current=evaluate(Reservations.calls,e=@v/e)"],
        false,
    );
    assert_eq!(result.status(), "complete");
    let owners = reservations_private_evaluations(&result, "e.to");
    assert_eq!(owners.len(), 2);
    let (first_source, first_value, _) = reservations_private_parts(&result, owners[0]);
    let (second_source, second_value, _) = reservations_private_parts(&result, owners[1]);
    assert_ne!(first_source, second_source);
    assert_ne!(first_value, second_value);
    assert_eq!(
        data_scalar_at(&result, first_value),
        data_scalar_at(&result, second_value)
    );
    completion_mutation(&result, owners[1], |nodes| {
        let Some(Payload::Evaluation { value, parts, .. }) = &mut nodes[owners[1]].payload else {
            unreachable!()
        };
        *value = Some(NodeRef(first_value));
        parts[0].value = Some(NodeRef(first_value));
        *nodes[owners[1]].arguments.last_mut().unwrap() = NodeRef(first_value);
    });
}

#[test]
fn reservations_chain_missing_and_counterexample_recheck_original_fact_and_evidence() {
    let missing = reservations_private_example(
        "view current(e:Reserve):Z=e.to.held;",
        &["current=evaluate(Reservations.current,e=@v/e)"],
        true,
    );
    assert_eq!(missing.status(), "partial");
    let target = reservations_private_evaluations(&missing, "e.to.held")[0];
    assert!(
        missing.nodes[target]
            .reasons
            .iter()
            .any(
                |reason| reason.missing.iter().any(|fact| fact.snapshot == "v"
                    && fact.subject == "q"
                    && fact.field.as_deref() == Some("Reservations.State.held"))
            )
    );
    completion_mutation(&missing, target, |nodes| {
        nodes[target].reasons[0].missing[0].subject = "p".into();
    });
    completion_mutation(&missing, target, |nodes| {
        nodes[target].reasons[0].dependencies.clear();
    });
    completion_mutation(&missing, target, |nodes| {
        nodes[target].reasons[0].location = Some(Location::Law { span: (0, 1) });
    });
    let result = reservations_private_example(
        "law required current(e:Reserve): e.to.free = 0;",
        &["current=check(Reservations.current,e=@v/e)"],
        false,
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let evidence = result.answers[0]
        .evidence
        .iter()
        .find(|r| {
            matches!(
                &result.nodes[r.0].payload,
                Some(Payload::EvaluationEvidence { .. })
            )
        })
        .unwrap()
        .0;
    let counter = result.answers[0]
        .evidence
        .iter()
        .find(|r| {
            matches!(
                &result.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )
        })
        .unwrap()
        .0;
    completion_mutation(&result, evidence, |nodes| {
        let Some(Payload::EvaluationEvidence { lhs, rhs, .. }) = &mut nodes[evidence].payload
        else {
            unreachable!()
        };
        std::mem::swap(lhs, rhs);
    });
    completion_mutation(&result, counter, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counter].payload else {
            unreachable!()
        };
        facts.pop();
    });
}

fn reservations_private_stop_usage(
    kind: usize,
) -> (
    super::super::control::Limits,
    super::super::control::Usage,
    StopReason,
) {
    use super::super::control::{Limits, Resource, Usage};
    match kind {
        0 => (
            Limits::default(),
            Usage {
                signal: Some(crate::result::Signal::Term),
                ..Usage::default()
            },
            StopReason::Cancelled(crate::result::Signal::Term),
        ),
        1 => (
            Limits {
                time_ms: Some(3),
                memory_mib: None,
            },
            Usage {
                elapsed_ms: 4,
                ..Usage::default()
            },
            StopReason::BudgetExhausted {
                resource: Resource::TimeMs,
                limit: 3,
                observed: 4,
            },
        ),
        _ => (
            Limits {
                time_ms: None,
                memory_mib: Some(7),
            },
            Usage {
                memory_mib: 8,
                ..Usage::default()
            },
            StopReason::BudgetExhausted {
                resource: Resource::MemoryMib,
                limit: 7,
                observed: 8,
            },
        ),
    }
}

fn reservations_private_phase_stop(phase: &'static str, at: usize, kind: usize) {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let body = "view seed():Unit=unit; law required prior(e:Reserve):e.from.free=0; view hole(e:Reserve):Z=e.to.held; view current(e:Reserve):Z=e.to.free;";
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior,e=@v/e)",
        "hole=evaluate(Reservations.hole,e=@v/e)",
        "current=evaluate(Reservations.current,e=@v/e)",
        "later=evaluate(Reservations.seed)",
    ];
    let inputs = reservations_private_fixture(body, true);
    let mut quiet = named_call_quiet();
    let prepared = prepare_observed(inputs.clone(), &asks, &mut quiet).unwrap();
    let Signature::View { body, .. } =
        &prepared.inputs().law().declarations["Reservations.current"].signature
    else {
        unreachable!()
    };
    let target = prepared.inputs().law().exprs[*body].span;
    let normal = evaluate_observed(prepared, &mut quiet).unwrap();
    assert_eq!(normal.status(), "partial", "{:?}", normal.issues);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert!(!normal.answers[1].evidence.is_empty());
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert!(
        normal.answers[2]
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Reservations.State.held"))
    );
    assert_eq!(normal.answers[3].status, Decision::Established);
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let seen = Rc::new(Cell::new(false));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |checkpoint| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(checkpoint, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Usage::default()
        }
    });
    let prepared = prepare_observed(inputs, &asks, &mut control).unwrap();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "hole" && phase != "answer" {
                let (arm, observed) = (armed.clone(), seen.clone());
                data::observe_iterations(move |span, context, operation, index| {
                    if context.request == 3 && span == target && operation == phase && index == at {
                        assert!(!observed.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && phase == "answer" {
                assert!(!seen.replace(true));
                armed.set(true);
            }
            Ok(())
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    let Json::Obj(ref normal_wire) = normal.wire() else {
        unreachable!()
    };
    let Json::Arr(normal_answers) = &normal_wire["answers"] else {
        unreachable!()
    };
    let Json::Obj(ref stopped_wire) = stopped.wire() else {
        unreachable!()
    };
    let Json::Arr(stopped_answers) = &stopped_wire["answers"] else {
        unreachable!()
    };
    let Json::Arr(normal_nodes) = &normal_wire["nodes"] else {
        unreachable!()
    };
    let Json::Arr(stopped_nodes) = &stopped_wire["nodes"] else {
        unreachable!()
    };
    assert_eq!(stopped_nodes.len(), stopped.nodes.len());
    assert_eq!(
        stopped_nodes.as_slice(),
        &normal_nodes[..stopped.nodes.len()]
    );
    assert_eq!(stopped.contexts.len(), stopped.nodes.len());
    assert_eq!(
        stopped.contexts.as_slice(),
        &normal.contexts[..stopped.nodes.len()]
    );
    // この固定fixtureは呼出し・量化・有限補完を使わない。停止が未生成の
    // frame/case等を追加しないことも、通常baselineと合わせて確認する。
    for result in [&normal, &stopped] {
        assert!(result.frames.is_empty());
        assert!(result.iterations.is_empty());
        assert!(result.instances.is_empty());
        assert!(result.cases.is_empty());
        assert!(result.universal_witnesses.is_empty());
    }
    let retained = if phase == "answer" { 4 } else { 3 };
    assert_eq!(&stopped_answers[..retained], &normal_answers[..retained]);
    for answer in &stopped.answers[retained..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty());
        assert!(answer.evidence.is_empty());
        let reason = answer
            .reasons
            .iter()
            .find(|reason| matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected))
            .unwrap();
        let Json::Obj(ref reason_wire) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected_wire) = expected.wire() else {
            unreachable!()
        };
        assert_eq!(reason_wire["details"], expected_wire["details"]);
    }
    if phase != "answer" {
        assert!(stopped.nodes.iter().enumerate().any(
            |(index, node)| stopped.contexts[index].request == 3
                && matches!(&node.payload, Some(Payload::Expression { .. }))
                && reservations_private_text(&stopped, NodeRef(index)) == "e.to"
        ));
        let current_evaluations: Vec<_> = reservations_private_evaluations(&stopped, "e.to")
            .into_iter()
            .filter(|i| stopped.contexts[*i].request == 3)
            .collect();
        assert_eq!(
            current_evaluations.len(),
            usize::from(phase == "field_evaluate")
        );
        let final_evaluations: Vec<_> = reservations_private_evaluations(&stopped, "e.to.free")
            .into_iter()
            .filter(|i| stopped.contexts[*i].request == 3)
            .collect();
        assert_eq!(
            final_evaluations.len(),
            usize::from(phase == "field_evaluate" && at == 2)
        );
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, node)| stopped.contexts[i].request == 3
                    && matches!(
                        &node.payload,
                        Some(
                            Payload::Counterexample { .. }
                                | Payload::EvaluationEvidence { .. }
                                | Payload::FiniteExhaustion { .. }
                        )
                    ))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}

#[test]
fn reservations_chain_prepare_cancel_retains_completed_source_prefix() {
    reservations_private_phase_stop("field_prepare", 1, 0);
}
#[test]
fn reservations_chain_evaluate_time_stop_retains_completed_reference_prefix() {
    reservations_private_phase_stop("field_evaluate", 1, 1);
}
#[test]
fn reservations_chain_evaluate_memory_stop_retains_completed_leaf_prefix() {
    reservations_private_phase_stop("field_evaluate", 2, 2);
}
#[test]
fn reservations_chain_post_validation_cancel_retains_verified_current_value() {
    reservations_private_phase_stop("answer", 0, 0);
}

#[test]
fn reservations_chain_recheck_stop_and_success_memo_remain_session_local() {
    use super::super::control::Usage;
    use std::{cell::Cell, rc::Rc};
    let result = reservations_private_example(
        "view current(e:Reserve):Z=e.to.free;",
        &["current=evaluate(Reservations.current,e=@v/e)"],
        false,
    );
    let evaluation = reservations_private_evaluations(&result, "e.to.free")[0];
    let (_, scalar, child) = reservations_private_parts(&result, evaluation);
    let (owner, _, _) = reservations_private_parts(&result, child);
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=scalar]).unwrap();
    let mut quiet = named_call_quiet();
    let environment = Environment::new(result.prepared.inputs(), &mut quiet).unwrap();
    environment
        .recheck_node(&graph, &graph.nodes[scalar], scalar)
        .unwrap();
    let scope = graph.nodes[owner].scope.clone();
    assert!(graph.nodes[owner].scope.readings.insert("Foreign".into()));
    assert!(matches!(
        environment.recheck_node(&graph, &graph.nodes[scalar], scalar),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[owner].scope = scope;
    environment
        .recheck_node(&graph, &graph.nodes[scalar], scalar)
        .unwrap();
    let before = format!(
        "{:?}",
        (&graph.nodes, &graph.contexts, &graph.frames, &graph.cases)
    );
    for kind in 0..3 {
        let (limits, usage, expected) = reservations_private_stop_usage(kind);
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let mut control = Control::new(limits, move |checkpoint| {
            count.set(count.get() + 1);
            if arm.replace(false) {
                assert_eq!(checkpoint, Checkpoint::FiniteIteration);
                usage
            } else {
                Usage::default()
            }
        });
        let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
        environment
            .recheck_node(&graph, &graph.nodes[scalar], scalar)
            .unwrap();
        let baseline = probes.get();
        armed.set(true);
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[scalar],scalar),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(probes.get(), baseline + 1);
        assert_eq!(control.stop_reason(), Some(expected.clone()));
        assert!(
            matches!(environment.recheck_node(&graph,&graph.nodes[scalar],scalar),Err(ValidationFailure::Stop(actual)) if actual==expected)
        );
        assert_eq!(probes.get(), baseline + 1);
        assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(probes.get(), baseline + 1);
        assert_eq!(
            format!(
                "{:?}",
                (&graph.nodes, &graph.contexts, &graph.frames, &graph.cases)
            ),
            before
        );
    }
}
