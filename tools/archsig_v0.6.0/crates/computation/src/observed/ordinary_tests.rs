#[test]
fn ordinary_actual_children_static_source_and_cold_mutations() {
    use std::{cell::Cell, rc::Rc};
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    data::observe_iterations(move |_, _, phase, _| {
        if phase == "ordinary_source" {
            seen.set(seen.get() + 1);
        }
    });
    let result = evaluate_observed_bytes(
        affine_private_fixture("view current(s:Sample):Bool=let held=s.p in if held then (true and not false) else (false or true);"),
        &["current=evaluate(Calc.current,s=@v/sample)"], &quiet()).unwrap();
    data::clear_iteration_observer();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    assert!(count.get() > 0);
    assert!(
        result.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let target = result.nodes.iter().position(|n| n.rule == Rule::Construction("ordinary_evaluation") && matches!(&n.payload, Some(Payload::Evaluation { parts, .. }) if parts[0].children.len() == 3)).unwrap();
    rejects_mutated_prefix(&result, target, |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[target].payload else {
            unreachable!()
        };
        parts[0].children.swap(1, 2);
    });
    rejects_mutated_prefix(&result, target, |nodes| {
        nodes[target].scope.readings.clear();
    });
    let source = result
        .nodes
        .iter()
        .position(|n| matches!(n.rule, Rule::OrdinarySource(_)))
        .unwrap();
    assert!(
        result.nodes[source]
            .support
            .is_empty(&archsig_common::control::Control::unlimited())
            .unwrap()
    );
    rejects_mutated_prefix(&result, source, |nodes| {
        nodes[source].scope.readings.clear();
    });
    let scalar = result
        .nodes
        .iter()
        .position(|n| {
            matches!(n.rule, Rule::OrdinaryValue(_))
                && matches!(n.scalar_payload(), Some(Scalar::Bool(_)))
        })
        .unwrap();
    rejects_mutated_prefix(&result, scalar, |nodes| {
        let Some(Scalar::Bool(value)) = nodes[scalar].scalar_payload_mut() else {
            unreachable!()
        };
        *value = !*value;
    });
}

#[test]
fn ordinary_actual_post_commit_stops_preserve_completed_producers() {
    use std::{cell::Cell, rc::Rc};
    for signal in [Signal::Int, Signal::Term] {
        for phase in ["ordinary_scalar", "ordinary_evaluation"] {
            let armed = Rc::new(Cell::new(false));
            let arm = armed.clone();
            let control = Control::new(move |_| {
                if arm.replace(false) {
                    Some(signal)
                } else {
                    None
                }
            });
            let sources = affine_private_fixture("view seed():Z=7; view current():Bool=not false;");
            let prepared = prepare_observed(
                sources,
                &["seed=evaluate(Calc.seed)", "current=evaluate(Calc.current)"],
                &control,
            )
            .unwrap();
            let Signature::View { body, .. } =
                prepared.inputs().law().declarations()["Calc.current"].signature
            else {
                unreachable!()
            };
            let target = prepared.inputs().law().exprs()[body].span;
            let arm = armed.clone();
            data::observe_iterations(move |span, context, operation, _| {
                if span == target && context.request == 1 && operation == phase {
                    arm.set(true);
                }
            });
            let stopped = evaluate_observed(prepared, &control).unwrap();
            data::clear_iteration_observer();
            assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
            assert_eq!(control.stop_reason(), Some(signal));
            assert_eq!(stopped.answers[0].status, Decision::Established);
            let evaluations = stopped.nodes.iter().filter(|node| node.rule == Rule::Construction("ordinary_evaluation") && matches!(&node.payload, Some(Payload::Evaluation { parts, .. }) if parts[0].location == Location::Law { span: target })).count();
            assert_eq!(evaluations, usize::from(phase == "ordinary_evaluation"));
            rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        }
    }
}

#[test]
fn ordinary_actual_case_and_call_frames_use_static_sources() {
    let cases = evaluate_observed_bytes(
        affine_private_fixture("law required current(s:Sample):s.p or not s.p;"),
        &["current=check(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    assert_ne!(cases.status(), "error", "{:?}", cases.issues);
    assert!(
        cases
            .nodes
            .iter()
            .zip(&cases.contexts)
            .any(|(node, context)| context.case.is_some()
                && matches!(node.rule, Rule::OrdinarySource(_)))
    );
    for (node, context) in cases.nodes.iter().zip(&cases.contexts) {
        if context.case.is_some() && matches!(node.rule, Rule::OrdinarySource(_)) {
            assert!(
                node.support
                    .is_empty(&archsig_common::control::Control::unlimited())
                    .unwrap()
            );
            assert!(node.reasons.is_empty());
            // Case自体のcompletion入力依存は残す。各式のfield読取りは先取りしない。
            for (other, other_context) in cases.nodes.iter().zip(&cases.contexts) {
                if other_context == context && matches!(other.rule, Rule::OrdinarySource(_)) {
                    assert_eq!(node.scope, other.scope);
                }
            }
        }
    }
    rebuild_for_origin_and_support_recheck(&cases, &cases.nodes).unwrap();
    let calls = owned_call_result(&["current=evaluate(Reservations.parameter,a=@v/A,s=@v/p)"]);
    assert!(
        calls
            .nodes
            .iter()
            .zip(&calls.contexts)
            .any(|(node, context)| context.frame.is_some()
                && matches!(node.rule, Rule::OrdinarySource(_)))
    );
    rebuild_for_origin_and_support_recheck(&calls, &calls.nodes).unwrap();
}

#[test]
fn ordinary_actual_and_cold_validation_preserve_read_collectors() {
    use std::collections::BTreeSet;
    let control = quiet();
    let prepared = prepare_observed(
        affine_private_fixture(
            "view seed():Bool=true; view current(s:Sample):Bool=let held=s.p in (held and true);",
        ),
        &[
            "seed=evaluate(Calc.seed)",
            "current=evaluate(Calc.current,s=@v/sample)",
        ],
        &control,
    )
    .unwrap();
    let expected = BTreeSet::from([Fact::from(archsig_input::archmap::FactData {
        snapshot: "v".into(),
        subject: "sample".into(),
        field: Some("Affine.Sample.p".into()),
        atom: None,
    })]);
    let mut captured = None;
    let result = evaluate_observed_with_validator(
        prepared,
        &control,
        |environment, graph, request, answer| {
            if request.id == "current" {
                captured = Some(environment.ordinary_test_read_collectors(None, None));
            }
            environment.validate_answer(graph, request, answer)?;
            if request.id == "seed" {
                environment
                    .ordinary_test_read_collectors(Some(BTreeSet::new()), Some(BTreeSet::new()));
            }
            Ok(())
        },
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    let (primitive, missing) = captured.expect("通常実行のcollector");
    assert_eq!(primitive, Some(expected.clone()));
    assert_eq!(missing, Some(expected.clone()));
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    let mut graph = Graph::new(&control);
    graph.requests = result.prepared.requests().requests().to_vec();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    environment.ordinary_test_read_collectors(Some(BTreeSet::new()), Some(BTreeSet::new()));
    for (index, node) in result.nodes.iter().enumerate() {
        graph.active = result.contexts[index];
        environment.validate(&graph, node).unwrap();
        graph.push(node.clone()).unwrap();
    }
    let (primitive, missing) = environment.ordinary_test_read_collectors(None, None);
    assert_eq!(primitive, Some(expected.clone()));
    assert_eq!(missing, Some(expected.clone()));
    // collector無しで実RHSを含むaliasをchecked/recheckedへ入れた後、
    // 新collectorで同じ実ref経路へ降りてleaf readが再び得られることを確認する。
    let alias = result.nodes.iter().enumerate().rev().find_map(|(index, node)| {
        (node.rule == Rule::Construction("alias_evaluation") && matches!(&node.payload, Some(Payload::Evaluation { parts, .. }) if parts[0].children.len()==1)).then_some(index)
    }).expect("実let RHSを保持するalias");
    environment
        .recheck_node(&graph, graph.get(NodeRef(alias)).unwrap(), alias)
        .unwrap();
    environment.ordinary_test_read_collectors(Some(BTreeSet::new()), Some(BTreeSet::new()));
    environment
        .recheck_node(&graph, graph.get(NodeRef(alias)).unwrap(), alias)
        .unwrap();
    let (primitive, missing) = environment.ordinary_test_read_collectors(None, None);
    assert_eq!(primitive, Some(expected.clone()));
    assert_eq!(missing, Some(expected));
}

#[test]
fn ordinary_cold_recheck_rejects_foreign_frame_request_and_missing_fact() {
    let mut calls = owned_call_result(&[
        "first=evaluate(Reservations.parameter,a=@v/A,s=@v/p)",
        "second=evaluate(Reservations.parameter,a=@v/A,s=@v/p)",
    ]);
    rebuild_for_origin_and_support_recheck(&calls, &calls.nodes).unwrap();
    let target = calls
        .nodes
        .iter()
        .zip(&calls.contexts)
        .position(|(node, context)| {
            context.request == 0
                && context.frame.is_some()
                && matches!(node.rule, Rule::OrdinarySource(_))
        })
        .unwrap();
    let original = calls.contexts[target];
    calls.contexts[target].request = 1;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&calls, &calls.nodes[..=target]),
        Err(ValidationFailure::Internal(_))
    ));
    calls.contexts[target] = original;
    rebuild_for_origin_and_support_recheck(&calls, &calls.nodes).unwrap();
    let missing = affine_private_example(
        "view current(s:Sample):Bool=not s.p;",
        &["current=evaluate(Calc.current,s=@v/sample)"],
    );
    let target = missing
        .nodes
        .iter()
        .position(|node| {
            node.rule == Rule::Construction("ordinary_evaluation")
                && node.reasons.iter().any(|r| !r.missing.is_empty())
        })
        .unwrap();
    rejects_mutated_prefix(&missing, target, |nodes| {
        nodes[target]
            .reasons
            .iter_mut()
            .find(|r| !r.missing.is_empty())
            .unwrap()
            .missing[0]
            .field = Some("Affine.Sample.absent".into());
    });
}

#[test]
fn field_read_retains_missing_before_supported_or_scalar_stop() {
    use std::{cell::Cell, rc::Rc};
    for signal in [Signal::Int, Signal::Term] {
        let armed = Rc::new(Cell::new(false));
        let trigger = armed.clone();
        let control = Control::new(move |_| {
            if trigger.replace(false) {
                Some(signal)
            } else {
                None
            }
        });
        let prepared = prepare_observed(
            affine_private_fixture("view current(s:Sample):Bool=s.p;"),
            &["current=evaluate(Calc.current,s=@v/sample)"],
            &control,
        )
        .unwrap();
        let arm = armed.clone();
        data::observe_iterations(move |_, _, phase, _| {
            if phase == "field_read" {
                arm.set(true);
            }
        });
        let stopped = evaluate_observed(prepared, &control).unwrap();
        data::clear_iteration_observer();
        assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
        assert!(stopped.answers[0].scope.completions);
        let missing = stopped.answers[0]
            .reasons
            .iter()
            .find(|reason| reason.kind == ReasonKind::Missing)
            .expect("actual field Missing survives Stop");
        assert_eq!(missing.request, "current");
        assert_eq!(missing.missing.len(), 1);
        assert_eq!(missing.missing[0].field.as_deref(), Some("Affine.Sample.p"));
        assert_eq!(missing.missing[0].atom, None);
        assert_eq!(missing.dependencies.len(), 1);
        let source = &stopped.nodes[missing.dependencies[0].0];
        assert!(matches!(source.rule, Rule::FieldSource(_)));
        assert!(
            matches!(&source.payload, Some(Payload::Expression { location, .. }) if Some(location)==missing.location.as_ref())
        );
        assert!(!stopped.nodes.iter().any(|node| matches!(
            node.rule,
            Rule::FieldValue { .. } | Rule::Construction("field_evaluation")
        )));
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    }
}

#[test]
fn field_actual_base_and_leaf_scope_reject_cold_mutations() {
    let result = evaluate_observed_bytes(
        numeric_recheck_fixture(&[], "view current(s:Sample):Q=(s.q);"),
        &["current=evaluate(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let scalar = result
        .nodes
        .iter()
        .position(|node| matches!(node.rule, Rule::FieldValue { .. }))
        .expect("new field Scalar producer");
    assert_eq!(result.nodes[scalar].support.materialize_for_test().len(), 1);
    let read_source = result.nodes[scalar].arguments[0].0;
    assert!(matches!(
        result.nodes[read_source].rule,
        Rule::FieldSource(_)
    ));
    rejects_mutated_prefix(&result, read_source, |nodes| {
        nodes[read_source].scope.snapshots.clear();
    });
    let Rule::FieldValue {
        kind: "atom",
        location: Some(location),
    } = &result.nodes[scalar].rule
    else {
        panic!("observed field keeps original atom pointer provenance")
    };
    let observed_field = result
        .prepared
        .inputs()
        .archmap()
        .snapshots()
        .iter()
        .flat_map(|snapshot| &snapshot.subjects)
        .flat_map(|subject| &subject.fields)
        .find(|field| field.name == "Numeric.Sample.q")
        .unwrap();
    let Slot::Known { pointer, .. } = &observed_field.slot else {
        unreachable!()
    };
    assert_eq!(
        location,
        &Location::ArchMap {
            pointer: pointer.clone(),
            span: None
        }
    );
    let mut legacy_wire = result.nodes[scalar].clone();
    let base = result.nodes[scalar].arguments[1];
    let Some(Payload::Evaluation {
        value: Some(owner), ..
    }) = &result.nodes[base.0].payload
    else {
        unreachable!()
    };
    legacy_wire.arguments = vec![*owner];
    legacy_wire.rule = Rule::Input {
        kind: "atom",
        location: location.clone(),
    };
    assert_eq!(
        result.nodes[scalar].wire(scalar, &result.nodes[..scalar]),
        legacy_wire.wire(scalar, &result.nodes[..scalar])
    );
    rejects_mutated_prefix(&result, scalar, |nodes| {
        nodes[scalar].scope.readings.clear();
    });
    rejects_mutated_prefix(&result, scalar, |nodes| {
        nodes[scalar].arguments.swap(0, 1);
    });
    rejects_mutated_prefix(&result, scalar, |nodes| {
        nodes[scalar].support = Support::default();
    });
    let evaluation = result
        .nodes
        .iter()
        .position(|node| node.rule == Rule::Construction("field_evaluation"))
        .unwrap();
    rejects_mutated_prefix(&result, evaluation, |nodes| {
        nodes[evaluation].reasons.push(Reason {
            kind: ReasonKind::Missing,
            request: "current".into(),
            dependencies: vec![NodeRef(0)],
            missing: vec![],
            location: None,
        });
    });
}

#[test]
fn static_aliases_keep_actual_formal_and_missing_let_producers() {
    let result = evaluate_observed_bytes(
        affine_private_fixture(
            "view relay(s:Sample):Sample=s; view current(a:Sample,b:Sample):Sample=relay(b);",
        ),
        &["current=evaluate(Calc.current,a=@v/sample,b=@v2/sample)"],
        &quiet(),
    )
    .unwrap_or_else(|failure| panic!("{:?}", failure.wire()));
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let output = data_scalar_at(&result, result.answers[0].outputs["value"].0);
    assert!(matches!(output, Scalar::Subject { snapshot, .. } if snapshot=="v2"));
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let formal = result
        .nodes
        .iter()
        .enumerate()
        .find(|(index, node)| {
            result.contexts[*index].frame.is_some()
                && node.rule == Rule::Construction("alias_evaluation")
        })
        .map(|(index, _)| index)
        .expect("formal alias uses actual caller input");
    rejects_mutated_prefix(&result, formal, |nodes| {
        nodes[formal].scope.snapshots.clear();
    });
    let missing = evaluate_observed_bytes(
        affine_private_fixture("view current(s:Sample):Bool=let held=s.p in held;"),
        &["current=evaluate(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    assert_ne!(missing.status(), "error", "{:?}", missing.issues);
    assert!(
        missing.answers[0]
            .reasons
            .iter()
            .any(|reason| reason.kind == ReasonKind::Missing)
    );
    assert!(missing.nodes.iter().any(|node| node.rule==Rule::Construction("alias_evaluation") && matches!(&node.payload,Some(Payload::Evaluation { value:None,parts,.. }) if parts[0].children.len()==1)));
    rebuild_for_origin_and_support_recheck(&missing, &missing.nodes).unwrap();
}

#[test]
fn ordinary_comparison_known_values_keep_real_counterexample_operands() {
    let r = evaluate_observed_bytes(
        affine_private_fixture(r#"view current(s:Sample):Bool=some(rat(1,2))=some(rat(1,2)); law required bad(s:Sample):"left"="right"; view unequal(s:Sample):Bool=some(rat(1,2))!=some(rat(2,3));"#),
        &["same=evaluate(Calc.current,s=@v/sample)", "different=check(Calc.bad,s=@v/sample)", "unequal=evaluate(Calc.unequal,s=@v/sample)"],
        &quiet(),
    ).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    assert_eq!(r.answers[0].status, Decision::Established);
    assert_eq!(r.answers[1].status, Decision::Refuted);
    assert_eq!(r.answers[2].status, Decision::Established);
    assert!(r.nodes.iter().any(|node| {
        let Some(Payload::Counterexample { left, right, .. }) = &node.payload else {
            return false;
        };
        matches!((r.nodes[left.0].scalar_payload(), r.nodes[right.0].scalar_payload()),
            (Some(Scalar::Text(a)), Some(Scalar::Text(b))) if a == "left" && b == "right")
    }));
    for (index, node) in r
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| matches!(node.rule, Rule::OperandValue(_)))
    {
        let [_, left, right] = node.arguments.as_slice() else {
            panic!("internal actual operands")
        };
        let scalar = |r0: NodeRef| {
            let Some(Payload::Evaluation {
                value: Some(value), ..
            }) = &r.nodes[r0.0].payload
            else {
                panic!("actual operand value")
            };
            *value
        };
        let mut legacy = node.clone();
        let Rule::OperandValue(location) = &node.rule else {
            unreachable!()
        };
        legacy.rule = Rule::Input {
            kind: "law",
            location: location.clone(),
        };
        legacy.arguments = vec![scalar(*left), scalar(*right)];
        assert_eq!(
            node.wire(index, &r.nodes[..index]),
            legacy.wire(index, &r.nodes[..index])
        );
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let index = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            if node.rule != Rule::Construction("ordinary_evaluation") {
                return None;
            }
            let Some(Payload::Evaluation { parts, .. }) = &node.payload else {
                return None;
            };
            (parts[0].children.len() == 2).then_some(index)
        })
        .unwrap();
    rejects_mutated_prefix(&r, index, |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[index].payload else {
            unreachable!()
        };
        parts[0].children.swap(0, 1);
    });
}

#[test]
fn ordinary_map_hit_and_legacy_domain_miss_keep_actual_children() {
    let hit = application_result(&["hit=evaluate(Applications.apply,m=@v/m,x=@v/p)"], "known");
    assert_ne!(hit.status(), "error", "{:?}", hit.issues);
    assert_eq!(hit.answers[0].status, Decision::Established);
    let index = hit.answers[0].outputs["evaluation"].0;
    assert_eq!(
        hit.nodes[index].rule,
        Rule::Construction("ordinary_evaluation")
    );
    let value = hit.answers[0].outputs["value"];
    let node = &hit.nodes[value.0];
    let [_, map, key] = node.arguments.as_slice() else {
        panic!("internal Map operands")
    };
    let operand_value = |r0: NodeRef| {
        let Some(Payload::Evaluation {
            value: Some(value), ..
        }) = &hit.nodes[r0.0].payload
        else {
            panic!("actual Map operand value")
        };
        *value
    };
    let Rule::OperandValue(location) = &node.rule else {
        panic!("Map operand projection rule")
    };
    let mut legacy = node.clone();
    legacy.rule = Rule::Input {
        kind: "law",
        location: location.clone(),
    };
    legacy.arguments = vec![operand_value(*map), operand_value(*key)];
    assert!(matches!(
        hit.nodes[legacy.arguments[0].0].scalar_payload(),
        Some(Scalar::Map { .. })
    ));
    assert!(matches!(
        hit.nodes[legacy.arguments[1].0].scalar_payload(),
        Some(Scalar::Subject { .. })
    ));
    assert_eq!(
        node.wire(value.0, &hit.nodes[..value.0]),
        legacy.wire(value.0, &hit.nodes[..value.0])
    );
    rebuild_for_origin_and_support_recheck(&hit, &hit.nodes).unwrap();
    rejects_mutated_prefix(&hit, index, |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[index].payload else {
            unreachable!()
        };
        parts[0].children.swap(0, 1);
    });
    let miss = application_result(
        &["miss=evaluate(Applications.apply,m=@v/m,x=@v/r)"],
        "known",
    );
    assert_ne!(miss.status(), "error", "{:?}", miss.issues);
    assert_eq!(miss.answers[0].status, Decision::Undetermined);
    assert!(
        miss.nodes
            .iter()
            .any(|node| matches!(node.payload, Some(Payload::MapDomainCondition { .. })))
    );
    assert!(
        miss.answers[0]
            .reasons
            .iter()
            .any(|reason| matches!(reason.kind, ReasonKind::ConditionFailed { .. }))
    );
    rebuild_for_origin_and_support_recheck(&miss, &miss.nodes).unwrap();
}

#[test]
fn ordinary_comparison_type_selection_propagates_stop() {
    use std::{cell::Cell, rc::Rc};
    let prepared = prepare_observed(
        affine_private_fixture("view current(s:Sample):Bool=some(rat(1,2))=some(rat(1,2));"),
        &["current=evaluate(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    let Signature::View { body, .. } =
        &prepared.inputs().law().declarations()["Calc.current"].signature
    else {
        unreachable!()
    };
    for signal in [Signal::Int, Signal::Term] {
        let active = Rc::new(Cell::new(false));
        let observed = active.clone();
        let control = Control::new(move |_| observed.get().then_some(signal));
        let environment = Environment::with_prepared(&prepared, &control).unwrap();
        let graph = Graph::new(&control);
        active.set(true);
        assert!(
            matches!(environment.ordinary_children(&graph, *body), Err(ValidationFailure::Stop(actual)) if actual == signal)
        );
    }
}

#[test]
fn ordinary_fallback_post_root_stop_retains_evaluation_and_does_not_repeat_children() {
    use std::{cell::Cell, rc::Rc};
    struct Observer;
    impl Drop for Observer {
        fn drop(&mut self) {
            data::clear_iteration_observer();
        }
    }
    for map in [false, true] {
        for signal in [Signal::Int, Signal::Term] {
            let armed = Rc::new(Cell::new(false));
            let seen = Rc::new(Cell::new(false));
            let trigger = armed.clone();
            let control = Control::new(move |checkpoint| {
                (checkpoint == Checkpoint::Expression && trigger.replace(false)).then_some(signal)
            });
            let inputs = if map {
                application_fixture::owned("known")
            } else {
                affine_private_fixture("view seed():Z=7; view current(s:Sample):Bool=s.p=s.p;")
            };
            let asks = if map {
                [
                    "seed=evaluate(Applications.seed)",
                    "current=evaluate(Applications.apply,m=@v/m,x=@v/r)",
                    "later=evaluate(Applications.seed)",
                ]
            } else {
                [
                    "seed=evaluate(Calc.seed)",
                    "current=evaluate(Calc.current,s=@v/sample)",
                    "later=evaluate(Calc.seed)",
                ]
            };
            let prepared = prepare_observed(inputs, &asks, &control).unwrap();
            let name = if map {
                "Applications.apply"
            } else {
                "Calc.current"
            };
            let Signature::View { body, .. } =
                &prepared.inputs().law().declarations()[name].signature
            else {
                unreachable!()
            };
            let law = prepared.inputs().law();
            let span = law.exprs()[*body].span;
            let children = match &law.exprs()[*body].kind {
                ExprKind::Binary { lhs, rhs, .. } => {
                    vec![law.exprs()[*lhs].span, law.exprs()[*rhs].span]
                }
                ExprKind::Call { callee, args } => {
                    vec![law.exprs()[*callee].span, law.exprs()[args[0]].span]
                }
                _ => unreachable!(),
            };
            let trigger = armed.clone();
            let observed = seen.clone();
            data::observe_iterations(move |actual, context, phase, _| {
                if actual == span
                    && context.request == 1
                    && context.case.is_none()
                    && phase == "ordinary_fallback_evaluation"
                {
                    assert!(!observed.replace(true));
                    trigger.set(true);
                }
            });
            let observer = Observer;
            let stopped = evaluate_observed(prepared, &control).unwrap();
            drop(observer);
            assert!(seen.get());
            assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
            assert_eq!(control.stop_reason(), Some(signal));
            assert_eq!(stopped.answers[0].status, Decision::Established);
            let answer = &stopped.answers[1];
            let root = answer.outputs["evaluation"];
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(!answer.outputs.contains_key("value"));
            assert!(answer.claim.is_none() && answer.evidence.is_empty());
            let node = &stopped.nodes[root.0];
            assert_eq!(node.rule, Rule::Construction("evaluation"));
            let Some(Payload::Evaluation { value, parts, .. }) = &node.payload else {
                panic!("completed fallback root")
            };
            assert!(value.is_none());
            assert_eq!(parts[0].location, Location::Law { span });
            assert!(node.reasons.iter().any(|reason| if map {
                matches!(reason.kind, ReasonKind::ConditionFailed { .. })
            } else {
                matches!(reason.kind, ReasonKind::Missing)
            }));
            assert!(answer.scope.snapshots.contains("v"));
            assert!(stopped.answers[2].outputs.is_empty());
            assert_eq!(stopped.answers[2].status, Decision::Undetermined);
            assert!(!stopped.contexts.iter().any(|context| context.request == 2));
            for child_span in children {
                let count = stopped.nodes.iter().zip(&stopped.contexts).filter(|(node,context)| {
                    context.request == 1 && context.case.is_none()
                        && matches!(&node.payload, Some(Payload::Evaluation { parts, .. }) if parts.len() == 1 && parts[0].location == Location::Law { span: child_span })
                }).count();
                assert_eq!(count, 1, "fallback must consume each original child once");
            }
            rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        }
    }
}

#[test]
fn ordinary_reduction_consumes_values_without_graph_and_keeps_condition_state() {
    use super::super::environment::ordinary::ReducedValue as OrdinaryReducedValue;
    let control = quiet();
    let prepared = prepare_observed(
        affine_private_fixture(
            "view current():Bool=let ignored=true in if true then (true and false) else false;",
        ),
        &["current=evaluate(Calc.current)"],
        &control,
    )
    .unwrap();
    let environment =
        Environment::with_requests(prepared.inputs(), prepared.requests().requests(), &control)
            .unwrap();
    let law = prepared.inputs().law();
    let find = |predicate: fn(&ExprKind) -> bool| {
        law.exprs()
            .iter()
            .position(|expression| predicate(&expression.kind))
            .unwrap()
    };
    let branch = find(|kind| matches!(kind, ExprKind::If { .. }));
    let and = find(|kind| matches!(kind, ExprKind::Binary { op: BinOp::And, .. }));
    let group = find(|kind| matches!(kind, ExprKind::Group(_)));
    let local = find(|kind| matches!(kind, ExprKind::Let { .. }));
    let yes = Scalar::Bool(true);
    let no = Scalar::Bool(false);
    // Unselected pending and a known selected value remain distinct from a
    // pending selected branch. Neither case requires an Evaluation/Scalar node.
    let result = environment
        .ordinary_reduce(
            branch,
            3,
            |i| Ok([Some(&yes), Some(&no), None][i]),
            &[false, false, true],
        )
        .unwrap();
    assert!(matches!(
        result.value,
        OrdinaryReducedValue::Fresh(Scalar::Bool(false))
    ));
    let result = environment
        .ordinary_reduce(
            branch,
            3,
            |i| Ok([Some(&yes), None, Some(&no)][i]),
            &[false, true, false],
        )
        .unwrap();
    assert!(matches!(result.value, OrdinaryReducedValue::Unknown));
    let result = environment
        .ordinary_reduce(and, 2, |i| Ok([Some(&no), None][i]), &[false, true])
        .unwrap();
    assert!(matches!(
        result.value,
        OrdinaryReducedValue::Fresh(Scalar::Bool(false))
    ));
    let result = environment
        .ordinary_reduce(and, 2, |i| Ok([Some(&no), None][i]), &[false, true])
        .unwrap()
        .with_condition_failed(true);
    assert!(matches!(result.value, OrdinaryReducedValue::Unknown));
    let result = environment
        .ordinary_reduce(group, 1, |i| Ok([Some(&yes)][i]), &[false])
        .unwrap();
    assert!(matches!(result.value, OrdinaryReducedValue::Reuse(0)));
    let result = environment
        .ordinary_reduce(group, 1, |i| Ok([Some(&yes)][i]), &[true])
        .unwrap();
    assert!(matches!(result.value, OrdinaryReducedValue::Unknown));
    let result = environment
        .ordinary_reduce(
            local,
            2,
            |i| {
                assert_eq!(
                    i, 1,
                    "Let must not consume discarded native RHS as a Scalar"
                );
                Ok(Some(&yes))
            },
            &[false, false],
        )
        .unwrap();
    assert!(matches!(
        result.value,
        OrdinaryReducedValue::Fresh(Scalar::Bool(true))
    ));
    let result = environment
        .ordinary_reduce(and, 2, |_| Ok(None), &[false, false])
        .unwrap();
    assert!(matches!(result.value, OrdinaryReducedValue::Unknown));
    assert!(
        environment
            .ordinary_reduce(branch, 0, |i| Ok([][i]), &[])
            .is_err()
    );
}

#[test]
fn ordinary_live_value_accessor_is_not_used_before_source_cutoff_check() {
    let control = quiet();
    let prepared = prepare_observed(
        affine_private_fixture("view current():Bool=true and false;"),
        &["current=evaluate(Calc.current)"],
        &control,
    )
    .unwrap();
    let mut checked = false;
    let result = evaluate_observed_with_validator(
        prepared,
        &control,
        |environment, graph, request, answer| {
            let (source, children) = graph
                .nodes
                .iter()
                .rev()
                .find_map(|node| {
                    if node.rule != Rule::Construction("ordinary_evaluation") {
                        return None;
                    }
                    let Some(Payload::Evaluation {
                        expression, parts, ..
                    }) = &node.payload
                    else {
                        return None;
                    };
                    Some((*expression, &parts[0].children))
                })
                .unwrap();
            assert!(
                environment
                    .ordinary_plan_with_values(graph, source, children, source.0, |_| panic!(
                        "cutoff must reject before accessing runtime values"
                    ))
                    .is_err()
            );
            assert!(
                environment
                    .ordinary_plan(graph, source, children, source.0)
                    .is_err()
            );
            checked = true;
            environment.validate_answer(graph, request, answer)
        },
    )
    .unwrap();
    assert!(checked);
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    // The public/raw path derives values from Graph and rejects forged Scalars.
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let scalar = result
        .nodes
        .iter()
        .position(|node| matches!(node.rule, Rule::OrdinaryValue(_)))
        .unwrap();
    rejects_mutated_prefix(&result, scalar, |nodes| {
        let Some(Scalar::Bool(value)) = nodes[scalar].scalar_payload_mut() else {
            unreachable!()
        };
        *value = !*value;
    });
}

#[test]
fn ordinary_runtime_scalar_shares_storage_and_survives_trace_drop_with_cow_mutation() {
    use std::sync::Arc;
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Scalar>();
    send_sync::<RuntimeValue>();
    let control = quiet();
    let result = evaluate_observed_bytes(
        affine_private_fixture("view current():Bool=(true) and true;"),
        &["current=evaluate(Calc.current)"],
        &control,
    )
    .unwrap();
    let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let (group, child) = graph
        .nodes
        .iter()
        .find_map(|node| {
            if node.rule != Rule::Construction("ordinary_evaluation") {
                return None;
            }
            let Some(Payload::Evaluation {
                expression,
                parts,
                value: Some(value),
                ..
            }) = &node.payload
            else {
                return None;
            };
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &graph.nodes[expression.0].payload
            else {
                return None;
            };
            let law = result.prepared.inputs().law();
            let id = law.program().expressions.get(span)?;
            if !matches!(law.exprs()[*id].kind, ExprKind::Group(_)) {
                return None;
            }
            let Some(Payload::Evaluation {
                value: Some(child), ..
            }) = &graph.nodes[parts[0].children[0].0].payload
            else {
                return None;
            };
            Some((*value, *child))
        })
        .expect("Group and its actual producer");
    assert_eq!(
        group, child,
        "Group must retain the actual producer identity"
    );
    let live = RuntimeValue::from_recorded(&graph, Some(group)).unwrap();
    let RuntimeValue::Scalar { scalar, producer } = &live else {
        panic!("owned runtime Scalar")
    };
    let Some(Payload::Scalar(recorded)) = &graph.nodes[group.0].payload else {
        panic!("recorded Scalar")
    };
    assert!(Arc::ptr_eq(scalar, recorded));
    assert_eq!(*producer, group);
    let fresh = graph
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (index != group.0
                && matches!(node.rule, Rule::OrdinaryValue(_))
                && node.scalar_payload() == Some(&Scalar::Bool(true)))
            .then_some(NodeRef(index))
        })
        .expect("fresh equal literal producer");
    assert_ne!(fresh, group);
    let fresh_live = RuntimeValue::from_recorded(&graph, Some(fresh)).unwrap();
    assert_ne!(fresh_live.producer(), live.producer());
    let RuntimeValue::Scalar {
        scalar: fresh_scalar,
        ..
    } = &fresh_live
    else {
        panic!()
    };
    assert!(!Arc::ptr_eq(scalar, fresh_scalar));
    *graph.nodes[group.0].scalar_payload_mut().unwrap() = Scalar::Bool(false);
    assert_eq!(graph.scalar(group).unwrap(), &Scalar::Bool(false));
    assert_eq!(live.scalar(&graph).unwrap(), Some(&Scalar::Bool(true)));
    assert_eq!(
        result.nodes[group.0].scalar_payload(),
        Some(&Scalar::Bool(true))
    );
    assert!(rebuild_for_origin_and_support_recheck(&result, &graph.nodes).is_err());
    drop(graph);
    drop(result);
    assert_eq!(
        Arc::strong_count(scalar),
        1,
        "the live result is now the only Scalar owner"
    );
    let empty = Graph::new(&control);
    assert_eq!(
        live.scalar(&empty).unwrap(),
        Some(&Scalar::Bool(true)),
        "ordinary runtime Scalar must not dereference its dropped trace"
    );
    assert_eq!(live.producer(), Some(group));
}

#[test]
fn ordinary_binder_shares_scalar_contents_without_aliasing_member_producer() {
    use std::sync::Arc;
    let result = evaluate_observed_bytes(
        affine_private_fixture(
            "view current():Bool=forall bit in set<Bool>{true,false}.(bit or not bit);",
        ),
        &["current=evaluate(Calc.current)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let mut checked = 0;
    for (index, node) in result.nodes.iter().enumerate() {
        if !matches!(node.rule, Rule::BinderValue(_)) {
            continue;
        }
        let iteration = result.contexts[index].iteration.expect("binder iteration");
        let member = result.iterations[iteration]
            .producer
            .expect("actual member producer");
        assert_ne!(NodeRef(index), member, "binder's producer remains distinct");
        let (Some(Payload::Scalar(binder)), Some(Payload::Scalar(member_value))) =
            (&node.payload, &result.nodes[member.0].payload)
        else {
            panic!("Scalar producers")
        };
        assert!(
            Arc::ptr_eq(binder, member_value),
            "immutable contents can share storage"
        );
        checked += 1;
    }
    assert!(checked >= 2);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
}

#[test]
fn field_receiver_boundary_keeps_blocked_state_without_reading_a_slot() {
    use super::super::environment::field_read::{FieldPlan, FieldReceiver};
    let control = quiet();
    let prepared = prepare_observed(
        affine_private_fixture("view current(s:Sample):Bool=s.p;"),
        &["current=evaluate(Calc.current,s=@v/sample)"],
        &control,
    )
    .unwrap();
    let environment = Environment::with_prepared(&prepared, &control).unwrap();
    let mut source_scope = Scope::default();
    source_scope.readings.insert("source".into());
    let mut receiver_scope = Scope::default();
    receiver_scope.readings.insert("receiver".into());
    for (pending, failed) in [(true, false), (false, true), (false, false)] {
        let reasons = if failed {
            vec![Reason {
                kind: ReasonKind::ConditionFailed {
                    condition: NodeRef(900),
                    construction: "fixture",
                },
                request: "current".into(),
                dependencies: vec![],
                missing: vec![],
                location: None,
            }]
        } else {
            vec![]
        };
        let plan = FieldPlan {
            // No Graph owns these refs, and no field exists at this span.
            span: (0, 0),
            source: NodeRef(901),
            origin: NodeRef(901),
            position: None,
            child: NodeRef(902),
            ty: Type::Bool,
            value: None,
            reused: None,
            assigned: None,
            scope: source_scope.clone(),
            scalar_scope: source_scope.clone(),
            support: Support::default(),
            scalar_support: Support::default(),
            scalar_rule: None,
            reasons: reasons.clone(),
        };
        let mut retained = None;
        let result = environment.observe_field_receiver(
            plan,
            &"No.Owner.slot".into(),
            FieldReceiver {
                value: None,
                pending,
                scope: &receiver_scope,
                request: None,
            },
            |scope, reasons| {
                assert!(reasons.is_empty());
                retained = Some(scope.clone());
            },
        );
        if pending || failed {
            let plan = result.unwrap();
            assert_eq!(plan.reasons, reasons);
            assert!(plan.position.is_none());
            assert!(plan.value.is_none());
            assert_eq!(plan.scalar_scope, source_scope);
            assert!(plan.scope.readings.contains("source"));
            assert!(plan.scope.readings.contains("receiver"));
            assert_eq!(retained.as_ref(), Some(&plan.scope));
        } else {
            assert!(matches!(
                result,
                Err(ValidationFailure::UnsupportedExpression { .. })
            ));
            assert!(retained.is_none());
        }
    }
}

#[test]
fn ordinary_source_scope_only_keeps_unused_binding_authentication() {
    let result = evaluate_observed_bytes(
        numeric_recheck_fixture(&[], "view current(s:Sample):Bool=true;"),
        &["current=evaluate(Calc.current,s=@v/sample)"],
        &quiet(),
    )
    .unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let (source_index, original) = result.nodes.iter().enumerate().find(|(_, node)| {
        matches!(node.rule, Rule::OrdinarySource(_))
            && matches!(node.ty, NodeType::Expression(Type::Bool))
    }).unwrap();
    let Some(Payload::Expression { location: Location::Law { span }, bindings, .. }) = &original.payload else {
        unreachable!()
    };
    let control = quiet();
    let environment = Environment::with_prepared(&result.prepared, &control).unwrap();
    let mut graph = Graph::new(&control);
    graph.requests = result.prepared.requests().requests().to_vec();
    for (index, node) in result.nodes[..source_index].iter().enumerate() {
        graph.active = result.contexts[index];
        graph.push(node.clone()).unwrap();
    }
    graph.active = result.contexts[source_index];
    let build = |graph: &Graph, bindings: &[Binding]| {
        environment.ordinary_source_at(graph, *span, &Type::Bool, bindings)
    };
    assert_eq!(build(&graph, bindings).unwrap(), *original);
    assert!(original.scope.snapshots.contains("v"));
    // Even an unused parameter must keep its original signature and selector.
    let mut wrong = bindings.clone();
    wrong[0].ty = Type::Bool;
    assert!(matches!(build(&graph, &wrong), Err(ValidationFailure::Internal(_))));
    let selector = graph.requests[0].arguments[0].value.clone();
    graph.requests[0].arguments[0].value = Selector::Subject { snapshot: "v".into(), subject: "other".into() };
    assert!(matches!(build(&graph, bindings), Err(ValidationFailure::Internal(_))));
    graph.requests[0].arguments[0].value = selector;
    let producer = bindings[0].value;
    let scope = graph.nodes[producer.0].scope.clone();
    graph.nodes[producer.0].scope.snapshots.clear();
    assert!(matches!(build(&graph, bindings), Err(ValidationFailure::Internal(_))));
    graph.nodes[producer.0].scope = scope;
    assert_eq!(build(&graph, bindings).unwrap(), *original);
}

#[test]
fn ordinary_scalar_scope_preserves_fresh_unknown_and_reused_producer_roles() {
    for unknown in [false, true] {
        let omitted = if unknown { vec!["p"] } else { vec![] };
        let result = evaluate_observed_bytes(
            numeric_recheck_fixture(&omitted, "view seed():Bool=true; view current(s:Sample):Bool=not s.p; view grouped(s:Sample,b:Bool):Bool=(b);"),
            &["seed=evaluate(Calc.seed)", "current=evaluate(Calc.current,s=@v/sample)", "grouped=evaluate(Calc.grouped,s=@v/sample,b=$seed.value)"],
            &quiet(),
        ).unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        let control = quiet();
        let environment = Environment::with_prepared(&result.prepared, &control).unwrap();
        for name in ["Calc.current", "Calc.grouped"] {
            let Signature::View {body, ..} = &result.prepared.inputs().law().declarations()[name].signature else { unreachable!() };
            let span = result.prepared.inputs().law().exprs()[*body].span;
            let (index, source, children) = result.nodes.iter().enumerate().find_map(|(index,node)| {
                let Some(Payload::Evaluation {expression,parts,..}) = &node.payload else { return None; };
                (node.rule == Rule::Construction("ordinary_evaluation") && result.contexts[index].case.is_none()
                    && matches!(&result.nodes[expression.0].payload, Some(Payload::Expression {location:Location::Law{span:actual},..}) if *actual == span))
                    .then(|| (index,*expression,parts[0].children.clone()))
            }).unwrap();
            graph.active = result.contexts[index];
            let plan = environment.ordinary_plan(&graph, source, &children, index).unwrap();
            assert!(plan.scope.snapshots.contains("v"));
            if name == "Calc.grouped" {
                let producer = plan.value.reused().expect("Group keeps the selected producer");
                assert!(graph.get(producer).unwrap().scope.snapshots.is_empty());
                assert_eq!(plan.scalar_scope, graph.get(producer).unwrap().scope);
                assert_ne!(plan.scalar_scope, plan.scope);
            } else {
                assert!(if unknown { matches!(plan.value, super::super::environment::ordinary::PlannedValue::Unknown) }
                    else { matches!(plan.value, super::super::environment::ordinary::PlannedValue::Fresh(_)) });
                assert_eq!(plan.scalar_scope, plan.scope);
            }
        }
    }
}

#[test]
fn ordinary_iteration_prefix_is_committed_once_per_activation() {
    let result = evaluate_observed_bytes(
        numeric_recheck_fixture(&[], "view current(s:Sample):Bool=forall b in list<Bool>[false,true] . b or s.p;"),
        &["current=evaluate(Calc.current,s=@v/sample)"], &quiet(),
    ).unwrap();
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let binder = result.prepared.inputs().law().program().nodes.iter().find(|expr|
        matches!(&expr.kind, ExprKind::Dotted(parts) if parts.len() == 1 && parts[0].name == "b")
        && expr.ty.is_some()).unwrap().span;
    let sources: Vec<_> = result.nodes.iter().enumerate().filter_map(|(index,node)| {
        matches!(&node.rule, Rule::OrdinarySource(Location::Law{span}) if *span == binder)
            .then_some(result.contexts[index])
    }).collect();
    assert_eq!(sources.len(), 2, "one static origin for each of the two actual iterations");
    assert_ne!(sources[0].iteration, sources[1].iteration);
}

#[test]
fn ordinary_iteration_prefix_reuse_rejects_carriers_foreign_context_and_enriched_handles() {
    let result = evaluate_observed_bytes(
        numeric_recheck_fixture(&[], "view current(s:Sample):Bool=forall b in list<Bool>[false,true] . b or s.p;"),
        &["current=evaluate(Calc.current,s=@v/sample)"], &quiet(),
    ).unwrap();
    let law = result.prepared.inputs().law();
    let (id, binder) = law.program().nodes.iter().enumerate().find_map(|(id,expr)| {
        (matches!(&expr.kind, ExprKind::Dotted(parts) if parts.len() == 1 && parts[0].name == "b")
            && expr.ty.is_some()).then_some((id,expr.span))
    }).unwrap();
    let source_refs: Vec<_> = result.nodes.iter().enumerate().filter_map(|(index,node)| {
        matches!(&node.rule, Rule::OrdinarySource(Location::Law{span}) if *span == binder).then_some(NodeRef(index))
    }).collect();
    assert_eq!(source_refs.len(), 2);
    let context = result.contexts[source_refs[0].0];
    let carrier = result.nodes.iter().enumerate().find_map(|(index,node)| {
        (matches!(node.rule, Rule::FieldSource(_)) && result.contexts[index] == context).then_some(NodeRef(index))
    }).expect("actual field-read carrier in the same body");
    let Some(Payload::Expression {bindings,..}) = &result.nodes[source_refs[0].0].payload else { unreachable!() };
    let declaration = &law.declarations()["Calc.current"];
    for kind in ["static", "carrier", "context", "scope", "condition"] {
        let control = quiet();
        let environment = Environment::with_prepared(&result.prepared, &control).unwrap();
        let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        graph.active = context;
        let reference = match kind { "carrier" => carrier, "context" => source_refs[1], _ => source_refs[0] };
        let mut handle = SourceHandle {
            expression: reference, scope: graph.get(reference).unwrap().scope.clone(),
            known_value: None, missing: None, condition_failed: false, condition_pending: false,
        };
        if kind == "scope" { handle.scope.modes.insert("changed".into()); }
        if kind == "condition" { handle.condition_pending = true; }
        let start = graph.nodes.len();
        let mut evaluator = Evaluator {
            environment: &environment, graph: &mut graph, control: &control,
            request: &result.prepared.requests().requests()[0], declaration,
            bindings: bindings.clone(), lexical: BTreeMap::new(), formal: BTreeMap::new(),
            base: result.nodes[source_refs[0].0].scope.clone(), retained_scope: Scope::default(),
            reasons: vec![], completed: BTreeMap::new(), answer_evaluation: None,
            verified_observed: None, completing: false, finite_universal: None,
            sources: BTreeMap::from([(binder,handle)]),
        };
        let value = evaluator.eval_inner(id).unwrap();
        if kind == "static" { assert_eq!(value.expression, reference); }
        else { assert!(value.expression.0 >= start, "{kind} keeps fresh Source construction"); }
        assert_eq!(evaluator.graph.get(value.expression).unwrap(), &result.nodes[source_refs[0].0]);
        assert_eq!(value.scalar(evaluator.graph).unwrap(), Some(evaluator.graph.scalar(evaluator.graph.iterations[context.iteration.unwrap()].producer.unwrap()).unwrap()));
        assert!(value.reasons.is_empty());
    }
}
