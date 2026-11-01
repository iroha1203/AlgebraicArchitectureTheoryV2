fn universal_private_example(body: &str, requests: &[&str]) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(
        affine_private_fixture(body),
        requests,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}

fn universal_private_normalization(result: &ObservedEvaluation, request: usize) -> usize {
    result.nodes.iter().enumerate().find_map(|(index,node)| {
        (result.contexts[index].request==request && matches!(&node.payload,Some(Payload::Normalization{before,..}) if result.nodes[before.0].scope.assignments)).then_some(index)
    }).unwrap()
}

#[test]
fn universal_mixed_reference_rational_rows_recheck_missing_and_subject_producers() {
    let result = universal_private_example(
        "law required example(s:Sample,z:Q):z+s.q=z+s.q+rat(1,1);",
        &["example=check(Calc.example)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let whole = result.answers[0].outputs["evaluation"];
    let Some(Payload::Evaluation { parts, .. }) = &result.nodes[whole.0].payload else {
        unreachable!()
    };
    let rows = &parts[0].children;
    let expected = result
        .prepared
        .inputs()
        .archmap()
        .snapshots
        .iter()
        .flat_map(|snapshot| snapshot.subjects.iter())
        .filter(|subject| subject.ty == "Affine.Sample")
        .count();
    assert_eq!(rows.len(), expected);
    for row in rows {
        let Some(Payload::Evaluation {
            bindings,
            value: Some(value),
            ..
        }) = &result.nodes[row.0].payload
        else {
            unreachable!()
        };
        assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(false));
        let binding = bindings.iter().find(|binding| binding.name == "s").unwrap();
        let Scalar::Subject {
            snapshot, subject, ..
        } = data_scalar_at(&result, binding.value.0)
        else {
            unreachable!()
        };
        assert!(
            result.nodes[row.0]
                .support
                .iter()
                .any(|fact| fact.snapshot == *snapshot
                    && fact.subject == *subject
                    && fact.field.is_none())
        );
        assert!(result.nodes[row.0].reasons.iter().any(|reason| {
            matches!(reason.kind, ReasonKind::Missing)
                && reason.missing.iter().any(|fact| {
                    fact.snapshot == *snapshot
                        && fact.subject == *subject
                        && fact.field.as_deref() == Some("Affine.Sample.q")
                })
        }));
        let context = result.contexts[row.0];
        assert!(result.answers[0].evidence.iter().any(|proof| {
            result.contexts[proof.0] == context
                && matches!(
                    &result.nodes[proof.0].payload,
                    Some(Payload::Counterexample { .. })
                )
        }));
    }
}

#[test]
fn universal_view_local_integer_binder_rechecks_header_domain_and_original_scope() {
    let result = universal_private_example(
        "view inner(x:Z):Bool=forall y:Z . x+y=y+x; law required example(z:Z):inner(z);",
        &["example=check(Calc.example)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Established);
    let domains = result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            matches!(&node.payload, Some(Payload::TypeDomain { ty: Type::Z })).then_some(index)
        })
        .collect::<Vec<_>>();
    assert_eq!(domains.len(), 2);
    let (root_domain, local_domain) = (domains[0], domains[1]);
    let header = result.nodes[local_domain].arguments[0];
    let context = result.contexts[local_domain];
    assert!(context.frame.is_some());
    assert!(result.contexts[root_domain].frame.is_none());
    let law = result.prepared.inputs().law();
    let callee = &law.declarations["Calc.inner"];
    let Signature::View { body, .. } = &callee.signature else {
        unreachable!()
    };
    let ExprKind::Quant {
        var,
        split: crate::law::ast::QuantSplit::Fixed { body: equation, .. },
        ..
    } = &law.exprs[*body].kind
    else {
        unreachable!()
    };
    let Some(Payload::Expression {
        location: Location::Law { span },
        parameters,
        ..
    }) = &result.nodes[header.0].payload
    else {
        unreachable!()
    };
    assert_eq!(*span, law.exprs[*body].span);
    assert_eq!(parameters, &[("x".into(), Type::Z)]);
    assert!(
        matches!(&result.nodes[local_domain].rule,Rule::Input {kind:"law",location:Location::Law {span}} if *span==var.span)
    );
    assert_eq!(result.contexts[header.0], context);
    assert!(
        result.nodes[header.0]
            .scope
            .quantifiers
            .iter()
            .any(|q| q.occurrence == var.span && q.domain.is_none())
    );
    let local=result.nodes.iter().enumerate().find_map(|(index,node)|
        (matches!(&node.payload,Some(Payload::Evaluation {expression,..}) if *expression==header)
            && node.arguments.get(1)==Some(&NodeRef(local_domain))).then_some(index)).unwrap();
    let Some(Payload::Evaluation {
        parts,
        value: Some(value),
        ..
    }) = &result.nodes[local].payload
    else {
        unreachable!()
    };
    assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(true));
    assert_eq!(parts[0].children.len(), 1);
    let body_eval = parts[0].children[0];
    let Some(Payload::Evaluation {
        expression: body_source,
        ..
    }) = &result.nodes[body_eval.0].payload
    else {
        unreachable!()
    };
    assert!(
        matches!(&result.nodes[body_source.0].payload,Some(Payload::Expression {location:Location::Law {span},parameters,..})
        if *span==law.exprs[*equation].span && parameters==&[("x".into(),Type::Z),("y".into(),Type::Z)])
    );
    let position = result.nodes[body_source.0]
        .arguments
        .iter()
        .position(|r| *r == NodeRef(local_domain))
        .unwrap();
    assert!(
        result.nodes[local]
            .scope
            .quantifiers
            .iter()
            .any(|q| q.occurrence == var.span
                && q.name == "y"
                && q.ty == Type::Z
                && q.domain == Some(NodeRef(local_domain))
                && q.context == Some(context))
    );
    for target in [local_domain, body_source.0, local] {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    }
    completion_mutation(&result, local_domain, |nodes| {
        nodes[local_domain].payload = Some(Payload::TypeDomain { ty: Type::Q })
    });
    completion_mutation(&result, local_domain, |nodes| {
        nodes[local_domain].rule = result.nodes[root_domain].rule.clone()
    });
    completion_mutation(&result, body_source.0, |nodes| {
        nodes[body_source.0].arguments[position] = NodeRef(root_domain)
    });
    completion_mutation(&result, local, |nodes| {
        let q = nodes[local]
            .scope
            .quantifiers
            .iter_mut()
            .find(|q| q.occurrence == var.span)
            .unwrap();
        q.domain = Some(NodeRef(root_domain));
    });
}

#[test]
fn universal_view_local_nonzero_binder_rechecks_concrete_closed_axis_counterexample() {
    let result = universal_private_example(
        "view inner(x:Z):Bool=forall y:Z . x+y=x; law required example(z:Z):inner(z);",
        &["example=check(Calc.example)"],
    );
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let whole = result.answers[0].outputs["evaluation"];
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization { steps, after, .. }) = &result.nodes[normalization].payload
    else {
        unreachable!()
    };
    assert_eq!(steps.len(), 2);
    assert_eq!(data_scalar_at(&result, after.0), &Scalar::Bool(false));
    assert!(
        matches!(&result.nodes[whole.0].payload,Some(Payload::Evaluation {parts,..}) if parts[0].residual.is_some())
    );
    let domain = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (result.contexts[index].frame.is_some()
                && matches!(&node.payload, Some(Payload::TypeDomain { ty: Type::Z })))
            .then_some(index)
        })
        .unwrap();
    let header = result.nodes[domain].arguments[0];
    let local=result.nodes.iter().enumerate().find_map(|(index,node)|
        matches!(&node.payload,Some(Payload::Evaluation {expression,value:Some(_),..}) if *expression==header).then_some(index)).unwrap();
    let Some(Payload::Evaluation {
        value: Some(value),
        parts,
        ..
    }) = &result.nodes[local].payload
    else {
        unreachable!()
    };
    assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(false));
    assert!(matches!(
        &result.nodes[parts[0].children[0].0].payload,
        Some(Payload::Evaluation { value: None, .. })
    ));
    assert_eq!(
        result.nodes[value.0].arguments,
        [header, NodeRef(domain), parts[0].children[0]]
    );
    let counterexample = result.answers[0]
        .evidence
        .iter()
        .find_map(|proof| {
            matches!(
                &result.nodes[proof.0].payload,
                Some(Payload::Counterexample { .. })
            )
            .then_some(*proof)
        })
        .unwrap();
    assert_eq!(result.nodes[counterexample.0].arguments.len(), 5);
    let Some(Payload::Counterexample { left, right, .. }) = &result.nodes[counterexample.0].payload
    else {
        unreachable!()
    };
    let mut closed_values = Vec::new();
    for (side, expected) in [(*left, 1), (*right, 0)] {
        let Some(Payload::Evaluation {
            expression,
            value: Some(value),
            bindings,
            ..
        }) = &result.nodes[side.0].payload
        else {
            unreachable!()
        };
        assert_eq!(
            data_scalar_at(&result, value.0),
            &Scalar::Z(expected.into())
        );
        assert!(
            matches!(&result.nodes[expression.0].payload,Some(Payload::ParameterizedTransform {parameters,..}) if parameters.is_empty())
        );
        for (name, expected) in [("x", 0), ("y", 1)] {
            let binding = bindings
                .iter()
                .find(|binding| binding.name == name)
                .unwrap();
            assert_eq!(
                data_scalar_at(&result, binding.value.0),
                &Scalar::Z(expected.into())
            );
            if name == "y" {
                closed_values.push(binding.value);
            }
        }
    }
    assert_ne!(closed_values[0], closed_values[1]);
    completion_mutation(&result, closed_values[1].0, |nodes| {
        nodes[closed_values[1].0].arguments[1] = result.nodes[closed_values[0].0].arguments[1];
    });
    completion_mutation(&result, value.0, |nodes| {
        nodes[value.0].payload = Some(Payload::Scalar(Scalar::Bool(true)))
    });
    completion_mutation(&result, local, |nodes| {
        nodes[local]
            .scope
            .quantifiers
            .retain(|q| q.domain != Some(NodeRef(domain)))
    });
}

#[test]
fn universal_view_local_missing_keeps_whole_counterexample_without_common_assignment() {
    let result = universal_private_example(
        "view inner(x:Z,s:Sample):Bool=forall y:Z . x+y=s.z; law required example(z:Z,s:Sample):inner(z,s);",
        &["example=check(Calc.example,s=@v/sample)"],
    );
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let whole = result.answers[0].outputs["evaluation"];
    let counterexample = result.answers[0]
        .evidence
        .iter()
        .find_map(|proof| {
            matches!(
                &result.nodes[proof.0].payload,
                Some(Payload::Counterexample { .. })
            )
            .then_some(*proof)
        })
        .unwrap();
    assert_eq!(result.nodes[counterexample.0].arguments.len(), 3);
    assert_eq!(result.nodes[counterexample.0].arguments[1], whole);
    assert!(
        !result
            .nodes
            .iter()
            .any(|node| matches!(&node.payload, Some(Payload::Scalar(Scalar::Z(_)))))
    );
    assert!(result.nodes[whole.0].reasons.iter().any(|reason| matches!(
        reason.kind,
        ReasonKind::Missing
    ) && reason.missing.iter().any(
        |fact| fact.snapshot == "v"
            && fact.subject == "sample"
            && fact.field.as_deref() == Some("Affine.Sample.z")
    )));
    completion_mutation(&result, whole.0, |nodes| nodes[whole.0].reasons.clear());
}

#[test]
fn universal_concrete_counterexample_rechecks_substitution_and_generated_parameter() {
    let result = universal_private_example(
        "law required shifted(z:Z,s:Sample):z+s.z=z+s.z+1;",
        &["shifted=check(Calc.shifted,s=@v/sample)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization { steps, .. }) = &result.nodes[normalization].payload else {
        unreachable!()
    };
    assert_eq!(steps.len(), 2);
    let substitute = steps[1].0;
    let Some(Payload::ParameterizedTransform {
        operation: TransformOp::Substitute,
        bindings,
        parameters,
        ..
    }) = &result.nodes[substitute].payload
    else {
        unreachable!()
    };
    assert!(parameters.is_empty());
    let parameter = bindings
        .iter()
        .find(|binding| binding.name == "z")
        .unwrap()
        .value
        .0;
    assert_eq!(data_scalar_at(&result, parameter), &Scalar::Z(0.into()));
    completion_mutation(&result, parameter, |nodes| {
        nodes[parameter].payload = Some(Payload::Scalar(Scalar::Z(1.into())))
    });
    completion_mutation(&result, substitute, |nodes| {
        let Some(Payload::ParameterizedTransform { bindings, .. }) = &mut nodes[substitute].payload
        else {
            unreachable!()
        };
        bindings
            .iter_mut()
            .find(|binding| binding.name == "z")
            .unwrap()
            .name = "foreign".into();
    });
    let counterexample = result.answers[0]
        .evidence
        .iter()
        .find_map(|r| {
            matches!(
                &result.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )
            .then_some(r.0)
        })
        .unwrap();
    let Some(Payload::Counterexample { left, right, .. }) = &result.nodes[counterexample].payload
    else {
        unreachable!()
    };
    for operand in [*left, *right] {
        assert!(
            matches!(
                &result.nodes[operand.0].payload,
                Some(Payload::Evaluation { value: None, .. })
            ),
            "欠測s.zへ代入を捏造しない"
        );
    }
    completion_mutation(&result, counterexample, |nodes| {
        let Some(Payload::Counterexample { left, right, .. }) = &mut nodes[counterexample].payload
        else {
            unreachable!()
        };
        std::mem::swap(left, right);
    });
}

#[test]
fn universal_no_common_assignment_counterexample_rechecks_whole_false() {
    let result = universal_private_example(
        "law required all(z:Z,s:Sample):2*z+s.z=0;",
        &["all=check(Calc.all,s=@v/sample)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Refuted);
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization { steps, .. }) = &result.nodes[normalization].payload else {
        unreachable!()
    };
    assert_eq!(steps.len(), 1, "共通具体pがなければsubstituteを捏造しない");
    let counterexample = result.answers[0]
        .evidence
        .iter()
        .find_map(|r| {
            matches!(
                &result.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )
            .then_some(r.0)
        })
        .unwrap();
    assert_eq!(result.nodes[counterexample].arguments.len(), 3);
    let Some(Payload::Counterexample {
        bindings,
        left,
        right,
        ..
    }) = &result.nodes[counterexample].payload
    else {
        unreachable!()
    };
    assert!(bindings.iter().all(|binding| binding.name != "z"));
    assert_eq!(data_scalar_at(&result, left.0), &Scalar::Bool(false));
    assert_eq!(data_scalar_at(&result, right.0), &Scalar::Bool(true));
    completion_mutation(&result, counterexample, |nodes| {
        nodes[counterexample].arguments[2] = NodeRef(normalization - 1)
    });
    completion_mutation(&result, counterexample, |nodes| {
        let Some(Payload::Counterexample { facts, .. }) = &mut nodes[counterexample].payload else {
            unreachable!()
        };
        facts.clear();
    });
}

#[test]
fn universal_guard_false_retains_body_source_without_body_evaluation() {
    let result = universal_private_example(
        "law required guarded(z:Z) when false:1=2;",
        &["guarded=check(Calc.guarded)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Established);
    let evaluation = result.answers[0].outputs["evaluation"].0;
    let Some(Payload::Evaluation {
        parts,
        applicability,
        value,
        ..
    }) = &result.nodes[evaluation].payload
    else {
        unreachable!()
    };
    assert_eq!(*applicability, "not_applicable");
    assert_eq!(parts.len(), 2);
    assert!(parts[1].children.is_empty());
    assert!(parts[1].value.is_none());
    assert!(parts[1].residual.is_none());
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization { steps, .. }) = &result.nodes[normalization].payload else {
        unreachable!()
    };
    assert_eq!(steps.len(), 1);
    assert_eq!(
        result.nodes[steps[0].0].ty,
        NodeType::Expression(Type::Bool)
    );
    completion_mutation(&result, evaluation, |nodes| {
        let Some(Payload::Evaluation { parts, .. }) = &mut nodes[evaluation].payload else {
            unreachable!()
        };
        parts[1].value = *value;
    });
    completion_mutation(&result, evaluation, |nodes| {
        let Some(Payload::Evaluation { applicability, .. }) = &mut nodes[evaluation].payload else {
            unreachable!()
        };
        *applicability = "applicable";
    });
}

#[test]
fn universal_counterexample_post_stop_retains_completed_evidence() {
    universal_private_stop(4);
}

fn universal_private_stop(stage: usize) {
    let current = if stage == 4 {
        "law required current(z:Z,s:Sample):z+s.z=z+s.z+1;"
    } else if stage == 6 {
        "view current(s:Sample):Bool=forall z:Z . z+s.z=z;"
    } else if stage == 8 {
        "view current(s:Sample):Bool=forall z:Z . 2*s.z+4*s.k=1;"
    } else {
        "view current(s:Sample):Bool=forall z:Z . z+s.z=z+s.z;"
    };
    let request = if stage == 4 {
        "current=check(Calc.current,s=@v/sample)"
    } else {
        "current=evaluate(Calc.current,s=@v/sample)"
    };
    universal_private_stop_with_current(stage, current, request);
}

fn universal_private_stop_with_current(stage: usize, current: &str, request: &str) {
    use super::super::affine;
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let sources = affine_private_fixture(&format!(
        "view seed():Z=7;law required prior():1=2;view hole(s:Sample):Z=s.k;{current}view later():Z=19;"
    ));
    let asks = [
        "seed=evaluate(Calc.seed)",
        "prior=check(Calc.prior)",
        "hole=evaluate(Calc.hole,s=@v/sample)",
        request,
        "later=evaluate(Calc.later)",
    ];
    let normal = evaluate_observed_bytes(sources.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[0].status, Decision::Established);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert!(!normal.answers[1].evidence.is_empty());
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert!(
        normal.answers[2]
            .reasons
            .iter()
            .any(|reason| matches!(reason.kind, ReasonKind::Missing))
    );
    assert_eq!(
        normal.answers[3].status,
        if stage == 4 {
            Decision::Refuted
        } else if stage == 6 {
            Decision::Undetermined
        } else {
            Decision::Established
        }
    );
    let expected = StopReason::Cancelled(Signal::Term);
    let ready = Rc::new(Cell::new(false));
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |point| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(point, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            Some(Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(sources, &asks, &mut control).unwrap();
    let (observer_ready, observer_arm) = (ready.clone(), armed.clone());
    let stopped = affine::with_observer(
        move |point| {
            if observer_ready.get()
                && ((stage == 0 && point == affine::TestPoint::Universal)
                    || (stage == 8 && point == affine::TestPoint::Gcd))
            {
                observer_arm.set(true)
            }
        },
        || {
            evaluate_observed_with_validator(
                prepared,
                &mut control,
                |environment, graph, request, answer| {
                    environment.validate_answer(graph, request, answer)?;
                    if request.id == "hole" {
                        ready.set(true);
                        if stage != 0 && stage != 7 && stage != 8 {
                            let armed = armed.clone();
                            data::observe_iterations(move |_, context, operation, index| {
                                if context.request == 3
                                    && ((operation == "universal" && index == stage)
                                        || (stage == 9 && operation == "family_row" && index == 1)
                                        || (stage == 10
                                            && operation == "universal_local"
                                            && index == 1))
                                {
                                    armed.set(true)
                                }
                            });
                        }
                    }
                    if request.id == "current" && stage == 7 {
                        armed.set(true)
                    }
                    Ok(())
                },
            )
        },
    );
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    let Json::Obj(ref normal_wire) = normal.wire() else {
        unreachable!()
    };
    let Json::Obj(ref stopped_wire) = stopped.wire() else {
        unreachable!()
    };
    let (Json::Arr(normal_answers), Json::Arr(stopped_answers)) =
        (&normal_wire["answers"], &stopped_wire["answers"])
    else {
        unreachable!()
    };
    assert_eq!(&normal_answers[..3], &stopped_answers[..3]);
    if stage == 7 {
        assert_eq!(normal_answers[3], stopped_answers[3]);
    } else {
        assert_eq!(stopped.answers[3].status, Decision::Undetermined);
        assert!(stopped.answers[3].outputs.is_empty());
        assert!(stopped.answers[3].evidence.is_empty());
        assert!(stopped.answers[3].claim.is_none());
    }
    for answer in &stopped.answers[if stage == 7 { 4 } else { 3 }..] {
        let reason = answer
            .reasons
            .iter()
            .find(|reason| matches!(&reason.kind,ReasonKind::Stop(actual) if actual==&expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            unreachable!()
        };
        let Json::Obj(ref expected) = expected.wire() else {
            unreachable!()
        };
        assert_eq!(actual["details"], expected["details"]);
    }
    assert!(stopped.answers[4].outputs.is_empty());
    assert!(!stopped.contexts.iter().any(|context| context.request == 4));
    if stage == 2 {
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(index, node)| stopped.contexts[index].request == 3
                    && matches!(&node.payload, Some(Payload::Normalization { .. })))
        );
    }
    if stage == 3 {
        assert!(matches!(
            &stopped.nodes.last().unwrap().payload,
            Some(Payload::Normalization { .. })
        ));
    }
    if stage == 4 {
        assert!(matches!(
            &stopped.nodes.last().unwrap().payload,
            Some(Payload::Counterexample { .. })
        ));
    }
    if stage == 6 {
        assert!(matches!(
            &stopped.nodes.last().unwrap().payload,
            Some(Payload::CompletionPair { .. })
        ));
        assert_eq!(stopped.universal_witnesses.len(), 2);
    }
    if stage == 9 {
        assert_eq!(stopped.instances.len(), 1);
        assert_eq!(stopped.instances[0].caller.request, 3);
        let rows = stopped
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                (stopped.contexts[index].request == 3
                    && stopped.contexts[index].instance == Some(0)
                    && matches!(
                        &node.payload,
                        Some(Payload::Evaluation { value: Some(_), .. })
                    )
                    && node.evidence.iter().any(|proof| {
                        matches!(
                            &stopped.nodes[proof.0].payload,
                            Some(Payload::Normalization { .. })
                        )
                    }))
                .then_some(index)
            })
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 1);
        assert!(
            !stopped
                .contexts
                .iter()
                .any(|context| context.request == 3 && context.instance == Some(1))
        );
        assert!(!stopped.nodes.iter().enumerate().any(|(index, node)| {
            stopped.contexts[index].request == 3
                && matches!(&node.payload, Some(Payload::FiniteExhaustion { .. }))
        }));
    }
    if stage == 10 {
        let local_domain = stopped.nodes.len() - 1;
        assert!(matches!(
            &stopped.nodes[local_domain].payload,
            Some(Payload::TypeDomain { ty: Type::Z })
        ));
        let header = stopped.nodes[local_domain].arguments[0];
        let context = stopped.contexts[local_domain];
        assert_eq!(context, stopped.contexts[header.0]);
        assert!(context.frame.is_some());
        assert_eq!(stopped.frames[context.frame.unwrap()].arguments.len(), 1);
        assert!(!stopped.nodes.iter().enumerate().any(|(index, node)| {
            stopped.contexts[index].request == 3
                && matches!(&node.payload, Some(Payload::Normalization { .. }))
        }));
        assert!(!stopped.nodes.iter().any(|node| matches!(&node.payload,
            Some(Payload::Evaluation {expression,..}) if *expression==header)));
    }
    let (Json::Arr(normal_nodes), Json::Arr(stopped_nodes)) =
        (&normal_wire["nodes"], &stopped_wire["nodes"])
    else {
        unreachable!()
    };
    assert_eq!(stopped_nodes, &normal_nodes[..stopped_nodes.len()]);
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    let before = probes.get();
    assert_eq!(probes.get(), before);
}

#[test]
fn universal_affine_guard_counterexamples_belong_to_the_actual_guard_fiber() {
    for (ty, guard, rhs, expected) in [
        ("Z", "n=0", "1", Scalar::Z(0.into())),
        (
            "Q",
            "2*n=rat(1,1)",
            "rat(1,1)",
            Scalar::Q(1.into(), 2.into()),
        ),
    ] {
        let result = universal_private_example(
            &format!("law required example(n:{ty}) when {guard}:n={rhs};"),
            &["c=check(Calc.example)"],
        );
        assert_eq!(result.answers[0].status, Decision::Refuted, "{ty}");
        let binding = result.answers[0]
            .evidence
            .iter()
            .find_map(|r| {
                let Some(Payload::Counterexample { bindings, .. }) = &result.nodes[r.0].payload
                else {
                    return None;
                };
                bindings.iter().find(|b| b.name == "n")
            })
            .unwrap();
        assert_eq!(data_scalar_at(&result, binding.value.0), &expected);
        completion_mutation(&result, binding.value.0, |nodes| {
            let Some(Payload::Scalar(value)) = &mut nodes[binding.value.0].payload else {
                panic!()
            };
            *value = if ty == "Q" {
                Scalar::Q(99.into(), 1.into())
            } else {
                Scalar::Z(99.into())
            };
        });
    }
}

#[test]
fn universal_guard_counterexamples_keep_unused_scalar_and_nested_tuple_parameters() {
    let result = universal_private_example(
        "law required example(n:Z,m:Q,p:(Z,(Z,Z))) when n=0:n=1;",
        &["c=check(Calc.example)"],
    );
    assert_eq!(
        result.answers[0].status,
        Decision::Refuted,
        "issues={:?} reasons={:?}",
        result.issues,
        result.answers[0].reasons
    );
    let bindings = result.answers[0]
        .evidence
        .iter()
        .find_map(|r| match &result.nodes[r.0].payload {
            Some(Payload::Counterexample { bindings, .. }) => Some(bindings),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
        ["n", "m", "p"]
    );
    for (binding, expected) in bindings.iter().zip([
        Scalar::Z(0.into()),
        Scalar::Q(0.into(), 1.into()),
        Scalar::Tuple(vec![
            Scalar::Z(0.into()),
            Scalar::Tuple(vec![Scalar::Z(0.into()), Scalar::Z(0.into())]),
        ]),
    ]) {
        assert_eq!(data_scalar_at(&result, binding.value.0), &expected);
    }
}

#[test]
fn universal_conjunctive_guards_solve_the_whole_system_and_keep_all_binders() {
    for (guard, expected) in [
        ("n=0 and n=1", Decision::Established),
        ("let zero=n in (zero=0 and m=1)", Decision::Refuted),
    ] {
        let result = universal_private_example(
            &format!("law required example(n:Z,m:Z,u:Q,p:(Z,(Z,Z))) when {guard}:n=m;"),
            &["c=check(Calc.example)"],
        );
        assert_eq!(
            result.answers[0].status, expected,
            "{guard}: {:?}",
            result.answers[0].reasons
        );
        let examples = result.answers[0]
            .evidence
            .iter()
            .filter_map(|r| match &result.nodes[r.0].payload {
                Some(Payload::Counterexample { bindings, .. }) => Some(bindings),
                _ => None,
            })
            .collect::<Vec<_>>();
        if expected == Decision::Established {
            assert!(examples.is_empty());
        } else {
            assert!(!examples.is_empty());
            for bindings in examples {
                assert_eq!(
                    bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
                    ["n", "m", "u", "p"]
                );
                let expected = [
                    Scalar::Z(0.into()),
                    Scalar::Z(1.into()),
                    Scalar::Q(0.into(), 1.into()),
                    Scalar::Tuple(vec![
                        Scalar::Z(0.into()),
                        Scalar::Tuple(vec![Scalar::Z(0.into()), Scalar::Z(0.into())]),
                    ]),
                ];
                for (binding, expected) in bindings.iter().zip(expected) {
                    assert_eq!(data_scalar_at(&result, binding.value.0), &expected);
                }
            }
        }
    }
}
