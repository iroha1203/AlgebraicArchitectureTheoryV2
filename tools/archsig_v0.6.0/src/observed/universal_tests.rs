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
fn universal_type_domains_and_free_parameters_recheck_original_binder_order() {
    let result = universal_private_example(
        "law required numericIdentity(x:Z,y:Z):x+y=x+y;",
        &["identity=check(Calc.numericIdentity)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Established);
    let domains = result
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            matches!(&node.payload, Some(Payload::TypeDomain { .. })).then_some(index)
        })
        .collect::<Vec<_>>();
    assert_eq!(domains.len(), 2);
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization {
        before,
        after,
        steps,
    }) = &result.nodes[normalization].payload
    else {
        unreachable!()
    };
    assert_eq!(data_scalar_at(&result, after.0), &Scalar::Bool(true));
    assert_eq!(steps.len(), 1);
    let Some(Payload::Expression {
        parameters,
        bindings,
        ..
    }) = &result.nodes[before.0].payload
    else {
        unreachable!()
    };
    assert_eq!(parameters, &[("x".into(), Type::Z), ("y".into(), Type::Z)]);
    assert!(bindings.is_empty());
    for &domain in &domains {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=domain]).unwrap();
        completion_mutation(&result, domain, |nodes| {
            nodes[domain].payload = Some(Payload::TypeDomain { ty: Type::Q })
        });
    }
    completion_mutation(&result, domains[1], |nodes| {
        nodes[domains[1]].rule = result.nodes[domains[0]].rule.clone()
    });
    completion_mutation(&result, normalization, |nodes| {
        let Some(Payload::Expression { parameters, .. }) = &mut nodes[before.0].payload else {
            unreachable!()
        };
        parameters.swap(0, 1);
    });
    completion_mutation(&result, normalization, |nodes| {
        let Some(Payload::ParameterizedTransform {
            operation: TransformOp::Difference,
            ..
        }) = &mut nodes[steps[0].0].payload
        else {
            unreachable!()
        };
        nodes[steps[0].0].arguments.swap(1, 2);
    });
}

#[test]
fn universal_whole_prefixes_recheck_difference_residual_bool_and_normalization() {
    let result = universal_private_example(
        "view numericIdentity(s:Sample):Bool=forall z:Q . z+s.q=z+s.q;",
        &["identity=evaluate(Calc.numericIdentity,s=@v/sample)"],
    );
    assert_eq!(result.status(), "complete");
    let evaluation = result.answers[0].outputs["evaluation"].0;
    let normalization = universal_private_normalization(&result, 0);
    let Some(Payload::Normalization {
        before,
        after,
        steps,
    }) = &result.nodes[normalization].payload
    else {
        unreachable!()
    };
    let Some(Payload::Expression { parameters, .. }) = &result.nodes[before.0].payload else {
        unreachable!()
    };
    assert!(
        parameters.is_empty(),
        "forall binderはwholeの自由parameterでない"
    );
    assert_eq!(data_scalar_at(&result, after.0), &Scalar::Bool(true));
    let Some(Payload::Evaluation { parts, .. }) = &result.nodes[evaluation].payload else {
        unreachable!()
    };
    let residual = parts[0].residual.unwrap().0;
    assert_eq!(result.nodes[residual].ty, NodeType::Evaluation(Type::Q));
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &result.nodes[residual].payload
    else {
        unreachable!()
    };
    assert_eq!(
        data_scalar_at(&result, value.0),
        &Scalar::Q(0.into(), 1.into())
    );
    for target in [steps[0].0, residual, after.0, normalization] {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
        assert!(target < evaluation);
        completion_mutation(&result, target, |nodes| {
            nodes[target].scope.assignments = false
        });
        assert!(!result.nodes[target].support.is_empty());
        completion_mutation(&result, target, |nodes| nodes[target].support.clear());
    }
    completion_mutation(&result, steps[0].0, |nodes| {
        let Some(Payload::ParameterizedTransform { operands, .. }) = &mut nodes[steps[0].0].payload
        else {
            unreachable!()
        };
        operands.swap(0, 1);
    });
    completion_mutation(&result, residual, |nodes| {
        let Some(Payload::Evaluation { value, parts, .. }) = &mut nodes[residual].payload else {
            unreachable!()
        };
        *value = None;
        parts[0].value = None;
    });
    completion_mutation(&result, after.0, |nodes| {
        nodes[after.0].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    completion_mutation(&result, normalization, |nodes| {
        let Some(Payload::Normalization { before, .. }) = &mut nodes[normalization].payload else {
            unreachable!()
        };
        *before = steps[0];
    });
    completion_mutation(&result, normalization, |nodes| {
        let Some(Payload::Normalization { steps, .. }) = &mut nodes[normalization].payload else {
            unreachable!()
        };
        steps.clear();
    });
    let missing = (0..normalization)
        .find(|index| !result.nodes[*index].reasons.is_empty())
        .unwrap();
    completion_mutation(&result, normalization, |nodes| {
        nodes[missing].reasons.clear()
    });
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
fn universal_guard_transform_prefixes_recheck_original_subject_support_before_domains() {
    let result = universal_private_example(
        "law required example(s:Sample,z:Z) when s.p: z+1=z+2;",
        &["example=check(Calc.example,s=@v/sample)"],
    );
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    let inputs = result.prepared.inputs();
    let subject = inputs
        .archmap()
        .snapshots
        .iter()
        .find(|snapshot| snapshot.id == "v")
        .unwrap()
        .subjects
        .iter()
        .find(|subject| subject.id == "sample")
        .unwrap();
    assert_eq!(subject.ty, "Affine.Sample");
    let field = subject
        .fields
        .iter()
        .find(|field| field.name == "Affine.Sample.p")
        .unwrap();
    assert_eq!(field.ty, Type::Bool);
    assert!(matches!(&field.slot, Slot::Missing));
    let expected_support = vec![Fact {
        snapshot: subject.snapshot.clone(),
        subject: subject.id.clone(),
        field: None,
        atom: None,
    }];
    let declaration = inputs
        .law()
        .declarations
        .values()
        .find(|declaration| declaration.name == "Calc.example")
        .unwrap();
    let Signature::Law {
        guard: Some(guard),
        body,
        ..
    } = &declaration.signature
    else {
        unreachable!()
    };
    let guard_span = inputs.law().exprs[*guard].span;
    assert_eq!(
        &inputs.sources().law().bytes()[guard_span.0..guard_span.1],
        b"s.p"
    );
    let and = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            (result.contexts[index].case.is_none()
                && matches!(
                    &node.payload,
                    Some(Payload::ParameterizedTransform {
                        operation: TransformOp::And,
                        ..
                    })
                ))
            .then_some(index)
        })
        .unwrap();
    let Some(Payload::ParameterizedTransform { operands, .. }) = &result.nodes[and].payload else {
        unreachable!()
    };
    let guard_source = operands[0];
    let body_not = operands[1];
    let Some(Payload::Expression {
        location: Location::Law { span },
        bindings,
        ..
    }) = &result.nodes[guard_source.0].payload
    else {
        unreachable!()
    };
    assert_eq!(*span, guard_span);
    let binding = bindings.iter().find(|binding| binding.name == "s").unwrap();
    assert!(matches!(data_scalar_at(&result,binding.value.0),
        Scalar::Subject {snapshot,subject:actual,entity}
            if snapshot==&subject.snapshot && actual==&subject.id && entity==&subject.ty));
    let Some(Payload::ParameterizedTransform { operands, .. }) = &result.nodes[body_not.0].payload
    else {
        unreachable!()
    };
    assert!(matches!(&result.nodes[operands[0].0].payload,
        Some(Payload::Expression {location:Location::Law {span},..}) if *span==inputs.law().exprs[*body].span));
    let root = result.nodes.iter().enumerate().find_map(|(index,node)| {
        (result.contexts[index].case.is_none()
            && matches!(&node.payload,Some(Payload::ParameterizedTransform {operation:TransformOp::Not,operands,..}) if operands==&[NodeRef(and)]))
            .then_some(index)
    }).unwrap();
    let domain = result
        .nodes
        .iter()
        .position(|node| matches!(&node.payload, Some(Payload::TypeDomain { .. })))
        .unwrap();
    assert!(body_not.0 < and && and < root && root < domain);
    assert!(result.nodes[body_not.0].support.is_empty());
    for target in [body_not.0, and, root] {
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=target]).unwrap();
    }
    for target in [and, root] {
        assert_eq!(result.nodes[target].support, expected_support);
        completion_mutation(&result, target, |nodes| nodes[target].support.clear());
    }
}

#[test]
fn universal_numeric_pair_rechecks_all_missing_slots_and_exact_witness_producers() {
    let result = universal_private_example(
        "view uncertain(s:Sample):Bool=forall z:Z . z+(s.z-s.z)+s.k=z;",
        &["uncertain=evaluate(Calc.uncertain,s=@v/sample)"],
    );
    assert_eq!(result.status(), "partial");
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    let pair = result
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            matches!(&node.payload, Some(Payload::CompletionPair { .. })).then_some(index)
        })
        .unwrap();
    let Some(Payload::CompletionPair {
        fields,
        first,
        second,
        first_result,
        second_result,
    }) = &result.nodes[pair].payload
    else {
        unreachable!()
    };
    assert_eq!(fields.len(), 2, "相殺したmissingも両具体補完へ含む");
    assert_eq!(
        fields
            .iter()
            .map(|fact| fact.field.as_deref().unwrap())
            .collect::<Vec<_>>(),
        vec!["Affine.Sample.k", "Affine.Sample.z"]
    );
    assert_eq!(data_scalar_at(&result, first[1].0), &Scalar::Z(0.into()));
    assert_eq!(data_scalar_at(&result, second[1].0), &Scalar::Z(0.into()));
    assert_ne!(first[1], second[1], "同じ0でも別witness producer");
    for &value in first.iter().chain(second) {
        assert_eq!(result.nodes[value.0].arguments.len(), 3);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=value.0]).unwrap();
    }
    completion_mutation(&result, second[1].0, |nodes| {
        nodes[second[1].0].arguments[1] = result.nodes[first[1].0].arguments[1]
    });
    completion_mutation(&result, second[1].0, |nodes| {
        nodes[second[1].0].payload = Some(Payload::Scalar(Scalar::Z(1.into())))
    });
    completion_mutation(&result, pair, |nodes| {
        let Some(Payload::CompletionPair { fields, .. }) = &mut nodes[pair].payload else {
            unreachable!()
        };
        fields.swap(0, 1);
    });
    completion_mutation(&result, pair, |nodes| {
        let Some(Payload::CompletionPair { second, .. }) = &mut nodes[pair].payload else {
            unreachable!()
        };
        second[1] = first[1];
    });
    completion_mutation(&result, pair, |nodes| {
        let Some(Payload::CompletionPair {
            first_result,
            second_result,
            ..
        }) = &mut nodes[pair].payload
        else {
            unreachable!()
        };
        std::mem::swap(first_result, second_result);
    });
    assert_ne!(first_result, second_result);
    let root = result.answers[0].outputs["evaluation"].0;
    assert!(result.nodes[root].evidence.contains(&NodeRef(pair)));
    completion_mutation(&result, root, |nodes| nodes[root].evidence.clear());
}

#[test]
fn universal_repeated_call_and_request_prefixes_reject_equivalent_producers() {
    let result = universal_private_example(
        "view same(x:Z):Bool=x+1=x+1; view all(s:Sample):Bool=forall z:Z . same(z+s.z);",
        &[
            "first=evaluate(Calc.all,s=@v/sample)",
            "again=evaluate(Calc.all,s=@v/sample)",
        ],
    );
    assert_eq!(result.status(), "complete");
    let first = universal_private_normalization(&result, 0);
    let second = universal_private_normalization(&result, 1);
    let Some(Payload::Normalization { steps: old, .. }) = &result.nodes[first].payload else {
        unreachable!()
    };
    let Some(Payload::Normalization {
        steps: new, after, ..
    }) = &result.nodes[second].payload
    else {
        unreachable!()
    };
    assert_eq!(data_scalar_at(&result, after.0), &Scalar::Bool(true));
    assert_ne!(
        result.nodes[old[0].0].arguments,
        result.nodes[new[0].0].arguments
    );
    for position in [
        0,
        result.nodes[new[0].0].arguments.len() - 2,
        result.nodes[new[0].0].arguments.len() - 1,
    ] {
        completion_mutation(&result, new[0].0, |nodes| {
            nodes[new[0].0].arguments[position] = result.nodes[old[0].0].arguments[position]
        });
    }
    completion_mutation(&result, second, |nodes| {
        let Some(Payload::Normalization { steps, .. }) = &mut nodes[second].payload else {
            unreachable!()
        };
        steps[0] = old[0];
    });
}

#[test]
fn universal_caller_substitution_retains_unknown_formals_and_exact_argument_producers() {
    let result = universal_private_example(
        "view eq(a:Z):Bool=a=a+1; law required example(s:Sample,z:Z):eq(z+s.z);",
        &[
            "first=check(Calc.example,s=@v/sample)",
            "again=check(Calc.example,s=@v/sample)",
        ],
    );
    assert_eq!(result.status(), "complete");
    assert!(
        result
            .answers
            .iter()
            .all(|answer| answer.status == Decision::Refuted)
    );
    let mut substitutions = Vec::new();
    for request in 0..2 {
        let normalization = universal_private_normalization(&result, request);
        let Some(Payload::Normalization { steps, .. }) = &result.nodes[normalization].payload
        else {
            unreachable!()
        };
        assert_eq!(steps.len(), 2);
        let substitute = steps[1];
        let Some(Payload::ParameterizedTransform {
            operands,
            bindings,
            parameters,
            ..
        }) = &result.nodes[substitute.0].payload
        else {
            unreachable!()
        };
        assert!(parameters.is_empty());
        assert_eq!(
            data_scalar_at(
                &result,
                bindings
                    .iter()
                    .find(|binding| binding.name == "z")
                    .unwrap()
                    .value
                    .0
            ),
            &Scalar::Z(0.into())
        );
        let source = operands[0];
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &result.nodes[source.0].payload
        else {
            unreachable!()
        };
        assert_eq!(
            &result.prepared.inputs().sources().law().bytes()[span.0..span.1],
            b"eq(z+s.z)"
        );
        let counterexample = result.answers[request]
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
        let Some(Payload::Counterexample { left, right, .. }) =
            &result.nodes[counterexample].payload
        else {
            unreachable!()
        };
        for side in [*left, *right] {
            let Some(Payload::Evaluation {
                expression,
                value,
                bindings,
                ..
            }) = &result.nodes[side.0].payload
            else {
                unreachable!()
            };
            assert!(value.is_none());
            assert!(bindings.is_empty());
            let Some(Payload::ParameterizedTransform {
                parameters,
                operands,
                ..
            }) = &result.nodes[expression.0].payload
            else {
                unreachable!()
            };
            assert_eq!(parameters, &[("a".into(), Type::Z)]);
            assert!(result.contexts[operands[0].0].frame.is_some());
        }
        substitutions.push((substitute, counterexample));
    }
    completion_mutation(&result, substitutions[1].1, |nodes| {
        nodes[substitutions[1].1].arguments[2] = substitutions[0].0
    });
    let target = substitutions[1].0.0;
    completion_mutation(&result, target, |nodes| {
        let Some(Payload::ParameterizedTransform { operands, .. }) = &mut nodes[target].payload
        else {
            unreachable!()
        };
        let Some(Payload::ParameterizedTransform {
            operands: prior, ..
        }) = &result.nodes[substitutions[0].0.0].payload
        else {
            unreachable!()
        };
        operands[0] = prior[0];
    });
}

#[test]
fn universal_bool_completion_cases_recheck_each_whole_before_coverage() {
    let result = universal_private_example(
        "view all(s:Sample):Bool=(s.p and (forall z:Q . z+s.q=z+s.q)) or not s.p;",
        &["all=evaluate(Calc.all,s=@v/sample)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    let proofs=result.nodes.iter().enumerate().filter_map(|(index,node)|(result.contexts[index].case.is_some()&&matches!(&node.payload,Some(Payload::Normalization{before,..}) if result.nodes[before.0].scope.assignments)).then_some(index)).collect::<Vec<_>>();
    assert_eq!(proofs.len(), 2);
    let Some(Payload::Normalization { steps: prior, .. }) = &result.nodes[proofs[0]].payload else {
        unreachable!()
    };
    let Some(Payload::Normalization { steps: current, .. }) = &result.nodes[proofs[1]].payload
    else {
        unreachable!()
    };
    assert_ne!(
        result.contexts[proofs[0]].case,
        result.contexts[proofs[1]].case
    );
    completion_mutation(&result, proofs[1], |nodes| {
        let Some(Payload::Normalization { steps, .. }) = &mut nodes[proofs[1]].payload else {
            unreachable!()
        };
        steps[0] = prior[0];
    });
    completion_mutation(&result, current[0].0, |nodes| {
        nodes[current[0].0].arguments[0] = result.nodes[prior[0].0].arguments[0]
    });
}

#[test]
fn universal_numeric_family_bool_cases_recheck_free_parameter_domains_and_sources() {
    let result = universal_private_example(
        "law required example(s:Sample,z:Z): if s.p then z=z else z=z;",
        &["example=check(Calc.example,s=@v/sample)"],
    );
    assert_eq!(result.status(), "complete");
    assert_eq!(result.answers[0].status, Decision::Established);
    let aggregate = result.answers[0].outputs["evaluation"];
    let Some(Payload::Evaluation {
        value: Some(value),
        parts,
        ..
    }) = &result.nodes[aggregate.0].payload
    else {
        unreachable!()
    };
    assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(true));
    assert_eq!(parts.len(), 1);
    let cases = &parts[0].children;
    assert_eq!(cases.len(), 2);
    let coverage = result.nodes[aggregate.0].evidence[0];
    let Some(Payload::FiniteExhaustion {
        domain,
        checked,
        instances,
    }) = &result.nodes[coverage.0].payload
    else {
        panic!("two Bool completions require finite coverage")
    };
    assert_eq!(*checked, 2);
    assert_eq!(instances, cases);
    assert_eq!(result.nodes[domain.0].ty, NodeType::Domain);
    let mut fields = Vec::new();
    for &case in cases {
        let Some(Payload::Evaluation {
            value: Some(value),
            expression: template,
            ..
        }) = &result.nodes[case.0].payload
        else {
            unreachable!()
        };
        assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(true));
        assert!(result.nodes[case.0].scope.assignments);
        assert!(result.nodes[case.0].scope.completions);
        let context = result.contexts[case.0];
        assert!(context.case.is_some());
        let field = result
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let Some(Payload::Expression {
                    location: Location::Law { span },
                    parameters,
                    ..
                }) = &node.payload
                else {
                    return None;
                };
                (result.contexts[index] == context
                    && node.arguments.first() == Some(template)
                    && &result.prepared.inputs().sources().law().bytes()[span.0..span.1] == b"s.p")
                    .then_some((index, parameters))
            })
            .unwrap();
        assert_eq!(field.1, &[("z".into(), Type::Z)]);
        let numeric_domain = result.nodes[field.0].arguments[1];
        assert!(matches!(
            &result.nodes[numeric_domain.0].payload,
            Some(Payload::TypeDomain { ty: Type::Z })
        ));
        assert_eq!(result.nodes[numeric_domain.0].arguments, [*template]);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=case.0]).unwrap();
        fields.push((field.0, numeric_domain));
    }
    assert_ne!(
        result.contexts[cases[0].0].case,
        result.contexts[cases[1].0].case
    );
    assert!(fields[0].0 < fields[1].0);
    assert_ne!(fields[0].1, fields[1].1);
    let target = fields[1].0;
    completion_mutation(&result, target, |nodes| {
        let Some(Payload::Expression { parameters, .. }) = &mut nodes[target].payload else {
            unreachable!()
        };
        parameters[0].1 = Type::Q;
    });
    completion_mutation(&result, target, |nodes| {
        nodes[target].arguments[1] = fields[0].1;
    });
    let evaluation = result.nodes.iter().enumerate().find_map(|(index,node)| {
        matches!(&node.payload,Some(Payload::Evaluation{expression,..}) if *expression==NodeRef(target))
            .then_some(index)
    }).unwrap();
    completion_mutation(&result, evaluation, |nodes| {
        let Some(Payload::Evaluation { expression, .. }) = &mut nodes[evaluation].payload else {
            unreachable!()
        };
        *expression = NodeRef(fields[0].0);
        nodes[evaluation].arguments[0] = NodeRef(fields[0].0);
    });
}

#[test]
fn universal_classification_stop_retains_prior_results_and_type_domain_prefix() {
    universal_private_stop(0, 0);
}
#[test]
fn universal_bool_post_stop_retains_value_without_unfinished_normalization() {
    universal_private_stop(2, 1);
}
#[test]
fn universal_normalization_post_stop_retains_completed_prefix() {
    universal_private_stop(3, 2);
}
#[test]
fn universal_counterexample_post_stop_retains_completed_evidence() {
    universal_private_stop(4, 0);
}
#[test]
fn universal_numeric_pair_post_stop_retains_both_completed_witnesses() {
    universal_private_stop(6, 2);
}
#[test]
fn universal_integer_gcd_stop_retains_original_type_domain_prefix() {
    universal_private_stop(8, 0);
}
#[test]
fn universal_verified_current_stop_retains_current_and_unstarted_request() {
    universal_private_stop(7, 0);
}

fn universal_private_stop(stage: usize, kind: usize) {
    use super::super::{
        affine,
        control::{Limits, Resource, Usage},
    };
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let current = if stage == 4 {
        "law required current(z:Z,s:Sample):z+s.z=z+s.z+1;"
    } else if stage == 6 {
        "view current(s:Sample):Bool=forall z:Z . z+s.z=z;"
    } else if stage == 8 {
        "view current(s:Sample):Bool=forall z:Z . 2*s.z+4*s.k=1;"
    } else {
        "view current(s:Sample):Bool=forall z:Z . z+s.z=z+s.z;"
    };
    let sources = affine_private_fixture(&format!(
        "view seed():Z=7;law required prior():1=2;view hole(s:Sample):Z=s.k;{current}view later():Z=19;"
    ));
    let asks = [
        "seed=evaluate(Calc.seed)",
        "prior=check(Calc.prior)",
        "hole=evaluate(Calc.hole,s=@v/sample)",
        if stage == 4 {
            "current=check(Calc.current,s=@v/sample)"
        } else {
            "current=evaluate(Calc.current,s=@v/sample)"
        },
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
    rebuild_for_origin_and_support_recheck(&normal, &normal.nodes).unwrap();
    let (limits, usage, expected) = match kind {
        0 => (
            Limits::default(),
            Usage {
                signal: Some(Signal::Term),
                ..Usage::default()
            },
            StopReason::Cancelled(Signal::Term),
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
    };
    let ready = Rc::new(Cell::new(false));
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |point| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(point, Checkpoint::FiniteIteration);
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Usage::default()
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
                                    && operation == "universal"
                                    && index == stage
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
    assert_eq!(Some(probes.get()), frozen.get());
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
    let (Json::Arr(normal_nodes), Json::Arr(stopped_nodes)) =
        (&normal_wire["nodes"], &stopped_wire["nodes"])
    else {
        unreachable!()
    };
    assert_eq!(stopped_nodes, &normal_nodes[..stopped_nodes.len()]);
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    let before = probes.get();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(probes.get(), before);
}

#[test]
fn universal_normalization_fresh_recheck_stop_does_not_reuse_success_memo() {
    use super::super::{
        affine,
        control::{Limits, Usage},
    };
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    let result = universal_private_example(
        "view all(s:Sample):Bool=forall z:Z . z+s.z=z+s.z;",
        &["all=evaluate(Calc.all,s=@v/sample)"],
    );
    let normalization = universal_private_normalization(&result, 0);
    let mut graph =
        rebuild_for_origin_and_support_recheck(&result, &result.nodes[..=normalization]).unwrap();
    graph.active = result.contexts[normalization];
    let armed = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let (arm, count) = (armed.clone(), probes.clone());
    let mut control = Control::new(Limits::default(), move |point| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert_eq!(point, Checkpoint::FiniteIteration);
            Usage {
                signal: Some(Signal::Term),
                ..Usage::default()
            }
        } else {
            Usage::default()
        }
    });
    let environment = Environment::new(result.prepared.inputs(), &mut control).unwrap();
    environment
        .recheck_node(&graph, &graph.nodes[normalization], normalization)
        .unwrap();
    let before = probes.get();
    let stopped = affine::with_observer(
        move |point| {
            if point == affine::TestPoint::Universal {
                armed.set(true)
            }
        },
        || environment.recheck_node(&graph, &graph.nodes[normalization], normalization),
    );
    assert!(matches!(
        stopped,
        Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
    ));
    assert!(probes.get() > before);
    let frozen = probes.get();
    assert!(matches!(
        environment.recheck_node(&graph, &graph.nodes[normalization], normalization),
        Err(ValidationFailure::Stop(StopReason::Cancelled(Signal::Term)))
    ));
    assert_eq!(probes.get(), frozen);
    assert_eq!(
        control.checkpoint(Checkpoint::Expression),
        Err(StopReason::Cancelled(Signal::Term))
    );
    assert_eq!(probes.get(), frozen);
    rebuild_for_origin_and_support_recheck(&result, &graph.nodes).unwrap();
}
