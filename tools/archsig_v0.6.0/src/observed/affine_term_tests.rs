mod affine_term_fixture {
    include!("../../tests/common/affine_terms.rs");
}
fn affine_term_inputs(revision: &str) -> InputSources {
    let defs = affine_term_fixture::definitions();
    let d = crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        affine_term_fixture::law(digest).into_bytes(),
        affine_term_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn affine_term_result(asks: &[&str]) -> ObservedEvaluation {
    let r =
        evaluate_observed_bytes(affine_term_inputs("r1"), asks, &mut named_call_quiet()).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn affine_term_rechecks_original_program_body_type_support_scope_and_same_environment() {
    let r = affine_term_result(&["e=evaluate(Terms.same,s=@v/s)"]);
    let (_, children, result) = equality_children(&r, 0);
    let left = equality_child_value(&r, children[0]);
    let right = equality_child_value(&r, children[1]);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let (a, b) = (g.scalar(left).unwrap(), g.scalar(right).unwrap());
    assert_ne!(a, b);
    assert_eq!(
        super::super::value_equality::equal(a, b, r.prepared.inputs.law(), &named_call_quiet())
            .unwrap(),
        Some(true)
    );
    let replacement = b.clone();
    for mode in 0..7 {
        completion_mutation(&r, left.0, |ns| {
            if mode == 0 {
                ns[left.0].support.clear();
                return;
            }
            if mode == 1 {
                ns[left.0].scope.snapshots.clear();
                return;
            }
            if mode == 6 {
                ns[left.0].payload = Some(Payload::Scalar(replacement.clone()));
                return;
            }
            let Some(Payload::Scalar(Scalar::Term(t))) = &mut ns[left.0].payload else {
                panic!("Term")
            };
            match mode {
                2 => t.body = t.body.replace("2*x", "3*x"),
                3 => {
                    t.types.insert(t.root, Type::Q);
                }
                4 => t.params.swap(0, 1),
                5 => {
                    t.params.pop();
                }
                _ => unreachable!(),
            }
        });
    }
    completion_mutation(&r, result.0, |ns| {
        ns[result.0].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
    let mut graph = g;
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    e.recheck_node(&graph, &graph.nodes[left.0], left.0)
        .unwrap();
    let original = graph.nodes[left.0].clone();
    graph.nodes[left.0].payload = Some(Payload::Scalar(replacement));
    assert!(matches!(
        e.recheck_node(&graph, &graph.nodes[left.0], left.0),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[left.0] = original;
    e.recheck_node(&graph, &graph.nodes[left.0], left.0)
        .unwrap();
}
#[test]
fn affine_term_equality_rejects_coherent_foreign_same_value_left_and_right_producers() {
    let r = affine_term_result(&[
        "first=evaluate(Terms.same,s=@v/s)",
        "second=evaluate(Terms.same,s=@v/s)",
    ]);
    let (_, donors, _) = equality_children(&r, 0);
    let (target, originals, result) = equality_children(&r, 1);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for position in 0..2 {
        let (original, donor) = (originals[position], donors[position]);
        let (a, b) = (
            equality_child_value(&r, original),
            equality_child_value(&r, donor),
        );
        assert!(donor.0 < original.0 && b.0 < a.0);
        assert_ne!(a, b);
        assert_eq!(g.scalar(a).unwrap().ty(), g.scalar(b).unwrap().ty());
        assert_eq!(
            super::super::value_equality::equal(
                g.scalar(a).unwrap(),
                g.scalar(b).unwrap(),
                r.prepared.inputs.law(),
                &named_call_quiet()
            )
            .unwrap(),
            Some(true)
        );
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Evaluation { parts, .. }) = &mut ns[target].payload else {
                panic!("evaluation")
            };
            parts[0].children[position] = donor;
            for edge in &mut ns[result.0].arguments {
                if *edge == a {
                    *edge = b
                }
            }
            for edge in &mut ns[target].arguments {
                if *edge == original {
                    *edge = donor
                }
            }
        });
    }
}
#[test]
fn affine_term_application_rejects_result_actual_argument_and_callee_producer_donation() {
    let r = affine_term_result(&[
        "first=evaluate(Terms.partial,s=@v/s)",
        "second=evaluate(Terms.partial,s=@v/s)",
    ]);
    let (_, donors, _) = equality_children(&r, 0);
    let (target, originals, result) = equality_children(&r, 1);
    assert_eq!(originals.len(), 3);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_eq!(g.scalar(result).unwrap(), &Scalar::Z(1.into()));
    assert_eq!(r.nodes[result.0].arguments.len(), 4);
    for position in 0..3 {
        let (original, donor) = (originals[position], donors[position]);
        assert!(donor.0 < original.0);
        assert_ne!(original, donor);
        assert_eq!(r.nodes[original.0].ty, r.nodes[donor.0].ty);
        if position != 1 {
            let (a, b) = (
                equality_child_value(&r, original),
                equality_child_value(&r, donor),
            );
            assert_ne!(a, b);
            assert_eq!(g.scalar(a).unwrap().ty(), g.scalar(b).unwrap().ty());
            assert_eq!(
                super::super::value_equality::equal(
                    g.scalar(a).unwrap(),
                    g.scalar(b).unwrap(),
                    r.prepared.inputs.law(),
                    &named_call_quiet()
                )
                .unwrap(),
                Some(true)
            );
        } else {
            let Some(Payload::Evaluation { value: None, .. }) = &r.nodes[original.0].payload else {
                panic!("missing actual")
            };
            assert!(r.nodes[original.0].reasons.iter().any(|r| {
                r.missing
                    .iter()
                    .any(|f| f.field.as_deref() == Some("Terms.Sample.h"))
            }));
        }
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Evaluation { parts, .. }) = &mut ns[target].payload else {
                panic!("evaluation")
            };
            parts[0].children[position] = donor;
            assert_eq!(ns[result.0].arguments[position + 1], original);
            ns[result.0].arguments[position + 1] = donor;
            for edge in &mut ns[target].arguments {
                if *edge == original {
                    *edge = donor
                }
            }
        });
    }
    completion_mutation(&r, result.0, |ns| {
        ns[result.0].payload = Some(Payload::Scalar(Scalar::Z(2.into())))
    });
    let mut graph = g;
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    e.recheck_node(&graph, &graph.nodes[result.0], result.0)
        .unwrap();
    let original = graph.nodes[result.0].clone();
    graph.nodes[result.0].payload = Some(Payload::Scalar(Scalar::Z(2.into())));
    assert!(matches!(
        e.recheck_node(&graph, &graph.nodes[result.0], result.0),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[result.0] = original;
    e.recheck_node(&graph, &graph.nodes[result.0], result.0)
        .unwrap();
}
#[test]
fn affine_term_application_rechecks_normalization_and_typed_algorithm_obligations() {
    let r = affine_term_result(&[
        "i=evaluate(Terms.cancelEquality,s=@v/s)",
        "o=evaluate(Terms.opaque)",
        "m=evaluate(Terms.opaqueMissing,s=@v/s)",
        "t=evaluate(Terms.tupleOutside,s=@v/s)",
    ]);
    let normalizations: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.payload, Some(Payload::Normalization { .. })).then_some(i))
        .collect();
    assert!(!normalizations.is_empty());
    for target in normalizations {
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Normalization { steps, .. }) = &mut ns[target].payload else {
                panic!("normalization")
            };
            assert!(!steps.is_empty());
            steps.pop();
        });
    }
    for index in [1, 2, 3] {
        let target = r.answers[index].outputs["evaluation"].0;
        for mode in 0..3 {
            completion_mutation(&r, target, |ns| {
                let reason = ns[target]
                    .reasons
                    .iter_mut()
                    .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                    .unwrap();
                if mode == 2 {
                    reason.dependencies.clear();
                    return;
                }
                let ReasonKind::UnsupportedAlgorithm {
                    operand_types,
                    method,
                    ..
                } = &mut reason.kind
                else {
                    unreachable!()
                };
                if mode == 0 {
                    *operand_types = vec![Type::Bool]
                } else {
                    *method = "different predicate".into()
                }
            });
        }
    }
}
fn affine_term_stop_in_batch(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let current = if recheck {
        "current=evaluate(Terms.partial,s=@v/s)"
    } else {
        "current=evaluate(Terms.mixed)"
    };
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        current,
        "later=evaluate(Terms.seed)",
    ];
    let normal = affine_term_result(&asks);
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let in_recheck = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, phase, s, p, f) = (
        armed.clone(),
        in_recheck.clone(),
        seen.clone(),
        probes.clone(),
        frozen.clone(),
    );
    let mut c = Control::new(limits, move |checkpoint| {
        p.set(p.get() + 1);
        let stop = if recheck {
            if phase.get() && checkpoint == Checkpoint::Expression {
                assert!(!s.replace(true));
                true
            } else {
                false
            }
        } else {
            a.replace(false)
        };
        if stop {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(affine_term_inputs("r1"), &asks, &mut c).unwrap();
    let mut recheck_control = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" && !recheck {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                if ctx.request == 2 && operation == "term_affine_case" && index == 1 {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::new(normal.prepared.inputs(), &mut recheck_control)?;
            in_recheck.set(true);
            let checked = fresh.validate_answer(g, request, answer);
            in_recheck.set(false);
            checked?;
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, &normal.contexts[..stopped.contexts.len()]);
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for (index, answer) in stopped.answers.iter().enumerate().skip(2) {
        assert!(answer.claim.is_none() && answer.evidence.is_empty());
        if recheck && index == 2 {
            // 元missingを伴う確定値はcomplete_answerで既に独立検査・保存されている。
            assert_eq!(answer.status, Decision::Established);
            assert_eq!(answer.outputs, normal.answers[index].outputs);
            assert!(!normal.answers[index].reasons.is_empty());
            for original in &normal.answers[index].reasons {
                assert!(answer.reasons.iter().any(|r| r.wire() == original.wire()));
            }
        } else {
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(answer.outputs.is_empty())
        }
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("details")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn affine_term_actual_case_stop_preserves_prior_value_refutation_and_verified_prefix() {
    affine_term_stop_in_batch(false)
}
#[test]
fn affine_term_actual_original_input_recheck_stop_preserves_prior_value_refutation_and_verified_prefix()
 {
    affine_term_stop_in_batch(true)
}
fn affine_term_certificate_mutations(ask: &str) {
    let r = affine_term_result(&[ask]);
    let proofs: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.payload, Some(Payload::TermComparison { .. })).then_some(i))
        .collect();
    assert_eq!(proofs.len(), 2);
    for &target in &proofs {
        for mode in 0..6 {
            completion_mutation(&r, target, |ns| {
                if mode == 0 {
                    ns[target].support.push(Fact {
                        snapshot: "v".into(),
                        subject: "s".into(),
                        field: None,
                        atom: None,
                    });
                    return;
                }
                if mode == 1 {
                    ns[target].scope.readings.clear();
                    return;
                }
                let Some(Payload::TermComparison {
                    certificate,
                    left,
                    right,
                    ..
                }) = &mut ns[target].payload
                else {
                    panic!("certificate")
                };
                match mode {
                    2 => {
                        certificate.cases.clear();
                    }
                    3 => {
                        certificate.cases[0].arguments.clear();
                    }
                    4 => {
                        let c = named_call_quiet();
                        let ty = certificate.cases[0].left.ty(&c).unwrap();
                        let changed = super::super::numeric::literal("17", &ty, &c).unwrap();
                        certificate.cases[0].left = super::super::term::affine::Value::Number(
                            super::super::affine::constant(&changed, &c)
                                .unwrap()
                                .unwrap(),
                        );
                    }
                    5 => {
                        std::mem::swap(left, right);
                    }
                    _ => unreachable!(),
                }
            });
        }
        if matches!(&r.nodes[target].payload,Some(Payload::TermComparison{certificate,..}) if certificate.point.is_some())
        {
            for mode in 0..3 {
                completion_mutation(&r, target, |ns| {
                    let Some(Payload::TermComparison { certificate, .. }) = &mut ns[target].payload
                    else {
                        panic!("certificate")
                    };
                    if mode == 0 {
                        certificate.point = None;
                        return;
                    }
                    let point = certificate.point.as_mut().unwrap();
                    if mode == 1 {
                        point.arguments.clear();
                    } else {
                        point.right = point.left.clone();
                    }
                });
            }
        }
    }
    let value = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| n.evidence.contains(&NodeRef(proofs[0])).then_some(i))
        .unwrap();
    completion_mutation(&r, value, |ns| ns[value].evidence.clear());
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    let target = proofs[0];
    e.recheck_node(&graph, &graph.nodes[target], target)
        .unwrap();
    let original = graph.nodes[target].clone();
    let Some(Payload::TermComparison { certificate, .. }) = &mut graph.nodes[target].payload else {
        panic!("certificate")
    };
    certificate.cases.clear();
    assert!(matches!(
        e.recheck_node(&graph, &graph.nodes[target], target),
        Err(ValidationFailure::Internal(_))
    ));
    graph.nodes[target] = original;
    e.recheck_node(&graph, &graph.nodes[target], target)
        .unwrap();
}
#[test]
fn affine_term_comparison_rechecks_retained_forms_points_and_evidence_after_normal_prefix() {
    affine_term_certificate_mutations("e=evaluate(Terms.same,s=@v/s)");
}
#[test]
fn affine_term_integer_point_rechecks_retained_forms_and_original_reapplication() {
    affine_term_certificate_mutations("d=check(Terms.unequal,s=@v/s)");
}
#[test]
fn affine_term_rational_point_rechecks_retained_forms_and_original_reapplication() {
    affine_term_certificate_mutations("q=evaluate(Terms.qCoefficient)");
}
#[test]
fn affine_term_comparison_rejects_foreign_coherent_same_value_certificate_producers() {
    let r = affine_term_result(&[
        "first=evaluate(Terms.same,s=@v/s)",
        "second=evaluate(Terms.same,s=@v/s)",
    ]);
    let proofs: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.payload, Some(Payload::TermComparison { .. })).then_some(i))
        .collect();
    assert_eq!(proofs.len(), 4);
    let (donor, target) = (proofs[0], proofs[2]);
    assert!(donor < target);
    let (
        Some(Payload::TermComparison { certificate: a, .. }),
        Some(Payload::TermComparison { certificate: b, .. }),
    ) = (&r.nodes[donor].payload, &r.nodes[target].payload)
    else {
        panic!("certificate")
    };
    assert!(a.identical(b, &named_call_quiet()).unwrap());
    completion_mutation(&r, target, |ns| {
        let foreign = ns[donor].clone();
        ns[target].payload = foreign.payload;
        ns[target].arguments = foreign.arguments;
    });
    let result = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| n.evidence.contains(&NodeRef(target)).then_some(i))
        .unwrap();
    completion_mutation(&r, result, |ns| ns[result].evidence[0] = NodeRef(donor));
}
#[test]
fn affine_tuple_binding_rechecks_unknown_actual_producers_and_cached_source_components() {
    let r = affine_term_result(&[
        "first=evaluate(Terms.viaTupleView,s=@v/s)",
        "second=evaluate(Terms.viaTupleView,s=@v/s)",
    ]);
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let mut applications = Vec::new();
    for (i, n) in r.nodes.iter().enumerate() {
        let Some(Payload::Evaluation {
            expression,
            parts,
            value: Some(v),
            ..
        }) = &n.payload
        else {
            continue;
        };
        let Some(Payload::Expression {
            location: Location::Law { span },
            ..
        }) = &r.nodes[expression.0].payload
        else {
            continue;
        };
        let source =
            std::str::from_utf8(&r.prepared.inputs.sources().law().bytes()[span.0..span.1])
                .unwrap();
        if source == "(fn(u:(Z,Q))=>u.1-u.1)(t)" {
            assert_eq!(graph.scalar(*v).unwrap(), &Scalar::Q(0.into(), 1.into()));
            assert_eq!(parts[0].children.len(), 2);
            applications.push((i, parts[0].children.clone(), *v));
        }
    }
    assert_eq!(applications.len(), 2);
    let (target, children, value) = &applications[1];
    let donor = applications[0].1[1];
    let original = children[1];
    assert!(donor.0 < original.0);
    assert_ne!(donor, original);
    assert_eq!(r.nodes[donor.0].ty, r.nodes[original.0].ty);
    assert!(matches!(
        &r.nodes[donor.0].payload,
        Some(Payload::Evaluation { value: None, .. })
    ));
    assert!(matches!(
        &r.nodes[original.0].payload,
        Some(Payload::Evaluation { value: None, .. })
    ));
    completion_mutation(&r, *target, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[*target].payload else {
            panic!("evaluation")
        };
        parts[0].children[1] = donor;
        for edge in &mut ns[*target].arguments {
            if *edge == original {
                *edge = donor;
            }
        }
        assert_eq!(ns[value.0].arguments[2], original);
        ns[value.0].arguments[2] = donor;
    });
    // 同じview本体を、一つの問いのh/qとk/qという異なる成分で再分析する。
    let r = affine_term_result(&["c=evaluate(Terms.tupleCache,s=@v/s)"]);
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_eq!(
        graph.scalar(r.answers[0].outputs["value"]).unwrap(),
        &Scalar::Bool(true)
    );
    assert_eq!(r.status(), "complete");
}

#[test]
fn affine_term_standard_evidence_rechecks_typed_matrix_point_nodes_and_foreign_producers() {
    let r = affine_term_result(&[
        "a=evaluate(Terms.same,s=@v/s)",
        "b=evaluate(Terms.same,s=@v/s)",
        "q=evaluate(Terms.qCoefficient)",
    ]);
    let normals: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| match &n.payload {
            Some(Payload::TermComparison { after, .. }) => Some((i, *after)),
            _ => None,
        })
        .collect();
    assert_eq!(normals.len(), 6);
    for &(proof, value) in &normals {
        completion_mutation(&r, value.0, |ns| {
            let Some(Payload::Scalar(Scalar::List { items, .. })) = &mut ns[value.0].payload else {
                panic!("matrix")
            };
            items.clear();
        });
        completion_mutation(&r, proof, |ns| {
            let Some(Payload::TermComparison { after, .. }) = &mut ns[proof].payload else {
                panic!("normal")
            };
            *after = NodeRef(0);
        });
    }
    let (donor, target) = (normals[0].1, normals[2].1);
    assert_eq!(r.nodes[donor.0].payload, r.nodes[target.0].payload);
    completion_mutation(&r, target.0, |ns| {
        ns[target.0].arguments = ns[donor.0].arguments.clone()
    });
    let (counter, bindings, left, right) = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| match &n.payload {
            Some(Payload::TermCounterexample {
                bindings,
                left,
                right,
                ..
            }) => Some((i, bindings.clone(), *left, *right)),
            _ => None,
        })
        .unwrap();
    for reference in bindings.iter().map(|b| b.value).chain([left, right]) {
        completion_mutation(&r, reference.0, |ns| {
            let Some(Payload::Scalar(value)) = &mut ns[reference.0].payload else {
                panic!("point")
            };
            *value =
                super::super::numeric::literal("17", &value.ty(), &named_call_quiet()).unwrap();
        });
    }
    for mode in 0..4 {
        completion_mutation(&r, counter, |ns| {
            let Some(Payload::TermCounterexample {
                bindings,
                left,
                right,
                ..
            }) = &mut ns[counter].payload
            else {
                panic!("counter")
            };
            match mode {
                0 => bindings[0].name = "foreign".into(),
                1 => bindings[0].ty = Type::Z,
                2 => std::mem::swap(left, right),
                3 => {
                    bindings.clear();
                }
                _ => unreachable!(),
            }
        });
    }
}
#[test]
fn affine_missing_tuple_rechecks_whole_slot_completions_and_component_correlations() {
    let r = affine_term_result(&[
        "e=evaluate(Terms.tupleSlotEq,s=@v/s)",
        "u=check(Terms.tupleSlotVary,s=@v/s)",
    ]);
    let (counter, first) = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| match &n.payload {
            Some(Payload::CompletionPair { first, .. }) => Some((i, first.clone())),
            _ => None,
        })
        .unwrap();
    assert_eq!(first.len(), 1);
    let slot = first[0];
    assert!(matches!(
        r.nodes[slot.0].payload,
        Some(Payload::Scalar(Scalar::Tuple(_)))
    ));
    completion_mutation(&r, slot.0, |ns| {
        let Some(Payload::Scalar(Scalar::Tuple(values))) = &mut ns[slot.0].payload else {
            panic!("whole Tuple")
        };
        values.swap(0, 1);
        values[0] = Scalar::Z(17.into());
    });
    completion_mutation(&r, counter, |ns| {
        let Some(Payload::CompletionPair { fields, .. }) = &mut ns[counter].payload else {
            panic!("pair")
        };
        fields[0].field = Some("Terms.Sample.t".into());
    });
}
#[test]
fn affine_term_point_rejects_coherent_foreign_same_value_arguments_outputs_and_evidence() {
    let r = affine_term_result(&[
        "first=evaluate(Terms.qCoefficient)",
        "second=evaluate(Terms.qCoefficient)",
    ]);
    let proofs: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| match &n.payload {
            Some(Payload::TermCounterexample {
                bindings,
                left,
                right,
                ..
            }) => Some((i, bindings.clone(), *left, *right)),
            _ => None,
        })
        .collect();
    assert_eq!(proofs.len(), 2);
    let (donor, target) = (&proofs[0], &proofs[1]);
    for (d, t) in donor
        .1
        .iter()
        .map(|b| b.value)
        .chain([donor.2, donor.3])
        .zip(target.1.iter().map(|b| b.value).chain([target.2, target.3]))
    {
        assert!(d.0 < t.0);
        assert_eq!(r.nodes[d.0].payload, r.nodes[t.0].payload);
        completion_mutation(&r, t.0, |ns| ns[t.0].arguments = ns[d.0].arguments.clone());
    }
    completion_mutation(&r, target.0, |ns| {
        let foreign = ns[donor.0].clone();
        ns[target.0].payload = foreign.payload;
        ns[target.0].arguments = foreign.arguments;
    });
}
