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
#[test]
fn affine_term_comparison_rechecks_retained_forms_points_and_evidence_after_normal_prefix() {
    let r = affine_term_result(&[
        "e=evaluate(Terms.same,s=@v/s)",
        "d=check(Terms.unequal,s=@v/s)",
        "q=evaluate(Terms.qCoefficient)",
    ]);
    let proofs: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.payload, Some(Payload::TermComparison { .. })).then_some(i))
        .collect();
    assert_eq!(proofs.len(), 3);
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
        .find_map(|(i, n)| (n.evidence == [NodeRef(proofs[0])]).then_some(i))
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
    assert_eq!(proofs.len(), 2);
    let (donor, target) = (proofs[0], proofs[1]);
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
        .find_map(|(i, n)| (n.evidence == [NodeRef(target)]).then_some(i))
        .unwrap();
    completion_mutation(&r, result, |ns| ns[result].evidence = vec![NodeRef(donor)]);
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
