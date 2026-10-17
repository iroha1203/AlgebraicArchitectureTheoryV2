mod equality_fixture {
    include!("../../tests/common/term_equality.rs");
}
fn equality_inputs(revision: &str) -> InputSources {
    let defs = equality_fixture::definitions();
    let checked =
        crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        equality_fixture::law(digest).into_bytes(),
        equality_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn equality_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(equality_inputs("r1"), asks, &mut named_call_quiet()).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn finite_term_equality_visits_all_original_argument_products() {
    use std::{cell::RefCell, rc::Rc};
    let counts = Rc::new(RefCell::new(BTreeMap::<usize, Vec<usize>>::new()));
    let seen = counts.clone();
    data::observe_iterations(move |_, ctx, op, index| {
        if op == "term_extensional_case" {
            seen.borrow_mut()
                .entry(ctx.request)
                .or_default()
                .push(index);
        }
    });
    let r = equality_result(&[
        "s=evaluate(Terms.selfEq,s=@v/s)",
        "m=evaluate(Terms.multi)",
        "z=evaluate(Terms.zero)",
        "f=evaluate(Terms.fp)",
        "d=evaluate(Terms.finiteData)",
        "t=evaluate(Terms.tuple)",
    ]);
    data::clear_iteration_observer();
    assert_eq!(r.status(), "complete");
    for (request, n) in [2, 8, 1, 3, 3, 8].into_iter().enumerate() {
        assert_eq!(counts.borrow()[&request], (0..n).collect::<Vec<_>>());
    }
}
#[test]
fn finite_term_equality_does_not_evaluate_skipped_boolean_or_quantifier_comparisons() {
    use std::{cell::RefCell, rc::Rc};
    let counts = Rc::new(RefCell::new(BTreeMap::<usize, usize>::new()));
    let seen = counts.clone();
    data::observe_iterations(move |_, ctx, op, _| {
        if op == "term_extensional_case" {
            *seen.borrow_mut().entry(ctx.request).or_default() += 1;
        }
    });
    let r = equality_result(&[
        "a=evaluate(Terms.andSkip)",
        "o=evaluate(Terms.orSkip)",
        "i=evaluate(Terms.impliesSkip)",
        "l=evaluate(Terms.allSkip)",
        "e=evaluate(Terms.anySkip)",
        "n=evaluate(Terms.andNeeded)",
        "nl=evaluate(Terms.allNeeded)",
        "ne=evaluate(Terms.anyNeeded)",
    ]);
    data::clear_iteration_observer();
    assert_eq!(r.status(), "complete");
    for request in 0..5 {
        assert_eq!(counts.borrow().get(&request).copied().unwrap_or(0), 0);
    }
    for request in 5..8 {
        assert_eq!(counts.borrow()[&request], 1);
    }
}
fn equality_children(r: &ObservedEvaluation, index: usize) -> (usize, Vec<NodeRef>, NodeRef) {
    let root = r.answers[index].outputs["evaluation"].0;
    let Some(Payload::Evaluation {
        parts,
        value: Some(value),
        ..
    }) = &r.nodes[root].payload
    else {
        panic!("evaluation")
    };
    (root, parts[0].children.clone(), *value)
}
fn equality_child_value(r: &ObservedEvaluation, reference: NodeRef) -> NodeRef {
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &r.nodes[reference.0].payload
    else {
        panic!("child")
    };
    *value
}
#[test]
fn finite_term_equality_rejects_foreign_same_value_operand_producers() {
    let r = equality_result(&[
        "first=evaluate(Terms.eq,s=@v/s)",
        "second=evaluate(Terms.eq,s=@v/s)",
    ]);
    let (_, donors, _) = equality_children(&r, 0);
    let (target, originals, result) = equality_children(&r, 1);
    assert_eq!(originals.len(), 2);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for position in [0, 1] {
        let (original, donor) = (originals[position], donors[position]);
        let (a, b) = (
            equality_child_value(&r, original),
            equality_child_value(&r, donor),
        );
        assert_ne!(original, donor);
        assert_ne!(a, b);
        assert!(donor.0 < original.0 && b.0 < a.0);
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
        assert!(r.nodes[result.0].arguments.contains(&a));
        assert!(r.nodes[target].arguments.contains(&original));
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Evaluation { parts, .. }) = &mut ns[target].payload else {
                panic!("root")
            };
            parts[0].children[position] = donor;
            for edge in &mut ns[result.0].arguments {
                if *edge == a {
                    *edge = b;
                }
            }
            for edge in &mut ns[target].arguments {
                if *edge == original {
                    *edge = donor;
                }
            }
        });
    }
    completion_mutation(&r, result.0, |ns| {
        ns[result.0].payload = Some(Payload::Scalar(Scalar::Bool(false)))
    });
}
#[test]
fn finite_term_equality_keeps_original_program_identity_after_semantic_comparison() {
    let r = equality_result(&["e=evaluate(Terms.eq,s=@v/s)"]);
    let (_, children, _) = equality_children(&r, 0);
    let (left, right) = (
        equality_child_value(&r, children[0]),
        equality_child_value(&r, children[1]),
    );
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let (a, b) = (g.scalar(left).unwrap(), g.scalar(right).unwrap());
    assert_ne!(a, b);
    assert_eq!(
        super::super::value_equality::equal(a, b, r.prepared.inputs.law(), &named_call_quiet())
            .unwrap(),
        Some(true)
    );
    for mode in 0..4 {
        completion_mutation(&r, left.0, |ns| match mode {
            0 => ns[left.0].support.clear(),
            1 => ns[left.0].scope.snapshots.clear(),
            _ => {
                let Some(Payload::Scalar(Scalar::Term(t))) = &mut ns[left.0].payload else {
                    panic!("Term")
                };
                if mode == 2 {
                    t.types.insert(t.root, Type::Q);
                } else {
                    t.body = t.body.replace("4", "5");
                }
            }
        });
    }
    let replacement = b.clone();
    completion_mutation(&r, left.0, |ns| {
        ns[left.0].payload = Some(Payload::Scalar(replacement.clone()))
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
fn finite_term_completion_rechecks_original_representative_and_unsupported_reason() {
    let r = equality_result(&[
        "s=evaluate(Terms.stable,s=@v/s)",
        "x=evaluate(Terms.unresolved,s=@v/s)",
    ]);
    let root = r.answers[0].outputs["evaluation"].0;
    let value = r.answers[0].outputs["value"];
    let Some(Payload::Evaluation { parts, .. }) = &r.nodes[root].payload else {
        panic!("root")
    };
    assert_eq!(parts[0].children.len(), 2);
    let values: Vec<_> = parts[0]
        .children
        .iter()
        .map(|e| equality_child_value(&r, *e))
        .collect();
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let original = g.scalar(value).unwrap();
    let donor = values
        .iter()
        .map(|v| g.scalar(*v).unwrap())
        .find(|v| *v != original)
        .unwrap()
        .clone();
    assert_eq!(
        super::super::value_equality::equal(
            original,
            &donor,
            r.prepared.inputs.law(),
            &named_call_quiet()
        )
        .unwrap(),
        Some(true)
    );
    completion_mutation(&r, value.0, |ns| {
        ns[value.0].payload = Some(Payload::Scalar(donor.clone()))
    });
    let target = r.answers[1].outputs["evaluation"].0;
    for mode in [0, 1] {
        completion_mutation(&r, target, |ns| {
            let reason = ns[target]
                .reasons
                .iter_mut()
                .find(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
                .unwrap();
            let ReasonKind::UnsupportedAlgorithm {
                operand_types,
                method,
                ..
            } = &mut reason.kind
            else {
                panic!("reason")
            };
            if mode == 0 {
                *operand_types = vec![Type::Bool];
            } else {
                *method = "different predicate".into();
            }
        });
    }
}

fn equality_stop_in_batch(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        "current=evaluate(Terms.eq,s=@v/s)",
        "later=evaluate(Terms.seed)",
    ];
    let normal = equality_result(&asks);
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
    let prepared = prepare_observed(equality_inputs("r1"), &asks, &mut c).unwrap();
    let mut recheck_control = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" && !recheck {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                if ctx.request == 2 && operation == "term_extensional_case" && index == 1 {
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
            // 元入力の独立検査を終えた値と判断を、fresh再検査の停止後も保持する。
            assert_eq!(answer.status, normal.answers[index].status);
            assert_eq!(answer.outputs, normal.answers[index].outputs);
            assert_eq!(answer.claim, normal.answers[index].claim);
            assert_eq!(answer.evidence, normal.answers[index].evidence);
            assert_eq!(answer.scope, normal.answers[index].scope);
        } else {
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(answer.outputs.is_empty());
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
fn finite_term_case_stop_preserves_prior_values_refutation_and_verified_prefix() {
    equality_stop_in_batch(false);
}
#[test]
fn finite_term_actual_recheck_stop_preserves_prior_values_refutation_and_verified_prefix() {
    equality_stop_in_batch(true);
}
