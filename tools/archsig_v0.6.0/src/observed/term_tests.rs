mod term_fixture {
    include!("../../tests/common/terms.rs");
}
fn term_private_inputs(revision: &str) -> InputSources {
    let d = crate::definition::check_definitions(&[(
        "definition0",
        term_fixture::DEFINITIONS.as_bytes(),
    )])
    .unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![term_fixture::DEFINITIONS.as_bytes().to_vec()],
        term_fixture::law(digest).into_bytes(),
        term_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn term_private_result(asks: &[&str]) -> ObservedEvaluation {
    let mut c = named_call_quiet();
    let p = prepare_observed(term_private_inputs("r1"), asks, &mut c).unwrap();
    evaluate_observed(p, &mut c).unwrap()
}
#[test]
fn closed_term_rechecks_body_parameters_hidden_ast_types_support_and_scope() {
    let r = term_private_result(&["f=evaluate(Terms.read,s=@v/s)"]);
    let t = r.answers[0].outputs["value"].0;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for mode in 0..7 {
        completion_mutation(&r, t, |ns| {
            if mode == 5 {
                ns[t].support.clear();
                return;
            }
            if mode == 6 {
                ns[t].scope.snapshots.clear();
                return;
            }
            let Some(Payload::Scalar(Scalar::Term(term))) = &mut ns[t].payload else {
                panic!("Term")
            };
            match mode {
                0 => term.body = term.body.replace("2*x", "3*x"),
                1 => term.params.swap(0, 1),
                2 => {
                    term.types.insert(term.root, Type::Q);
                }
                3 => {
                    let id = term
                        .nodes
                        .iter()
                        .find_map(|(i, e)| {
                            matches!(e.kind, ExprKind::Binary { op: BinOp::Sub, .. }).then_some(*i)
                        })
                        .unwrap();
                    let ExprKind::Binary { op, .. } = &mut term.nodes.get_mut(&id).unwrap().kind
                    else {
                        panic!("binary")
                    };
                    *op = BinOp::Add;
                }
                4 => {
                    term.params.pop();
                }
                _ => unreachable!(),
            }
        });
    }
}
#[test]
fn closed_term_rechecks_application_value_and_equal_earlier_request_producers() {
    let r = term_private_result(&[
        "first=evaluate(Terms.applied,s=@v/s)",
        "second=evaluate(Terms.applied,s=@v/s)",
    ]);
    let target = r.answers[1].outputs["evaluation"].0;
    let donor = r.answers[0].outputs["evaluation"].0;
    let Some(Payload::Evaluation {
        parts: donor_parts, ..
    }) = &r.nodes[donor].payload
    else {
        panic!("donor")
    };
    let donor_callee = donor_parts[0].children[0];
    let Some(Payload::Evaluation {
        parts,
        value: Some(result),
        ..
    }) = &r.nodes[target].payload
    else {
        panic!("application")
    };
    let original_callee = parts[0].children[0];
    let result = *result;
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let Some(Payload::Evaluation { value: Some(a), .. }) = &r.nodes[original_callee.0].payload
    else {
        panic!("callee value")
    };
    let Some(Payload::Evaluation { value: Some(b), .. }) = &r.nodes[donor_callee.0].payload else {
        panic!("donor value")
    };
    let (a, b) = (*a, *b);
    assert_eq!(g.scalar(a).unwrap(), g.scalar(b).unwrap());
    assert!(donor_callee.0 < original_callee.0);
    completion_mutation(&r, target, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[target].payload else {
            panic!("evaluation")
        };
        parts[0].children[0] = donor_callee;
        for edge in &mut ns[result.0].arguments {
            if *edge == a {
                *edge = b;
            }
        }
        for edge in &mut ns[target].arguments {
            if *edge == original_callee {
                *edge = donor_callee
            }
        }
    });
    completion_mutation(&r, result.0, |ns| {
        ns[result.0].payload = Some(Payload::Scalar(Scalar::Z(12.into())))
    });
}
#[test]
fn closed_term_same_environment_rejects_changed_resident_program() {
    let r = term_private_result(&["f=evaluate(Terms.read,s=@v/s)"]);
    let t = r.answers[0].outputs["value"].0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.nodes[t].clone();
    let Some(Payload::Scalar(Scalar::Term(term))) = &mut g.nodes[t].payload else {
        panic!("Term")
    };
    term.types.insert(term.root, Type::Q);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[t] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
}
#[test]
fn closed_term_body_cancel_keeps_prior_value_refutation_and_verified_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        "current=evaluate(Terms.applied,s=@v/s)",
        "later=evaluate(Terms.seed)",
    ];
    let normal = term_private_result(&asks);
    let (limits, usage, expected) = reservations_private_stop_usage(0);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            f.set(Some(p.get()));
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(term_private_inputs("r1"), &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, op, _| {
                if ctx.request == 2 && op == "term_body" {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
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
    assert_eq!(normal.answers[0].status, Decision::Established);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    for answer in &stopped.answers[2..] {
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty() && answer.claim.is_none());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if *s==expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            panic!("reason")
        };
        let Json::Obj(ref wanted) = expected.wire() else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn closed_term_structural_recheck_stops_without_changing_program_or_reprobing() {
    use std::{cell::Cell, rc::Rc};
    let r = term_private_result(&["f=evaluate(Terms.read,s=@v/s)"]);
    let t = r.answers[0].outputs["value"].0;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let Some(Payload::Scalar(Scalar::Term(term))) = &r.nodes[t].payload else {
        panic!("Term")
    };
    let original = term.clone();
    let (limits, usage, expected) = reservations_private_stop_usage(2);
    let probes = Rc::new(Cell::new(0));
    let p = probes.clone();
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if p.get() == 3 {
            usage
        } else {
            Default::default()
        }
    });
    assert!(matches!(term.check(&c),Err(ValidationFailure::Stop(ref stop)) if *stop==expected));
    assert_eq!(probes.get(), 3);
    assert_eq!(**term, *original);
    assert!(matches!(term.check(&c),Err(ValidationFailure::Stop(ref stop)) if *stop==expected));
    assert_eq!(probes.get(), 3);
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(probes.get(), 3);
}

#[test]
fn closed_term_rechecks_original_constructor_references_and_quantifier_binder_types() {
    let r = term_private_result(&[
        "m=evaluate(Terms.inspector,s=@v/s)",
        "q=evaluate(Terms.quantifier)",
    ]);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].outputs["value"].0;
    let Some(Payload::Scalar(Scalar::Term(term))) = &r.nodes[t].payload else {
        panic!("Term")
    };
    assert!(
        term.references
            .iter()
            .any(|(_, n)| n == "Terms.Choice.Left")
    );
    completion_mutation(&r, t, |ns| {
        let Some(Payload::Scalar(Scalar::Term(term))) = &mut ns[t].payload else {
            panic!("Term")
        };
        let entry = term
            .references
            .iter_mut()
            .find(|(_, n)| n == "Terms.Choice.Left")
            .unwrap();
        entry.1 = "Terms.Choice.Right".into();
    });
    let q = r.answers[1].outputs["value"].0;
    let Some(Payload::Scalar(Scalar::Term(term))) = &r.nodes[q].payload else {
        panic!("Term")
    };
    assert_eq!(term.quantifier_types.len(), 1);
    assert!(term.quantifier_types.values().all(|t| *t == Type::Bool));
    completion_mutation(&r, q, |ns| {
        let Some(Payload::Scalar(Scalar::Term(term))) = &mut ns[q].payload else {
            panic!("Term")
        };
        *term.quantifier_types.values_mut().next().unwrap() = Type::Z;
    });
}

#[test]
fn closed_term_rechecks_equal_earlier_request_argument_producers() {
    let r = term_private_result(&[
        "first=evaluate(Terms.applied,s=@v/s)",
        "second=evaluate(Terms.applied,s=@v/s)",
    ]);
    let donor = r.answers[0].outputs["evaluation"].0;
    let target = r.answers[1].outputs["evaluation"].0;
    let Some(Payload::Evaluation {
        parts: donor_parts, ..
    }) = &r.nodes[donor].payload
    else {
        panic!("donor")
    };
    let Some(Payload::Evaluation {
        parts,
        value: Some(result),
        ..
    }) = &r.nodes[target].payload
    else {
        panic!("target")
    };
    let result = *result;
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert_eq!(parts[0].children.len(), 3);
    for position in [1, 2] {
        let original = parts[0].children[position];
        let replacement = donor_parts[0].children[position];
        let Some(Payload::Evaluation { value: Some(a), .. }) = &r.nodes[original.0].payload else {
            panic!("argument")
        };
        let Some(Payload::Evaluation { value: Some(b), .. }) = &r.nodes[replacement.0].payload
        else {
            panic!("donor argument")
        };
        let (a, b) = (*a, *b);
        assert_ne!(original, replacement);
        assert_ne!(a, b);
        assert!(replacement.0 < original.0 && b.0 < a.0);
        assert_eq!(g.scalar(a).unwrap().ty(), g.scalar(b).unwrap().ty());
        assert_eq!(g.scalar(a).unwrap(), g.scalar(b).unwrap());
        assert!(r.nodes[result.0].arguments.contains(&a));
        assert!(r.nodes[target].arguments.contains(&original));
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Evaluation { parts, .. }) = &mut ns[target].payload else {
                panic!("evaluation")
            };
            parts[0].children[position] = replacement;
            for edge in &mut ns[result.0].arguments {
                if *edge == a {
                    *edge = b;
                }
            }
            for edge in &mut ns[target].arguments {
                if *edge == original {
                    *edge = replacement;
                }
            }
        });
    }
}
