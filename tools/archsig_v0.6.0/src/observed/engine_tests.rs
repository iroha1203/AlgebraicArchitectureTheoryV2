#[allow(dead_code)]
mod engine_fixture {
    include!("../../tests/common/engine.rs");
}
fn engine_private_inputs(missing: bool) -> InputSources {
    InputSources::from_bytes(
        vec![engine_fixture::DEFINITIONS.to_vec()],
        engine_fixture::law(true),
        engine_fixture::smaller(missing, Some("r1")),
    )
}
fn engine_private_result(asks: &[&str], missing: bool) -> ObservedEvaluation {
    let mut c = named_call_quiet();
    let p = prepare_observed(engine_private_inputs(missing), asks, &mut c).unwrap();
    evaluate_observed(p, &mut c).unwrap()
}
#[test]
fn engine_rechecks_generated_ir_constructor_order_type_support_and_scope() {
    let r = engine_private_result(&["ir=evaluate(Engine.generated,c=@engine/subtract)"], false);
    assert_eq!(r.status(), "complete");
    let t = r.answers[0].outputs["value"].0;
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    completion_mutation(&r, t, |ns| {
        let Some(Payload::Scalar(Scalar::Data { constructor, .. })) = &mut ns[t].payload else {
            panic!("IR")
        };
        *constructor = "Engine.IR.Plus".into();
    });
    completion_mutation(&r, t, |ns| {
        let Some(Payload::Scalar(Scalar::Data { args, .. })) = &mut ns[t].payload else {
            panic!("IR")
        };
        args.swap(0, 1);
    });
    completion_mutation(&r, t, |ns| {
        ns[t].ty = NodeType::Value(Type::Data("Engine.Expr".into()));
    });
    completion_mutation(&r, t, |ns| {
        ns[t].support.clear();
    });
    completion_mutation(&r, t, |ns| {
        ns[t].scope.snapshots.clear();
    });
    completion_mutation(&r, t, |ns| {
        ns[t].rule = Rule::Input {
            kind: "law",
            location: Location::Law { span: (0, 1) },
        };
    });
}
#[test]
fn engine_rechecks_all_z_coefficients_counterexample_assignment_and_original_sides() {
    let r = engine_private_result(&["a=check(Engine.preserves,c=@engine/subtract)"], false);
    assert_eq!(r.answers[0].status, Decision::Refuted);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let norm = universal_private_normalization(&r, 0);
    let Some(Payload::Normalization { before, .. }) = r.nodes[norm].payload else {
        panic!("normalization")
    };
    let domains: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            matches!(n.payload, Some(Payload::TypeDomain { ty: Type::Z })).then_some(NodeRef(i))
        })
        .collect();
    assert_eq!(domains.len(), 1);
    let Some(Payload::Expression { bindings, .. }) = &r.nodes[before.0].payload else {
        panic!("template")
    };
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    let a = e
        .universal_analysis(&g, before, &domains, bindings)
        .unwrap();
    let classification = a.classification.unwrap();
    assert_eq!(classification.value, Some(false));
    assert!(classification.parameter_coefficients.is_empty());
    assert!(classification.missing_coefficients.is_empty());
    assert_eq!(
        classification
            .difference
            .value(&named_call_quiet())
            .unwrap(),
        Some(Scalar::Z((-2).into()))
    );
    let example = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::Counterexample { .. })))
        .unwrap();
    let Some(Payload::Counterexample {
        bindings,
        left,
        right,
        ..
    }) = &r.nodes[example].payload
    else {
        panic!("counterexample")
    };
    let x = bindings.iter().find(|b| b.name == "x").unwrap().value.0;
    completion_mutation(&r, x, |ns| {
        ns[x].payload = Some(Payload::Scalar(Scalar::Z(99.into())));
    });
    completion_mutation(&r, example, |ns| {
        let Some(Payload::Counterexample { left: actual, .. }) = &mut ns[example].payload else {
            panic!("example")
        };
        *actual = *right;
    });
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &r.nodes[left.0].payload
    else {
        panic!("left")
    };
    let t = value.0;
    completion_mutation(&r, t, |ns| {
        ns[t].payload = Some(Payload::Scalar(Scalar::Z(77.into())));
    });
    completion_mutation(&r, norm, |ns| {
        let Some(Payload::Normalization { steps, .. }) = &mut ns[norm].payload else {
            panic!("proof")
        };
        steps.clear();
    });
}
#[test]
fn engine_original_bytes_rejects_changed_normalization_residual_and_difference_operands() {
    let mut c = named_call_quiet();
    let prepared = prepare_observed(
        InputSources::from_bytes(
            vec![engine_fixture::DEFINITIONS.to_vec()],
            engine_fixture::law(false),
            engine_fixture::map(false, None),
        ),
        &["a=check(Engine.preserves,c=@engine/subtract)"],
        &mut c,
    )
    .unwrap();
    let r = evaluate_observed(prepared, &mut c).unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(r.answers[0].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let norm = universal_private_normalization(&r, 0);
    let Some(Payload::Normalization { steps, .. }) = &r.nodes[norm].payload else {
        panic!("normalization")
    };
    let difference = steps
        .iter()
        .copied()
        .find(|s| {
            matches!(
                &r.nodes[s.0].payload,
                Some(Payload::ParameterizedTransform {
                    operation: TransformOp::Difference,
                    operands,
                    ..
                }) if operands.len() == 2 && operands[0] != operands[1]
            )
        })
        .unwrap();
    let residual = r
        .nodes
        .iter()
        .find_map(|n| match &n.payload {
            Some(Payload::Evaluation {
                expression,
                value: Some(value),
                ..
            }) if *expression == difference && n.ty == NodeType::Evaluation(Type::Z) => {
                Some(*value)
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(data_scalar_at(&r, residual.0), &Scalar::Z((-2).into()));
    completion_mutation(&r, residual.0, |ns| {
        ns[residual.0].payload = Some(Payload::Scalar(Scalar::Z(77.into())));
    });
    completion_mutation(&r, difference.0, |ns| {
        let Some(Payload::ParameterizedTransform { operands, .. }) = &mut ns[difference.0].payload
        else {
            panic!("difference")
        };
        operands.swap(0, 1);
    });
}
#[test]
fn engine_symbolic_match_rejects_equal_other_request_call_producers() {
    let mut r = engine_private_result(
        &[
            "first=check(Engine.preserves,c=@engine/add)",
            "again=check(Engine.preserves,c=@engine/add)",
        ],
        false,
    );
    let law = r.prepared.inputs().sources().law().bytes();
    let frames: Vec<_> = r
        .frames
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &r.nodes[f.source.0].payload
            else {
                return None;
            };
            (&law[span.0..span.1] == b"evalSource(c.source, x)").then_some(i)
        })
        .collect();
    assert_eq!(frames.len(), 2);
    let donor = r.frames[frames[0]].arguments[0];
    let original = r.frames[frames[1]].arguments[0];
    assert_ne!(donor, original);
    let scalar = |r: &ObservedEvaluation, n: NodeRef| {
        let Some(Payload::Evaluation { value: Some(v), .. }) = &r.nodes[n.0].payload else {
            panic!("value")
        };
        data_scalar_at(r, v.0).clone()
    };
    assert_eq!(scalar(&r, donor), scalar(&r, original));
    let t = r
        .contexts
        .iter()
        .enumerate()
        .find_map(|(i, c)| {
            (c.frame == Some(frames[1])
                && matches!(r.nodes[i].payload, Some(Payload::Expression { .. })))
            .then_some(i)
        })
        .unwrap();
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=t]).unwrap();
    r.frames[frames[1]].arguments[0] = donor;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes[..=t]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn engine_same_environment_rejects_modified_resident_nodes_and_hidden_binding_types() {
    let r = engine_private_result(&["a=evaluate(Engine.generated,c=@engine/add)"], false);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].outputs["evaluation"].0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let atom=g.nodes.iter().position(|n|matches!((&n.payload,&n.rule),(Some(Payload::Scalar(Scalar::Data{family,..})),Rule::Input{kind:"atom",..}) if family=="Engine.Expr")).unwrap();
    let original = g.nodes[atom].clone();
    let Some(Payload::Scalar(Scalar::Data { args, .. })) = &mut g.nodes[atom].payload else {
        panic!("tree")
    };
    args.swap(0, 1);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[atom] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let source = g
        .nodes
        .iter()
        .position(
            |n| matches!(&n.payload,Some(Payload::Expression{bindings,..}) if !bindings.is_empty()),
        )
        .unwrap();
    let original = g.nodes[source].clone();
    let Some(Payload::Expression { bindings, .. }) = &mut g.nodes[source].payload else {
        panic!("source")
    };
    bindings[0].ty = Type::Z;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[source] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
}
#[test]
fn engine_same_environment_rejects_changed_frame_context_request_and_old_frame_append() {
    let r = engine_private_result(&["a=check(Engine.preserves,c=@engine/subtract)"], false);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].claim.unwrap().0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.frames[0].arguments.clone();
    g.frames[0].arguments.pop();
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.frames[0].arguments = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let index = r.contexts.iter().position(|c| c.frame.is_some()).unwrap();
    let original = g.contexts[index];
    g.contexts[index].request = 1;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.contexts[index] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.requests[0].clone();
    let arg = g.requests[0]
        .arguments
        .iter_mut()
        .find(|a| a.name == "bind.c")
        .unwrap();
    let super::super::request::Selector::Subject { subject, .. } = &mut arg.value else {
        panic!("selector")
    };
    *subject = "add".into();
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.requests[0] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original_len = g.frames.len();
    g.frames.push(g.frames[0].clone());
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.frames.truncate(original_len);
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
}

#[test]
fn engine_validation_snapshot_rechecks_changed_numeric_witness_registry() {
    let r = universal_private_example(
        "law required example(s:Sample):forall x:Z . x+s.z=x;",
        &["a=check(Calc.example,s=@v/sample)"],
    );
    assert_eq!(r.status(), "partial");
    assert_eq!(r.universal_witnesses.len(), 2);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].claim.unwrap().0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.universal_witnesses[0].clone();
    g.universal_witnesses[0].ordinal = usize::MAX;
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.universal_witnesses[0] = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
}

#[test]
fn engine_same_environment_rejects_modified_completion_case_assignment() {
    let r = engine_private_result(&["a=check(Engine.preserves,c=@engine/add)"], true);
    assert_eq!(r.status(), "partial");
    assert_eq!(r.cases.len(), 2);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].claim.unwrap().0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.cases[0].member;
    g.cases[0].member = g.cases[1].member;
    assert_ne!(g.cases[0].member, original);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
    g.cases[0].member = original;
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
}

fn engine_stop(kind: usize, missing: bool, phase: &'static str, at: usize, after_answer: bool) {
    use std::{cell::Cell, rc::Rc};
    let current = if missing {
        "current=check(Engine.preserves,c=@engine/add)"
    } else {
        "current=check(Engine.preserves,c=@engine/subtract)"
    };
    let asks = [
        "seed=evaluate(Engine.seed)",
        "prior=check(Engine.prior)",
        current,
        "later=evaluate(Engine.seed)",
    ];
    let normal = engine_private_result(&asks, missing);
    assert_eq!(normal.answers[0].status, Decision::Established);
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (arm, count, freeze) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        count.set(count.get() + 1);
        if arm.replace(false) {
            assert!(freeze.replace(Some(count.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(engine_private_inputs(missing), &asks, &mut c).unwrap();
    let stopped =
        evaluate_observed_with_validator(prepared, &mut c, |environment, g, request, answer| {
            environment.validate_answer(g, request, answer)?;
            if request.id == "prior" && !after_answer {
                let (arm, saw) = (armed.clone(), seen.clone());
                data::observe_iterations(move |_, ctx, op, i| {
                    if ctx.request == 2 && ctx.case.is_none() && op == phase && i == at {
                        assert!(!saw.replace(true));
                        arm.set(true);
                    }
                });
            }
            if request.id == "current" && after_answer {
                assert!(!seen.replace(true));
                armed.set(true);
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
    if after_answer {
        assert_eq!(stopped.answers[2].status, Decision::Refuted);
        assert_eq!(
            format!("{:?}", stopped.answers[2]),
            format!("{:?}", normal.answers[2])
        );
    }
    for a in &stopped.answers[if after_answer { 3 } else { 2 }..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if s==&expected))
            .unwrap();
        let Json::Obj(ref actual) = reason.wire() else {
            panic!("reason")
        };
        let Json::Obj(ref wanted) = expected.wire() else {
            panic!("details")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn engine_recursive_match_cancel_keeps_verified_prefix_and_prior_refutation() {
    engine_stop(0, false, "universal_match", 2, false)
}
#[test]
fn engine_finite_operator_completion_time_stop_keeps_completed_case_and_prior_refutation() {
    engine_stop(1, true, "completion_case", 1, false)
}
#[test]
fn engine_counterexample_memory_stop_keeps_typed_substitutions_and_prior_refutation() {
    engine_stop(2, false, "universal", 2, false)
}
#[test]
fn engine_answer_cancel_keeps_completed_engine_counterexample_and_prior_answer() {
    engine_stop(0, false, "", 0, true)
}
#[test]
fn engine_snapshot_comparison_stops_freeze_the_shared_control_without_cached_authority() {
    use std::{cell::Cell, rc::Rc};
    let r = engine_private_result(&["a=evaluate(Engine.generated,c=@engine/add)"], false);
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].outputs["evaluation"].0;
    for kind in 0..3 {
        let (limits, usage, expected) = reservations_private_stop_usage(kind);
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let steps = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (arm, count, step, freeze) =
            (armed.clone(), probes.clone(), steps.clone(), frozen.clone());
        let mut c = Control::new(limits, move |_| {
            count.set(count.get() + 1);
            if arm.get() {
                step.set(step.get() + 1);
                if step.get() == 5 {
                    assert!(freeze.replace(Some(count.get())).is_none());
                    return usage;
                }
            }
            Default::default()
        });
        let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
        e.recheck_node(&g, &g.nodes[t], t).unwrap();
        armed.set(true);
        assert!(
            matches!(e.recheck_node(&g,&g.nodes[t],t),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        assert_eq!(steps.get(), 5);
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(g.nodes, r.nodes);
        assert!(
            matches!(e.recheck_node(&g,&g.nodes[t],t),Err(ValidationFailure::Stop(s)) if s==expected)
        );
        assert_eq!(Some(probes.get()), frozen.get());
    }
}

#[test]
fn engine_snapshot_rejects_duplicate_map_pairs_after_normal_validation() {
    let r = known_map_private_result(&["a=evaluate(Maps.read,s=@v/s)"]);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].outputs["evaluation"].0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let i = known_map_private_atom(&r);
    let original = g.nodes[i].clone();
    let Some(Payload::Scalar(Scalar::Map { pairs, .. })) = &mut g.nodes[i].payload else {
        panic!("map")
    };
    pairs[1] = pairs[0].clone();
    assert_eq!(
        g.nodes[i], original,
        "通常の外延比較を改変検出に使わないための境界例"
    );
    assert_ne!(format!("{:?}", g.nodes[i]), format!("{original:?}"));
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
}

#[test]
fn engine_snapshot_rejects_duplicate_nested_set_members_after_normal_validation() {
    let original = known_map_private_inputs();
    let law = std::str::from_utf8(original.law().bytes()).unwrap();
    let end = law.rfind('}').unwrap();
    let script = format!(
        "{} view both(s:Sample):Set<Map<Item,Item>> = set<Map<Item,Item>>{{s.m,s.different}}; {}",
        &law[..end],
        &law[end..]
    );
    let input = InputSources::new(
        original.definitions().to_vec(),
        super::super::input::InputBytes::new("law", script.into_bytes()),
        original.archmap().clone(),
    );
    let mut c = named_call_quiet();
    let p = prepare_observed(input, &["a=evaluate(Maps.both,s=@v/s)"], &mut c).unwrap();
    let r = evaluate_observed(p, &mut c).unwrap();
    assert_eq!(r.status(), "complete");
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let t = r.answers[0].outputs["evaluation"].0;
    let value = r.answers[0].outputs["value"].0;
    let mut c = named_call_quiet();
    let e = Environment::new(r.prepared.inputs(), &mut c).unwrap();
    e.recheck_node(&g, &g.nodes[t], t).unwrap();
    let original = g.nodes[value].clone();
    let Some(Payload::Scalar(Scalar::Set { items, .. })) = &mut g.nodes[value].payload else {
        panic!("set")
    };
    assert_eq!(items.len(), 2);
    items[1] = items[0].clone();
    assert_eq!(g.nodes[value], original);
    assert_ne!(format!("{:?}", g.nodes[value]), format!("{original:?}"));
    assert!(
        matches!(
            rebuild_for_origin_and_support_recheck(&r, &g.nodes[..=t]),
            Err(ValidationFailure::Internal(_))
        ),
        "fresh structural recheck"
    );
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[t], t),
        Err(ValidationFailure::Internal(_))
    ));
}
