mod owned_call_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_calls.rs");
}
fn owned_call_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        owned_call_fixture::input(false, true, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn owned_condition(r: &ObservedEvaluation, request: usize) -> usize {
    r.nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| {
            (r.contexts[i].request == request
                && matches!(n.payload, Some(Payload::OwnedCallCondition { .. })))
            .then_some(i)
        })
        .unwrap()
}
#[test]
fn owned_call_success_rechecks_value_body_arguments_owner_support_and_scope() {
    let r = owned_call_result(&["x=evaluate(Reservations.returned,a=@v/A,s=@v/p)"]);
    assert_eq!(r.status(), "complete");
    let target = r.answers[0].outputs["value"].0;
    assert!(
        r.nodes[target]
            .support
            .iter()
            .any(|f| f.field.as_deref() == Some("Reservations.State.owner")
                && f.atom.as_deref() == Some("p-owner"))
    );
    completion_mutation(&r, target, |ns| {
        ns[target]
            .support
            .retain(|f| f.field.as_deref() != Some("Reservations.State.owner"))
    });
    completion_mutation(&r, target, |ns| ns[target].scope.snapshots.clear());
    completion_mutation(&r, target, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[target].payload else {
            panic!("ref")
        };
        *subject = "q".into();
    });
    let body = *r.nodes[target].arguments.last().unwrap();
    completion_mutation(&r, body.0, |ns| {
        let Some(Payload::Evaluation { value, .. }) = &mut ns[body.0].payload else {
            panic!("body")
        };
        *value = None;
    });
    completion_mutation(&r, target, |ns| ns[target].arguments.swap(0, 1));
    completion_mutation(&r, target, |ns| {
        ns[target].arguments.pop();
    });
}
#[test]
fn owned_call_condition_rechecks_original_owners_counterexample_and_exact_reason() {
    for name in ["parameter", "returned"] {
        let ask = format!("x=evaluate(Reservations.{name},a=@v/B,s=@v/p)");
        let r = owned_call_result(&[&ask]);
        assert_eq!(r.status(), "partial");
        let p = owned_condition(&r, 0);
        let n = r.nodes[p].arguments.len();
        let (left, right, evidence) = (
            r.nodes[p].arguments[n - 3],
            r.nodes[p].arguments[n - 2],
            r.nodes[p].arguments[n - 1],
        );
        for t in [left.0, right.0] {
            completion_mutation(&r, t, |ns| ns[t].support.clear());
            completion_mutation(&r, t, |ns| ns[t].scope.snapshots.clear());
            let other = if t == left.0 { right.0 } else { left.0 };
            let replacement = r.nodes[other].payload.clone();
            completion_mutation(&r, t, |ns| ns[t].payload = replacement.clone());
        }
        completion_mutation(&r, evidence.0, |ns| {
            let Some(Payload::OwnedCallCounterexample { facts, .. }) = &mut ns[evidence.0].payload
            else {
                panic!("evidence")
            };
            facts.clear();
        });
        completion_mutation(&r, p, |ns| {
            ns[p].judgment.as_mut().unwrap().status = Decision::Established
        });
        completion_mutation(&r, p, |ns| {
            ns[p].evidence.clear();
            ns[p].judgment.as_mut().unwrap().evidence.clear();
        });
        let t = r.answers[0].outputs["evaluation"].0;
        for mode in 0..4 {
            completion_mutation(&r, t, |ns| match mode {
                0 => ns[t].reasons.clear(),
                1 => ns[t].reasons[0].dependencies.clear(),
                2 => {
                    let ReasonKind::ConditionFailed { construction, .. } =
                        &mut ns[t].reasons[0].kind
                    else {
                        panic!("reason")
                    };
                    *construction = "domain";
                }
                _ => {
                    let Some(Location::Law { span }) = &mut ns[t].reasons[0].location else {
                        panic!("location")
                    };
                    span.0 += 1;
                }
            });
        }
    }
}
#[test]
fn owned_call_condition_rejects_coherent_equal_foreign_call_producers() {
    let r = owned_call_result(&[
        "first=evaluate(Reservations.parameter,a=@v/B,s=@v/p)",
        "second=evaluate(Reservations.parameter,a=@v/B,s=@v/p)",
    ]);
    let (donor, target) = (owned_condition(&r, 0), owned_condition(&r, 1));
    let n = r.nodes[target].arguments.len();
    assert_eq!(n, 6);
    let own = r.nodes[target].arguments.clone();
    let foreign = r.nodes[donor].arguments.clone();
    assert!(foreign.iter().all(|r| r.0 < target));
    for i in 1..3 {
        let Some(Payload::Evaluation { value: a, .. }) = &r.nodes[own[i].0].payload else {
            panic!("argument")
        };
        let Some(Payload::Evaluation { value: b, .. }) = &r.nodes[foreign[i].0].payload else {
            panic!("argument")
        };
        assert_eq!(
            data_scalar_at(&r, a.unwrap().0),
            data_scalar_at(&r, b.unwrap().0)
        );
    }
    for index in 0..3 {
        completion_mutation(&r, target, |ns| {
            for r in [own[3], own[4], own[5], NodeRef(target)] {
                ns[r.0].arguments[index] = foreign[index];
            }
        });
    }
    let evaluation = r.answers[1].outputs["evaluation"].0;
    completion_mutation(&r, evaluation, |ns| {
        let ReasonKind::ConditionFailed { condition, .. } = &mut ns[evaluation].reasons[0].kind
        else {
            panic!("reason")
        };
        *condition = NodeRef(donor);
    });
}
#[test]
fn owned_call_same_environment_rechecks_mutated_owner_proof_and_shortened_frame() {
    let r = owned_call_result(&["x=evaluate(Reservations.parameter,a=@v/B,s=@v/p)"]);
    let p = owned_condition(&r, 0);
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    e.recheck_node(&g, &g.nodes[p], p).unwrap();
    let left = r.nodes[p].arguments[3];
    let right = r.nodes[p].arguments[4];
    let old = g.nodes[left.0].clone();
    g.nodes[left.0].payload = g.nodes[right.0].payload.clone();
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[p], p),
        Err(ValidationFailure::Internal(_))
    ));
    g.nodes[left.0] = old;
    e.recheck_node(&g, &g.nodes[p], p).unwrap();
    let r = owned_call_result(&["x=evaluate(Reservations.returned,a=@v/A,s=@v/p)"]);
    let value = r.answers[0].outputs["value"].0;
    let body = *r.nodes[value].arguments.last().unwrap();
    let frame = r.contexts[body.0].frame.unwrap();
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    e.recheck_node(&g, &g.nodes[value], value).unwrap();
    let old = g.frames[frame].arguments.clone();
    g.frames[frame].arguments.pop();
    assert_ne!(g.frames[frame].arguments, old);
    assert!(matches!(
        e.recheck_node(&g, &g.nodes[value], value),
        Err(ValidationFailure::Internal(_))
    ));
    g.frames[frame].arguments = old;
    e.recheck_node(&g, &g.nodes[value], value).unwrap();
}
#[test]
fn owned_call_universal_condition_rechecks_binders_and_unknown_foreign_arguments() {
    for name in ["affineCall", "affineReturn"] {
        let asks = [
            format!("first=check(Reservations.{name},a=@v/B,s=@v/p)"),
            format!("second=check(Reservations.{name},a=@v/B,s=@v/p)"),
        ];
        let r = owned_call_result(&[&asks[0], &asks[1]]);
        assert_eq!(r.status(), "partial");
        let (donor, target) = (owned_condition(&r, 0), owned_condition(&r, 1));
        let source = r.nodes[target].arguments[0];
        let Some(Payload::Expression { parameters, .. }) = &r.nodes[source.0].payload else {
            panic!("source")
        };
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters[0].1, Type::Z);
        completion_mutation(&r, source.0, |ns| {
            let Some(Payload::Expression { parameters, .. }) = &mut ns[source.0].payload else {
                panic!("source")
            };
            parameters.clear();
        });
        let n = r.nodes[target].arguments.len();
        let edges = r.nodes[target].arguments.clone();
        let foreign = r.nodes[donor].arguments[3];
        for reference in [edges[3], foreign] {
            let Some(Payload::Evaluation { value, .. }) = &r.nodes[reference.0].payload else {
                panic!("argument")
            };
            assert!(value.is_none(), "全域parameterを具体値にしない");
        }
        assert!(foreign.0 < edges[3].0);
        completion_mutation(&r, target, |ns| {
            for r in [edges[n - 3], edges[n - 2], edges[n - 1], NodeRef(target)] {
                ns[r.0].arguments[3] = foreign;
            }
        });
        completion_mutation(&r, edges[n - 3].0, |ns| {
            ns[edges[n - 3].0].scope.quantifiers.clear()
        });
    }
}
fn owned_call_stop_in_batch(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "current=evaluate(Reservations.parameter,a=@v/A,s=@v/p)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = owned_call_result(&asks);
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared =
        prepare_observed(owned_call_fixture::input(false, true, "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, s, ph) = (armed.clone(), seen.clone(), phase.clone());
            data::observe_iterations(move |_, ctx, operation, _| {
                if ctx.request == 2
                    && operation
                        == if recheck {
                            "owned_call_constraint"
                        } else {
                            "owned_call_parameter"
                        }
                    && (!recheck || ph.get())
                {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::new(normal.prepared.inputs(), &mut cc)?;
            phase.set(true);
            let result = fresh.validate_answer(g, request, answer);
            phase.set(false);
            result?;
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
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        if recheck && i == 2 {
            // 元値は検査済みで残るが、停止した現在Answerの最終検査は未完了。
            assert_eq!(a.status, Decision::Undetermined);
            assert_eq!(a.outputs, normal.answers[i].outputs);
        } else {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
        }
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("stop details")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn owned_call_actual_constraint_stop_keeps_prior_value_refutation_and_prefix() {
    owned_call_stop_in_batch(false)
}
#[test]
fn owned_call_original_input_recheck_stop_keeps_prior_value_refutation_and_prefix() {
    owned_call_stop_in_batch(true)
}
#[test]
fn named_call_actual_stages_keep_argument_callee_and_caller_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "current=evaluate(Reservations.plainCaller)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = owned_call_result(&asks);
    assert_eq!(
        data_scalar_at(&normal, normal.answers[2].outputs["value"].0),
        &Scalar::Z(5.into())
    );
    let law = normal.prepared.inputs().law();
    let Signature::View { body: caller, .. } =
        &law.declarations["Reservations.plainCaller"].signature
    else {
        panic!("caller")
    };
    let ExprKind::Let { value: call, .. } = &law.exprs[*caller].kind else {
        panic!("let")
    };
    let ExprKind::Call { args, .. } = &law.exprs[*call].kind else {
        panic!("call")
    };
    let call_span = law.exprs[*call].span;
    let caller_span = law.exprs[*caller].span;
    let arg_span = law.exprs[args[0]].span;
    let Signature::View { body, .. } = &law.declarations["Reservations.plainAdd"].signature else {
        panic!("callee")
    };
    let ExprKind::Binary { lhs, .. } = &law.exprs[*body].kind else {
        panic!("body")
    };
    let body_span = law.exprs[*body].span;
    let inner_span = law.exprs[*lhs].span;
    for stage in 0..3 {
        let (limits, usage, expected) = reservations_private_stop_usage(stage);
        let armed = Rc::new(Cell::new(false));
        let seen = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
        let mut c = Control::new(limits, move |_| {
            p.set(p.get() + 1);
            if a.replace(false) {
                assert!(f.replace(Some(p.get())).is_none());
                usage
            } else {
                Default::default()
            }
        });
        let prepared =
            prepare_observed(owned_call_fixture::input(false, true, "r1"), &asks, &mut c).unwrap();
        let (a, s) = (armed.clone(), seen.clone());
        data::observe_iterations(move |span, ctx, operation, _| {
            let at = match stage {
                0 => {
                    operation == "call_arguments_complete"
                        && span == call_span
                        && ctx.frame.is_none()
                }
                1 => operation == "expression" && span == inner_span && ctx.frame.is_some(),
                _ => {
                    operation == "call_evaluation_complete"
                        && span == call_span
                        && ctx.frame.is_none()
                }
            };
            if ctx.request == 2 && at {
                assert!(!s.replace(true));
                a.set(true);
            }
        });
        let stopped = evaluate_observed(prepared, &mut c);
        data::clear_iteration_observer();
        let stopped = stopped.unwrap();
        assert!(seen.get());
        assert_eq!(stopped.status(), "interrupted");
        assert_eq!(c.stop_reason(), Some(expected.clone()));
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
        let expression_span = |r: NodeRef| {
            let Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) = &stopped.nodes[r.0].payload
            else {
                panic!("source")
            };
            *span
        };
        let mut argument = None;
        let mut callee_body = None;
        let mut call_value = None;
        let mut framed_sources = 0;
        for (i, node) in stopped.nodes.iter().enumerate() {
            let ctx = stopped.contexts[i];
            if ctx.request != 2 {
                continue;
            }
            if ctx.frame.is_some() && matches!(node.payload, Some(Payload::Expression { .. })) {
                framed_sources += 1;
            }
            if let Some(Payload::Evaluation {
                expression, value, ..
            }) = &node.payload
            {
                let span = expression_span(*expression);
                if span == arg_span && ctx.frame.is_none() {
                    argument = *value;
                }
                if span == body_span && ctx.frame.is_some() {
                    callee_body = *value;
                }
                if span == call_span && ctx.frame.is_none() {
                    call_value = *value;
                }
                assert_ne!(span, caller_span, "未完成callerのletを通常値へ昇格しない");
            }
        }
        assert_eq!(
            data_scalar_at(&stopped, argument.unwrap().0),
            &Scalar::Z(3.into())
        );
        match stage {
            0 => assert_eq!(framed_sources, 0, "引数完了後・callee開始前"),
            1 => {
                assert!(framed_sources > 0);
                assert!(callee_body.is_none(), "callee内部でbody未完了");
            }
            _ => {
                assert_eq!(
                    data_scalar_at(&stopped, callee_body.unwrap().0),
                    &Scalar::Z(4.into())
                );
                assert_eq!(
                    data_scalar_at(&stopped, call_value.unwrap().0),
                    &Scalar::Z(4.into())
                );
            }
        }
        if stage < 2 {
            assert!(call_value.is_none());
        }
        for a in stopped.answers.iter().skip(2) {
            assert_eq!(a.status, Decision::Undetermined);
            assert!(a.outputs.is_empty());
            let reason = a
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
        assert_eq!(Some(probes.get()), frozen.get());
        assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
        assert_eq!(Some(probes.get()), frozen.get());
    }
}

#[test]
fn owned_counterexample_type_is_rechecked_in_the_same_environment_after_success() {
    let r = owned_call_result(&["x=evaluate(Reservations.parameter,a=@v/B,s=@v/p)"]);
    let p = owned_condition(&r, 0);
    let proof = r.nodes[p].arguments.last().unwrap().0;
    let evaluation = r.answers[0].outputs["evaluation"].0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    for target in [proof, p, evaluation] {
        e.recheck_node(&g, &g.nodes[target], target).unwrap();
        let old = g.nodes[proof].ty.clone();
        assert_eq!(old, NodeType::Evidence);
        g.nodes[proof].ty = NodeType::Value(Type::Bool);
        assert_ne!(g.nodes[proof].ty, old);
        assert!(
            matches!(
                e.recheck_node(&g, &g.nodes[target], target),
                Err(ValidationFailure::Internal(_))
            ),
            "target={target}"
        );
        g.nodes[proof].ty = old;
        e.recheck_node(&g, &g.nodes[target], target).unwrap();
    }
}

#[test]
fn owned_snapshot_condition_rechecks_actual_text_values_facts_and_prefixes() {
    let r = evaluate_observed_bytes(
        owned_call_fixture::cross_snapshot_input(),
        &[
            "p=evaluate(Reservations.parameter,a=@w/A,s=@v/p)",
            "r=evaluate(Reservations.returned,a=@w/A,s=@v/p)",
            "a=check(Reservations.affineCall,a=@w/A,s=@v/p)",
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for request in 0..3 {
        let p = owned_condition(&r, request);
        let n = r.nodes[p].arguments.len();
        let l = r.nodes[p].arguments[n - 3].0;
        let right = r.nodes[p].arguments[n - 2].0;
        assert_eq!(data_scalar_at(&r, l), &Scalar::Text("v".into()));
        assert_eq!(data_scalar_at(&r, right), &Scalar::Text("w".into()));
        assert_eq!(r.nodes[l].ty, NodeType::Value(Type::Text));
        assert!(r.nodes[p].support.iter().any(|f| f.snapshot == "v"
            && f.subject == "p"
            && f.atom.as_deref() == Some("p-owner")));
        assert!(
            r.nodes[p].scope.snapshots.contains("v") && r.nodes[p].scope.snapshots.contains("w")
        );
        completion_mutation(&r, l, |ns| {
            ns[l].payload = Some(Payload::Scalar(Scalar::Text("w".into())))
        });
        completion_mutation(&r, right, |ns| ns[right].support.clear());
        completion_mutation(&r, p, |ns| {
            ns[p].scope.snapshots.remove("v");
        });
    }
}
#[test]
fn owned_failed_inner_calls_keep_original_reasons_and_never_create_an_outer_frame() {
    let r = owned_call_result(&[
        "plain=evaluate(Reservations.invalidIgnored,a=@v/B,s=@v/p)",
        "owned=evaluate(Reservations.invalidIgnoredOwned,a=@v/B,b=@v/A,s=@v/p,t=@v/q)",
        "binding=evaluate(Reservations.invalidLet,a=@v/B,s=@v/p)",
        "affine=check(Reservations.ignoredAffine,a=@v/B,s=@v/p)",
    ]);
    assert_eq!(r.status(), "partial");
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    let mut found = vec![];
    for (i, node) in r.nodes.iter().enumerate() {
        let Some(Payload::Evaluation {
            expression,
            parts,
            value,
            ..
        }) = &node.payload
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
        let Some(id) = r
            .prepared
            .inputs()
            .law()
            .exprs
            .iter()
            .position(|e| e.span == *span)
        else {
            continue;
        };
        let Some(d) = e.named_view(id).unwrap() else {
            continue;
        };
        if ![
            "Reservations.ignore",
            "Reservations.ignoreOwned",
            "Reservations.ignoreZ",
        ]
        .contains(&d.name.as_str())
        {
            continue;
        }
        let Signature::View { params, .. } = &d.signature else {
            panic!("view")
        };
        e.recheck_node(&g, node, i).unwrap();
        assert!(value.is_none());
        assert_eq!(parts[0].children.len(), params.len());
        assert!(!r.frames.iter().any(|f| f.source == *expression));
        assert!(
            node.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
        );
        completion_mutation(&r, i, |ns| ns[i].reasons.clear());
        found.push(r.contexts[i].request);
    }
    found.sort();
    found.dedup();
    assert_eq!(found, vec![0, 1, 2, 3]);
}

#[test]
fn owned_failed_quantifier_keeps_partial_counterexamples_without_a_boolean_value() {
    let r = owned_call_result(&["x=evaluate(Reservations.invalidForall,a=@v/A)"]);
    assert_eq!(r.status(), "partial");
    let target = r.answers[0].outputs["evaluation"].0;
    assert!(!r.answers[0].outputs.contains_key("value"));
    let n = &r.nodes[target];
    assert!(!n.evidence.is_empty());
    assert!(
        n.evidence
            .iter()
            .all(|p| matches!(r.nodes[p.0].payload, Some(Payload::Counterexample { .. })))
    );
    assert!(
        n.reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
    );
    completion_mutation(&r, target, |ns| ns[target].evidence.clear());
    let proof = n.evidence[0].0;
    completion_mutation(&r, proof, |ns| {
        let Some(Payload::Counterexample { facts, .. }) = &mut ns[proof].payload else {
            panic!("proof")
        };
        facts.clear();
    });
}
