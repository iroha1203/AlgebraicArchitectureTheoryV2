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
    rejects_mutated_prefix(&r, target, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[target].payload else {
            panic!("ref")
        };
        *subject = "q".into();
    });
}
fn owned_call_stop_in_batch(recheck: bool, failed_field: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        if failed_field {
            "current=evaluate(Reservations.fieldDirect,a=@v/B,s=@v/p)"
        } else {
            "current=evaluate(Reservations.parameter,a=@v/A,s=@v/p)"
        },
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
                        == if failed_field {
                            "failed_field"
                        } else if recheck {
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
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for (i, a) in stopped.answers.iter().enumerate().skip(2) {
        if recheck && i == 2 {
            // fresh再検査の前に独立検査済みの確定Answerを、判断とともに保持する。
            assert_eq!(a.status, normal.answers[i].status);
            assert_eq!(a.outputs, normal.answers[i].outputs);
            assert_eq!(a.claim, normal.answers[i].claim);
            assert_eq!(a.evidence, normal.answers[i].evidence);
            assert_eq!(a.scope, normal.answers[i].scope);
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
}
#[test]
fn owned_call_actual_constraint_stop_keeps_prior_value_refutation_and_prefix() {
    owned_call_stop_in_batch(false, false)
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
    for request in 0..3 {
        let p = owned_condition(&r, request);
        let n = r.nodes[p].arguments.len();
        let l = r.nodes[p].arguments[n - 3].0;
        let right = r.nodes[p].arguments[n - 2].0;
        assert_eq!(data_scalar_at(&r, l), &Scalar::Text("v".into()));
        assert_eq!(data_scalar_at(&r, right), &Scalar::Text("w".into()));
        assert!(r.nodes[p].support.iter().any(|f| f.snapshot == "v"
            && f.subject == "p"
            && f.atom.as_deref() == Some("p-owner")));
    }
}
#[test]
fn owned_failed_fields_recheck_original_children_reasons_type_scope_and_value_absence() {
    let r = owned_call_result(&[
        "seed=evaluate(Reservations.seed)",
        "first=evaluate(Reservations.fieldDirect,a=@v/B,s=@v/p)",
        "lexical=evaluate(Reservations.fieldLexical,a=@v/B,s=@v/p)",
        "owner=evaluate(Reservations.failedFieldOwner,a=@v/B,s=@v/p)",
        "affine=check(Reservations.fieldAffine,a=@v/B,s=@v/p)",
        "parameter=evaluate(Reservations.parameter,a=@v/B,s=@v/p)",
        "returned=evaluate(Reservations.returned,a=@v/B,s=@v/p)",
        "universal=evaluate(Reservations.invalidForall,a=@v/A)",
        "plain=evaluate(Reservations.invalidIgnored,a=@v/B,s=@v/p)",
        "owned=evaluate(Reservations.invalidIgnoredOwned,a=@v/B,b=@v/A,s=@v/p,t=@v/q)",
        "binding=evaluate(Reservations.invalidLet,a=@v/B,s=@v/p)",
        "ignored=check(Reservations.ignoredAffine,a=@v/B,s=@v/p)",
    ]);
    assert_eq!(r.status(), "partial");
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    let bytes = r.prepared.inputs().sources().law().bytes();
    let law = r.prepared.inputs().law();
    let mut fields = vec![];
    let mut inner = vec![];
    for (i, n) in r.nodes.iter().enumerate() {
        let Some(Payload::Evaluation {
            expression, value, ..
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
        let request = r.contexts[i].request;
        // 所有者の合わないfield読みは値を出さず、条件の失敗と根拠を残す。
        let text = std::str::from_utf8(&bytes[span.0..span.1]).unwrap();
        if (1..=4).contains(&request)
            && ["(narrow(a,s)).free", "selected.free", "(narrow(a,s)).owner"].contains(&text)
        {
            assert!(value.is_none());
            assert!(
                n.reasons
                    .iter()
                    .any(|x| matches!(x.kind, ReasonKind::ConditionFailed { .. }))
            );
            assert!(!n.support.is_empty());
            fields.push(request);
        }
        // 失敗した内側の呼出しは値を出さず、元の条件の失敗を残す。
        if (8..=11).contains(&request)
            && let Some(id) = law.exprs.iter().position(|e| e.span == *span)
            && let Some(d) = e.named_view(id).unwrap()
            && [
                "Reservations.ignore",
                "Reservations.ignoreOwned",
                "Reservations.ignoreZ",
            ]
            .contains(&d.name.as_str())
        {
            assert!(value.is_none());
            assert!(
                n.reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            );
            inner.push(request);
        }
    }
    for found in [&mut fields, &mut inner] {
        found.sort();
        found.dedup();
    }
    assert_eq!(fields, vec![1, 2, 3, 4]);
    assert_eq!(inner, vec![8, 9, 10, 11]);
    // 判断の再検査の代表: 失敗したowner条件の判断を反転すると核が拒否する。
    owned_condition(&r, 6);
    let p = owned_condition(&r, 5);
    rejects_mutated_prefix(&r, p, |ns| {
        ns[p].judgment.as_mut().unwrap().status = Decision::Established
    });
    // 失敗した量化は真偽値を出さず、部分的な反例を証拠に残す。
    let target = r.answers[7].outputs["evaluation"].0;
    assert!(!r.answers[7].outputs.contains_key("value"));
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
}
