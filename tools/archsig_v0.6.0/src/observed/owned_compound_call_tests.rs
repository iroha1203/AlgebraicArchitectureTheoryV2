mod compound_call_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_compound_calls.rs");
}
fn compound_call_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        compound_call_fixture::input(false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
const COMPOUND_GOOD: &str =
    "x=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,e=@v/e)";
const COMPOUND_BAD: &str =
    "x=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/p,e=@v/e)";

#[test]
fn compound_calls_recheck_nested_return_members_types_order_support_and_scope() {
    let r = compound_call_result(&[COMPOUND_GOOD]);
    assert_eq!(r.status(), "complete");
    let target = r.answers[0].outputs["value"].0;
    for mode in 0..4 {
        completion_mutation(&r, target, |ns| {
            let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut ns[target].payload else {
                panic!("tuple")
            };
            match mode {
                0 => {
                    let Scalar::List { items, .. } = &mut items[0] else {
                        panic!("list")
                    };
                    items.swap(0, 1);
                }
                1 => {
                    let Scalar::List { items, .. } = &mut items[0] else {
                        panic!("list")
                    };
                    items.pop();
                }
                2 => {
                    let Scalar::Option { value, .. } = &mut items[1] else {
                        panic!("option")
                    };
                    *value = None;
                }
                _ => {
                    let Scalar::Set { element, .. } = &mut items[2] else {
                        panic!("set")
                    };
                    *element = Type::Bool;
                }
            }
        });
    }
    completion_mutation(&r, target, |ns| {
        ns[target]
            .support
            .retain(|f| f.atom.as_deref() != Some("q-owner"))
    });
    completion_mutation(&r, target, |ns| ns[target].scope.snapshots.clear());
    let g = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let e = Environment::new(r.prepared.inputs(), &mut named_call_quiet()).unwrap();
    let call = r
        .prepared
        .inputs()
        .law()
        .exprs
        .iter()
        .position(|x| {
            matches!(x.kind, ExprKind::Call { .. })
                && std::str::from_utf8(
                    &r.prepared.inputs().sources().law().bytes()[x.span.0..x.span.1],
                )
                .unwrap()
                    == "ccMap(a,m)"
        })
        .unwrap();
    assert!(e.named_view(call).unwrap().is_some());
    e.recheck_node(&g, &g.nodes[target], target).unwrap();
}

#[test]
fn compound_failed_member_rechecks_original_container_evidence_and_exact_condition() {
    let r = compound_call_result(&[COMPOUND_BAD]);
    assert_eq!(r.status(), "partial");
    let p = owned_condition(&r, 0);
    let n = r.nodes[p].arguments.len();
    let [left, right, proof]: [NodeRef; 3] = r.nodes[p].arguments[n - 3..].try_into().unwrap();
    let replacement = r.nodes[right.0].payload.clone();
    completion_mutation(&r, left.0, |ns| ns[left.0].payload = replacement.clone());
    completion_mutation(&r, proof.0, |ns| {
        ns[proof.0].ty = NodeType::Value(Type::Bool)
    });
    completion_mutation(&r, proof.0, |ns| {
        let Some(Payload::OwnedCallCounterexample { facts, .. }) = &mut ns[proof.0].payload else {
            panic!("proof")
        };
        facts.clear();
    });
    completion_mutation(&r, p, |ns| ns[p].scope.snapshots.clear());
    completion_mutation(&r, p, |ns| ns[p].support.clear());
    let argument = r.nodes[p].arguments[3];
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &r.nodes[argument.0].payload
    else {
        panic!("actual tuple")
    };
    let value = *value;
    completion_mutation(&r, value.0, |ns| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut ns[value.0].payload else {
            panic!("tuple")
        };
        let Scalar::Option {
            value: Some(list), ..
        } = &mut items[1]
        else {
            panic!("some")
        };
        let Scalar::List { items, .. } = &mut **list else {
            panic!("list")
        };
        assert_ne!(items[0], items[1]);
        items[1] = items[0].clone();
    });
    let evaluation = r.answers[0].outputs["evaluation"].0;
    completion_mutation(&r, evaluation, |ns| ns[evaluation].reasons.clear());
    let span = r.nodes[p].arguments[0];
    assert!(!r.frames.iter().any(|f| f.source == span));
}

fn compound_call_member_stop(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "current=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/s,e=@v/e)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = compound_call_result(&asks);
    let bytes = normal.prepared.inputs().sources().law().bytes();
    let span = normal
        .prepared
        .inputs()
        .law()
        .exprs
        .iter()
        .find(|x| {
            &bytes[x.span.0..x.span.1]
                == b"ccAccept(a,b,(p,some(list<State>[r,s,r])),set<State>{p,q,p},some(e))"
        })
        .unwrap()
        .span;
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let traversing = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
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
        prepare_observed(compound_call_fixture::input(false, "r1"), &asks, &mut c).unwrap();
    let mut cc = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, ph, t, s) = (
                armed.clone(),
                phase.clone(),
                traversing.clone(),
                seen.clone(),
            );
            data::observe_iterations(move |at, ctx, operation, _| {
                if at != span {
                    return;
                }
                if !recheck && ctx.request == 2 && operation == "call_arguments_complete" {
                    t.set(true);
                }
                if operation == "owned_call_constraint"
                    && (if recheck {
                        ph.get() && ctx.request == 2
                    } else {
                        t.get()
                    })
                {
                    let i = s.get();
                    s.set(i + 1);
                    if i == 2 {
                        a.set(true);
                    }
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
    assert_eq!(seen.get(), 3);
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
            // fresh再検査の前に、理由のない確定Answerも独立検査を終えている。
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
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn compound_call_actual_third_member_stop_keeps_prior_values_refutation_and_prefix() {
    compound_call_member_stop(false)
}
