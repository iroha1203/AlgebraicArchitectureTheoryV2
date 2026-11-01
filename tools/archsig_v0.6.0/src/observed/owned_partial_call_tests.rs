mod partial_call_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_calls.rs");
}
fn partial_call_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        partial_call_fixture::input(false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
const PARTIAL_BAD: &str = "x=check(Reservations.pcListGood,a=@v/A,p=@v/p,q=@v/r)";
#[test]
fn partial_owned_calls_reject_original_binder_member_and_condition_mutations() {
    let r = partial_call_result(&[PARTIAL_BAD]);
    assert_eq!(r.status(), "partial");
    let container = r.nodes[owned_condition(&r, 0)].arguments[2];
    let Some(Payload::Evaluation { value, .. }) = &r.nodes[container.0].payload else {
        panic!("container")
    };
    assert!(value.is_none());
    let member = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, node)| match &node.payload {
            Some(Payload::Scalar(Scalar::Subject { subject, .. }))
                if subject == "r" && i < container.0 =>
            {
                Some(i)
            }
            _ => None,
        })
        .unwrap();
    rejects_mutated_prefix(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[member].payload else {
            panic!("member")
        };
        *subject = "q".into();
    });
}

#[test]
fn partial_owned_actual_member_stop_keeps_values_refutation_and_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        "current=evaluate(Reservations.pcMissing,a=@v/A,p=@v/p,q=@v/q)",
        "later=evaluate(Reservations.seed)",
    ];
    let normal = partial_call_result(&asks);
    let bytes = normal.prepared.inputs().sources().law().bytes();
    let span = normal
        .prepared
        .inputs()
        .law()
        .exprs
        .iter()
        .find(|x| {
            &bytes[x.span.0..x.span.1]
                == b"pcList(a,list<(State,Z)>[(p,q.free),(p,q.free+1),(p,q.free)])"
        })
        .unwrap()
        .span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let traversing = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared =
        prepare_observed(partial_call_fixture::input(false, "r1"), &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, t, s) = (armed.clone(), traversing.clone(), seen.clone());
            data::observe_iterations(move |at, ctx, operation, _| {
                if at != span {
                    return;
                }
                if ctx.request == 2 && operation == "call_arguments_complete" {
                    t.set(true);
                }
                if operation == "owned_call_constraint" && t.get() {
                    let i = s.get();
                    s.set(i + 1);
                    if i == 2 {
                        a.set(true);
                    }
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert_eq!(seen.get(), 3);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for a in stopped.answers.iter().skip(2) {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty());
        let reason = a
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s)if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!("stop")
        };
        assert_eq!(actual["details"], wanted["details"]);
        assert_eq!(reason.request, a.id);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}

#[test]
fn partial_owned_pending_calls_recheck_original_reasons_children_and_value_absence() {
    let r = evaluate_observed_bytes(
        partial_call_fixture::missing_reference_input(),
        &[
            "seed=evaluate(Reservations.seed)",
            "first=evaluate(Reservations.pcPendingPlain,a=@v/B,e=@v/e,p=@v/r)",
            "whole=check(Reservations.pcPendingAffine,a=@v/B,e=@v/e)",
            "implication=check(Reservations.pcSkipImpliesLaw,a=@v/B,e=@v/e)",
        ],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    let law = r.prepared.inputs().sources().law().bytes();
    let sources: Vec<_> = r
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| match &n.payload {
            Some(Payload::Expression {
                location: Location::Law { span },
                ..
            }) if r.contexts[i].request == 1
                && &law[span.0..span.1] == b"pcIgnoreNumeric(read(a,e.to))" =>
            {
                Some(NodeRef(i))
            }
            _ => None,
        })
        .collect();
    assert!(!sources.is_empty());
    // 未確定の引数を持つ呼出しは値を出さず Missing を残す。補完した各caseは条件の失敗も残す。
    for source in &sources {
        let evaluation = r.nodes.iter().find(|n|
            matches!(&n.payload, Some(Payload::Evaluation { expression, .. }) if expression==source)
        ).unwrap();
        assert!(matches!(
            evaluation.payload,
            Some(Payload::Evaluation { value: None, .. })
        ));
        assert!(
            evaluation
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing))
        );
        if r.contexts[source.0].case.is_some() {
            assert!(
                evaluation
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. }))
            );
        }
    }
    assert_eq!(r.answers[2].status, Decision::Undetermined);
    // short-circuit の含意は Missing を含んでも真で確定する。
    assert_eq!(r.answers[3].status, Decision::Established);
    let whole = r.answers[3].outputs["evaluation"];
    let Some(Payload::Evaluation {
        value: Some(value), ..
    }) = &r.nodes[whole.0].payload
    else {
        panic!("true whole")
    };
    assert!(matches!(
        r.nodes[value.0].payload,
        Some(Payload::Scalar(Scalar::Bool(true)))
    ));
}
