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
    r
}
const COMPOUND_GOOD: &str =
    "x=evaluate(Reservations.ccReturned,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,e=@v/e)";
const COMPOUND_BAD: &str =
    "x=evaluate(Reservations.ccParameter,a=@v/A,b=@v/B,p=@v/p,q=@v/q,r=@v/r,s=@v/p,e=@v/e)";

#[test]
fn compound_calls_recheck_nested_return_members_types_order_support_and_scope() {
    let bad = COMPOUND_BAD.replacen("x=", "y=", 1);
    let r = compound_call_result(&[COMPOUND_GOOD, &bad]);
    assert_eq!(r.status(), "partial");
    assert_eq!(r.answers[0].status, Decision::Established);
    // 入れ子の戻り値の再検査の代表: 戻り値のlistの要素を落とすと核が拒否する。
    let target = r.answers[0].outputs["value"].0;
    rejects_mutated_prefix(&r, target, |ns| {
        let Some(Payload::Scalar(Scalar::Tuple(items))) = &mut ns[target].payload else {
            panic!("tuple")
        };
        let Scalar::List { items, .. } = &mut items[0] else {
            panic!("list")
        };
        items.pop();
    });
    // 所有者の合わないmemberを渡した呼出しは、owner条件の失敗を理由に残す。
    owned_condition(&r, 1);
    assert!(
        !r.nodes[r.answers[1].outputs["evaluation"].0]
            .reasons
            .is_empty()
    );
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
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
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
    assert_eq!(c.stop_reason(), Some(expected));
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
fn compound_call_actual_third_member_stop_keeps_prior_values_refutation_and_prefix() {
    compound_call_member_stop(false)
}
