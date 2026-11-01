use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/path_answer_projections.rs");
}

#[test]
fn path_answer_projection_actual_walk_stop_keeps_verified_prefix_and_independent_answers() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "p=evaluate(Walk.join,e=@v/e,f=@v/next)",
        "take=evaluate(Walk.keep_node,x=$p.value.target)",
        "later=evaluate(Walk.seed)",
    ];
    let normal =
        evaluate_observed_bytes(fixture::composed(false, "r1"), &asks, &quiet()).unwrap();
    assert_eq!(normal.status(), "complete");
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations()["Walk.keep_node"].signature
    else {
        panic!()
    };
    let span = params[0].span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let control = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(fixture::composed(false, "r1"), &asks, &control).unwrap();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "p" {
                let (a, s) = (armed.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, _| {
                    if at == span
                        && context.request == 3
                        && operation == "answer_projection_check_step"
                    {
                        assert_eq!(s.get(), 0);
                        s.set(1);
                        a.set(true);
                    }
                });
            }
            Ok(())
        },
    )
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 1);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected));
    assert_eq!(&stopped.answers[..3], &normal.answers[..3]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(stopped.answers[1].claim.is_some() && !stopped.answers[1].evidence.is_empty());
    for index in 3..5 {
        assert_eq!(stopped.answers[index].status, Decision::Undetermined);
        assert!(stopped.answers[index].outputs.is_empty());
        let reason = stopped.answers[index]
            .reasons
            .iter()
            .find(|reason| matches!(&reason.kind, ReasonKind::Stop(actual) if actual == &expected))
            .unwrap();
        assert_eq!(reason.request, stopped.answers[index].id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
