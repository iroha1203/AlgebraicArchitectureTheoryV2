use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/finite_reference_fields.rs");
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut quiet(),
    )
    .unwrap()
}
fn example() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, false, false),
        &[
            "first=evaluate(Inspect.chosen,h=@v/h)",
            "target=evaluate(Inspect.chosen,h=@v/h)",
            "later=evaluate(Inspect.seed)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.answers);
    r
}
fn mutate() {
    let r = example();
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    assert!(elements.len() > 1);
    let foreign_domain = r.nodes[r.answers[0].outputs["evaluation"].0].arguments[1];
    let cut = r.contexts.iter().position(|c| c.request == 2).unwrap();
    for nodes in [&r.nodes[..cut], r.nodes.as_slice()] {
        let mut graph = rebuild_for_origin_and_support_recheck(&r, nodes).unwrap();
        let e = environment(&r);
        e.validate_answer(&graph, request, answer).unwrap();
        let original_nodes = graph.nodes.clone();
        let original_cases = graph.cases.clone();
        let original_request = graph.requests[1].clone();
        for kind in [0, 1, 22] {
            match kind {
                0 => {
                    let Some(Payload::Domain { elements, .. }) = &mut graph.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements.pop();
                    graph.nodes[domain].arguments.pop();
                }
                1 => {
                    let Some(Payload::Domain { elements, .. }) = &mut graph.nodes[domain].payload
                    else {
                        panic!()
                    };
                    elements[1] = elements[0];
                    graph.nodes[domain].arguments[2] = elements[0];
                }
                22 => {
                    assert_ne!(graph.nodes[root].arguments[1], foreign_domain);
                    graph.nodes[root].arguments[1] = foreign_domain;
                }
                _ => panic!(),
            }
            assert!(
                graph.nodes != original_nodes
                    || graph.cases != original_cases
                    || graph.requests[1] != original_request,
                "real {kind}"
            );
            assert!(
                matches!(
                    e.validate_answer(&graph, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "same {kind}"
            );
            assert!(
                matches!(
                    environment(&r).validate_answer(&graph, request, answer),
                    Err(ValidationFailure::Internal(_))
                ),
                "fresh {kind}"
            );
            graph.nodes = original_nodes.clone();
            graph.cases = original_cases.clone();
            graph.requests[1] = original_request.clone();
            e.validate_answer(&graph, request, answer).unwrap();
            environment(&r)
                .validate_answer(&graph, request, answer)
                .unwrap();
        }
    }
}
#[test]
fn finite_reference_field_domains_reject_missing_duplicate_and_foreign_whole() {
    mutate();
}

#[test]
fn finite_reference_field_internal_pins_validate_original_shapes_refs_and_missing_identity() {
    use crate::archmap::{FieldAssignment, check_completion_with_values};
    use crate::control::CheckFailure;
    let r = example();
    let input = r.prepared.inputs();
    let pin = |field: &str, value: Json| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("Fields.Holder.{field}"),
        value,
    };
    let ref_p = fixture::reference("v", "p");
    let root_a = fixture::reference("v", "A");
    for pins in [
        vec![pin("chosen", fixture::reference("v", "ghost"))],
        vec![pin("chosen", root_a.clone())],
        vec![pin("owner", root_a.clone())],
        vec![pin("chosen", ref_p.clone()), pin("chosen", ref_p.clone())],
        vec![pin(
            "mixed",
            Json::Arr(vec![root_a.clone(), Json::Bool(false)]),
        )],
        vec![pin("members", Json::Arr(vec![root_a.clone()]))],
        vec![pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![ref_p.clone(), Json::Bool(false)])),
            ]),
        )],
        vec![pin(
            "choice",
            Json::obj([("tag", Json::str("ghost")), ("args", Json::Arr(vec![]))]),
        )],
        vec![pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![root_a.clone()])),
            ]),
        )],
    ] {
        assert!(matches!(
            check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
                &input.archmap().snapshots(),
                &input.law().definitions(),
                &pins,
                &mut quiet()
            ),
            Err(CheckFailure::Input(_))
        ));
    }
    for p in [
        pin("chosen", ref_p.clone()),
        pin("mixed", Json::Arr(vec![ref_p.clone(), Json::Bool(false)])),
        pin("members", Json::Arr(vec![ref_p])),
        pin(
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                ("args", Json::Arr(vec![root_a, Json::Bool(true)])),
            ]),
        ),
    ] {
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots(),
            &input.law().definitions(),
            &[p],
            &mut quiet(),
        )
        .unwrap();
    }
    assert!(
        matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots(),&input.law().definitions(),&[pin("chosen",fixture::reference("v","r"))],&mut quiet()),Err(CheckFailure::Input(issue))if issue.code==crate::issue::Code::InconsistentObservation)
    );
}

#[test]
fn finite_reference_field_coverage_stop_never_promotes_unfinished_whole() {
    use crate::control::Control;
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(false, false, false);
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.size,h=@v/h)",
        "current=evaluate(Inspect.stable,h=@v/h)",
        "later=evaluate(Inspect.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    let target = normal.prepared.inputs().law().declarations()["Inspect.stable"].span;
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.get() {
            a.set(false);
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "hole" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |span, ctx, operation, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && operation == "completion_coverage"
                    && index == 0
                {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        stopped.frames.as_slice(),
        &normal.frames[..stopped.frames.len()]
    );
    assert_eq!(
        stopped.iterations.as_slice(),
        &normal.iterations[..stopped.iterations.len()]
    );
    assert_eq!(
        stopped.instances.as_slice(),
        &normal.instances[..stopped.instances.len()]
    );
    assert_eq!(
        stopped.cases.as_slice(),
        &normal.cases[..stopped.cases.len()]
    );
    assert_eq!(
        stopped.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..stopped.universal_witnesses.len()]
    );
    let Json::Obj(ref nw) = normal.wire() else {
        panic!()
    };
    let Json::Obj(ref sw) = stopped.wire() else {
        panic!()
    };
    let Json::Arr(na) = &nw["answers"] else {
        panic!()
    };
    let Json::Arr(sa) = &sw["answers"] else {
        panic!()
    };
    assert_eq!(&sa[..3], &na[..3]);
    for a in &stopped.answers[3..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
        );
    }
    assert!(
        !stopped
            .nodes
            .iter()
            .enumerate()
            .any(|(i, n)| stopped.contexts[i].request == 3
                && stopped.contexts[i].case.is_none()
                && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
    );
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
