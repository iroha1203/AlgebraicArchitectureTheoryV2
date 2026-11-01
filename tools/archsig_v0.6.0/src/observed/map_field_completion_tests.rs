use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/map_field_completions.rs");
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn example(mode: usize) -> ObservedEvaluation {
    let question = match mode {
        0 | 9 => "evaluate(Inspect.read,h=@v/h)",
        1 => "evaluate(Inspect.mixed,h=@v/h)",
        2 => "evaluate(Inspect.bag,h=@v/h)",
        3 => "evaluate(Inspect.choice,h=@v/h)",
        4 => "check(Inspect.valid,h=@v/h)",
        5 => "evaluate(Inspect.independent,h=@v/h)",
        6 => "evaluate(Inspect.partial,h=@v/h)",
        7 => "evaluate(Inspect.pending,h=@v/h,a=@v/B)",
        8 => "evaluate(Inspect.plain,h=@v/h)",
        _ => panic!(),
    };
    let first = format!("first={question}");
    let target = format!("target={question}");
    let r = evaluate_observed_bytes(
        fixture::input(mode == 8 || mode == 9, false, mode == 4 || mode == 6, false),
        &[&first, &target, "later=evaluate(Inspect.seed)"],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.answers);
    r
}
fn map_mut(value: &mut Scalar) -> (&mut Type, &mut Type, &mut Vec<(Scalar, Scalar)>) {
    match value {
        Scalar::Map {
            domain,
            codomain,
            pairs,
        } => (domain, codomain, pairs),
        _ => panic!("Map expected"),
    }
}
fn scalar_mut(node: &mut Node) -> &mut Scalar {
    match node.payload.as_mut().unwrap() {
        Payload::Scalar(s) => s,
        _ => panic!("Scalar expected"),
    }
}
#[test]
fn map_field_totality_owned_key_image_and_duplicate_rows_are_rechecked() {
    let r = example(9);
    let request = &r.prepared.requests().requests()[1];
    let answer = &r.answers[1];
    let root = answer.outputs["evaluation"].0;
    let domain = r.nodes[root].arguments[1].0;
    let Some(Payload::Domain { elements, .. }) = &r.nodes[domain].payload else {
        panic!()
    };
    let first = elements
        .iter()
        .find(|m| matches!(&r.nodes[m.0].payload, Some(Payload::Scalar(Scalar::Map { pairs, .. })) if !pairs.is_empty()))
        .unwrap()
        .0;
    // 全域性の再検査の代表: 候補のMapから行を消すと核が拒否する。
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let (_, _, pairs) = map_mut(scalar_mut(&mut graph.nodes[first]));
    pairs.clear();
    let t = scalar_mut(&mut graph.nodes[first]).ty();
    graph.nodes[first].ty = NodeType::Value(t);
    assert!(matches!(
        environment(&r).validate_answer(&graph, request, answer),
        Err(ValidationFailure::Internal(_))
    ));
}
fn stop(phase: &'static str, at: usize, kind: usize) {
    use crate::control::Control;
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(true, false, false, false);
    let asks = [
        "seed=evaluate(Inspect.seed)",
        "prior=check(Inspect.prior)",
        "hole=evaluate(Inspect.partial,h=@v/h)",
        "current=evaluate(Inspect.same,h=@v/h)",
        "later=evaluate(Inspect.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert_eq!(normal.status(), "partial");
    assert_eq!(normal.answers[1].status, Decision::Refuted);
    assert_eq!(normal.answers[2].status, Decision::Undetermined);
    assert_eq!(normal.answers[3].status, Decision::Established);
    let target = normal.prepared.inputs().law().declarations["Inspect.same"].span;
    let (limits, usage, expected) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let pin_gate = Rc::new(Cell::new(false));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            None
        }
    });
    if phase == "map_reader" || phase == "map_cover" {
        let (gate, a, s) = (pin_gate.clone(), armed.clone(), seen.clone());
        crate::archmap::observe_map_validation(move |operation, index| {
            if gate.get() && operation == phase && index == 0 {
                assert!(!s.replace(true));
                a.set(true);
                gate.set(false);
            }
        });
    }
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "hole" && phase != "answer" {
            let (a, s, gate) = (armed.clone(), seen.clone(), pin_gate.clone());
            data::observe_iterations(move |span, ctx, operation, index| {
                if span == target
                    && ctx.request == 3
                    && ctx.case.is_none()
                    && operation
                        == if phase == "map_reader" || phase == "map_cover" {
                            "completion_reference_constraints"
                        } else {
                            phase
                        }
                    && index == at
                {
                    if phase == "map_reader" || phase == "map_cover" {
                        gate.set(true);
                    } else {
                        assert!(!s.replace(true));
                        a.set(true);
                    }
                }
            });
        }
        if q.id == "current" && phase == "answer" {
            assert!(!seen.replace(true));
            armed.set(true);
        }
        Ok(())
    })
    .unwrap();
    data::clear_iteration_observer();
    crate::archmap::clear_map_validation_observer();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted", "{:?}", stopped.issues);
    assert_eq!(c.stop_reason(), Some(expected.clone()));
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
    let retained = if phase == "answer" { 4 } else { 3 };
    assert_eq!(&sa[..retained], &na[..retained]);
    for a in &stopped.answers[retained..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&expected))
        );
    }
    if phase != "answer" {
        assert!(
            !stopped
                .nodes
                .iter()
                .enumerate()
                .any(|(i, n)| stopped.contexts[i].request == 3
                    && stopped.contexts[i].case.is_none()
                    && matches!(n.payload, Some(Payload::FiniteExhaustion { .. })))
        );
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn map_field_coverage_memory_stop_never_promotes_unfinished_whole() {
    stop("completion_coverage", 0, 2);
}

#[test]
fn map_field_internal_pins_validate_original_map_shapes_refs_totality_and_missing_identity() {
    use crate::archmap::{FieldAssignment, check_completion_with_values};
    use crate::control::CheckFailure;
    let pin = |field: &str, value: Json| FieldAssignment {
        snapshot: "v".into(),
        subject: "h".into(),
        field: format!("MapFields.Holder.{field}"),
        value,
    };
    let r = example(9);
    let input = r.prepared.inputs();
    let kx = fixture::table("v", "k", "x");
    let row = |key: Json, image: Json| Json::Arr(vec![key, image]);
    let malformed = [
        ("table", fixture::table("v", "ghost", "x")),
        ("table", fixture::table("v", "x", "x")),
        ("table", fixture::table("v", "k", "A")),
        (
            "table",
            Json::Arr(vec![
                row(fixture::reference("v", "k"), fixture::reference("v", "x")),
                row(fixture::reference("v", "k"), fixture::reference("v", "y")),
            ]),
        ),
        (
            "table",
            Json::Arr(vec![Json::Arr(vec![fixture::reference("v", "k")])]),
        ),
        ("table", Json::Bool(true)),
        ("owner", fixture::reference("v", "A")),
        (
            "mixed",
            Json::Arr(vec![Json::Bool(false), fixture::table("v", "k", "A")]),
        ),
        ("bag", Json::Arr(vec![fixture::table("v", "x", "x")])),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("wrap")),
                ("args", Json::Arr(vec![fixture::table("v", "k", "A")])),
            ]),
        ),
    ];
    for (field, value) in malformed {
        assert!(
            matches!(
                check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
                    &input.archmap().snapshots,
                    &input.law().definitions,
                    &[pin(field, value)],
                    &mut named_call_quiet()
                ),
                Err(CheckFailure::Input(_))
            ),
            "malformed {field}"
        );
    }
    assert!(matches!(
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots,
            &input.law().definitions,
            &[pin("table", kx.clone()), pin("table", kx.clone())],
            &mut named_call_quiet()
        ),
        Err(CheckFailure::Input(_))
    ));
    for bad in [
        Json::Arr(vec![]),
        fixture::table("w", "k", "x"),
        Json::Arr(vec![row(
            fixture::reference("v", "k"),
            fixture::reference("w", "x"),
        )]),
        Json::Arr(vec![
            row(fixture::reference("v", "k"), fixture::reference("v", "x")),
            row(fixture::reference("w", "k"), fixture::reference("v", "y")),
        ]),
    ] {
        assert!(
            matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots,&input.law().definitions,&[pin("table",bad)],&mut named_call_quiet()),Err(CheckFailure::Input(issue)) if issue.code==crate::issue::Code::InconsistentObservation)
        );
    }
    for good in [kx, fixture::table("v", "k", "y")] {
        check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
            &input.archmap().snapshots,
            &input.law().definitions,
            &[pin("table", good)],
            &mut named_call_quiet(),
        )
        .unwrap();
    }
    let unknown = example(4);
    let input = unknown.prepared.inputs();
    check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(
        &input.archmap().snapshots,
        &input.law().definitions,
        &[pin("table", Json::Arr(vec![]))],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert!(
        matches!(check_completion_with_values::<CheckFailure<Box<crate::issue::Issue>>>(&input.archmap().snapshots,&input.law().definitions,&[pin("table",Json::Arr(vec![])),pin("owner",fixture::reference("v","A"))],&mut named_call_quiet()),Err(CheckFailure::Input(issue)) if issue.code==crate::issue::Code::InconsistentObservation)
    );
}
