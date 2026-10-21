use super::*;
use crate::observed::{
    control::{Limits, Usage},
    *,
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/architecture_environment.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn example(qs: &[&str]) -> ObservedEvaluation {
    let result = evaluate_observed_bytes(fixture::input("", None), qs, &mut quiet()).unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    result
}
fn replay(result: &ObservedEvaluation, nodes: &[Node]) -> Result<(), ValidationFailure> {
    let mut c = quiet();
    let environment = Environment::with_prepared(result.prepared(), &mut c)?;
    let mut graph = Graph::new(&c);
    graph.requests = result.prepared().requests().requests().to_vec();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    for (index, node) in nodes.iter().enumerate() {
        graph.active = result.contexts[index];
        environment.validate(&graph, node)?;
        graph.push(node.clone())?;
    }
    if nodes.len() == result.nodes.len() {
        for (request, answer) in graph.requests.iter().zip(&result.answers) {
            environment.validate_answer(&graph, request, answer)?;
        }
    }
    Ok(())
}
#[test]
fn architecture_environment_edges_sources_domains_and_equal_but_foreign_producers_are_rechecked() {
    let result = example(&[
        fixture::MAP,
        "alias=map(Reservations.Migration,on=@v/mm,reading=Reservations)",
        "source=evaluate(Reservations.smallStates,on=$m.candidate.source)",
        "target=evaluate(Reservations.smallStates,on=$m.candidate.target)",
        "constant=evaluate(Reservations.no,on=$m.candidate.source)",
    ]);
    replay(&result, &result.nodes).unwrap();
    let environment = |answer: usize| {
        let Some(Payload::Evaluation {
            environment: Some(r),
            ..
        }) = &result.nodes[result.answers[answer].outputs["evaluation"].0].payload
        else {
            panic!("explicit environment")
        };
        *r
    };
    let source = environment(2);
    let target = environment(3);
    let candidate = result.answers[1].outputs["candidate"];
    let Some(Payload::Construction(c)) = &result.nodes[candidate.0].payload else {
        panic!("native")
    };
    let ConstructionData::MapCandidate { source: alias, .. } = c.data else {
        panic!("candidate")
    };
    assert_ne!(source, alias);
    let eval = result.answers[4].outputs["evaluation"].0;
    for replacement in [
        None,
        Some(target),
        Some(alias),
        Some(NodeRef(result.nodes.len())),
    ] {
        let mut nodes = result.nodes.clone();
        let Some(Payload::Evaluation { environment, .. }) = &mut nodes[eval].payload else {
            panic!("evaluation")
        };
        *environment = replacement;
        assert!(matches!(
            replay(&result, &nodes[..=eval]),
            Err(ValidationFailure::Internal(_))
        ));
        assert!(matches!(
            replay(&result, &nodes),
            Err(ValidationFailure::Internal(_))
        ));
    }
    let domain = result
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            result.contexts[*i].request == 2 && matches!(n.payload, Some(Payload::Domain { .. }))
        })
        .unwrap()
        .0;
    let mut nodes = result.nodes.clone();
    if let Some(Payload::Domain { elements, .. }) = &mut nodes[domain].payload {
        elements.pop();
    }
    assert!(matches!(
        replay(&result, &nodes),
        Err(ValidationFailure::Internal(_))
    ));
    let mut nodes = result.nodes.clone();
    nodes[eval].support.push(crate::construction::FactPointer {
        snapshot: "v".into(),
        subject: "B".into(),
        field: None,
        atom: None,
    });
    assert!(matches!(
        replay(&result, &nodes),
        Err(ValidationFailure::Internal(_))
    ));
    // Same value is insufficient when the selected current request changes its root.
    let mut changed = result;
    let qs = [
        fixture::MAP,
        "alias=map(Reservations.Migration,on=@v/mm,reading=Reservations)",
        "source=evaluate(Reservations.smallStates,on=$m.candidate.source)",
        "target=evaluate(Reservations.smallStates,on=$m.candidate.target)",
        "constant=evaluate(Reservations.no,on=$m.candidate.target)",
    ];
    changed.prepared = prepare_observed(fixture::input("", None), &qs, &mut quiet()).unwrap();
    assert!(matches!(
        replay(&changed, &changed.nodes),
        Err(ValidationFailure::Internal(_))
    ));
}

#[test]
fn architecture_environment_stops_retain_independent_value_and_refutation_and_freeze_probes() {
    let qs = [
        fixture::MAP,
        "keep=evaluate(Reservations.no,on=$m.candidate.source)",
        "bad=check(Reservations.small,on=$m.candidate.target)",
        "todo=evaluate(Reservations.smallStates,on=$m.candidate.source)",
    ];
    for phase in [Checkpoint::ObjectEvaluation, Checkpoint::Expression] {
        let armed = Rc::new(Cell::new(false));
        let seen = armed.clone();
        crate::observed::data::observe_iterations(move |_, context, operation, _| {
            if operation == "architecture_environment" && context.request == 3 {
                seen.set(true)
            }
        });
        let count = Rc::new(Cell::new(0));
        let observed = count.clone();
        let a = armed.clone();
        let mut normal = Control::new(Limits::default(), move |p| {
            if a.get() && p == phase {
                observed.set(observed.get() + 1)
            }
            Usage::default()
        });
        let result = evaluate_observed_bytes(fixture::input("", None), &qs, &mut normal).unwrap();
        crate::observed::data::clear_iteration_observer();
        assert_eq!(result.status(), "complete");
        let total = count.get();
        assert!(total > 1);
        for at in [1, total / 2, total] {
            for mode in 0..4 {
                let armed = Rc::new(Cell::new(false));
                let a = armed.clone();
                crate::observed::data::observe_iterations(move |_, context, operation, _| {
                    if operation == "architecture_environment" && context.request == 3 {
                        a.set(true)
                    }
                });
                let count = Rc::new(Cell::new(0));
                let observed = count.clone();
                let a = armed.clone();
                let limits = Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                };
                let mut c = Control::new(limits, move |p| {
                    if a.get() && p == phase {
                        observed.set(observed.get() + 1);
                    }
                    if observed.get() < at {
                        return Usage::default();
                    }
                    Usage {
                        elapsed_ms: if mode == 0 { 1 } else { 0 },
                        memory_mib: if mode == 1 { 1 } else { 0 },
                        signal: match mode {
                            2 => Some(crate::result::Signal::Int),
                            3 => Some(crate::result::Signal::Term),
                            _ => None,
                        },
                    }
                });
                let result =
                    evaluate_observed_bytes(fixture::input("", None), &qs, &mut c).unwrap();
                crate::observed::data::clear_iteration_observer();
                assert!(c.stop_reason().is_some(), "{phase:?} {at} {mode}");
                assert_eq!(result.answers[1].status, Decision::Established);
                assert_eq!(result.answers[2].status, Decision::Refuted);
                assert!(!result.answers[2].evidence.is_empty());
                assert!(
                    !result
                        .issues
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::Internal(_))),
                    "{:?}",
                    result.issues
                );
                let stopped = count.get();
                assert!(c.checkpoint(phase).is_err());
                assert_eq!(count.get(), stopped);
            }
        }
    }
}

#[test]
fn architecture_on_resolution_stops_are_latched_before_evaluation() {
    let inputs =
        crate::observed::input::check_inputs(fixture::input("", None), &mut quiet()).unwrap();
    let qs = [
        fixture::MAP,
        "v=evaluate(Reservations.no,on=$m.candidate.source)",
    ];
    for phase in [Checkpoint::RequestBinding, Checkpoint::Projection] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut normal = Control::new(Limits::default(), move |p| {
            if p == phase {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        crate::observed::request::resolve_observed_requests_controlled(
            inputs.law(),
            inputs.archmap(),
            &qs,
            &mut normal,
        )
        .unwrap();
        let total = count.get();
        assert!(total > 0);
        for at in [1, (total / 2).max(1), total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0));
                let seen = count.clone();
                let mut c = Control::new(
                    Limits {
                        time_ms: (mode == 0).then_some(1),
                        memory_mib: (mode == 1).then_some(1),
                    },
                    move |p| {
                        if p == phase {
                            seen.set(seen.get() + 1);
                        }
                        if seen.get() < at {
                            return Usage::default();
                        }
                        Usage {
                            elapsed_ms: if mode == 0 { 1 } else { 0 },
                            memory_mib: if mode == 1 { 1 } else { 0 },
                            signal: match mode {
                                2 => Some(crate::result::Signal::Int),
                                3 => Some(crate::result::Signal::Term),
                                _ => None,
                            },
                        }
                    },
                );
                let result = crate::observed::request::resolve_observed_requests_controlled(
                    inputs.law(),
                    inputs.archmap(),
                    &qs,
                    &mut c,
                );
                assert!(
                    matches!(
                        result,
                        Err(crate::observed::request::ResolveFailure::Interrupted { .. })
                    ),
                    "{phase:?} {at} {mode}: {result:?}"
                );
                let stopped = count.get();
                assert!(c.checkpoint(phase).is_err());
                assert_eq!(count.get(), stopped);
            }
        }
    }
}
