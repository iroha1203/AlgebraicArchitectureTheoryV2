use super::*;
use crate::observed::construction_result::ConstructionData as D;
use crate::observed::control::{Limits, Usage};
const D_BYTES: &[u8] = include_bytes!("../../tests/fixtures/reservations.atoms.json");
const L_BYTES: &[u8] = include_bytes!("../../tests/fixtures/reservations.law");
const A_BYTES: &str = include_str!("../../tests/fixtures/reservations.archmap.json");
const MAP_ASK: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";
fn inputs(map: &str) -> InputSources {
    InputSources::from_bytes(
        vec![D_BYTES.to_vec()],
        L_BYTES.to_vec(),
        map.as_bytes().to_vec(),
    )
}
fn example(map: &str) -> ObservedEvaluation {
    let result =
        evaluate_observed_bytes(inputs(map), &[MAP_ASK], &mut Control::unlimited()).unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn changed_native(
    result: &ObservedEvaluation,
    select: impl Fn(&D) -> bool,
    change: impl Fn(&mut D),
) {
    let i = result
        .nodes
        .iter()
        .position(|n| matches!(&n.payload,Some(Payload::Construction(v)) if select(&v.data)))
        .unwrap();
    completion_mutation(result, i, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[i].payload else {
            unreachable!()
        };
        change(&mut v.data);
    });
}
#[test]
fn native_map_prefixes_reject_forged_architecture_action_law_provenance_and_operation() {
    let result = example(A_BYTES);
    assert_eq!(result.status(), "complete");
    let target = result
        .nodes
        .iter()
        .filter_map(|n| match &n.payload {
            Some(Payload::Construction(v)) => match &v.data {
                D::Configuration(c) => Some(c.clone()),
                _ => None,
            },
            _ => None,
        })
        .nth(1)
        .unwrap();
    changed_native(
        &result,
        |d| matches!(d, D::Configuration(_)),
        |d| {
            if let D::Configuration(c) = d {
                *c = target.clone();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Architecture { .. }),
        |d| {
            if let D::Architecture { laws, .. } = d {
                laws.clear();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::AtomUniverse(_)),
        |d| {
            if let D::AtomUniverse(atoms) = d {
                atoms.pop();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::AtomMap { .. }),
        |d| {
            if let D::AtomMap { images, .. } = d {
                images[0].subject = "A".into();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::MapCandidate { .. }),
        |d| {
            if let D::MapCandidate { source, target, .. } = d {
                std::mem::swap(source, target);
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Source { .. }),
        |d| {
            if let D::Source { parameters, .. } = d {
                parameters.push(("forged".into(), Type::Z));
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::LawInstance { .. }),
        |d| {
            if let D::LawInstance { occurrence, .. } = d {
                *occurrence = Location::Law { span: (0, 1) };
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Operation { .. }),
        |d| {
            if let D::Operation {
                configuration_map,
                candidate,
                ..
            } = d
            {
                *configuration_map = *candidate;
            }
        },
    );
    let i = result.answers[0].outputs["candidate"].0;
    for field in 0..3 {
        completion_mutation(&result, i, |nodes| match field {
            0 => nodes[i].support.clear(),
            1 => nodes[i].scope.readings.clear(),
            _ => nodes[i].scope.modes.clear(),
        });
    }
}
#[test]
fn native_map_rechecks_the_actual_input_triad_and_resolved_request() {
    let result = example(A_BYTES);
    let altered = A_BYTES.replace("\"value\": \"2\"", "\"value\": \"3\"");
    let prepared =
        prepare_observed(inputs(&altered), &[MAP_ASK], &mut Control::unlimited()).unwrap();
    let mut control = Control::unlimited();
    let environment = Environment::with_prepared(&prepared, &mut control).unwrap();
    let mut graph = Graph::new(&control);
    graph.requests = prepared.requests().requests().to_vec();
    graph.active = result.contexts[0];
    assert!(matches!(
        environment.validate(&graph, &result.nodes[0]),
        Err(ValidationFailure::Internal(_))
    ));
    let prepared = prepare_observed(
        inputs(A_BYTES),
        &["other=map(Reservations.Migration,on=@v/m,reading=Reservations)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    let environment = Environment::with_prepared(&prepared, &mut control).unwrap();
    graph.requests = prepared.requests().requests().to_vec();
    assert!(matches!(
        environment.validate(&graph, &result.nodes[0]),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn native_counterexamples_reject_changed_facts_bindings_and_evidence_coverage() {
    let map = A_BYTES
        .lines()
        .map(|line| {
            if line.contains("\"id\": \"m-states\"") {
                line.replace("[\"v\", \"r\"]", "[\"v\", \"temp\"]")
                    .replace("[\"v\", \"s\"]", "[\"v\", \"r\"]")
                    .replace("[\"v\", \"temp\"]", "[\"v\", \"s\"]")
            } else {
                line.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let result = example(&map);
    assert_eq!(result.answers[0].status, Decision::Refuted);
    changed_native(
        &result,
        |d| matches!(d, D::Counterexample { .. }),
        |d| {
            if let D::Counterexample { facts, .. } = d {
                facts.clear();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Counterexample { .. }),
        |d| {
            if let D::Counterexample { subject, left, .. } = d {
                *subject = *left;
            }
        },
    );
    let claim = result.answers[0].claim.unwrap().0;
    completion_mutation(&result, claim, |nodes| {
        nodes[claim].evidence.pop();
        nodes[claim].judgment.as_mut().unwrap().evidence.pop();
    });
}
#[test]
fn native_partial_configuration_rejects_lost_paths_and_changed_missing_positions() {
    let map = A_BYTES
        .lines()
        .filter(|line| !line.contains("\"id\": \"p-owner\""))
        .collect::<Vec<_>>()
        .join("\n");
    let result = example(&map);
    assert_eq!(result.status(), "partial");
    changed_native(
        &result,
        |d| matches!(d, D::Pending { .. }),
        |d| {
            if let D::Pending { parts, .. } = d {
                parts.pop();
            }
        },
    );
    let candidate = result.answers[0].outputs["candidate"].0;
    completion_mutation(&result, candidate, |nodes| {
        nodes[candidate].reasons[0].missing[0].subject = "q".into()
    });
}
#[test]
fn native_map_stops_latch_without_discarding_checked_maps_or_resuming_computation() {
    use std::{cell::Cell, rc::Rc};
    for point in [
        Checkpoint::ConfigurationMap,
        Checkpoint::ConfigurationOperation,
        Checkpoint::NativeResultNode,
    ] {
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let original = evaluate_observed_bytes(inputs(A_BYTES), &[MAP_ASK], &mut probe).unwrap();
        assert_eq!(original.status(), "complete");
        let total = count.get();
        assert!(total > 0);
        for at in [1, (total / 2).max(1), total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0usize));
                let seen = count.clone();
                let mut control = Control::new(
                    Limits {
                        time_ms: (mode == 0).then_some(1),
                        memory_mib: (mode == 1).then_some(1),
                    },
                    move |p| {
                        if p == point {
                            seen.set(seen.get() + 1);
                        }
                        let stopped = seen.get() >= at;
                        Usage {
                            elapsed_ms: u128::from(stopped && mode == 0),
                            memory_mib: u128::from(stopped && mode == 1),
                            signal: if stopped {
                                match mode {
                                    2 => Some(crate::result::Signal::Int),
                                    3 => Some(crate::result::Signal::Term),
                                    _ => None,
                                }
                            } else {
                                None
                            },
                        }
                    },
                );
                let result =
                    evaluate_observed_bytes(inputs(A_BYTES), &[MAP_ASK], &mut control).unwrap();
                assert_eq!(
                    result.status(),
                    "interrupted",
                    "{point:?}/{at}/{mode}: {:?}",
                    result.issues
                );
                assert!(
                    !result
                        .issues
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::Internal(_))),
                    "{:?}",
                    result.issues
                );
                let stopped = control.stop_reason().unwrap();
                assert_eq!(count.get(), at);
                assert_eq!(
                    control.checkpoint(Checkpoint::Expression).unwrap_err(),
                    stopped
                );
                assert_eq!(count.get(), at);
                if at == total {
                    assert!(
                        result.answers[0].outputs.contains_key("map"),
                        "{point:?}: {:?}",
                        result.answers
                    );
                    assert_eq!(result.answers[0].status, Decision::Established);
                    if matches!(
                        point,
                        Checkpoint::NativeResultNode | Checkpoint::ConfigurationOperation
                    ) {
                        assert!(result.answers[0].outputs.contains_key("operation"));
                    }
                    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
                }
            }
        }
    }
}
