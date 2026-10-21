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
    changed_native(
        &result,
        |d| matches!(d, D::ConfigurationMap { .. }),
        |d| {
            if let D::ConfigurationMap {
                candidate,
                preservation,
            } = d
            {
                *preservation = *candidate;
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Operation { .. }),
        |d| {
            if let D::Operation {
                configuration_map,
                preservation,
                ..
            } = d
            {
                *preservation = *configuration_map;
            }
        },
    );
    let claim = result.answers[0].claim.unwrap().0;
    completion_mutation(&result, claim, |nodes| {
        nodes[claim].judgment.as_mut().unwrap().status = Decision::Refuted
    });
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

#[test]
fn projected_map_rechecks_original_projection_value_edges_scope_and_dynamic_conditions() {
    let sources = || {
        InputSources::from_bytes(
            vec![D_BYTES.to_vec()],
            include_bytes!("../../tests/fixtures/public-map-projections.law").to_vec(),
            A_BYTES.as_bytes().to_vec(),
        )
    };
    let result = evaluate_observed_bytes(
        sources(),
        &[
            "copy=map(Reservations.Migration,on=$v.value.some,reading=Reservations)",
            "v=evaluate(Reservations.present,m=@v/m)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Established);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let projection = result
        .nodes
        .iter()
        .position(|n| matches!(n.rule, Rule::Projection(_)))
        .unwrap();
    for variant in 0..4 {
        completion_mutation(&result, projection, |nodes| match variant {
            0 => {
                nodes[projection].payload = Some(Payload::Scalar(Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "e".into(),
                    entity: "Reservations.Reserve".into(),
                }))
            }
            1 => nodes[projection].arguments.clear(),
            2 => nodes[projection].support.clear(),
            _ => nodes[projection].scope.readings.clear(),
        });
    }
    changed_native(
        &result,
        |d| matches!(d, D::MapCandidate { .. }),
        |d| {
            if let D::MapCandidate {
                subject, source, ..
            } = d
            {
                *subject = *source;
            }
        },
    );
    let result = evaluate_observed_bytes(
        sources(),
        &[
            "bad=map(Reservations.Migration,on=$v.value.some,reading=Reservations)",
            "v=evaluate(Reservations.absent,m=@v/m)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Undetermined);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let condition = result
        .nodes
        .iter()
        .position(|n| {
            matches!(
                n.rule,
                Rule::ProjectionCheck {
                    part: ProjectionCheckPart::Condition,
                    ..
                }
            )
        })
        .unwrap();
    completion_mutation(&result, condition, |nodes| {
        nodes[condition].evidence.clear()
    });
    completion_mutation(&result, condition, |nodes| {
        nodes[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
}
#[test]
fn dynamic_map_projection_stops_preserve_checked_prefix_without_resuming_derivation() {
    use std::{cell::Cell, rc::Rc};
    let sources = || {
        InputSources::from_bytes(
            vec![D_BYTES.to_vec()],
            include_bytes!("../../tests/fixtures/public-map-projections.law").to_vec(),
            A_BYTES.as_bytes().to_vec(),
        )
    };
    let asks = [
        "bad=map(Reservations.Migration,on=$v.value.some,reading=Reservations)",
        "v=evaluate(Reservations.absent,m=@v/m)",
    ];
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::Projection {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let prepared = prepare_observed(sources(), &asks, &mut Control::unlimited()).unwrap();
    let complete = evaluate_observed(prepared, &mut control).unwrap();
    assert_eq!(complete.answers[0].status, Decision::Undetermined);
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
                    if p == Checkpoint::Projection {
                        seen.set(seen.get() + 1);
                    }
                    let stop = seen.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && mode == 0),
                        memory_mib: u128::from(stop && mode == 1),
                        signal: if stop {
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
            let prepared = prepare_observed(sources(), &asks, &mut Control::unlimited()).unwrap();
            let result = evaluate_observed(prepared, &mut control).unwrap();
            assert_eq!(
                result.status(),
                "interrupted",
                "{at}/{mode}: {:?}",
                result.issues
            );
            assert!(
                !result
                    .issues
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
            );
            assert_eq!(count.get(), at);
            let stop = control.stop_reason().unwrap();
            assert_eq!(
                control.checkpoint(Checkpoint::Expression).unwrap_err(),
                stop
            );
            assert_eq!(count.get(), at);
            assert!(result.answers[1].outputs.contains_key("value"));
            rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
        }
    }
}

#[test]
fn failed_candidate_conditions_recheck_original_counterexample_and_construction_inputs() {
    let left: &[u8] = include_bytes!("../../tests/fixtures/configuration-map-left.atoms.json");
    let right = include_str!("../../tests/fixtures/configuration-map-right.atoms.json").replacen(
        "\"name\": \"count\"",
        "\"name\": \"other\"",
        1,
    );
    let definitions = crate::definition::check_definitions(&[
        ("definition0", left),
        ("definition1", right.as_bytes()),
    ])
    .unwrap();
    let ld = &definitions.vocabularies["Left"].digest;
    let rd = &definitions.vocabularies["Right"].digest;
    let bridge = include_str!("../../tests/fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let definitions = crate::definition::check_definitions(&[
        ("definition0", left),
        ("definition1", right.as_bytes()),
        ("definition2", bridge.as_bytes()),
    ])
    .unwrap();
    let law = include_str!("../../tests/fixtures/configuration-map-bridge.law")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let map = include_str!("../../tests/fixtures/configuration-map-bridge.archmap.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd)
        .replace(
            "@BRIDGE_DIGEST@",
            &definitions.vocabularies["Bridge"].digest,
        )
        .replace("Right.Root.count", "Right.Root.other");
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![left.to_vec(), right.into_bytes(), bridge.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &["m=map(Bridge.Move,on=@v/m,reading=LeftRead,to_reading=RightRead)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(result.answers[0].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    changed_native(
        &result,
        |d| matches!(d, D::ConstructionLabel(_)),
        |d| {
            if let D::ConstructionLabel(label) = d {
                *label = Scalar::Text("configuration_map".into());
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::CandidateCondition { .. }),
        |d| {
            if let D::CandidateCondition { source, target, .. } = d {
                std::mem::swap(source, target);
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Counterexample { .. }),
        |d| {
            if let D::Counterexample { facts, .. } = d {
                facts.clear();
            }
        },
    );
    let claim = result.answers[0].claim.unwrap().0;
    completion_mutation(&result, claim, |nodes| {
        nodes[claim].evidence.clear();
        nodes[claim].judgment.as_mut().unwrap().evidence.clear();
    });
    completion_mutation(&result, claim, |nodes| {
        nodes[claim].judgment.as_mut().unwrap().status = Decision::Established
    });
    let candidate = result.answers[0].outputs["candidate"].0;
    completion_mutation(&result, candidate, |nodes| nodes[candidate].reasons.clear());
    completion_mutation(&result, candidate, |nodes| {
        let ReasonKind::ConditionFailed { condition, .. } = &mut nodes[candidate].reasons[0].kind
        else {
            panic!("元構成の反証理由");
        };
        *condition = NodeRef(0);
    });
}

#[test]
fn completion_reference_evidence_and_claims_reject_dropped_or_forged_scope() {
    let definition = include_bytes!("../../tests/fixtures/configuration-map-graph.atoms.json");
    let checked = crate::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &checked.vocabularies["Graph"].digest;
    let law = include_str!("../../tests/fixtures/configuration-map-graph.law")
        .replace("@DIGEST@", digest);
    let map = include_str!("../../tests/fixtures/configuration-map-graph.archmap.json")
        .replace("@DIGEST@", digest)
        .replace(r#""@LINKS_A@""#, r#"[["v","p"],["v","p"]]"#)
        .replace(r#""@LINKS_B@""#, r#"[["v","r"],["v","s"]]"#)
        .replace(r#""@MEMBERS_A@""#, "[]")
        .replace(r#""@MEMBERS_B@""#, "[]")
        .lines()
        .filter(|line| !line.contains("m-entries"))
        .collect::<Vec<_>>()
        .join("\n");
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![definition.to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &["m=map(Graph.Move,on=@v/m,reading=GraphRead)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    let a = &result.answers[0];
    assert_eq!(a.status, Decision::Undetermined);
    assert!(a.scope.completions);
    assert_eq!(a.evidence.len(), 1);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    for index in [a.evidence[0].0, a.claim.unwrap().0] {
        assert!(result.nodes[index].scope.completions);
        completion_mutation(&result, index, |nodes| {
            nodes[index].scope.completions = false
        });
    }
}
