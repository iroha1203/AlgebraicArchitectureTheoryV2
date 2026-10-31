use super::*;
use crate::{
    control::{Limits, Usage},
    observed::*,
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
    assert!(result.nodes[eval].scope.snapshots.contains("v"));
    assert!(result.nodes[eval].scope.modes.contains("specification"));
    for part in 0..2 {
        let mut nodes = result.nodes.clone();
        if part == 0 {
            nodes[eval].scope.snapshots.clear();
        } else {
            nodes[eval].scope.modes.clear();
        }
        assert!(matches!(
            replay(&result, &nodes),
            Err(ValidationFailure::Internal(_))
        ));
    }

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
    nodes[eval].support.push(crate::archmap::Fact {
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
    let original = std::mem::replace(
        &mut changed.prepared,
        prepare_observed(fixture::input("", None), &qs, &mut quiet()).unwrap(),
    );
    assert!(matches!(
        replay(&changed, &changed.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    changed.prepared = original;
    changed.answers[4].scope.snapshots.clear();
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
    let inputs = crate::input::check_inputs(fixture::input("", None), &mut quiet()).unwrap();
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

#[test]
fn unbound_owner_templates_recheck_the_actual_row_producers() {
    let mut c = quiet();
    let result = evaluate_observed_bytes(
        fixture::input(
            "law required nestedOwner(x:System):forall s:State[x] . s.free+s.held=2;",
            None,
        ),
        &[
            fixture::MAP,
            "a=check(Reservations.nestedOwner,on=$m.candidate.source)",
            "b=check(Reservations.nestedOwner,on=$m.candidate.target)",
        ],
        &mut c,
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(result.answers[1].status, Decision::Established);
    assert_eq!(result.answers[2].status, Decision::Refuted);
    replay(&result, &result.nodes).unwrap();
    let domains: Vec<_> = result
        .nodes
        .iter()
        .enumerate()
        .filter(|(index, node)| {
            result.contexts[*index].instance.is_some()
                && matches!(node.payload, Some(Payload::Domain { .. }))
                && matches!(node.rule, Rule::Construction("domain"))
        })
        .map(|(index, _)| index)
        .collect();
    assert_eq!(domains.len(), 2);
    let other_owner = result.nodes[domains[1]].arguments[1];
    let mut nodes = result.nodes.clone();
    assert_ne!(nodes[domains[0]].arguments[1], other_owner);
    nodes[domains[0]].arguments[1] = other_owner;
    assert!(matches!(
        replay(&result, &nodes),
        Err(ValidationFailure::Internal(_))
    ));
    let mut nodes = result.nodes.clone();
    nodes[domains[0]].arguments.remove(1);
    assert!(matches!(
        replay(&result, &nodes),
        Err(ValidationFailure::Internal(_))
    ));
}

fn owned_graph() -> (
    ObservedEvaluation,
    Graph,
    crate::observed::object_component_diagram::Diagram,
    NodeRef,
) {
    owned_graph_with_map(None)
}
fn owned_graph_with_map(
    map: Option<&str>,
) -> (
    ObservedEvaluation,
    Graph,
    crate::observed::object_component_diagram::Diagram,
    NodeRef,
) {
    let result = evaluate_observed_bytes(
        fixture::input("", map),
        &[
            fixture::MAP,
            "keep=evaluate(Reservations.no,on=$m.candidate.source)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    let mut c = quiet();
    let env = Environment::with_prepared(result.prepared(), &mut c).unwrap();
    let mut graph = Graph::new(&c);
    graph.requests = result.prepared().requests().requests().to_vec();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    for (index, node) in result.nodes.iter().enumerate() {
        graph.active = result.contexts[index];
        env.validate(&graph, node).unwrap();
        graph.push(node.clone()).unwrap();
    }
    let root = NodeRef(graph.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!((&v.witness,&v.data),(Witness::Architecture(a),ConstructionData::Architecture{..}) if a.construction().root().subject=="A"))).unwrap());
    graph.active = graph.context_at(root.0);
    let diagram = crate::observed::object_component_diagram::retain(
        &mut graph,
        result.prepared.shared_inputs(),
        root,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    graph.active = *result.contexts.last().unwrap();
    assert_eq!(graph.active.request, 1);
    (result, graph, diagram, root)
}
fn state_values(
    env: &Environment<'_>,
    context: &ArchitectureContext,
    compound: bool,
) -> Vec<String> {
    let mut domain = env
        .reference_roster("Reservations.State", &mut |_| {})
        .unwrap();
    let ty = if compound {
        Type::Tuple(vec![Type::Ref("Reservations.State".into()), Type::Bool])
    } else {
        Type::Ref("Reservations.State".into())
    };
    if compound {
        domain.values = domain
            .values
            .into_iter()
            .map(|v| Scalar::Tuple(vec![v, Scalar::Bool(false)]))
            .collect();
    }
    let mut values = Some(domain.values);
    context
        .domain
        .restrict(
            &ty,
            &mut values,
            &mut vec![],
            &mut domain.support,
            &mut domain.scope,
            &env.control,
            &[],
            None,
        )
        .unwrap();
    values
        .unwrap()
        .iter()
        .map(|v| {
            let value = if let Scalar::Tuple(items) = v {
                &items[0]
            } else {
                v
            };
            let Scalar::Subject { subject, .. } = value else {
                panic!("state")
            };
            subject.clone()
        })
        .collect()
}
#[test]
fn native_owned_environments_keep_the_containing_root_reading_and_exact_subject_domains() {
    let (result, graph, d, root) = owned_graph();
    let env = Environment::with_prepared(result.prepared(), &mut quiet()).unwrap();
    assert_eq!(d.architectures.len(), 3);
    for (index, (reference, expected, subject)) in [
        (root, vec!["p", "q"], "A"),
        (d.architectures[1], vec!["p"], "p"),
        (d.architectures[2], vec!["q"], "q"),
    ]
    .into_iter()
    .enumerate()
    {
        let selected = env.select_architecture(&graph, reference).unwrap().unwrap();
        assert_eq!(selected.reference, reference);
        assert_eq!(selected.scope, graph.get(reference).unwrap().scope);
        assert_eq!(selected.domain.identity.reading(), "Reservations");
        assert_eq!(selected.domain.identity.root().subject, "A");
        assert_eq!(selected.domain.identity.subject().subject, subject);
        assert_eq!(
            state_values(&env, &selected, false),
            expected,
            "object {index}"
        );
        assert_eq!(state_values(&env, &selected, true), ["p", "q", "r", "s"]);
    }
    let selected = env
        .select_architecture(&graph, d.architectures[1])
        .unwrap()
        .unwrap();
    let mut roster = env
        .reference_roster("Reservations.Migration", &mut |_| {})
        .unwrap();
    let original = roster.values.clone();
    let mut values = Some(roster.values);
    selected
        .domain
        .restrict(
            &Type::Ref("Reservations.Migration".into()),
            &mut values,
            &mut vec![],
            &mut roster.support,
            &mut roster.scope,
            &env.control,
            &[],
            None,
        )
        .unwrap();
    assert_eq!(values.unwrap(), original);
    let Some(Payload::Construction(value)) = &graph.get(d.architectures[1]).unwrap().payload else {
        panic!("owned")
    };
    let Witness::Architecture(w) = &value.witness else {
        panic!("origin")
    };
    assert_eq!(w.readings().construction().root().subject, "A");
    assert!(
        w.readings()
            .instances()
            .iter()
            .any(|i| i.declaration().name == "Reservations.symbolic"
                && i.parameters().iter().any(|p| p.ty == Type::Z))
    );
}
#[test]
fn nested_environment_selection_restores_owned_context_and_rejects_changed_producer_request() {
    let (result, mut graph, d, root) = owned_graph();
    let env = Environment::with_prepared(result.prepared(), &mut quiet()).unwrap();
    let owned = d.architectures[1];
    let selected = env.select_architecture(&graph, owned).unwrap().unwrap();
    env.architecture.replace(Some(selected));
    {
        let _guard = env.enter_architecture(&graph).unwrap();
        assert_eq!(env.architecture_ref(), Some(root));
        assert_eq!(env.object_domain().unwrap().identity.subject().subject, "A");
    }
    assert_eq!(env.architecture_ref(), Some(owned));
    assert_eq!(env.object_domain().unwrap().identity.subject().subject, "p");
    graph.requests[0].text.push(' ');
    assert!(env.select_architecture(&graph, owned).is_err());
    assert_eq!(env.architecture_ref(), Some(owned));
}
#[test]
fn owned_environment_rejects_false_type_origin_edges_inputs_and_future_references() {
    let (result, graph, d, root) = owned_graph();
    let owned = d.architectures[1];
    for mode in 0..4 {
        let (_, mut changed, same_objects, _) = owned_graph();
        assert_eq!(same_objects.architectures, d.architectures);
        match mode {
            0 => changed.nodes[owned.0].arguments.clear(),
            1 => changed.nodes[owned.0].rule = Rule::Construction("configuration"),
            2 => {
                changed.nodes[d.objects[1].0].ty =
                    NodeType::Construction(ConstructionType::Architecture)
            }
            _ => {
                let Some(Payload::Construction(foreign)) = &graph.get(root).unwrap().payload else {
                    panic!("root")
                };
                let Some(Payload::Construction(value)) = &mut changed.nodes[owned.0].payload else {
                    panic!("owned")
                };
                value.data = foreign.data.clone();
            }
        }
        let env = Environment::with_prepared(result.prepared(), &mut quiet()).unwrap();
        let reference = if mode == 2 { d.objects[1] } else { owned };
        assert!(
            env.select_architecture(&changed, reference).is_err(),
            "mode {mode}"
        );
    }
    let env = Environment::with_prepared(result.prepared(), &mut quiet()).unwrap();
    assert!(
        env.select_architecture(&graph, d.objects[1])
            .unwrap()
            .is_none()
    );
    assert!(
        env.select_architecture(&graph, NodeRef(graph.nodes.len()))
            .is_err()
    );
    env.cutoff.set(owned.0);
    assert!(env.select_architecture(&graph, owned).is_err());
    let prepared = prepare_observed(
        fixture::input("view added():Bool=true;", None),
        &[
            fixture::MAP,
            "keep=evaluate(Reservations.no,on=$m.candidate.source)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &mut quiet()).unwrap();
    assert!(env.select_architecture(&graph, owned).is_err());
}
#[test]
fn all_four_owned_environment_stops_restore_the_previous_context_and_preserve_producers() {
    let (result, graph, d, root) = owned_graph();
    let before = graph.nodes.clone();
    for mode in 0..4 {
        let armed = Rc::new(Cell::new(false));
        let a = armed.clone();
        let limits = Limits {
            time_ms: (mode == 0).then_some(1),
            memory_mib: (mode == 1).then_some(1),
        };
        let mut c = Control::new(limits, move |phase| {
            if !a.get() || phase != Checkpoint::ObjectEvaluation {
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
        let env = Environment::with_prepared(result.prepared(), &mut c).unwrap();
        let base = env.select_architecture(&graph, root).unwrap().unwrap();
        env.architecture.replace(Some(base));
        armed.set(true);
        assert!(
            matches!(
                env.select_architecture(&graph, d.architectures[1]),
                Err(ValidationFailure::Stop(_))
            ),
            "mode {mode}"
        );
        assert!(c.stop_reason().is_some());
        assert_eq!(env.architecture_ref(), Some(root));
        assert_eq!(env.object_domain().unwrap().identity.subject().subject, "A");
        assert_eq!(graph.nodes, before);
    }
}

#[test]
fn equal_field_values_keep_distinct_owned_environment_subjects() {
    let map = fixture::changed_map(|j| {
        for atom in fixture::atoms(j) {
            let Json::Obj(fields) = atom else {
                panic!("atom")
            };
            match fields.get("id") {
                Some(Json::Str(id)) if id == "q-free" => {
                    fields.insert("value".into(), Json::str("2"));
                }
                Some(Json::Str(id)) if id == "q-held" => {
                    fields.insert("value".into(), Json::str("0"));
                }
                _ => {}
            }
        }
    });
    let (result, graph, d, _) = owned_graph_with_map(Some(&map));
    let env = Environment::with_prepared(result.prepared(), &mut quiet()).unwrap();
    for name in ["Reservations.State.free", "Reservations.State.held"] {
        let (left, right) = (
            env.field("v", "p", name).unwrap(),
            env.field("v", "q", name).unwrap(),
        );
        let (
            crate::archmap::Slot::Known { value: a, .. },
            crate::archmap::Slot::Known { value: b, .. },
        ) = (&left.slot, &right.slot)
        else {
            panic!("known")
        };
        assert_eq!(a, b);
    }
    let left = env
        .select_architecture(&graph, d.architectures[1])
        .unwrap()
        .unwrap();
    let right = env
        .select_architecture(&graph, d.architectures[2])
        .unwrap()
        .unwrap();
    assert_eq!(left.domain.identity.root(), right.domain.identity.root());
    assert_ne!(left.domain.identity, right.domain.identity);
    assert_ne!(left.reference, right.reference);
    assert_eq!(state_values(&env, &left, false), ["p"]);
    assert_eq!(state_values(&env, &right, false), ["q"]);
}
