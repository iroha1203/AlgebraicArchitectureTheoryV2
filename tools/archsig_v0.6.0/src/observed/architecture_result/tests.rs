use super::*;
use crate::{
    control::{Limits, Usage},
    input::{InputSources, check_inputs},
    observed::{PreparedObserved, request::resolve_native_for_test},
};
use std::{cell::Cell, rc::Rc};
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../../tests/common/request_acceptance_data.rs");
}
#[allow(dead_code)]
mod reservations {
    use crate as archsig;
    include!("../../../tests/common/architecture_environment.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
const BODY: &str = "law required bound(p:Item) when p.quantity>=0:p.quantity=0;law optional root(a:Root):true;view amount(p:Item):Z=p.quantity;law optional symbolic(p:Item,z:Z):z=z;";
fn sources(missing_owner: bool, body: &str) -> InputSources {
    let original = fixture::input();
    let defs =
        crate::definition::check_definitions(&[("definition0", fixture::D.as_bytes())]).unwrap();
    let digest = &defs.vocabularies["Requests"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading R{{use vocabulary Requests version \"1\" digest \"{digest}\";{body}}}"
    );
    let mut map = String::from_utf8(original.archmap().bytes().to_vec()).unwrap();
    if missing_owner {
        let atom = r#"{"id":"owner-i","subject":"i","field":"Requests.Item.owner","value":["v","A"],"origin":"spec"}"#;
        assert!(map.contains(atom));
        map = map.replace(atom, "");
    }
    InputSources::from_bytes(
        vec![fixture::D.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn prepared(input: InputSources, asks: &[&str]) -> PreparedObserved {
    let inputs = Arc::new(check_inputs(input, &mut quiet()).unwrap());
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), asks, &mut quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn empty(p: &PreparedObserved, c: &Control) -> Graph {
    let mut g = Graph::new(c);
    g.requests = p.requests().requests().to_vec();
    g
}
fn replay(
    p: &PreparedObserved,
    original: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c)?;
    let mut g = empty(p, &c);
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    for (index, node) in nodes.iter().enumerate() {
        g.active = original.contexts[index];
        env.validate(&g, node)?;
        g.push(node.clone())?;
    }
    Ok(g)
}
fn value(g: &Graph, r: NodeRef) -> &ConstructionValue {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    v
}
#[test]
fn build_request_keeps_original_architecture_law_occurrences_and_all_object_readings() {
    let p = prepared(sources(false, BODY), &["b=build(R,on=@v/A)"]);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    assert!(a.complete);
    assert!(a.reasons.is_empty());
    assert_eq!(
        g.scalar(a.root).unwrap(),
        &Scalar::Subject {
            snapshot: "v".into(),
            subject: "A".into(),
            entity: "Requests.Root".into()
        }
    );
    let D::Architecture {
        reading,
        root,
        configuration,
        laws,
        arrows,
    } = &value(&g, a.reference).data
    else {
        panic!("Architecture")
    };
    assert_eq!(reading, "R");
    assert_eq!(*root, a.root);
    assert!(arrows.is_empty());
    assert_eq!(laws.len(), 3);
    let names = laws
        .iter()
        .map(|r| match &value(&g, *r).data {
            D::LawInstance {
                name,
                occurrence,
                body,
                ..
            } => {
                assert!(matches!(occurrence, Location::Law { .. }));
                assert!(matches!(
                    &value(&g, *body).data,
                    D::Source {
                        location: Location::Law { .. },
                        ..
                    }
                ));
                name.as_str()
            }
            _ => panic!("LawInstance"),
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["R.bound", "R.root", "R.symbolic"]);
    let original_law = std::str::from_utf8(p.inputs().sources().law().bytes()).unwrap();
    for (&reference, expected) in laws.iter().zip(["p.quantity=0", "true", "z=z"]) {
        let D::LawInstance {
            name,
            body,
            guard,
            bindings,
            role,
            ..
        } = &value(&g, reference).data
        else {
            unreachable!()
        };
        let D::Source {
            location: Location::Law { span },
            parameters,
            ..
        } = &value(&g, *body).data
        else {
            panic!("source position")
        };
        assert_eq!(original_law[span.0..span.1].trim(), expected);
        assert_eq!(bindings.len(), 1);
        let subject = if name == "R.root" { "A" } else { "i" };
        assert!(
            matches!(g.scalar(bindings[0].value).unwrap(),Scalar::Subject{subject:actual,..} if actual==subject)
        );
        if name == "R.symbolic" {
            assert_eq!(parameters, &vec![("z".into(), crate::types::Type::Z)]);
        } else {
            assert!(parameters.is_empty());
        }
        if name == "R.bound" {
            assert_eq!(*role, crate::law::ast::Role::Required);
            let D::Source {
                location: Location::Law { span },
                guard: true,
                ..
            } = &value(&g, guard.unwrap()).data
            else {
                panic!("guard source")
            };
            assert_eq!(original_law[span.0..span.1].trim(), "p.quantity>=0");
        } else {
            assert_eq!(*role, crate::law::ast::Role::Optional);
            assert!(guard.is_none());
        }
    }

    let D::Configuration(config) = &value(&g, *configuration).data else {
        panic!("configuration")
    };
    assert!(config.requirements().iter().any(|f| f.subject == "i"
        && f.field.as_deref() == Some("Requests.Item.quantity")
        && f.atom.is_none()));
    let diagram = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut c,
    )
    .unwrap()
    .unwrap();
    assert_eq!(diagram.objects.len(), 2);
    assert_eq!(diagram.architectures[0], a.reference);
    assert_eq!(diagram.readings.len(), 8);
    assert_eq!(a.witness.construction().root().subject, "A");
    assert_eq!(
        a.witness.readings().objects()[1].identity().root().subject,
        "A"
    );
    assert_eq!(
        a.witness.readings().objects()[1]
            .identity()
            .subject()
            .subject,
        "i"
    );
    let declarations = diagram
        .readings
        .iter()
        .map(|r| match &value(&g, r.expression).wire() {
            crate::canonical::Json::Obj(o) => o["declaration"].clone(),
            _ => panic!("reading"),
        })
        .collect::<Vec<_>>();
    for name in ["R.amount", "R.bound", "R.root", "R.symbolic"] {
        assert_eq!(
            declarations
                .iter()
                .filter(|n| **n == crate::canonical::Json::str(name))
                .count(),
            2
        );
    }
    assert!(g.nodes[a.reference.0].scope.readings.contains("R"));
    assert!(g.nodes[a.reference.0].scope.snapshots.contains("v"));
    assert!(g.nodes[a.reference.0].scope.modes.contains("specification"));
    assert!(g.nodes.iter().all(|n| n.judgment.is_none()));
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn missing_membership_keeps_partial_architecture_and_never_completes_the_object_family() {
    let p = prepared(sources(true, BODY), &["b=build(R,on=@v/A)"]);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    assert!(!a.complete);
    assert!(value(&g, a.reference).is_blocked());
    assert!(a.reasons.iter().any(|r| {
        matches!(r.kind, ReasonKind::Missing)
            && r.missing
                .iter()
                .any(|f| f.subject == "i" && f.field.as_deref() == Some("Requests.Item.owner"))
    }));
    assert!(g.nodes.iter().all(|n| !matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Architecture{..}))));
    replay(&p, &g, &g.nodes).unwrap();
    let before = g.nodes.clone();
    assert!(
        crate::observed::object_component_diagram::retain(
            &mut g,
            p.shared_inputs(),
            a.reference,
            &mut c
        )
        .is_err()
    );
    assert_eq!(g.nodes, before);
}
#[test]
fn build_origin_rejects_modified_root_reading_request_inputs_edges_support_and_scope() {
    let p = prepared(
        sources(false, BODY),
        &["b=build(R,on=@v/A)", "other=build(R,on=@v/B)"],
    );
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    replay(&p, &g, &g.nodes).unwrap();
    for mode in 0..7 {
        let mut nodes = g.nodes.clone();
        let n = &mut nodes[a.reference.0];
        match mode {
            0 => n.ty = NodeType::Construction(T::Configuration),
            1 => n.arguments.clear(),
            2 => n.support.clear(),
            3 => {
                n.scope.readings.insert("Foreign".into());
            }
            4 => n.rule = Rule::Construction("configuration"),
            _ => {
                let Some(Payload::Construction(v)) = &mut n.payload else {
                    unreachable!()
                };
                let D::Architecture { reading, root, .. } = &mut v.data else {
                    unreachable!()
                };
                if mode == 5 {
                    *reading = "Other".into()
                } else {
                    *root = a.reference
                }
            }
        }
        assert!(replay(&p, &g, &nodes).is_err(), "mode {mode}");
    }
    let mut foreign = empty(&p, &c);
    foreign.requests[0].arguments[0].value = Selector::Subject {
        snapshot: "v".into(),
        subject: "B".into(),
    };
    foreign.contexts = g.contexts.clone();
    assert!(replay(&p, &foreign, &g.nodes).is_err());
    assert!(
        super::validate_build_origin(
            &env,
            &g,
            &p.requests().requests()[1],
            value(&g, a.reference)
        )
        .is_err()
    );
    let changed = prepared(
        sources(false, &BODY.replace("=0", "=1")),
        &["b=build(R,on=@v/A)", "other=build(R,on=@v/B)"],
    );
    assert!(replay(&changed, &g, &g.nodes).is_err());
    let before = g.nodes.clone();
    g.active.request = 1;
    assert!(
        build(
            changed.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[1],
            &mut c
        )
        .is_err()
    );
    assert_eq!(g.nodes, before);
}
#[test]
fn root_handles_keep_actual_producer_references_and_build_request_identity() {
    let asks = [
        reservations::MAP,
        "b=build(Reservations,on=$m.candidate.source.root)",
    ];
    let p = prepared(reservations::input("", None), &asks);
    let previous = crate::observed::evaluate_observed_bytes(
        reservations::input("", None),
        &[reservations::MAP],
        &mut quiet(),
    )
    .unwrap();
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    g.checked_answers = previous.answers.iter().cloned().enumerate().collect();
    g.frames = previous.frames.clone();
    g.iterations = previous.iterations.clone();
    g.instances = previous.instances.clone();
    g.cases = previous.cases.clone();
    g.universal_witnesses = previous.universal_witnesses.clone();
    for (index, node) in previous.nodes.iter().enumerate() {
        g.active = previous.contexts[index];
        env.validate(&g, node).unwrap();
        g.push(node.clone()).unwrap();
    }
    g.active = crate::observed::call::Context {
        request: 1,
        frame: None,
        iteration: None,
        instance: None,
        case: None,
    };
    let selector = &p.requests().requests()[1].arguments[0].value;
    let AnswerBinding::Reference(expected) = env.answer_binding(&g, selector, (0, 0)).unwrap()
    else {
        panic!("actual root ref")
    };
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut c,
    )
    .unwrap();
    assert_eq!(a.root, expected);
    assert_eq!(a.witness.construction().root().subject, "A");
    assert_eq!(a.witness.construction().reading(), "Reservations");
    assert_eq!(
        a.witness
            .readings()
            .objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["A", "p", "q"]
    );
    assert_eq!(g.contexts[a.reference.0].request, 1);
    let d = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut c,
    )
    .unwrap()
    .unwrap();
    assert_eq!(d.architectures[0], a.reference);
    assert_eq!(d.objects.len(), 3);
    replay(&p, &g, &g.nodes).unwrap();
    let mut changed = g.nodes.clone();
    let Some(Payload::Construction(v)) = &mut changed[a.reference.0].payload else {
        unreachable!()
    };
    let D::Architecture { root, .. } = &mut v.data else {
        unreachable!()
    };
    // 表示値が同じでも、別producerの参照を元Handleの代わりに使えない。
    let duplicate=g.nodes.iter().enumerate().find_map(|(i,n)|(i!=expected.0 && matches!(&n.payload,Some(Payload::Construction(v)) if v.scalar()==g.scalar(expected).ok())).then_some(NodeRef(i))).unwrap();
    *root = duplicate;
    changed[a.reference.0].arguments[0] = duplicate;
    assert!(replay(&p, &g, &changed).is_err());
}
#[test]
fn four_stops_preserve_every_finished_native_prefix() {
    let p = prepared(sources(false, BODY), &["b=build(R,on=@v/A)"]);
    let mut normal = quiet();
    let env = Environment::with_prepared(&p, &mut normal).unwrap();
    let mut graph = empty(&p, &normal);
    build(
        p.shared_inputs(),
        &env,
        &mut graph,
        &p.requests().requests()[0],
        &mut normal,
    )
    .unwrap();
    let total = Rc::new(Cell::new(0));
    let count = total.clone();
    let mut c = Control::new(move |phase| {
        if phase == Checkpoint::NativeResultNode {
            count.set(count.get() + 1)
        }
        None
    });
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    assert!(total.get() > 2);
    for at in [1, total.get() / 2, total.get()] {
        for mode in 0..4 {
            let reached = Rc::new(Cell::new(0));
            let count = reached.clone();
            let limits = Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            };
            let mut c = Control::new(limits, move |phase| {
                if phase == Checkpoint::NativeResultNode {
                    count.set(count.get() + 1)
                }
                if count.get() < at {
                    return None;
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
            let env = Environment::with_prepared(&p, &mut c).unwrap();
            let mut g = empty(&p, &c);
            assert!(matches!(
                build(
                    p.shared_inputs(),
                    &env,
                    &mut g,
                    &p.requests().requests()[0],
                    &mut c
                ),
                Err(ValidationFailure::Stop(_))
            ));
            assert!(c.stop_reason().is_some());
            assert!(g.nodes.len() <= graph.nodes.len());
            assert_eq!(g.nodes, graph.nodes[..g.nodes.len()]);
            replay(&p, &g, &g.nodes).unwrap();
        }
    }
}
#[test]
fn view_root_and_tuple_projection_are_rechecked_from_the_actual_original_handle() {
    let extra = "view box(a:System):(System,Z)=(a,7);";
    for (producer, selector, projection) in [
        (
            "e=evaluate(Reservations.sourceOf,m=@v/m)",
            "$e.value",
            false,
        ),
        ("e=evaluate(Reservations.box,a=@v/A)", "$e.value[0]", true),
    ] {
        let ask = format!("b=build(Reservations,on={selector})");
        let p = prepared(reservations::input(extra, None), &[producer, &ask]);
        let previous = crate::observed::evaluate_observed_bytes(
            reservations::input(extra, None),
            &[producer],
            &mut quiet(),
        )
        .unwrap();
        let mut c = quiet();
        let env = Environment::with_prepared(&p, &mut c).unwrap();
        let mut g = empty(&p, &c);
        g.checked_answers = previous.answers.iter().cloned().enumerate().collect();
        g.frames = previous.frames.clone();
        g.iterations = previous.iterations.clone();
        g.instances = previous.instances.clone();
        g.cases = previous.cases.clone();
        g.universal_witnesses = previous.universal_witnesses.clone();
        for (index, node) in previous.nodes.iter().enumerate() {
            g.active = previous.contexts[index];
            env.validate(&g, node).unwrap();
            g.push(node.clone()).unwrap();
        }
        let start = g.nodes.len();
        g.active = crate::observed::call::Context {
            request: 1,
            frame: None,
            iteration: None,
            instance: None,
            case: None,
        };
        let a = build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[1],
            &mut c,
        )
        .unwrap();
        assert!(a.complete);
        assert_eq!(a.witness.construction().root().subject, "A");
        if projection {
            assert_eq!(a.root.0, start);
            assert!(!matches!(
                g.nodes[a.root.0].payload,
                Some(Payload::Construction(_))
            ));
        } else {
            assert_eq!(a.root, previous.answers[0].outputs["value"]);
        }
        assert_eq!(
            g.scalar(a.root).unwrap(),
            &Scalar::Subject {
                snapshot: "v".into(),
                subject: "A".into(),
                entity: "Reservations.System".into()
            }
        );
        replay(&p, &g, &g.nodes).unwrap();
        if projection {
            for mode in 0..4 {
                let mut nodes = g.nodes.clone();
                let n = &mut nodes[a.root.0];
                match mode {
                    0 => {
                        n.payload = Some(Payload::Scalar(Scalar::Subject {
                            snapshot: "v".into(),
                            subject: "B".into(),
                            entity: "Reservations.System".into(),
                        }))
                    }
                    1 => n.arguments.clear(),
                    2 => n.support.clear(),
                    _ => {
                        n.scope.readings.insert("Foreign".into());
                    }
                }
                assert!(replay(&p, &g, &nodes).is_err(), "projection mode {mode}");
            }
        }
    }
}
#[test]
fn equal_configurations_in_different_readings_keep_distinct_architecture_producers() {
    let p = prepared(
        reservations::input("", None),
        &[
            "b=build(Reservations,on=@v/A)",
            "c=build(Alternative,on=@v/A)",
        ],
    );
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    g.active.request = 1;
    let b = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut c,
    )
    .unwrap();
    assert!(a.complete && b.complete);
    assert_ne!(a.reference, b.reference);
    assert_eq!(
        a.witness.construction().root(),
        b.witness.construction().root()
    );
    assert_eq!(
        a.witness.construction().base().configuration(),
        b.witness.construction().base().configuration()
    );
    assert_eq!(a.universe, b.universe);
    assert!(
        g.nodes[a.reference.0]
            .scope
            .readings
            .contains("Reservations")
    );
    assert!(
        g.nodes[b.reference.0]
            .scope
            .readings
            .contains("Alternative")
    );
    let d = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        b.reference,
        &mut c,
    )
    .unwrap()
    .unwrap();
    assert_eq!(d.objects.len(), 3);
    assert!(d.readings.is_empty());
    replay(&p, &g, &g.nodes).unwrap();
    assert!(
        super::validate_build_origin(
            &env,
            &g,
            &p.requests().requests()[0],
            value(&g, b.reference)
        )
        .is_err()
    );
}
#[test]
fn stopped_second_build_keeps_the_previous_request_producer_unchanged() {
    let p = prepared(
        sources(false, BODY),
        &["a=build(R,on=@v/A)", "b=build(R,on=@v/B)"],
    );
    for mode in 0..4 {
        let armed = Rc::new(Cell::new(false));
        let a = armed.clone();
        let reached = Rc::new(Cell::new(0));
        let count = reached.clone();
        let mut c = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |phase| {
                if a.get() && phase == Checkpoint::NativeResultNode {
                    count.set(count.get() + 1)
                }
                if count.get() == 0 {
                    return None;
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
        let env = Environment::with_prepared(&p, &mut c).unwrap();
        let mut g = empty(&p, &c);
        let first = build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[0],
            &mut c,
        )
        .unwrap();
        assert!(first.complete);
        let before = g.nodes.clone();
        g.active.request = 1;
        armed.set(true);
        assert!(matches!(
            build(
                p.shared_inputs(),
                &env,
                &mut g,
                &p.requests().requests()[1],
                &mut c
            ),
            Err(ValidationFailure::Stop(_))
        ));
        assert!(c.stop_reason().is_some());
        assert!(g.nodes.len() >= before.len());
        assert_eq!(g.nodes[..before.len()], before);
        assert_eq!(g.nodes[first.reference.0], before[first.reference.0]);
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn build_generation_rejects_foreign_request_context_and_invalid_root_selectors_before_append() {
    let p = prepared(sources(false, BODY), &["b=build(R,on=@v/A)"]);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = empty(&p, &c);
    for mode in 0..7 {
        let mut request = p.requests().requests()[0].clone();
        match mode {
            0 => request.kind = QuestionKind::Map,
            1 => {
                request.arguments[0].value = Selector::Subject {
                    snapshot: "v".into(),
                    subject: "i".into(),
                }
            }
            2 => {
                request.arguments[0].value = Selector::Subject {
                    snapshot: "v".into(),
                    subject: "absent".into(),
                }
            }
            3 => request.arguments.push(request.arguments[0].clone()),
            4 => request.arguments.clear(),
            5 => {
                request.head = Selector::Declaration {
                    name: "Missing".into(),
                }
            }
            _ => {
                request.arguments[0].value = Selector::Enum {
                    value: "not-a-root".into(),
                }
            }
        }
        assert!(
            selected_build(&env, &g, &request).is_err(),
            "selector mode {mode}"
        );
        g.requests[0] = request.clone();
        assert!(
            build(p.shared_inputs(), &env, &mut g, &request, &mut c).is_err(),
            "foreign request mode {mode}"
        );
        assert!(g.nodes.is_empty());
    }
    g.requests = p.requests().requests().to_vec();
    g.active.frame = Some(0);
    assert!(
        build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[0],
            &mut c
        )
        .is_err()
    );
    assert!(g.nodes.is_empty());
}
fn prior_roots(
    p: &PreparedObserved,
    previous: &crate::observed::ObservedEvaluation,
    env: &Environment<'_>,
    c: &Control,
) -> Graph {
    let mut g = empty(p, c);
    g.checked_answers = previous.answers.iter().cloned().enumerate().collect();
    g.frames = previous.frames.clone();
    g.iterations = previous.iterations.clone();
    g.instances = previous.instances.clone();
    g.cases = previous.cases.clone();
    g.universal_witnesses = previous.universal_witnesses.clone();
    for (index, node) in previous.nodes.iter().enumerate() {
        g.active = previous.contexts[index];
        env.validate(&g, node).unwrap();
        g.push(node.clone()).unwrap();
    }
    g
}
fn replace_partial_reference(node: &mut Node, name: &str, replacement: NodeRef) {
    let Some(Payload::Construction(v)) = &mut node.payload else {
        panic!("native")
    };
    let D::Pending {
        ty: T::Architecture,
        parts,
    } = &mut v.data
    else {
        panic!("partial Architecture")
    };
    let old = parts
        .iter_mut()
        .find(|(path, _)| path == &field(name))
        .unwrap();
    let previous = old.1;
    old.1 = replacement;
    let arg = node.arguments.iter_mut().find(|r| **r == previous).unwrap();
    *arg = replacement;
}
#[test]
fn missing_membership_with_direct_and_projected_root_handles_keeps_partial_architecture() {
    let map = reservations::remove_atom("q-owner");
    let extra = "view box(a:System):(System,Z)=(a,7);";
    for (producer, selector, projection) in [
        (
            "e=evaluate(Reservations.sourceOf,m=@v/m)",
            "$e.value",
            false,
        ),
        ("e=evaluate(Reservations.box,a=@v/A)", "$e.value[0]", true),
    ] {
        let ask = format!("b=build(Reservations,on={selector})");
        let p = prepared(reservations::input(extra, Some(&map)), &[producer, &ask]);
        let previous = crate::observed::evaluate_observed_bytes(
            reservations::input(extra, Some(&map)),
            &[producer],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(previous.status(), "complete");
        let mut c = quiet();
        let env = Environment::with_prepared(&p, &mut c).unwrap();
        let mut g = prior_roots(&p, &previous, &env, &c);
        let before = g.nodes.clone();
        g.active = crate::observed::call::Context {
            request: 1,
            frame: None,
            iteration: None,
            instance: None,
            case: None,
        };
        let a = build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[1],
            &mut c,
        )
        .expect("合法なroot Handleと欠測は部分構成へ保持する");
        assert!(!a.complete);
        assert!(value(&g, a.reference).is_blocked());
        assert_eq!(g.nodes[..before.len()], before);
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.subject == "q"
                        && f.field.as_deref() == Some("Reservations.State.owner")
                        && f.atom.is_none()))
        );
        if projection {
            assert_eq!(a.root.0, before.len());
            assert!(!matches!(
                g.nodes[a.root.0].payload,
                Some(Payload::Construction(_))
            ));
        } else {
            assert_eq!(a.root, previous.answers[0].outputs["value"]);
        }
        let D::Pending {
            ty: T::Architecture,
            parts,
        } = &value(&g, a.reference).data
        else {
            panic!("partial Architecture")
        };
        assert_eq!(
            parts
                .iter()
                .find(|(path, _)| path == &field("root"))
                .unwrap()
                .1,
            a.root
        );
        assert!(g.nodes.iter().all(|n|!matches!(&n.payload,Some(Payload::Construction(v))if matches!(v.data,D::Architecture{..}))));
        replay(&p, &g, &g.nodes).unwrap();
        let before = g.nodes.clone();
        assert!(
            crate::observed::object_component_diagram::retain(
                &mut g,
                p.shared_inputs(),
                a.reference,
                &mut c
            )
            .is_err()
        );
        assert_eq!(g.nodes, before);
        for mode in 0..3 {
            let mut nodes = g.nodes.clone();
            let n = &mut nodes[a.reference.0];
            match mode {
                0 => n.support.clear(),
                1 => {
                    n.scope.readings.insert("Foreign".into());
                }
                _ => n.reasons.clear(),
            }
            assert!(
                replay(&p, &g, &nodes).is_err(),
                "partial metadata mode {mode}"
            );
        }
        let mut foreign = empty(&p, &c);
        foreign.requests = g.requests.clone();
        foreign.requests[1].text.push(' ');
        foreign.contexts = g.contexts.clone();
        foreign.checked_answers = g.checked_answers.clone();
        foreign.frames = g.frames.clone();
        foreign.instances = g.instances.clone();
        foreign.iterations = g.iterations.clone();
        foreign.cases = g.cases.clone();
        foreign.universal_witnesses = g.universal_witnesses.clone();
        assert!(replay(&p, &foreign, &g.nodes).is_err());
    }
}
#[test]
fn partial_root_handle_exception_rejects_aliases_foreign_parts_and_raw_root_substitution() {
    let map = reservations::remove_atom("q-owner");
    let producers = [
        "e=evaluate(Reservations.sourceOf,m=@v/m)",
        "alias=evaluate(Reservations.sourceOf,m=@v/m)",
    ];
    let p = prepared(
        reservations::input("", Some(&map)),
        &[
            producers[0],
            producers[1],
            "b=build(Reservations,on=$e.value)",
            "c=build(Reservations,on=$e.value)",
            "raw=build(Reservations,on=@v/A)",
        ],
    );
    let previous = crate::observed::evaluate_observed_bytes(
        reservations::input("", Some(&map)),
        &producers,
        &mut quiet(),
    )
    .unwrap();
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    let mut g = prior_roots(&p, &previous, &env, &c);
    g.active = crate::observed::call::Context {
        request: 2,
        frame: None,
        iteration: None,
        instance: None,
        case: None,
    };
    let a = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[2],
        &mut c,
    )
    .unwrap();
    g.active.request = 3;
    let other = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[3],
        &mut c,
    )
    .unwrap();
    g.active.request = 4;
    let raw = build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[4],
        &mut c,
    )
    .unwrap();
    assert!(!a.complete && !other.complete && !raw.complete);
    let alias = previous.answers[1].outputs["value"];
    assert_ne!(a.root, alias);
    assert_eq!(g.scalar(a.root).unwrap(), g.scalar(alias).unwrap());
    replay(&p, &g, &g.nodes).unwrap();
    let mut nodes = g.nodes.clone();
    replace_partial_reference(&mut nodes[a.reference.0], "root", alias);
    assert!(
        replay(&p, &g, &nodes).is_err(),
        "同値の別producerは元Handleの代わりにならない"
    );
    let D::Pending { parts, .. } = &value(&g, other.reference).data else {
        panic!("partial")
    };
    let config = parts
        .iter()
        .find(|(path, _)| path == &field("configuration"))
        .unwrap()
        .1;
    let mut nodes = g.nodes.clone();
    replace_partial_reference(&mut nodes[a.reference.0], "configuration", config);
    assert!(
        native::validate_shape(&g, &nodes[a.reference.0]).is_err(),
        "root以外の別Request部分は許さない"
    );
    assert!(replay(&p, &g, &nodes).is_err());
    let mut nodes = g.nodes.clone();
    replace_partial_reference(&mut nodes[raw.reference.0], "root", a.root);
    assert!(
        native::validate_shape(&g, &nodes[raw.reference.0]).is_err(),
        "原始root指定へ外部producerの例外を適用しない"
    );
    assert!(replay(&p, &g, &nodes).is_err());
}
