use super::*;
use crate::{
    input::InputSources,
    observed::{PreparedObserved, request::resolve_native_for_test},
};
const DEFINITION: &[u8] =
    include_bytes!("../../../tests/fixtures/configuration-profile.atoms.json");
const LAW: &str = include_str!("../../../tests/fixtures/configuration-profile.law");
const MAP: &str = include_str!("../../../tests/fixtures/configuration-profile.archmap.json");
use crate::control::quiet;
fn prepared(law: &str, map: &str) -> PreparedObserved {
    let definitions = crate::definition::check_definitions(&[("definition0", DEFINITION)]).unwrap();
    let digest = &definitions.vocabularies()["Profile"].digest;
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![DEFINITION.to_vec()],
                law.replace("@PROFILE_DIGEST@", digest).into_bytes(),
                map.replace("@PROFILE_DIGEST@", digest).into_bytes(),
            ),
            &quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(ProfileRead,on=@v/A)"],
        &quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, super::super::object_component_diagram::Diagram) {
    let env = Environment::with_prepared(p, &quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &quiet(),
    )
    .unwrap()
    .unwrap();
    (g, objects)
}
fn copy(g: &Graph, c: &Control) -> Graph {
    let mut p = Graph::new(c);
    p.nodes = g.nodes.clone();
    p.contexts = g.contexts.clone();
    p.frames = g.frames.clone();
    p.instances = g.instances.clone();
    p.iterations = g.iterations.clone();
    p.cases = g.cases.clone();
    p.universal_witnesses = g.universal_witnesses.clone();
    p.requests = g.requests.clone();
    p.checked_answers = g.checked_answers.clone();
    p.active = g.active;
    p
}
fn replay(p: &PreparedObserved, g: &Graph) {
    let env = Environment::with_prepared(p, &quiet()).unwrap();
    let mut prefix = copy(g, &quiet());
    prefix.nodes.clear();
    prefix.contexts.clear();
    for (i, n) in g.nodes.iter().enumerate() {
        prefix.active = g.contexts[i];
        let checked = env.validate(&prefix, n);
        assert!(checked.is_ok(), "node {i}: {checked:?}");
        prefix.push(n.clone()).unwrap();
    }
}
#[test]
fn closed_views_keep_actual_body_types_values_and_original_object_identity() {
    let p = prepared(LAW, MAP);
    let (mut g, objects) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut amounts = vec![];
    let mut roots = vec![];
    let mut outside = 0;
    for r in &objects.readings {
        let (_, o) = origin(&g, r.expression).unwrap();
        let caller = g.active;
        match evaluate(&env, &mut g, r.expression, &quiet()).unwrap() {
            Outcome::Body { instance, side } => {
                assert_eq!(g.instances[instance].source, r.expression);
                assert_eq!(g.context_at(side.evaluation.0).instance, Some(instance));
                let Some(Payload::Evaluation {
                    expression,
                    environment,
                    value,
                    ..
                }) = &g.get(side.evaluation).unwrap().payload
                else {
                    panic!()
                };
                assert_eq!(*expression, side.expression);
                assert_eq!(*environment, Some(o.architecture));
                assert_eq!(*value, side.value);
                assert_eq!(
                    g.get(side.expression).unwrap().ty,
                    NodeType::Expression(if o.declaration.ends_with(".amount") {
                        Type::Z
                    } else {
                        Type::Bool
                    })
                );
                let value = g.scalar(side.value.unwrap()).unwrap().clone();
                if o.declaration.ends_with(".amount") {
                    amounts.push((r.object, value));
                } else {
                    roots.push((r.object, value));
                }
                assert!(
                    g.get(side.evaluation)
                        .unwrap()
                        .scope
                        .readings
                        .contains("ProfileRead")
                );
            }
            Outcome::NotApplicable => {
                assert!(o.declaration.ends_with(".root"));
                assert_eq!(r.object, 1);
                outside += 1;
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(g.active, caller);
    }
    assert_eq!(
        amounts,
        vec![(0, Scalar::Z(2.into())), (1, Scalar::Z(2.into()))]
    );
    assert_eq!(roots, vec![(0, Scalar::Bool(true))]);
    assert_eq!(outside, 1);
    replay(&p, &g);
}
fn selected(
    g: &Graph,
    o: &super::super::object_component_diagram::Diagram,
    object: usize,
    name: &str,
) -> NodeRef {
    o.readings
        .iter()
        .find(|r| {
            r.object == object
                && origin(g, r.expression)
                    .unwrap()
                    .1
                    .declaration
                    .ends_with(name)
        })
        .unwrap()
        .expression
}
#[test]
fn helpers_preserve_compound_results_bindings_and_original_field_support() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view helper(p:Part,n:Z):Z=amount(p)+n; view packed(p:Part):(Option<Part>,Z)=(some(p),helper(p,3));");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    for object in 0..2 {
        let r = selected(&g, &o, object, ".packed");
        let Outcome::Body { side, .. } = evaluate(&env, &mut g, r, &quiet()).unwrap() else {
            panic!()
        };
        assert_eq!(
            g.scalar(side.value.unwrap()).unwrap(),
            &Scalar::Tuple(vec![
                Scalar::Option {
                    element: Type::Ref("Profile.Part".into()),
                    value: Some(Box::new(Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "p".into(),
                        entity: "Profile.Part".into()
                    }))
                },
                Scalar::Z(5.into())
            ])
        );
        assert!(
            g.get(side.evaluation)
                .unwrap()
                .support
                .iter()
                .any(|f| f.subject == "p" && f.field.as_deref() == Some("Profile.Part.quantity"))
        );
        assert!(g.frames.len() >= 2);
    }
    replay(&p, &g);
}
#[test]
fn missing_body_value_keeps_its_actual_evaluation_and_missing_reason() {
    let map = MAP
        .lines()
        .filter(|l| !l.contains("\"id\":\"p-quantity\""))
        .collect::<Vec<_>>()
        .join("\n");
    let p = prepared(LAW, &map);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    for object in 0..2 {
        let r = selected(&g, &o, object, ".amount");
        let Outcome::Body { side, .. } = evaluate(&env, &mut g, r, &quiet()).unwrap() else {
            panic!()
        };
        assert!(side.value.is_none());
        assert!(!side.reasons.is_empty());
        assert!(
            side.reasons
                .iter()
                .flat_map(|r| &r.missing)
                .any(|f| f.subject == "p" && f.field.as_deref() == Some("Profile.Part.quantity"))
        );
        assert_eq!(
            g.get(side.evaluation).unwrap().ty,
            NodeType::Evaluation(Type::Z)
        );
        assert_eq!(g.get(side.evaluation).unwrap().reasons, side.reasons);
    }
    replay(&p, &g);
}
#[test]
fn unbound_parameters_keep_the_whole_expression_without_sampling_or_new_nodes() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view shift(p:Part,n:Z,b:Bool):Z=amount(p)+n;",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    for object in 0..2 {
        let r = selected(&g, &o, object, ".shift");
        let before = copy(&g, &quiet());
        let Outcome::Parameters(parameters) = evaluate(&env, &mut g, r, &quiet()).unwrap() else {
            panic!()
        };
        assert_eq!(
            parameters,
            vec![("n".into(), Type::Z), ("b".into(), Type::Bool)]
        );
        assert_eq!(g.nodes, before.nodes);
        assert_eq!(g.contexts, before.contexts);
        assert_eq!(g.instances, before.instances);
        assert_eq!(g.active, before.active);
        assert_eq!(
            g.get(r)
                .unwrap()
                .scope
                .quantifiers
                .iter()
                .map(|q| q.name.as_str())
                .collect::<Vec<_>>(),
            vec!["n", "b"]
        );
    }
    replay(&p, &g);
}
#[test]
fn a_later_request_consumes_old_frames_and_body_results_but_cannot_create_them() {
    let mut p = prepared(LAW, MAP);
    p.requests = resolve_native_for_test(
        p.inputs.law(),
        p.inputs.archmap(),
        &[
            "b=build(ProfileRead,on=@v/A)",
            "later=build(ProfileRead,on=@v/B)",
        ],
        &quiet(),
    )
    .unwrap();
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let expression = selected(&g, &o, 1, ".amount");
    let old = g.nodes.len();
    let Outcome::Body { side, .. } = evaluate(&env, &mut g, expression, &quiet()).unwrap() else {
        panic!()
    };
    let end = g.nodes.len();
    g.active.request = 1;
    let later = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &quiet(),
    )
    .unwrap();
    assert!(later.complete);
    let before = copy(&g, &quiet());
    for at in old..end {
        let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
        let checked = fresh.recheck_node(&g, g.get(NodeRef(at)).unwrap(), at);
        assert!(checked.is_ok(), "node {at}: {checked:?}");
    }
    assert_eq!(g.scalar(side.value.unwrap()).unwrap(), &Scalar::Z(2.into()));
    assert!(evaluate(&env, &mut g, expression, &quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    for mode in 0..2 {
        let mut bad = copy(&g, &quiet());
        if mode == 0 {
            bad.requests[0].id = "forged".into()
        } else {
            bad.contexts[side.evaluation.0].request = 1
        };
        let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(side.evaluation).unwrap(), side.evaluation.0)
                .is_err()
        );
    }
}
#[test]
fn frame_payload_edges_metadata_and_actual_instance_cannot_be_rebound() {
    let p = prepared(LAW, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let expression = selected(&g, &o, 0, ".amount");
    let base = g.nodes.len();
    let Outcome::Body { instance, side } = evaluate(&env, &mut g, expression, &quiet()).unwrap()
    else {
        panic!()
    };
    let r = NodeRef(base);
    let node = g.get(r).unwrap();
    for mode in 0..12 {
        let mut n = node.clone();
        let Some(Payload::Construction(v)) = &mut n.payload else {
            panic!()
        };
        let D::ObjectReadingFrame(d) = &mut v.data else {
            panic!()
        };
        match mode {
            0 => Arc::make_mut(&mut d.source).base += 1,
            1 => Arc::make_mut(&mut d.source).origin.body += 1,
            2 => Arc::make_mut(&mut d.source).origin.declaration = "ProfileRead.root".into(),
            3 => Arc::make_mut(&mut d.source).origin.expression = o.base,
            4 => Arc::make_mut(&mut d.source).origin.architecture = o.architectures[1],
            5 => Arc::make_mut(&mut d.source).origin.bindings[0].value = o.base,
            6 => Arc::make_mut(&mut d.source).support.clear(),
            7 => Arc::make_mut(&mut d.source).scope = Scope::default(),
            8 => {
                Arc::make_mut(&mut d.source).origin.application = InstanceApplication::NotApplicable
            }
            9 => {
                let s = Arc::make_mut(&mut d.source);
                s.architecture = Arc::new((*s.architecture).clone());
            }
            10 => {
                d.kind = Kind::Parameter {
                    position: usize::MAX,
                    value: Scalar::Bool(true),
                }
            }
            _ => {
                d.kind = Kind::Parameter {
                    position: 0,
                    value: Scalar::Subject {
                        snapshot: "v".into(),
                        subject: "q".into(),
                        entity: "Profile.Part".into(),
                    },
                }
            }
        }
        assert!(env.recheck_node(&g, &n, base).is_err(), "payload {mode}");
    }
    for mode in 0..6 {
        let mut n = node.clone();
        match mode {
            0 => n.arguments.clear(),
            1 => n.arguments.push(r),
            2 => n.support.clear(),
            3 => n.scope = Scope::default(),
            4 => n.ty = NodeType::Value(Type::Bool),
            _ => n.rule = Rule::Construction("domain"),
        };
        assert!(env.recheck_node(&g, &n, base).is_err(), "node {mode}");
    }
    assert!(env.recheck_node(&g, node, base + 1).is_err());
    for mode in 0..5 {
        let mut bad = copy(&g, &quiet());
        let record = &mut bad.instances[instance];
        match mode {
            0 => record.source = selected(&g, &o, 0, ".root"),
            1 => record.domain = r,
            2 => record.member = r,
            3 => record.caller.frame = Some(usize::MAX),
            _ => record.caller.request = 1,
        };
        let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(side.evaluation).unwrap(), side.evaluation.0)
                .is_err(),
            "instance {mode}"
        );
    }
    let p2 = prepared(LAW, &MAP.replace("\"value\":\"2\"", "\"value\":\"8\""));
    let foreign = Environment::with_prepared(&p2, &quiet()).unwrap();
    assert!(
        foreign
            .recheck_node(&g, g.get(side.evaluation).unwrap(), side.evaluation.0)
            .is_err()
    );
    let before = copy(&g, &quiet());
    for bad in [o.base, NodeRef(usize::MAX)] {
        assert!(evaluate(&env, &mut g, bad, &quiet()).is_err());
        assert_eq!(g.nodes, before.nodes);
        assert_eq!(g.instances, before.instances);
    }
    replay(&p, &g);
}
#[test]
fn four_stops_keep_finished_frames_instances_and_body_prefix_and_restore_context() {
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };
    let p = prepared(LAW, MAP);
    let (initial, o) = start(&p);
    let expression = selected(&initial, &o, 0, ".amount");
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let native_points = Rc::new(RefCell::new(Vec::new()));
    let points = native_points.clone();
    let control = Control::new(move |point| {
        seen.set(seen.get() + 1);
        if point == Checkpoint::NativeResultNode {
            points.borrow_mut().push(seen.get());
        }
        None
    });
    let mut full = copy(&initial, &control);
    assert!(matches!(
        evaluate(&env, &mut full, expression, &control).unwrap(),
        Outcome::Body { .. }
    ));
    let total = count.get();
    assert!(total > 10);
    assert!(native_points.borrow().len() >= 2);
    let frame_point = native_points.borrow()[1];
    let mut frame_prefix = false;
    let mut body_prefix = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, frame_point, total / 2, total - 2, total - 1, total] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let control = Control::new(move |_| {
                seen.set(seen.get() + 1);
                (seen.get() >= at).then_some(signal)
            });
            let mut g = copy(&initial, &control);
            let result = evaluate(&env, &mut g, expression, &control);
            assert!(
                matches!(result, Err(ValidationFailure::Stop(_))),
                "{signal:?}, at {at}: {result:?}"
            );
            assert_eq!(g.active, initial.active);
            assert!(g.nodes.len() <= full.nodes.len());
            for (i, n) in g.nodes.iter().enumerate() {
                assert_eq!(
                    n.wire(i, &g.nodes[..i]),
                    full.nodes[i].wire(i, &full.nodes[..i])
                );
            }
            assert!(env.state.architecture_ref().is_none());
            assert_eq!(g.contexts, &full.contexts[..g.contexts.len()]);
            assert_eq!(g.instances, &full.instances[..g.instances.len()]);
            frame_prefix |= g.nodes.len() > initial.nodes.len() && g.instances.is_empty();
            body_prefix |= !g.instances.is_empty();
            replay(&p, &g);
        }
    }
    assert!(frame_prefix && body_prefix);
}
#[test]
fn unresolved_external_membership_does_not_execute_the_constant_body() {
    let left = include_bytes!("../../../tests/fixtures/object-view-transport.atoms.json");
    let right = include_bytes!("../../../tests/fixtures/configuration-map-right.atoms.json");
    let defs = crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
    let ld = &defs.vocabularies()["Left"].digest;
    let rd = &defs.vocabularies()["Right"].digest;
    let bridge = include_str!("../../../tests/fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let definitions = crate::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace(
                "@BRIDGE_DIGEST@",
                &definitions.vocabularies()["Bridge"].digest,
            )
            .into_bytes()
    };
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.clone().into_bytes()],
                expand(include_str!(
                    "../../../tests/fixtures/object-view-transport.law"
                )),
                expand(include_str!(
                    "../../../tests/fixtures/object-view-transport.archmap.json"
                )),
            ),
            &quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Before,on=@v/a)"],
        &quiet(),
    )
    .unwrap();
    let p = PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut count = 0;
    for reading in &o.readings {
        let (_, source) = origin(&g, reading.expression).unwrap();
        if source.declaration == "Before.conditional"
            && matches!(&source.application,InstanceApplication::Applicable{conditions} if !conditions.is_empty())
        {
            let before = copy(&g, &quiet());
            let Outcome::Conditional(conditions) =
                evaluate(&env, &mut g, reading.expression, &quiet()).unwrap()
            else {
                panic!()
            };
            let InstanceApplication::Applicable {
                conditions: expected,
            } = source.application
            else {
                panic!()
            };
            assert_eq!(conditions, expected);
            assert!(!conditions.is_empty());
            assert_eq!(g.nodes, before.nodes);
            assert_eq!(g.contexts, before.contexts);
            assert_eq!(g.instances, before.instances);
            count += 1;
        }
    }
    assert!(count > 0);
    replay(&p, &g);
}
#[test]
fn unknown_ownership_retains_the_pending_architecture_and_never_fakes_a_view_source() {
    let map = MAP
        .lines()
        .filter(|l| !l.contains("\"id\":\"p-owner\""))
        .collect::<Vec<_>>()
        .join("\n");
    let p = prepared(LAW, &map);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert!(!a.complete);
    let before = copy(&g, &quiet());
    assert!(
        crate::observed::object_component_diagram::retain(
            &mut g,
            p.shared_inputs(),
            a.reference,
            &quiet()
        )
        .is_err()
    );
    assert!(evaluate(&env, &mut g, a.reference, &quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    assert!(
        g.get(a.reference)
            .unwrap()
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Profile.Part.owner"))
    );
    replay(&p, &g);
}
#[test]
fn paths_inside_compound_return_values_keep_the_actual_typed_nodes() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view route(p:Part):Path<Part,Part> = identity(p); view nested(p:Part):Option<List<Path<Part,Part>>> = some(list<Path<Part,Part>>[route(p)]);");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    for object in 0..2 {
        let expression = selected(&g, &o, object, ".nested");
        let Outcome::Body { side, .. } = evaluate(&env, &mut g, expression, &quiet()).unwrap()
        else {
            panic!()
        };
        let Scalar::Option {
            value: Some(value), ..
        } = g.scalar(side.value.unwrap()).unwrap()
        else {
            panic!()
        };
        let Scalar::List { items, .. } = &**value else {
            panic!()
        };
        assert_eq!(items.len(), 1);
        let Scalar::Path(path) = &items[0] else {
            panic!()
        };
        assert_eq!(
            (
                &*path.reading,
                &*path.snapshot,
                &*path.subject,
                &*path.entity
            ),
            ("ProfileRead", "v", "p", "Profile.Part")
        );
        assert!(path.step.is_none());
        assert_ne!(
            g.get(expression).unwrap().ty,
            g.get(side.expression).unwrap().ty
        );
        let at = side.value.unwrap().0;
        let wire = g.get(NodeRef(at)).unwrap().wire(at, &g.nodes[..at]);
        assert!(wire.canonical().contains("\"node\""));
    }
    replay(&p, &g);
}
