use super::*;
use crate::{
    input::InputSources,
    observed::{PreparedObserved, request::resolve_native_for_test},
};
use std::sync::Arc;
const DEFINITION: &[u8] = include_bytes!("../../../tests/fixtures/configuration-profile.atoms.json");
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
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(ProfileRead,on=@v/A)"],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, super::super::object_component_diagram::Diagram) {
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut quiet(),
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
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
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
                && body::origin(g, r.expression)
                    .unwrap()
                    .1
                    .declaration
                    .ends_with(name)
        })
        .unwrap()
        .expression
}
fn run(env: &Environment<'_>, g: &mut Graph, r: NodeRef) -> (NodeRef, Option<NodeRef>) {
    let Outcome::Evaluation { evaluation, value } = evaluate(env, g, r, &mut quiet()).unwrap()
    else {
        panic!()
    };
    (evaluation, value)
}
#[test]
fn whole_view_returns_some_actual_values_and_none_only_outside_the_domain() {
    let p = prepared(LAW, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for r in &o.readings {
        let (_, origin) = body::origin(&g, r.expression).unwrap();
        let before = g.instances.len();
        let (e, v) = run(&env, &mut g, r.expression);
        let expected = if origin.declaration.ends_with(".amount") {
            Scalar::Option {
                element: Type::Z,
                value: Some(Box::new(Scalar::Z(2.into()))),
            }
        } else {
            Scalar::Option {
                element: Type::Bool,
                value: (r.object == 0).then(|| Box::new(Scalar::Bool(true))),
            }
        };
        assert_eq!(g.scalar(v.unwrap()).unwrap(), &expected);
        assert_eq!(
            g.get(e).unwrap().ty,
            NodeType::Evaluation(origin.returns.clone())
        );
        let Some(Payload::Evaluation {
            expression,
            environment,
            bindings,
            parts,
            applicability,
            ..
        }) = &g.get(e).unwrap().payload
        else {
            panic!()
        };
        assert_eq!(*expression, r.expression);
        assert_eq!(*environment, Some(origin.architecture));
        assert_eq!(*bindings, origin.bindings);
        assert_eq!(parts.len(), 1);
        env.object_reading_recheck_evaluation_for_test(&g, e)
            .unwrap();
        if r.object == 1 && origin.declaration.ends_with(".root") {
            assert_eq!(*applicability, "not_applicable");
            assert!(parts[0].children.is_empty());
            assert!(parts[0].value.is_none());
            assert_eq!(g.instances.len(), before);
        } else {
            assert_eq!(*applicability, "applicable");
            assert_eq!(parts[0].children.len(), 1);
            assert_eq!(g.instances.len(), before + 1);
            let child = g.get(parts[0].children[0]).unwrap();
            let Type::Option(t) = &origin.returns else {
                panic!()
            };
            assert_eq!(child.ty, NodeType::Evaluation((**t).clone()));
        }
        count += 1;
    }
    assert_eq!(count, 4);
    replay(&p, &g);
}
#[test]
fn some_false_and_some_none_remain_distinct_from_the_outer_none() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view root(r: Root): Bool = false; view maybeNumber(p:Part):Option<Z> = none<Z>;",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = selected(&g, &o, 0, ".root");
    let (_, v) = run(&env, &mut g, r);
    assert_eq!(
        g.scalar(v.unwrap()).unwrap(),
        &Scalar::Option {
            element: Type::Bool,
            value: Some(Box::new(Scalar::Bool(false)))
        }
    );
    let r = selected(&g, &o, 1, ".root");
    let (_, v) = run(&env, &mut g, r);
    assert_eq!(
        g.scalar(v.unwrap()).unwrap(),
        &Scalar::Option {
            element: Type::Bool,
            value: None
        }
    );
    for object in 0..2 {
        let r = selected(&g, &o, object, ".maybeNumber");
        let (e, v) = run(&env, &mut g, r);
        assert_eq!(
            g.scalar(v.unwrap()).unwrap(),
            &Scalar::Option {
                element: Type::Option(Box::new(Type::Z)),
                value: Some(Box::new(Scalar::Option {
                    element: Type::Z,
                    value: None
                }))
            }
        );
        assert!(g.get(e).unwrap().reasons.is_empty());
    }
    replay(&p, &g);
}
#[test]
fn missing_body_is_blocked_and_unbound_parameters_are_never_sampled() {
    let map = MAP
        .lines()
        .filter(|l| !l.contains("\"id\":\"p-quantity\""))
        .collect::<Vec<_>>()
        .join("\n");
    let p = prepared(LAW, &map);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for object in 0..2 {
        let r = selected(&g, &o, object, ".amount");
        let before = g.nodes.len();
        let (e, v) = run(&env, &mut g, r);
        assert!(v.is_none());
        let n = g.get(e).unwrap();
        assert_eq!(n.ty, NodeType::Evaluation(Type::Option(Box::new(Type::Z))));
        let Some(Payload::Evaluation {
            parts,
            applicability,
            value,
            ..
        }) = &n.payload
        else {
            panic!()
        };
        assert_eq!(*applicability, "applicable");
        assert!(value.is_none());
        env.object_reading_recheck_evaluation_for_test(&g, e)
            .unwrap();
        assert!(
            env.object_reading_projection_for_test(
                &g,
                e,
                &[crate::observed::projection::ProjectionStep::Field(
                    "value".into()
                )],
                (0, 0)
            )
            .is_err()
        );
        assert!(parts[0].value.is_none());
        assert_eq!(parts[0].children.len(), 1);
        assert_eq!(
            g.get(parts[0].children[0]).unwrap().ty,
            NodeType::Evaluation(Type::Z)
        );
        assert!(
            n.reasons
                .iter()
                .flat_map(|r| &r.missing)
                .any(|f| f.subject == "p" && f.field.as_deref() == Some("Profile.Part.quantity"))
        );
        assert!(!g.nodes[before..].iter().any(|n| matches!(
            &n.payload,
            Some(Payload::Scalar(Scalar::Option {
                element: Type::Z,
                value: None
            }))
        )));
    }
    replay(&p, &g);
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view shift(p:Part,n:Z,b:Bool):Z=amount(p)+n;",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for object in 0..2 {
        let r = selected(&g, &o, object, ".shift");
        let before = copy(&g, &quiet());
        let Outcome::Parameters(ps) = evaluate(&env, &mut g, r, &mut quiet()).unwrap() else {
            panic!()
        };
        assert_eq!(ps, vec![("n".into(), Type::Z), ("b".into(), Type::Bool)]);
        assert_eq!(g.nodes, before.nodes);
        assert_eq!(g.instances, before.instances);
        assert_eq!(g.contexts, before.contexts);
        assert_eq!(g.active, before.active);
        assert_eq!(g.get(r).unwrap().scope.quantifiers.len(), 2);
    }
    replay(&p, &g);
}

#[test]
fn conditional_membership_keeps_the_original_slots_without_executing_true_body() {
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
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Before,on=@v/a)"],
        &mut quiet(),
    )
    .unwrap();
    let p = PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for r in &o.readings {
        let (_, origin) = body::origin(&g, r.expression).unwrap();
        if origin.declaration == "Before.conditional"
            && matches!(&origin.application,InstanceApplication::Applicable{conditions} if !conditions.is_empty())
        {
            let before = copy(&g, &quiet());
            let (e, v) = run(&env, &mut g, r.expression);
            assert!(v.is_none());
            assert_eq!(g.nodes.len(), before.nodes.len() + 1);
            assert_eq!(g.instances, before.instances);
            assert_eq!(g.active, before.active);
            let n = g.get(e).unwrap();
            let Some(Payload::Evaluation {
                parts,
                applicability,
                value,
                ..
            }) = &n.payload
            else {
                panic!()
            };
            assert_eq!(*applicability, "undetermined");
            assert!(value.is_none());
            assert!(parts[0].children.is_empty());
            assert!(parts[0].value.is_none());
            let InstanceApplication::Applicable { conditions } = origin.application else {
                panic!()
            };
            for condition in conditions {
                assert!(
                    n.reasons
                        .iter()
                        .any(|reason| reason.dependencies == vec![r.expression]
                            && reason.missing.contains(condition.slot()))
                );
            }
            count += 1;
        }
    }
    assert!(count > 0);
    replay(&p, &g);
}
#[test]
fn nested_path_options_preserve_actual_nodes_and_existing_value_environment_projection() {
    use crate::canonical::Json;
    use crate::observed::{environment::AnswerBinding, projection::ProjectionStep as P};
    let law=LAW.replace("view root(r: Root): Bool = true;","view route(p:Part):Path<Part,Part> = identity(p); view nested(p:Part):Option<List<Path<Part,Part>>> = some(list<Path<Part,Part>>[route(p)]);");
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for object in 0..2 {
        let expression = selected(&g, &o, object, ".nested");
        let (_, origin) = body::origin(&g, expression).unwrap();
        let (e, v) = run(&env, &mut g, expression);
        let v = v.unwrap();
        let Scalar::Option {
            element,
            value: Some(inner),
        } = g.scalar(v).unwrap()
        else {
            panic!()
        };
        assert_eq!(
            element,
            &Type::Option(Box::new(Type::List(Box::new(Type::Path(
                "Profile.Part".into(),
                "Profile.Part".into()
            )))))
        );
        let Scalar::Option {
            value: Some(inner), ..
        } = &**inner
        else {
            panic!()
        };
        let Scalar::List { items, .. } = &**inner else {
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
        let Some(Payload::Evaluation { parts, .. }) = &g.get(e).unwrap().payload else {
            panic!()
        };
        let body_value = parts[0].value.unwrap();
        let Json::Obj(ref wire) = g.get(v).unwrap().wire(v.0, &g.nodes[..v.0]) else {
            panic!()
        };
        assert_eq!(wire["value"], Json::obj([("some", body_value.wire())]));
        assert!(
            matches!(env.object_reading_projection_for_test(&g,e,&[P::Field("value".into())],(0,0)).unwrap(),AnswerBinding::Reference(r) if r==v)
        );
        assert!(
            matches!(env.object_reading_projection_for_test(&g,e,&[P::Field("environment".into())],(0,0)).unwrap(),AnswerBinding::Reference(r) if r==origin.architecture)
        );
        let result = env
            .object_reading_projection_for_test(
                &g,
                e,
                &[
                    P::Field("value".into()),
                    P::Field("some".into()),
                    P::Field("some".into()),
                    P::Index(0),
                ],
                (0, 0),
            )
            .unwrap();
        let AnswerBinding::Reference(r) = result else {
            panic!("Pathの既出Refがない")
        };
        assert!(matches!(g.scalar(r).unwrap(), Scalar::Path(_)));
        assert!(r.0 < v.0);
    }
    replay(&p, &g);
}

#[test]
fn four_stops_keep_completed_body_option_and_whole_evaluation_prefix() {
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };
    let p = prepared(LAW, MAP);
    let (initial, o) = start(&p);
    let expression = selected(&initial, &o, 0, ".amount");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let native_points = Rc::new(RefCell::new(Vec::new()));
    let points = native_points.clone();
    let mut control = Control::new(move |point| {
        seen.set(seen.get() + 1);
        if point == Checkpoint::NativeResultNode {
            points.borrow_mut().push(seen.get());
        }
        None
    });
    let mut full = copy(&initial, &control);
    assert!(matches!(
        evaluate(&env, &mut full, expression, &mut control).unwrap(),
        Outcome::Evaluation { .. }
    ));
    let total = count.get();
    assert!(total > 10);
    assert!(native_points.borrow().len() >= 2);
    let frame_point = native_points.borrow()[1];
    let mut frame_prefix = false;
    let mut body_prefix = false;
    let mut option_prefix = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [1, frame_point, total / 2, total - 2, total - 1, total] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut control = Control::new(move |_| {
                seen.set(seen.get() + 1);
                (seen.get() >= at).then_some(signal)
            });
            let mut g = copy(&initial, &control);
            let result = evaluate(&env, &mut g, expression, &mut control);
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
            option_prefix |= g.nodes.iter().any(|n|matches!(&n.payload,Some(Payload::Scalar(Scalar::Option{element:Type::Z,value:Some(_)})))) && !g.nodes.iter().any(|n|matches!(&n.payload,Some(Payload::Evaluation{expression:e,..}) if *e==expression));
            replay(&p, &g);
        }
    }
    assert!(frame_prefix && body_prefix && option_prefix);
}
#[test]
fn later_request_rechecks_old_whole_results_and_rejects_new_generation_and_context_forgery() {
    let mut p = prepared(LAW, MAP);
    p.requests = resolve_native_for_test(
        p.inputs.law(),
        p.inputs.archmap(),
        &[
            "b=build(ProfileRead,on=@v/A)",
            "later=build(ProfileRead,on=@v/B)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let expression = selected(&g, &o, 1, ".amount");
    let start = g.nodes.len();
    let (e, v) = run(&env, &mut g, expression);
    let end = g.nodes.len();
    g.active.request = 1;
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut quiet(),
    )
    .unwrap();
    assert!(a.complete);
    for at in start..end {
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let checked = fresh.recheck_node(&g, g.get(NodeRef(at)).unwrap(), at);
        assert!(checked.is_ok(), "{at}: {checked:?}");
    }
    assert_eq!(
        g.scalar(v.unwrap()).unwrap(),
        &Scalar::Option {
            element: Type::Z,
            value: Some(Box::new(Scalar::Z(2.into())))
        }
    );
    let before = copy(&g, &quiet());
    assert!(evaluate(&env, &mut g, expression, &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    for mode in 0..3 {
        let mut bad = copy(&g, &quiet());
        if mode == 0 {
            bad.requests[0].id = "forged".into();
        } else if mode == 1 {
            bad.contexts[e.0].request = 1;
        } else {
            bad.contexts[v.unwrap().0].request = 1;
        }
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh.recheck_node(&bad, bad.get(e).unwrap(), e.0).is_err(),
            "mode {mode}"
        );
    }
}
#[test]
fn whole_evaluation_value_body_and_original_view_cannot_be_rebound() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view root(r: Root): Bool = true; view twin(p:Part):Z=amount(p);",
    );
    let p = prepared(&law, MAP);
    let (mut g, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r0 = selected(&g, &o, 0, ".amount");
    let r1 = selected(&g, &o, 1, ".amount");
    let r2 = selected(&g, &o, 0, ".twin");
    let (e1, v1) = run(&env, &mut g, r1);
    let (e2, v2) = run(&env, &mut g, r2);
    let (e0, v0) = run(&env, &mut g, r0);
    let v2 = v2.unwrap();
    let Some(Payload::Evaluation { parts, .. }) = &g.get(e2).unwrap().payload else {
        panic!()
    };
    let b2 = parts[0].children[0];
    let body_value2 = parts[0].value.unwrap();
    assert!(v1.unwrap().0 < e0.0 && v2.0 < e0.0 && b2.0 < e0.0);
    let v0 = v0.unwrap();
    let v1 = v1.unwrap();
    let Some(Payload::Evaluation { parts, .. }) = &g.get(e0).unwrap().payload else {
        panic!()
    };
    let b0 = parts[0].children[0];
    let Some(Payload::Evaluation { parts, .. }) = &g.get(e1).unwrap().payload else {
        panic!()
    };
    let b1 = parts[0].children[0];
    for mode in 0..21 {
        let mut bad = copy(&g, &quiet());
        let n = &mut bad.nodes[e0.0];
        match mode {
            0 => n.ty = NodeType::Evaluation(Type::Bool),
            1 => n.rule = Rule::Construction("expression"),
            2 => {
                n.arguments.pop();
            }
            3 => n.support.clear(),
            4 => n.scope.assignments = !n.scope.assignments,
            5 => n.scope.readings.clear(),
            6 => n.evidence.push(v0),
            7 => {
                n.judgment = Some(Judgment {
                    status: Decision::Refuted,
                    evidence: vec![],
                    reasons: vec![],
                })
            }
            other => {
                let Some(Payload::Evaluation {
                    expression,
                    environment,
                    bindings,
                    parts,
                    value,
                    applicability,
                }) = &mut n.payload
                else {
                    panic!()
                };
                match other {
                    8 => *expression = r1,
                    9 => *value = Some(v1),
                    10 => *environment = Some(body::origin(&g, r1).unwrap().1.architecture),
                    11 => bindings.clear(),
                    12 => parts[0].location = Location::Law { span: (0, 0) },
                    13 => parts[0].children = vec![b1],
                    14 => parts[0].value = None,
                    15 => parts[0].residual = Some(v0),
                    16 => *applicability = "not_applicable",
                    17 => parts.push(parts[0].clone()),
                    18 => *expression = r2,
                    19 => *value = Some(v2),
                    20 => parts[0].children = vec![b2],
                    _ => unreachable!(),
                }
            }
        }
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(e0).unwrap(), e0.0)
                .is_err(),
            "evaluation mode {mode}"
        );
    }
    for mode in 0..9 {
        let mut bad = copy(&g, &quiet());
        let n = &mut bad.nodes[v0.0];
        match mode {
            0 => {
                n.payload = Some(Payload::Scalar(Scalar::Option {
                    element: Type::Z,
                    value: Some(Box::new(Scalar::Z(3.into()))),
                }))
            }
            1 => n.arguments.push(v0),
            2 => n.support.clear(),
            3 => n.scope.assignments = !n.scope.assignments,
            4 => n.ty = NodeType::Value(Type::Bool),
            5 => n.arguments[0] = r1,
            6 => n.rule = Rule::Construction("expression"),
            7 => {
                let position = n.arguments.iter().position(|r| *r == b0).unwrap();
                n.arguments[position] = b2;
            }
            8 => {
                let body_value = match &g.get(b0).unwrap().payload {
                    Some(Payload::Evaluation { value: Some(r), .. }) => *r,
                    _ => panic!(),
                };
                let position = n.arguments.iter().position(|r| *r == body_value).unwrap();
                n.arguments[position] = body_value2;
            }
            _ => unreachable!(),
        };
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(v0).unwrap(), v0.0)
                .is_err(),
            "value mode {mode}"
        );
    }
    for mode in 0..3 {
        let mut bad = copy(&g, &quiet());
        match mode {
            0 => bad.contexts[b0.0].instance = None,
            1 => {
                let Some(Payload::Evaluation { value, .. }) = &mut bad.nodes[b0.0].payload else {
                    panic!()
                };
                *value = Some(v1);
            }
            2 => bad.requests[0].id = "foreign".into(),
            _ => unreachable!(),
        };
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh
                .recheck_node(&bad, bad.get(e0).unwrap(), e0.0)
                .is_err(),
            "body mode {mode}"
        );
    }
    let foreign = prepared(&LAW.replace("p.quantity", "p.quantity + 1"), MAP);
    let foreign_env = Environment::with_prepared(&foreign, &mut quiet()).unwrap();
    assert!(
        foreign_env
            .recheck_node(&g, g.get(e0).unwrap(), e0.0)
            .is_err()
    );
    let before = copy(&g, &quiet());
    assert!(evaluate(&foreign_env, &mut g, r0, &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    replay(&p, &g);
}
