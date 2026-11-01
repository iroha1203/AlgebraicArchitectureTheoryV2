use super::*;
use crate::{
    input::InputSources,
    observed::{PreparedObserved, request::resolve_native_for_test},
};
use std::sync::Arc;
const DEFINITION: &[u8] =
    include_bytes!("../../../tests/fixtures/configuration-profile.atoms.json");
const LAW: &str = include_str!("../../../tests/fixtures/configuration-profile.law");
const MAP: &str = include_str!("../../../tests/fixtures/configuration-profile.archmap.json");
use crate::control::quiet;
fn prepared(law: &str, map: &str) -> PreparedObserved {
    prepared_with_definition(law, map, DEFINITION)
}
fn prepared_with_definition(law: &str, map: &str, definition: &[u8]) -> PreparedObserved {
    let definitions = crate::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &definitions.vocabularies()["Profile"].digest;
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![definition.to_vec()],
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
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let D::ViewInvariant(d) = &v.data else {
        panic!()
    };
    d
}
fn complete(p: &PreparedObserved) -> (Graph, Diagram) {
    let (mut g, o) = start(p);
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let diagram = retain(&env, &mut g, o.base, &mut quiet()).unwrap();
    (g, diagram)
}
#[test]
fn numeric_view_families_keep_domains_objects_and_missing_values() {
    for ty in ["Z", "Q"] {
        for missing in [false, true] {
            let law = LAW.replace("view amount(p: Part): Z = p.quantity;", &format!(
                "view amount(p:Part,x:{ty},y:{ty}):{ty}=let a=x+y in a+p.quantity;view outside(r:Root,x:{ty}):{ty}=x+1;"));
            let mut map = MAP
                .lines()
                .filter(|line| !missing || !line.contains("p-quantity"))
                .collect::<Vec<_>>()
                .join("\n");
            let definition = std::str::from_utf8(DEFINITION)
                .unwrap()
                .replace("\"type\": \"Z\"", &format!("\"type\": \"{ty}\""));
            if ty == "Q" {
                for z in [2, 7, 11] {
                    map = map.replace(
                        &format!("\"value\":\"{z}\""),
                        &format!("\"value\":[\"{z}\",\"1\"]"),
                    );
                }
            }
            let p = prepared_with_definition(&law, &map, definition.as_bytes());
            let (g, d) = complete(&p);
            assert!(d.pending.is_empty());
            let axis = d
                .axes
                .iter()
                .find(|axis| {
                    data(&g, axis.invariant)
                        .output
                        .declaration
                        .ends_with(".amount")
                })
                .unwrap();
            let output = &data(&g, axis.invariant).output;
            assert_eq!(output.parameters.len(), 2);
            assert_eq!(
                output.reasons.iter().any(|r| !r.missing.is_empty()),
                missing
            );
            for v in &output.values {
                let n = g.get(v.evaluation).unwrap();
                let Some(Payload::Evaluation {
                    value: None, parts, ..
                }) = &n.payload
                else {
                    panic!()
                };
                assert_eq!(parts[0].children.len(), 1);
                let body = g.get(parts[0].children[0]).unwrap();
                let Some(Payload::Evaluation {
                    expression,
                    value: None,
                    ..
                }) = &body.payload
                else {
                    panic!()
                };
                let Some(Payload::Expression { parameters, .. }) =
                    &g.get(*expression).unwrap().payload
                else {
                    panic!()
                };
                assert_eq!(parameters, &output.parameters);
                let mut changed = n.clone();
                changed.reasons.clear();
                if missing {
                    assert!(whole::validate(&g, &changed, v.evaluation.0).is_err());
                }
            }
            let outside = d
                .axes
                .iter()
                .find(|axis| {
                    data(&g, axis.invariant)
                        .output
                        .declaration
                        .ends_with(".outside")
                })
                .unwrap();
            assert!(data(&g, outside.invariant).output.values.iter().any(|v| {
                matches!(&g.get(v.evaluation).unwrap().payload, Some(Payload::Evaluation { applicability: "not_applicable", parts, .. }) if parts[0].children.is_empty())
            }));
            replay(&p, &g);
        }
    }
}
#[test]
fn each_original_instance_covers_all_objects_and_only_function_axes_are_selected() {
    let p = prepared(LAW, MAP);
    let (g, d) = complete(&p);
    assert!(d.pending.is_empty());
    assert_eq!(d.axes.len(), 2);
    let amount = d
        .axes
        .iter()
        .find(|a| {
            data(&g, a.invariant)
                .output
                .declaration
                .ends_with(".amount")
        })
        .unwrap();
    let x = data(&g, amount.invariant);
    assert_eq!(x.source.instance, amount.instance);
    assert_eq!(x.output.returns, Type::Option(Box::new(Type::Z)));
    assert_eq!(x.output.values.len(), 2);
    assert!(x.output.parameters.is_empty());
    assert_eq!(x.output.bindings.len(), 1);
    for v in &x.output.values {
        let Some(Payload::Evaluation {
            expression,
            value: Some(r),
            ..
        }) = &g.get(v.evaluation).unwrap().payload
        else {
            panic!()
        };
        assert_eq!(*expression, v.expression);
        assert_eq!(
            g.scalar(*r).unwrap(),
            &Scalar::Option {
                element: Type::Z,
                value: Some(Box::new(Scalar::Z(2.into())))
            }
        );
        assert_eq!(
            reading::origin(&g, v.expression).unwrap().1.component,
            v.object
        );
    }
    for a in &d.axes {
        let invariant = data(&g, a.invariant);
        let axis = data(&g, a.signature);
        assert!(!invariant.axis && axis.axis);
        assert!(Arc::ptr_eq(&invariant.source, &axis.source));
        assert_eq!(
            g.get(a.signature).unwrap().ty,
            NodeType::Construction(T::SignatureAxis)
        );
        assert_eq!(
            axis.wire(),
            Json::obj([
                ("invariant", a.invariant.wire()),
                ("value_type", invariant.output.returns.wire()),
                ("selected", Json::Bool(true))
            ])
        );
        assert!(g.get(a.signature).unwrap().arguments.contains(&a.invariant));
    }
    replay(&p, &g);
}
#[test]
fn finite_parameters_keep_the_whole_function_per_object_and_never_a_sample_value() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view adjusted(p:Part,a:Bool,b:Bool):Z=amount(p)+(if a then 1 else 0)+(if b then 1 else 0);");
    let p = prepared(&law, MAP);
    let (g, d) = complete(&p);
    assert!(d.pending.is_empty());
    let a = d
        .axes
        .iter()
        .find(|a| {
            data(&g, a.invariant)
                .output
                .declaration
                .ends_with(".adjusted")
        })
        .unwrap();
    let x = data(&g, a.invariant);
    assert_eq!(
        x.output.parameters,
        vec![("a".into(), Type::Bool), ("b".into(), Type::Bool)]
    );
    assert_eq!(x.output.values.len(), 2);
    for v in &x.output.values {
        let n = g.get(v.evaluation).unwrap();
        let Some(Payload::Evaluation {
            value: None, parts, ..
        }) = &n.payload
        else {
            panic!()
        };
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].children.len(), 4);
        let values = parts[0]
            .children
            .iter()
            .map(|r| {
                let Some(Payload::Evaluation { value: Some(r), .. }) = &g.get(*r).unwrap().payload
                else {
                    panic!()
                };
                g.scalar(*r).unwrap().clone()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            values,
            [2, 3, 3, 4]
                .into_iter()
                .map(|z| Scalar::Option {
                    element: Type::Z,
                    value: Some(Box::new(Scalar::Z(z.into())))
                })
                .collect::<Vec<_>>()
        );
        assert_eq!(
            n.scope
                .quantifiers
                .iter()
                .filter(|q| q.domain.is_some())
                .count(),
            2
        );
    }
}
#[test]
fn same_values_keep_distinct_declarations_and_distinct_fixed_reference_instances() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view first(p:Part):Bool=false;view second(p:Part):Bool=false;",
    );
    let map = MAP.replace(
        "\"subject\":\"q\",\"field\":\"Profile.Part.owner\",\"value\":[\"v\",\"B\"]",
        "\"subject\":\"q\",\"field\":\"Profile.Part.owner\",\"value\":[\"v\",\"A\"]",
    );
    let p = prepared(&law, &map);
    let (g, d) = complete(&p);
    let xs = d
        .axes
        .iter()
        .filter(|a| {
            let n = &data(&g, a.invariant).output.declaration;
            n.ends_with(".first") || n.ends_with(".second")
        })
        .collect::<Vec<_>>();
    assert_eq!(xs.len(), 4);
    let first = xs
        .iter()
        .filter(|a| data(&g, a.invariant).output.declaration.ends_with(".first"))
        .collect::<Vec<_>>();
    assert_eq!(first.len(), 2);
    assert_ne!(
        g.scalar(data(&g, first[0].invariant).output.bindings[0].value)
            .unwrap(),
        g.scalar(data(&g, first[1].invariant).output.bindings[0].value)
            .unwrap()
    );
    assert_ne!(xs[0].invariant, xs[1].invariant);
    assert!(xs.iter().any(|a| {
        data(&g, a.invariant)
            .output
            .declaration
            .ends_with(".second")
    }));
    for a in xs {
        let x = data(&g, a.invariant);
        let Scalar::Subject { subject, .. } = g.scalar(x.output.bindings[0].value).unwrap() else {
            panic!()
        };
        assert_eq!(x.output.values.len(), 3);
        for (object, v) in x.output.values.iter().enumerate() {
            let Some(Payload::Evaluation { value: Some(r), .. }) =
                &g.get(v.evaluation).unwrap().payload
            else {
                panic!()
            };
            let applies =
                object == 0 || (subject == "p" && object == 1) || (subject == "q" && object == 2);
            assert_eq!(
                g.scalar(*r).unwrap(),
                &Scalar::Option {
                    element: Type::Bool,
                    value: applies.then(|| Box::new(Scalar::Bool(false)))
                }
            );
        }
    }
    replay(&p, &g);
}
#[test]
fn missing_applicable_values_and_inapplicable_none_remain_distinct_on_axes() {
    let map = MAP
        .lines()
        .filter(|line| !line.contains("p-quantity"))
        .collect::<Vec<_>>()
        .join("\n");
    let p = prepared(LAW, &map);
    let (g, d) = complete(&p);
    let amount = d
        .axes
        .iter()
        .find(|a| {
            data(&g, a.invariant)
                .output
                .declaration
                .ends_with(".amount")
        })
        .unwrap();
    let x = data(&g, amount.invariant);
    assert!(x.output.reasons.iter().any(|r| !r.missing.is_empty()));
    for v in &x.output.values {
        assert!(matches!(
            &g.get(v.evaluation).unwrap().payload,
            Some(Payload::Evaluation { value: None, .. })
        ));
    }
    let root = d
        .axes
        .iter()
        .find(|a| data(&g, a.invariant).output.declaration.ends_with(".root"))
        .unwrap();
    let xs = &data(&g, root.invariant).output.values;
    assert_eq!(xs.len(), 2);
    let n = g.get(xs[1].evaluation).unwrap();
    let Some(Payload::Evaluation {
        value: Some(v),
        applicability,
        ..
    }) = &n.payload
    else {
        panic!()
    };
    assert_eq!(*applicability, "not_applicable");
    assert_eq!(
        g.scalar(*v).unwrap(),
        &Scalar::Option {
            element: Type::Bool,
            value: None
        }
    );
    replay(&p, &g);
}
#[test]
fn unmaterialized_parameters_keep_all_original_expressions_and_full_domain_readings() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view pending(p:Part,n:Text,b:Bool):Z=amount(p);",
    );
    let p = prepared(&law, MAP);
    let (g, d) = complete(&p);
    assert_eq!(d.axes.len(), 1);
    assert_eq!(d.pending.len(), 1);
    let pending = &d.pending[0];
    assert_eq!(pending.expressions.len(), 2);
    assert_eq!(pending.parameters.len(), 2);
    assert_eq!(pending.parameters[0].declaration.name, "n");
    assert_eq!(pending.parameters[0].declaration.ty, Type::Text);
    assert!(pending.parameters[0].values.is_none());
    assert_eq!(
        pending.parameters[1].values,
        Some(vec![Scalar::Bool(false), Scalar::Bool(true)])
    );
    for r in &pending.expressions {
        let o = reading::origin(&g, *r).unwrap().1;
        assert_eq!(o.instance_index, pending.instance);
        assert!(o.declaration.ends_with(".pending"));
    }
    assert!(!g.nodes.iter().any(|n|matches!(&n.payload,Some(Payload::Construction(v))if matches!(&v.data,D::ViewInvariant(x)if x.output.declaration.ends_with(".pending")))));
    replay(&p, &g);
}
#[test]
fn private_axis_and_graph_mutations_cannot_drop_reorder_or_borrow_another_axis() {
    let law = LAW.replace(
        "view root(r: Root): Bool = true;",
        "view first(p:Part):Bool=false;view second(p:Part):Bool=false;",
    );
    let p = prepared(&law, MAP);
    let (g, d) = complete(&p);
    let a = d
        .axes
        .iter()
        .find(|a| {
            data(&g, a.invariant)
                .output
                .declaration
                .ends_with(".second")
        })
        .unwrap();
    let older = d
        .axes
        .iter()
        .find(|a| data(&g, a.invariant).output.declaration.ends_with(".first"))
        .unwrap();
    for target in [a.invariant, a.signature] {
        for mode in 0..13 {
            let mut bad = copy(&g, &quiet());
            let n = &mut bad.nodes[target.0];
            match mode {
                0 => {
                    n.arguments.pop();
                }
                1 => n.arguments.reverse(),
                2 => n.support.clear(),
                3 => n.scope = Scope::default(),
                4 => n.ty = NodeType::Construction(T::CircuitPattern),
                5 => {
                    n.judgment = Some(Judgment {
                        status: Decision::Established,
                        evidence: vec![],
                        reasons: vec![],
                    })
                }
                _ => {
                    let Some(Payload::Construction(v)) = &mut n.payload else {
                        panic!()
                    };
                    let D::ViewInvariant(x) = &mut v.data else {
                        panic!()
                    };
                    let s = Arc::make_mut(&mut x.source);
                    match mode {
                        6 => {
                            x.output.values.pop();
                        }
                        7 => x.output.values.reverse(),
                        8 => x.output.values[1] = x.output.values[0].clone(),
                        9 => {
                            x.output.declaration =
                                data(&g, older.invariant).output.declaration.clone()
                        }
                        10 => s.instance = older.instance,
                        11 => {
                            s.evaluations.reverse();
                            x.output
                                .values
                                .iter_mut()
                                .zip(&s.evaluations)
                                .for_each(|(v, r)| v.evaluation = *r);
                        }
                        12 => x.axis = !x.axis,
                        _ => unreachable!(),
                    }
                    // metadataも含めた整合した偽recordでも元instanceから再導出する。
                    s.output = x.output.clone();
                }
            }
            let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
            assert!(
                fresh
                    .recheck_node(&bad, bad.get(target).unwrap(), target.0)
                    .is_err(),
                "target{target:?}/mode{mode}"
            );
        }
    }
    let foreign = prepared(&law, &MAP.replace("\"value\":\"2\"", "\"value\":\"3\""));
    let env = Environment::with_prepared(&foreign, &mut quiet()).unwrap();
    assert!(
        env.recheck_node(&g, g.get(a.signature).unwrap(), a.signature.0)
            .is_err()
    );
    replay(&p, &g);
}
#[test]
fn later_request_consumes_original_axes_but_cannot_rebind_or_regenerate_them() {
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
    let d = retain(&env, &mut g, o.base, &mut quiet()).unwrap();
    g.active.request = 1;
    assert!(
        crate::observed::architecture_result::build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[1],
            &mut quiet()
        )
        .unwrap()
        .complete
    );
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for a in &d.axes {
        for r in [a.invariant, a.signature] {
            assert!(fresh.recheck_node(&g, g.get(r).unwrap(), r.0).is_ok());
        }
    }
    let before = copy(&g, &quiet());
    assert!(retain(&env, &mut g, o.base, &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.active, before.active);
    for mode in 0..3 {
        let mut bad = copy(&g, &quiet());
        let r = d.axes[0].signature;
        match mode {
            0 => bad.requests[0].id = "foreign".into(),
            1 => bad.contexts[r.0].request = 1,
            2 => bad.contexts[r.0].frame = Some(0),
            _ => unreachable!(),
        }
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh.recheck_node(&bad, bad.get(r).unwrap(), r.0).is_err(),
            "mode{mode}"
        );
    }
}
#[test]
fn four_stops_keep_only_completed_evaluations_invariants_and_axes_as_exact_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(LAW, MAP);
    let (initial, o) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(move |_| {
        seen.set(seen.get() + 1);
        None
    });
    let mut full = copy(&initial, &control);
    let d = retain(&env, &mut full, o.base, &mut control).unwrap();
    assert_eq!(d.axes.len(), 2);
    let total = count.get();
    assert!(total > 20);
    let mut partial = false;
    for signal in [crate::result::Signal::Int, crate::result::Signal::Term] {
        for at in [
            1,
            total / 3,
            total / 2,
            total - 3,
            total - 2,
            total - 1,
            total,
        ] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut control = Control::new(move |_| {
                seen.set(seen.get() + 1);
                (seen.get() >= at).then_some(signal)
            });
            let mut g = copy(&initial, &control);
            assert!(
                matches!(
                    retain(&env, &mut g, o.base, &mut control),
                    Err(ValidationFailure::Stop(_))
                ),
                "{signal:?}/at{at}"
            );
            assert_eq!(g.active, initial.active);
            assert!(env.state.architecture_ref().is_none());
            for (i, n) in g.nodes.iter().enumerate() {
                assert_eq!(
                    n.wire(i, &g.nodes[..i]),
                    full.nodes[i].wire(i, &full.nodes[..i])
                );
            }
            assert_eq!(g.contexts, &full.contexts[..g.contexts.len()]);
            assert_eq!(g.instances, &full.instances[..g.instances.len()]);
            assert_eq!(g.frames, &full.frames[..g.frames.len()]);
            assert_eq!(g.iterations, &full.iterations[..g.iterations.len()]);
            assert_eq!(g.cases, &full.cases[..g.cases.len()]);
            partial |= g.nodes.len() > initial.nodes.len() && g.nodes.len() < full.nodes.len();
            replay(&p, &g);
        }
    }
    assert!(partial);
}

fn external_prepared(extra: &str) -> PreparedObserved {
    let left = include_bytes!("../../../tests/fixtures/object-view-transport.atoms.json");
    let right = include_bytes!("../../../tests/fixtures/configuration-map-right.atoms.json");
    let defs = crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
    let ld = &defs.vocabularies()["Left"].digest;
    let rd = &defs.vocabularies()["Right"].digest;
    let bridge = include_str!("../../../tests/fixtures/configuration-map-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let defs = crate::definition::check_definitions(&[
        ("left", left),
        ("right", right),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let expand = |s: &str| {
        s.replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies()["Bridge"].digest)
            .into_bytes()
    };
    let law = include_str!("../../../tests/fixtures/object-view-transport.law").replacen(
        "  view amount(c:",
        &format!("{extra}\n  view amount(c:"),
        1,
    );
    let inputs = Arc::new(
        crate::input::check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                expand(&law),
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
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
#[test]
fn some_none_is_a_real_function_value_and_empty_parameter_domains_are_complete() {
    let law=LAW.replace("view root(r: Root): Bool = true;","view maybeNumber(p:Part):Option<Z> = none<Z>; view empty(p:Part,x:(External,Bool),b:Bool):Bool=true;");
    let map = MAP
        .lines()
        .filter(|line| !line.contains("\"id\":\"x\"") && !line.contains("x-quantity"))
        .collect::<Vec<_>>()
        .join("\n")
        .replace("\"origin\":\"model\"},\n]", "\"origin\":\"model\"}\n]");
    let p = prepared(&law, &map);
    let (g, d) = complete(&p);
    assert!(d.pending.is_empty());
    let a = d
        .axes
        .iter()
        .find(|a| {
            data(&g, a.invariant)
                .output
                .declaration
                .ends_with(".maybeNumber")
        })
        .unwrap();
    for v in &data(&g, a.invariant).output.values {
        let Some(Payload::Evaluation { value: Some(r), .. }) =
            &g.get(v.evaluation).unwrap().payload
        else {
            panic!()
        };
        assert_eq!(
            g.scalar(*r).unwrap(),
            &Scalar::Option {
                element: Type::Option(Box::new(Type::Z)),
                value: Some(Box::new(Scalar::Option {
                    element: Type::Z,
                    value: None
                }))
            }
        );
    }
    let a = d
        .axes
        .iter()
        .find(|a| data(&g, a.invariant).output.declaration.ends_with(".empty"))
        .unwrap();
    assert_eq!(data(&g, a.invariant).output.parameters.len(), 2);
    for v in &data(&g, a.invariant).output.values {
        let n = g.get(v.evaluation).unwrap();
        let Some(Payload::Evaluation {
            value: None, parts, ..
        }) = &n.payload
        else {
            panic!()
        };
        assert_eq!(parts.len(), 1);
        assert!(parts[0].children.is_empty());
        assert!(n.reasons.is_empty());
    }
    replay(&p, &g);
}
#[test]
fn external_membership_retains_missing_owner_and_never_promotes_true_bodies() {
    let p = external_prepared(
        "view ownershipProbe(c:Left.Child,a:Left.ExternalRoot,x:Option<Left.ExternalChild[a]>,b:Bool):Bool=true;",
    );
    let (g, d) = complete(&p);
    assert!(!d.pending.is_empty());
    let mut pending = 0;
    for x in &d.pending {
        let o = reading::origin(&g, x.expressions[0]).unwrap().1;
        if !o.declaration.ends_with(".ownershipProbe") {
            continue;
        }
        assert_eq!(
            x.parameters[0].declaration.ty,
            Type::Option(Box::new(Type::Owned(
                "Left.ExternalChild".into(),
                "a".into()
            )))
        );
        assert!(x.parameters[0].missing.iter().any(|f|f.subject=="y"&&f.field.as_deref()==Some("Left.ExternalChild.owner")));
        assert_eq!(
            x.parameters[1].values,
            Some(vec![Scalar::Bool(false), Scalar::Bool(true)])
        );
        pending += 1;
    }
    assert!(pending > 0);
    let mut conditional = 0;
    for a in &d.axes {
        let x = data(&g, a.invariant);
        if !x.output.declaration.ends_with(".conditional") {
            continue;
        }
        for v in &x.output.values {
            let o = reading::origin(&g, v.expression).unwrap().1;
            if !matches!(o.application,crate::construction::readings::InstanceApplication::Applicable{ref conditions}if !conditions.is_empty())
            {
                continue;
            }
            let n = g.get(v.evaluation).unwrap();
            let Some(Payload::Evaluation {
                value: None,
                parts,
                applicability,
                ..
            }) = &n.payload
            else {
                panic!()
            };
            assert_eq!(*applicability, "undetermined");
            assert!(parts[0].children.is_empty());
            assert!(n.reasons.iter().flat_map(|r| &r.missing).any(
                |f| f.subject == "y" && f.field.as_deref() == Some("Left.ExternalChild.owner")
            ));
            conditional += 1;
        }
    }
    assert!(conditional > 0);
    replay(&p, &g);
}
