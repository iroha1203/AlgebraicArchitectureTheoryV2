use super::*;
use crate::observed::{
    PreparedObserved,
    control::{Limits, Usage},
    request::resolve_native_for_test,
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/polynomial_law_family_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(missing: bool, tuple: bool, body: &str, root: &str) -> PreparedObserved {
    let inputs = fixture::inputs(missing, tuple, body);
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &[ask.as_str()],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn built(p: &PreparedObserved) -> (Graph, NodeRef) {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c).unwrap();
    let mut g = Graph::new(&c);
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    assert!(a.complete, "{:?}", a.reasons);
    (g, a.reference)
}
fn replay(
    p: &PreparedObserved,
    original: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c)?;
    let mut g = Graph::new(&c);
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
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::PolynomialLaw(d) = &v.data else {
        panic!("finite")
    };
    d
}
fn terms(g: &Graph, r: NodeRef) -> Vec<(Json, Vec<usize>)> {
    let Part::Polynomial { terms, parameters, .. } = data(g, r).part() else {
        panic!("polynomial")
    };
    assert!(parameters.is_empty());
    let Json::Obj(ref wire) = data(g, r).wire() else { panic!() };
    assert!(!wire.contains_key("parameters"));
    terms
        .iter()
        .map(|(coefficient, powers)| (g.scalar(*coefficient).unwrap().wire(), powers.clone()))
        .collect()
}
const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
#[test]
fn parameter_polynomials_are_typed_families_and_reject_changed_domains() {
    let p = prepared(false, false, "law required zero(c:Part,n:Z):n=0;", "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let nu = ds[0].coordinates[0].nu.unwrap();
    let d = data(&g, nu);
    assert!(d.polynomial().is_none());
    let (ring, family) = d.parameter_difference(&mut quiet()).unwrap().unwrap();
    assert_eq!(Some(ring), ds[0].coordinates[0].ring);
    assert_eq!(family.parameters.len(), 1);
    let original = d.source.clone();
    for change in 0..4 {
        let mut source = original.as_ref().clone();
        let Part::Polynomial { parameters, terms, .. } = &mut source.parts[d.index] else { panic!() };
        match change {
            0 => parameters.clear(),
            1 => parameters[0].1 = Type::Q,
            2 => parameters[0].0 = "other".into(),
            3 => terms[0].1.push(1),
            _ => unreachable!(),
        }
        assert!(source.recheck(&p.inputs, &original.architecture, &mut quiet()).is_err());
    }
    original.recheck(&p.inputs, &original.architecture, &mut quiet()).unwrap();
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn shared_polynomial_family_maps_distinct_local_symbols_into_the_same_z_ring() {
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let before = g.nodes.len();
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    let source = &data(&g, ds[0].rings[0]).source;
    assert_eq!(source.owned_outputs.as_ref().unwrap().len(), 2);
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Ring { .. }))
            .count(),
        1
    );
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Base(_)))
            .count(),
        1
    );
    assert_eq!(
        source
            .parts
            .iter()
            .filter(|p| matches!(p, Part::Evaluation { .. }))
            .count(),
        1
    );
    let Part::Ring { variables, .. } = data(&g, ds[0].rings[0]).part() else {
        panic!("ring")
    };
    assert_eq!(
        variables
            .iter()
            .map(|v| (v.field.subject.as_str(), v.component.clone()))
            .collect::<Vec<_>>(),
        [("p", vec![]), ("q", vec![])]
    );
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.bases, ds[0].bases);
        assert_eq!(d.domains, ds[0].domains);
        assert_eq!(d.evaluations, ds[0].evaluations);
        assert_eq!(d.status, EquationPresentationStatus::Ready);
        assert!(d.presentations.iter().all(Option::is_some));
        assert_eq!(d.coordinates.len(), 4);
        let Part::Ideal {
            ring,
            generators,
            required,
            parameters,
        } = data(&g, d.required[0]).part()
        else {
            panic!("required")
        };
        assert!(*required);
        assert!(parameters.is_empty());
        assert_eq!(*ring, d.rings[0]);
        assert_eq!(
            *generators,
            d.coordinates
                .iter()
                .filter(|q| q.required && q.guard == EquationGuard::AlwaysTrue)
                .map(|q| q.nu.unwrap())
                .collect::<Vec<_>>()
        );
        for q in &d.coordinates {
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            let binding = g.scalar(original.bindings[0].value).unwrap();
            let Scalar::Subject { subject, .. } = binding else {
                panic!("binding")
            };
            if q.guard == EquationGuard::OutsideObject {
                assert!(object > 0 && subject != if object == 1 { "p" } else { "q" });
                assert_eq!(q.status, EquationPresentationStatus::NotApplicable);
                assert!(
                    q.left.is_some() && q.right.is_some() && q.nu.is_some() && q.epsilon.is_none()
                );
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                continue;
            }
            assert!(object == 0 || subject == if object == 1 { "p" } else { "q" });
            let powers = if subject == "p" {
                vec![1, 0]
            } else {
                vec![0, 1]
            };
            assert_eq!(
                terms(&g, q.left.unwrap()),
                [(Json::str("1"), powers.clone())]
            );
            let Part::LawInstance { name, .. } = data(&g, original.reference).part() else {
                panic!("instance")
            };
            let is_one = name.ends_with("one");
            let mut expected = if is_one {
                vec![(Json::str("-1"), vec![0, 0])]
            } else {
                vec![]
            };
            expected.push((Json::str("1"), powers));
            assert_eq!(terms(&g, q.nu.unwrap()), expected);
            let value = i32::from(subject == "q") - i32::from(is_one);
            assert_eq!(
                terms(&g, q.epsilon.unwrap()),
                if value == 0 {
                    vec![]
                } else {
                    vec![(Json::str(value.to_string()), vec![0, 0])]
                }
            );
            assert_eq!(q.ring, Some(ds[0].rings[0]));
        }
    }
    for (at, n) in g.nodes.iter().enumerate().skip(before) {
        assert!(n.arguments.iter().all(|r| r.0 < at));
        let Some(Payload::Construction(v)) = &n.payload else {
            panic!("construction")
        };
        let D::PolynomialLaw(d) = &v.data else {
            panic!("polynomial")
        };
        assert!(Arc::ptr_eq(source, &d.source));
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn shared_polynomial_tuple_components_keep_z_and_q_separate_across_all_objects() {
    let p = prepared(
        false,
        true,
        "law required pair(c:Part):c.quantity=(0,0);",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    assert_eq!(ds[0].rings.len(), 2);
    assert_ne!(ds[0].rings[0], ds[0].rings[1]);
    for d in &ds {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.evaluations, ds[0].evaluations);
        for q in &d.coordinates {
            let index = usize::from(q.ty == Type::Q);
            assert_eq!(q.component, [index]);
            assert_eq!(q.ring, Some(ds[0].rings[index]));
            let Part::Ring { variables, .. } = data(&g, ds[0].rings[index]).part() else {
                panic!("ring")
            };
            assert_eq!(variables.len(), 2);
            assert!(
                variables
                    .iter()
                    .all(|v| v.ty == q.ty && v.component == [index])
            );
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(original.bindings[0].value).unwrap()
            else {
                panic!("binding")
            };
            if q.guard == EquationGuard::OutsideObject {
                assert!(q.nu.is_some() && q.epsilon.is_none());
                assert!(terms(&g, q.residual.unwrap()).is_empty());
                continue;
            }
            let expected = if index == 0 {
                Json::str("1")
            } else {
                Json::Arr(vec![Json::str("1"), Json::str("1")])
            };
            assert_eq!(
                terms(&g, q.nu.unwrap()),
                [(
                    expected,
                    if subject == "p" {
                        vec![1, 0]
                    } else {
                        vec![0, 1]
                    }
                )]
            );
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn missing_shared_slot_omits_global_evaluation_but_keeps_known_original_epsilon() {
    let p = prepared(true, false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    for d in &ds {
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.evaluations, [None]);
        let Part::Equation(crate::observed::equation_presentation_node::Part::Context {
            dependencies,
            ..
        }) = data(&g, d.context.unwrap()).part()
        else {
            panic!("context")
        };
        let mut quantity_subjects = dependencies
            .iter()
            .filter(|(_, f)| f == "Family.Part.quantity")
            .map(|(r, _)| match g.scalar(*r).unwrap() {
                Scalar::Subject { subject, .. } => subject.as_str(),
                _ => panic!("subject"),
            })
            .collect::<Vec<_>>();
        quantity_subjects.sort();
        assert_eq!(quantity_subjects, ["p", "q"]);
        assert!(d.presentations.iter().all(Option::is_some));
        for r in d.presentations.iter().flatten() {
            let Part::Equation(crate::observed::equation_presentation_node::Part::Presentation {
                coordinates,
                evaluation,
                omissions,
                ..
            }) = data(&g, *r).part()
            else {
                panic!("presentation")
            };
            assert!(evaluation.is_none());
            assert!(
                omissions
                    .iter()
                    .flat_map(|r| &r.missing)
                    .any(|f| f.subject == "q"
                        && f.field.as_deref() == Some("Family.Part.quantity")
                        && f.atom.is_none())
            );
            for q in coordinates {
                let o = d
                    .originals
                    .iter()
                    .find(|o| o.reference == q.instance)
                    .unwrap();
                let Scalar::Subject { subject, .. } = g.scalar(o.bindings[0].value).unwrap() else {
                    panic!("binding")
                };
                let applicable = d.coordinates.iter().any(|coordinate| coordinate.instance == q.instance && coordinate.guard == EquationGuard::AlwaysTrue);
                assert_eq!(q.epsilon.is_some(), subject == "p" && applicable);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn shared_polynomial_source_rejects_object_output_and_symbol_mapping_tampering() {
    let p = prepared(false, false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let original = data(&g, ds[0].rings[0]).source.clone();
    for kind in 0..10 {
        let mut changed = (*original).clone();
        match kind {
            0 => {
                changed.owned_outputs.as_mut().unwrap().pop();
            }
            1 => changed.owned_outputs.as_mut().unwrap().swap(0, 1),
            2 => {
                let d = changed.owned_outputs.as_ref().unwrap()[0].clone();
                changed.owned_outputs.as_mut().unwrap().push(d);
            }
            3 => changed.owned_outputs.as_mut().unwrap()[0].rings[0] = changed.outputs.bases[0],
            4 => changed.owned_outputs.as_mut().unwrap()[0].domains[0] = changed.outputs.rings[0],
            5 => changed.outputs.coordinates.swap(0, 1),
            6 => {
                let Part::Ring { variables, .. } =
                    &mut changed.parts[ds[0].rings[0].0 - changed.base]
                else {
                    panic!("ring")
                };
                variables.swap(0, 1);
            }
            7 => changed.object = 1,
            8 => changed.base += 1,
            _ => changed.owned_outputs.as_mut().unwrap()[1].evaluations[0] = None,
        }
        assert!(
            changed
                .recheck(p.inputs(), &original.architecture, &mut quiet())
                .is_err(),
            "source {kind}"
        );
        let mut nodes = g.nodes.clone();
        let Some(Payload::Construction(v)) = &mut nodes[ds[0].rings[0].0].payload else {
            panic!("native")
        };
        let D::PolynomialLaw(d) = &mut v.data else {
            panic!("polynomial")
        };
        d.source = Arc::new(changed);
        assert!(replay(&p, &g, &nodes).is_err(), "graph {kind}");
    }
    let missing = prepared(true, false, BODY, "root");
    assert!(
        original
            .recheck(missing.inputs(), &original.architecture, &mut quiet())
            .is_err()
    );
    let before = g.nodes.len();
    assert!(retain_family(&mut g, p.shared_inputs(), NodeRef(usize::MAX), &mut quiet()).is_err());
    assert_eq!(before, g.nodes.len());
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn empty_shared_polynomial_family_preserves_base_and_owned_objects_without_rings() {
    for (root, count) in [("root", 3), ("r2", 1)] {
        let p = prepared(false, false, "", root);
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
        assert_eq!(ds.len(), count);
        for d in &ds {
            assert!(
                d.rings.is_empty()
                    && d.domains.is_empty()
                    && d.coordinates.is_empty()
                    && d.originals.is_empty()
            );
            assert!(d.presentations.is_empty() && d.unavailable.is_none());
            let source = &data(&g, d.context.unwrap()).source;
            assert_eq!(source.architecture.construction().root().subject, root);
            assert_eq!(source.owned_outputs.as_ref().unwrap().len(), count - 1);
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn finite_parameter_rows_and_symbolic_numeric_families_are_preserved() {
    let p = prepared(
        false,
        false,
        "law required choose(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    for d in &ds {
        assert_eq!(d.coordinates.len(), 4);
        assert_eq!(d.rings, ds[0].rings);
        let mut rows = vec![];
        for original in d.originals.iter().filter(|o| o.row.is_some()) {
            let parameter = original.bindings.iter().find(|b| b.name == "b").unwrap();
            let entity = original.bindings.iter().find(|b| b.name == "c").unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(entity.value).unwrap() else {
                panic!("subject")
            };
            let Scalar::Bool(value) = g.scalar(parameter.value).unwrap() else {
                panic!("parameter")
            };
            rows.push((subject.as_str(), *value));
        }
        rows.sort();
        let expected = vec![("p", false), ("p", true), ("q", false), ("q", true)];
        assert_eq!(rows, expected);
        for q in d
            .coordinates
            .iter()
            .filter(|q| q.guard == EquationGuard::OutsideObject)
        {
            // 有限rowは残るが、適用外では条件式を評価して原式を補わない。
            assert!(q.row.is_some() && q.nu.is_none() && q.epsilon.is_none());
            assert!(terms(&g, q.residual.unwrap()).is_empty());
            let original = d
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .unwrap();
            assert!(original.parameters.is_empty());
            assert!(original.bindings.iter().any(|b| b.name == "b" && b.ty == Type::Bool));
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
    let p = prepared(
        false,
        false,
        "law required symbolic(c:Part,k:Z):c.quantity=k;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    assert_eq!(ds.len(), 3);
    for d in &ds {
        assert!(d.unavailable.is_none());
        assert_eq!(d.status, EquationPresentationStatus::Ready);
        assert_eq!(d.rings, ds[0].rings);
        assert_eq!(d.coordinates.len(), 2);
        assert!(d.evaluations.iter().all(Option::is_some));
        for q in &d.coordinates {
            assert!(data(&g, q.nu.unwrap()).parameter_family(&[("k".into(), Type::Z)]));
            if q.guard == EquationGuard::OutsideObject {
                assert!(q.epsilon.is_none());
                assert!(terms(&g, q.residual.unwrap()).is_empty());
            } else {
                assert!(data(&g, q.epsilon.unwrap()).parameter_difference(&mut quiet()).unwrap().is_some());
            }
        }
        assert!(
            d.originals
                .iter()
                .all(|o| o.parameters.iter().any(|(n, t)| n == "k" && t == &Type::Z))
        );
    }
    replay(&p, &g, &g.nodes).unwrap();
}

fn prefix(original: &Graph, c: &Control) -> Graph {
    let mut g = Graph::new(c);
    g.nodes = original.nodes.clone();
    g.contexts = original.contexts.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    g.active = original.active;
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g
}
#[test]
fn shared_polynomial_four_stops_keep_exact_finished_basis_and_object_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, false, BODY, "root");
    let (initial, a) = built(&p);
    let before = initial.nodes.len();
    let mut complete = prefix(&initial, &quiet());
    let ds = retain_family(&mut complete, p.shared_inputs(), a, &mut quiet()).unwrap();
    for mode in 0..4 {
        for at in [
            1,
            2 * (ds[0].rings[0].0 - before + 1),
            2 * (ds[0].context.unwrap().0 - before + 1),
            2 * (ds[1].context.unwrap().0 - before + 1),
            2 * (ds[2].context.unwrap().0 - before + 1),
        ] {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::NativeResultNode {
                        count.set(count.get() + 1);
                    }
                    let stop = count.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && mode == 0),
                        memory_mib: u128::from(stop && mode == 1),
                        signal: if stop && mode >= 2 {
                            Some(if mode == 2 {
                                crate::result::Signal::Int
                            } else {
                                crate::result::Signal::Term
                            })
                        } else {
                            None
                        },
                    }
                },
            );
            let mut g = prefix(&initial, &c);
            assert!(matches!(
                retain_family(&mut g, p.shared_inputs(), a, &mut c),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.nodes.len(), before + at.div_ceil(2));
            assert_eq!(g.nodes.len(), g.contexts.len());
            for (left, right) in g.nodes.iter().zip(&complete.nodes) {
                assert_eq!(
                    (
                        &left.ty,
                        &left.rule,
                        &left.arguments,
                        &left.support,
                        &left.scope,
                        &left.reasons,
                        &left.judgment
                    ),
                    (
                        &right.ty,
                        &right.rule,
                        &right.arguments,
                        &right.support,
                        &right.scope,
                        &right.reasons,
                        &right.judgment
                    )
                );
                match (&left.payload, &right.payload) {
                    (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                        assert_eq!(a.wire(), b.wire())
                    }
                    _ => assert_eq!(left, right),
                }
            }
            replay(&p, &g, &g.nodes).unwrap();
        }
    }
}

#[test]
fn shared_polynomial_family_rejects_foreign_root_request_input_and_cached_witness_without_appending()
 {
    let mut p = prepared(false, false, BODY, "root");
    p.requests = resolve_native_for_test(
        p.inputs().law(),
        p.inputs().archmap(),
        &["b=build(Selected,on=@v/root)", "c=build(Selected,on=@v/r2)"],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, a) = built(&p);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    g.active.request = 1;
    let before = g.nodes.len();
    assert!(retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let other = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut c,
    )
    .unwrap();
    assert!(other.complete);
    let second = retain_family(&mut g, p.shared_inputs(), other.reference, &mut quiet()).unwrap();
    assert_eq!(second.len(), 1);
    assert_eq!(
        data(&g, second[0].context.unwrap())
            .source
            .architecture
            .construction()
            .root()
            .subject,
        "r2"
    );
    g.active.request = 0;
    let first = retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).unwrap();
    let Some(Payload::Construction(value)) = &g.nodes[first[0].context.unwrap().0].payload else {
        panic!("native")
    };
    env.recheck_polynomial_law_diagram(&g, value).unwrap();
    let mut foreign = (**value).clone();
    foreign.witness = Witness::Architecture(
        data(&g, second[0].context.unwrap())
            .source
            .architecture
            .clone(),
    );
    assert!(env.recheck_polynomial_law_diagram(&g, &foreign).is_err());
    let missing = prepared(true, false, BODY, "root");
    let before = g.nodes.len();
    assert!(retain_family(&mut g, missing.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let before = g.nodes.len();
    assert!(
        retain_family(
            &mut g,
            p.shared_inputs(),
            objects.architectures[1],
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes.len(), before);
    replay(&p, &g, &g.nodes).unwrap();
}
