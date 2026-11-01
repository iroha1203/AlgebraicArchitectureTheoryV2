use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
use crate::control::quiet;
fn prepared(missing: bool) -> PreparedObserved {
    let inputs = fixture::inputs(
        missing,
        false,
        "view amount(c:Part):Z=c.quantity;law required zero(c:Part):c.quantity=0;",
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn graph(p: &PreparedObserved) -> Graph {
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    g
}

#[test]
fn universal_numeric_build_laws_preserve_parameter_functions() {
    use crate::{canonical::Json, types::Type};
    for (ty, tuple, body, truth) in [
        ("Q", false, "n=n", true),
        ("Q", false, "n=0", false),
        ("Z", true, "n=n+1", false),
        ("Z", true, "n=0", false),
    ] {
        let parameter_type = if tuple {
            format!("({ty},{ty})")
        } else {
            ty.to_owned()
        };
        let expression = if tuple {
            body.replace("n", "(n.0+n.1)")
        } else {
            body.to_owned()
        };
        let p = single_part(&format!(
            "law required reflexive(c:Part,n:{parameter_type}):{expression};"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let table = plan.laws.as_ref().unwrap();
        let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
            .unwrap()
            .unwrap();
        assert_eq!(circuits.len(), 1);
        assert_eq!(
            circuits[0].parameters.len(),
            if body == "n=0" { 1 } else { 0 }
        );
        assert!(!circuits[0].cases.is_empty());
        for case in &circuits[0].cases {
            assert_eq!(case.when, if body == "n=0" { None } else { Some(!truth) });
        }
        assert!(!table.objects.is_empty());
        for row in &table.objects {
            assert_eq!(
                g.get(row.holds[0])
                    .unwrap()
                    .judgment
                    .as_ref()
                    .unwrap()
                    .status,
                if truth {
                    Decision::Established
                } else {
                    Decision::Refuted
                }
            );
        }
        assert_eq!(plan.predicates.len(), 1);
        let predicate = &plan.predicates[0];
        for reference in &predicate.evaluations {
            let node = g.get(*reference).unwrap();
            env.recheck_node(&g, node, reference.0).unwrap();
            let Some(Payload::Construction(value)) = &node.payload else {
                panic!()
            };
            let Json::Obj(ref wire) = value.wire() else {
                panic!()
            };
            // The function n=0 is not the constant false function, although its
            // universal closure is false. Retain the expression, not that Bool.
            assert!(!wire.contains_key("value"));
            assert!(wire.contains_key("expression"));
        }
        let node = g.get(predicate.invariant).unwrap();
        env.recheck_node(&g, node, predicate.invariant.0).unwrap();
        let Some(Payload::Construction(value)) = &node.payload else {
            panic!()
        };
        let Json::Obj(ref wire) = value.wire() else {
            panic!()
        };
        assert_eq!(
            wire["parameters"],
            Json::Arr(vec![Json::obj([
                ("name", Json::str("n")),
                (
                    "type",
                    if tuple {
                        Type::Tuple(vec![if ty == "Z" { Type::Z } else { Type::Q }; 2])
                    } else if ty == "Z" {
                        Type::Z
                    } else {
                        Type::Q
                    }
                    .wire()
                ),
            ])])
        );
    }
}

fn single_part(body: &str) -> PreparedObserved {
    use crate::input::{InputSources, check_inputs};
    let initial = fixture::inputs(false, false, body);
    let sources = initial.sources();
    let map = String::from_utf8(sources.archmap().bytes().to_vec()).unwrap()
        .replace(r#",{"id":"q","type":"Family.Part","origin":"model"}"#, "")
        .replace(r#",{"id":"oq","subject":"q","field":"Family.Part.owner","value":["v","root"],"origin":"model"}"#, "")
        .replace(r#",{"id":"xq","subject":"q","field":"Family.Part.quantity","value":"1","origin":"model"}"#, "");
    let inputs = Arc::new(
        check_inputs(
            InputSources::from_bytes(
                sources
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                sources.law().bytes().to_vec(),
                map.into_bytes(),
            ),
            &quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}

#[test]
fn identical_patterns_compare_all_readings_and_reject_different_applicability() {
    for (body, expected) in [
        (
            "view amount(c:Part):Z=c.quantity;law required zero(c:Part):c.quantity=0;",
            true,
        ),
        (
            "view amount(c:Root):Z=0;law required zero(c:Part):c.quantity=0;",
            false,
        ),
        (
            "view amount(c:Part,b:Bool):Z=if b then c.quantity else 1;law required zero(c:Part):c.quantity=0;",
            true,
        ),
        ("", true),
    ] {
        let p = single_part(body);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let comparisons =
            crate::observed::build_compare::compare(&env, &g, &plan, &quiet()).unwrap();
        assert_eq!(comparisons.len(), 1, "{body}");
        assert_eq!(comparisons[0].equal, Some(expected), "{body}");
    }
}

#[test]
fn closed_circuits_use_the_actual_component_residual_and_keep_reject_cases() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
        .unwrap()
        .unwrap();
    assert_eq!(circuits.len(), 2);
    assert_eq!(circuits[0].cases.len(), 2);
    assert_eq!(circuits[1].cases.len(), 2);
    assert!(circuits[0].cases.iter().all(|c| c.when == Some(false)));
    assert!(circuits[1].cases.iter().all(|c| c.when == Some(true)));
    assert_eq!(
        circuits[0].cases[0].object,
        plan.objects.as_ref().unwrap().base
    );
    assert_eq!(
        circuits[1].cases[1].object,
        plan.objects.as_ref().unwrap().objects[2]
    );
    for detector in &circuits {
        for case in &detector.cases {
            assert_eq!(case.index, detector.index);
            assert_eq!(case.component, detector.component);
            assert!(case.epsilon.0 < plan.boundary.start());
            assert!(case.evaluation.0 < plan.boundary.start());
        }
    }
    let p = prepared(true);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert!(
        crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
            .unwrap()
            .is_none()
    );
}

#[test]
fn native_build_answer_contains_rechecked_algebra_and_component_circuits() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert_eq!(answer.status, Decision::Established);
    assert_eq!(answer.outputs.len(), 3);
    assert!(answer.outputs.contains_key("object"));
    assert!(answer.outputs.contains_key("algebra"));
    env.validate_answer(&g, &p.requests().requests()[0], &answer)
        .unwrap();
}

#[test]
fn finite_parameter_circuits_keep_every_bound_law_row() {
    use crate::input::{InputSources, check_inputs};
    let initial = fixture::inputs(
        false,
        false,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    );
    let sources = initial.sources();
    let definition = String::from_utf8(sources.definitions()[0].bytes().to_vec())
        .unwrap()
        .replace(r#""type":"Z""#, r#""type":["Fp","2"]"#);
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let old = &initial.definitions().vocabularies()["Family"].digest;
    let new = &defs.vocabularies()["Family"].digest;
    let law = String::from_utf8(sources.law().bytes().to_vec())
        .unwrap()
        .replace(old, new);
    let map = String::from_utf8(sources.archmap().bytes().to_vec())
        .unwrap()
        .replace(old, new);
    let inputs = Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definition.into_bytes()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &quiet(),
    )
    .unwrap();
    let p = PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert_eq!(answer.status, Decision::Established);
    let detectors = g
        .nodes
        .iter()
        .filter(|n| n.ty == NodeType::Construction(T::CircuitDetector))
        .count();
    assert_eq!(detectors, 4);
    env.validate_answer(&g, &p.requests().requests()[0], &answer)
        .unwrap();
}

#[test]
fn refuted_extension_keeps_the_object_and_names_the_actual_condition() {
    let p = single_part("view amount(c:Root):Z=0;law required zero(c:Part):c.quantity=0;");
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert_eq!(answer.status, Decision::Refuted);
    assert!(!answer.evidence.is_empty());
    for proof in &answer.evidence {
        g.expect(*proof, &NodeType::Evidence).unwrap();
    }
    assert!(answer.outputs.contains_key("object"));
    assert!(!answer.outputs.contains_key("algebra"));
    assert!(answer.reasons.iter().any(|r| matches!(
        r.kind,
        ReasonKind::ConditionFailed {
            construction: "object_algebra",
            ..
        }
    )));
    env.validate_answer(&g, &p.requests().requests()[0], &answer)
        .unwrap();
}

#[test]
fn interrupt_keeps_a_completed_object_without_publishing_unfinished_algebra() {
    for at in [1, 6] {
        let mut armed = false;
        let mut seen = 0;
        let control = Control::new(move |point| {
            armed |= point == Checkpoint::ObjectLawCircuits;
            if armed && point == Checkpoint::NativeResultNode {
                seen += 1;
            }
            let stop = seen >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let p = prepared(false);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = Graph::new(&control);
        g.requests = p.requests().requests().to_vec();
        let answer = crate::observed::build_result::evaluate(
            &p,
            &env,
            &mut g,
            &p.requests().requests()[0],
            &control,
        )
        .unwrap();
        assert!(control.stop_reason().is_some());
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.contains_key("object"));
        assert!(!answer.outputs.contains_key("algebra"));
        assert!(answer.claim.is_none());
        assert!(matches!(answer.reasons[0].kind, ReasonKind::Stop(_)));
        assert_eq!(g.nodes.len(), g.contexts.len());
    }
}

#[test]
fn one_build_uses_the_same_native_objects_laws_patterns_equations_and_invariants() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert!(plan.architecture.complete);
    let objects = plan.objects.as_ref().unwrap();
    assert_eq!(objects.objects.len(), 3);
    assert_eq!(objects.architectures[0], plan.architecture.reference);
    let laws = plan.laws.as_ref().unwrap();
    assert_eq!(laws.indices.len(), 2);
    assert_eq!(laws.component_source(), objects.base);
    assert_eq!(
        laws.objects.iter().map(|o| o.object).collect::<Vec<_>>(),
        objects.objects
    );
    let patterns = plan.patterns.as_ref().unwrap();
    assert_eq!(patterns.universe, plan.architecture.universe);
    assert_eq!(
        patterns.rows.iter().map(|r| r.object).collect::<Vec<_>>(),
        objects.objects
    );
    assert!(plan.arrows.as_ref().unwrap().rows.is_empty());
    assert!(
        plan.polynomial.as_ref().unwrap().data.complete,
        "polynomial layout: {:?}; finite: {:?}; equations: {:?}",
        plan.polynomial.as_ref().unwrap().data,
        plan.finite.as_ref().map(|l| l.data.complete),
        plan.equations
    );
    assert!(plan.equations.is_some());
    let views = plan.views.as_ref().unwrap();
    assert!(views.pending.is_empty());
    assert_eq!(views.axes.len(), 2);
    assert_eq!(plan.predicates.len(), 2);
    for i in &plan.predicates {
        assert_eq!(i.evaluations.len(), 3);
    }
    assert_eq!(plan.boundary.start(), g.nodes.len());
    assert!(plan.boundary.inputs().contains(&objects.base));
    assert!(
        crate::observed::build_compare::compare(&env, &g, &plan, &quiet())
            .unwrap()
            .is_empty()
    ); // この入力の全3対象は完全patternがそれぞれ異なる。
    plan.boundary
        .recheck(&env, &g, g.nodes.len(), &quiet())
        .unwrap();
    assert!(env.state.architecture_ref().is_none());
}

#[test]
fn source_validation_rejects_context_reference_order_and_original_node_changes_together() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let original_contexts = g.contexts.clone();
    let original_active = g.active;
    for mode in 0..8 {
        let boundary = plan.boundary.clone();
        let reference = plan.objects.as_ref().unwrap().readings[0].expression;
        let original = g.nodes[reference.0].clone();
        match mode {
            0 => {
                g.contexts.pop();
            }
            1 => g.contexts.clear(),
            2 => g.contexts.push(g.active),
            3 => g.active.request += 1,
            4 | 5 => (),
            6 => g.nodes[reference.0].rule = Rule::Construction("binding"),
            7 => g.contexts[plan.architecture.reference.0].request += 1,
            _ => unreachable!(),
        }
        let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
        let result = if matches!(mode, 4 | 5) {
            let mut inputs = boundary.inputs().to_vec();
            inputs.push(NodeRef(g.nodes.len() + usize::from(mode == 5)));
            Boundary::capture(&fresh, &g, plan.architecture.reference, inputs, &quiet()).map(|_| ())
        } else {
            boundary.recheck(&fresh, &g, g.nodes.len(), &quiet())
        };
        assert!(
            matches!(result, Err(ValidationFailure::Internal(_))),
            "mode{mode}: {result:?}"
        );
        g.contexts = original_contexts.clone();
        g.active = original_active;
        g.nodes[reference.0] = original;
    }
    plan.boundary
        .recheck(&env, &g, g.nodes.len(), &quiet())
        .unwrap();
}

#[test]
fn outside_polynomial_keeps_the_original_symbolic_difference_without_an_evaluated_epsilon() {
    use crate::observed::observable_layout::{Placed, Reading, Source};
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let layout = plan.polynomial.as_ref().unwrap();
    let checked = layout.checked(&env, &g, &quiet()).unwrap();
    assert!(checked.is_complete());
    // 部分対象pで、qのquantity=0は対象外。元の差はx_qであり零でない。
    let Source::Polynomial(q) = &layout.data.objects[1].coordinates[1].source else {
        panic!()
    };
    assert_eq!(
        q.guard,
        crate::observed::object_equation_presentation::EquationGuard::OutsideObject
    );
    assert!(q.left.is_some() && q.right.is_some() && q.nu.is_some());
    assert!(q.epsilon.is_none());
    let Some(Payload::Construction(v)) = &g.get(q.nu.unwrap()).unwrap().payload else {
        panic!()
    };
    let crate::canonical::Json::Obj(ref w) = v.wire() else {
        panic!()
    };
    let crate::canonical::Json::Arr(terms) = &w["terms"] else {
        panic!()
    };
    assert_eq!(terms.len(), 1);
    let crate::canonical::Json::Obj(term) = &terms[0] else {
        panic!()
    };
    let crate::canonical::Json::Arr(powers) = &term["powers"] else {
        panic!()
    };
    assert!(powers.iter().any(|p| *p == crate::canonical::Json::Nat(1)));
    assert!(matches!(
        checked
            .at(1, 1, Reading::Epsilon, 0, &layout.data.anchor, &quiet())
            .unwrap(),
        Placed::Uncomputed { .. }
    ));
    let Placed::Value { reference, .. } = checked
        .at(1, 1, Reading::Residual, 0, &layout.data.anchor, &quiet())
        .unwrap()
    else {
        panic!()
    };
    let Some(Payload::Construction(v)) = &g.get(reference).unwrap().payload else {
        panic!()
    };
    let crate::canonical::Json::Obj(ref w) = v.wire() else {
        panic!()
    };
    assert_eq!(w["terms"], crate::canonical::Json::Arr(vec![]));
    let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut prefix = Graph::new(&quiet());
    prefix.requests = g.requests.clone();
    prefix.frames = g.frames.clone();
    prefix.instances = g.instances.clone();
    prefix.iterations = g.iterations.clone();
    prefix.cases = g.cases.clone();
    prefix.universal_witnesses = g.universal_witnesses.clone();
    prefix.checked_answers = g.checked_answers.clone();
    for (i, n) in g.nodes.iter().enumerate() {
        prefix.active = g.contexts[i];
        fresh.validate(&prefix, n).unwrap();
        prefix.push(n.clone()).unwrap();
    }
}

#[test]
fn checked_build_rejects_changed_existing_instance_and_accepts_restoration() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let equation = plan.equations.unwrap();
    env.recheck_node(&g, g.get(equation).unwrap(), equation.0)
        .unwrap();
    assert!(!g.instances.is_empty());
    let saved = g.instances[0].clone();
    g.instances[0].caller.request += 1;
    assert!(
        env.recheck_node(&g, g.get(equation).unwrap(), equation.0)
            .is_err()
    );
    let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
    assert!(
        fresh
            .recheck_node(&g, g.get(equation).unwrap(), equation.0)
            .is_err()
    );
    g.instances[0] = saved;
    env.recheck_node(&g, g.get(equation).unwrap(), equation.0)
        .unwrap();
}

#[test]
fn numeric_guarded_zero_body_keeps_the_complete_zero_equation_family() {
    for (ty, zero) in [("Z", "0"), ("Q", "rat(0,1)")] {
        let p = single_part(&format!(
            "law required reflexive(c:Part,n:{ty}) when n={zero}: n-n={zero};"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert!(
            plan.equations.is_some(),
            "the guarded residual is zero for every argument"
        );
        let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
            .unwrap()
            .unwrap();
        assert_eq!(circuits.len(), 1);
        for case in &circuits[0].cases {
            assert_eq!(case.when, Some(false));
        }
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Established);
        assert!(answer.outputs.contains_key("algebra"));
    }
}

#[test]
fn affine_guard_fibers_keep_raw_equations_separate_from_zero_residuals() {
    use crate::observed::observable_layout::Reading;
    for (ty, guard, body) in [
        ("Z", "n=0", "n=0"),
        ("Q", "n=rat(1,2)", "rat(2,1)*n=rat(1,1)"),
    ] {
        let p = single_part(&format!(
            "law required reflexive(c:Part,n:{ty}) when {guard}: {body};"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let layout = plan.polynomial.as_ref().unwrap();
        let mut checked = 0;
        for object in &layout.data.objects {
            for coordinate in &object.coordinates {
                let super::super::observable_layout::Source::Polynomial(q) = &coordinate.source
                else {
                    panic!()
                };
                if q.guard
                    == super::super::object_equation_presentation::EquationGuard::OutsideObject
                {
                    continue;
                }
                checked += 1;
                assert_eq!(
                    q.guard,
                    super::super::object_equation_presentation::EquationGuard::Undetermined
                );
                let residual = coordinate.value(Reading::Residual).unwrap();
                for kind in [Reading::Nu, Reading::Epsilon] {
                    let original = coordinate.value(kind).unwrap();
                    assert_ne!(original, residual);
                    let Some(Payload::Construction(value)) = &g.get(original).unwrap().payload
                    else {
                        panic!()
                    };
                    let D::PolynomialLaw(data) = &value.data else {
                        panic!()
                    };
                    assert!(data.parameter_family(&[(
                        "n".into(),
                        if ty == "Z" {
                            crate::types::Type::Z
                        } else {
                            crate::types::Type::Q
                        }
                    )]));
                    env.recheck_node(&g, g.get(original).unwrap(), original.0)
                        .unwrap();
                }
                let Some(Payload::Construction(value)) = &g.get(residual).unwrap().payload else {
                    panic!()
                };
                let D::PolynomialLaw(data) = &value.data else {
                    panic!()
                };
                assert!(data.polynomial().unwrap().1.is_empty());
                let source =
                    super::super::object_equation_presentation::parameter_source_on_guard_fiber(
                        &p.shared_inputs(),
                        plan.architecture.witness.readings(),
                        q.position.instance,
                        &[],
                        &quiet(),
                    )
                    .unwrap()
                    .unwrap();
                assert!(source.guard.zero_at(q.position.object, &quiet()).unwrap());
                assert_eq!(source.difference.parameters.len(), 1);
                assert_eq!(source.difference.parameters[0].0.name, "n");
                let constant = if ty == "Z" {
                    Scalar::Z(0.into())
                } else {
                    Scalar::Q((-1).into(), 1.into())
                };
                let coefficient = if ty == "Z" {
                    Scalar::Z(1.into())
                } else {
                    Scalar::Q(2.into(), 1.into())
                };
                assert_eq!(
                    source
                        .difference
                        .constant
                        .evaluate(&[], &quiet())
                        .unwrap()
                        .unwrap()
                        .scalar(),
                    &constant
                );
                assert_eq!(
                    source.difference.parameters[0]
                        .1
                        .evaluate(&[], &quiet())
                        .unwrap()
                        .unwrap()
                        .scalar(),
                    &coefficient
                );
            }
        }
        assert!(checked > 0);
        let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
            .unwrap()
            .unwrap();
        assert!(!circuits[0].cases.is_empty());
        assert!(
            circuits[0]
                .cases
                .iter()
                .all(|case| case.when == Some(false))
        );
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Established);
        assert!(answer.outputs.contains_key("algebra"));
    }
}

#[test]
fn guarded_circuit_when_keeps_the_original_application_expression() {
    use crate::canonical::Json;
    for (guard_text, body) in [("n=0", "n=0"), ("n=0", "n-n=0"), ("true", "n-n=0")] {
        let p = single_part(&format!(
            "law required reflexive(c:Part,n:Z) when {guard_text}: {body};"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Established);
        let reference = |value: &Json| {
            let Json::Obj(fields) = value else { panic!() };
            let Json::Str(id) = &fields["node"] else {
                panic!()
            };
            NodeRef(id.strip_prefix('n').unwrap().parse().unwrap())
        };
        let wire = |r: NodeRef| {
            let Some(Payload::Construction(value)) = &g.get(r).unwrap().payload else {
                panic!()
            };
            let value = value.wire();
            let Json::Obj(fields) = &value else { panic!() };
            fields.clone()
        };
        let mut cases = 0;
        for node in &g.nodes {
            if node.ty != NodeType::Construction(T::CircuitCase) {
                continue;
            }
            cases += 1;
            let Some(Payload::Construction(value)) = &node.payload else {
                panic!()
            };
            let value = value.wire();
            let Json::Obj(case) = &value else { panic!() };
            let when = wire(reference(&case["when"]));
            assert_eq!(when["operation"], Json::str("and"));
            assert_eq!(
                when["parameters"],
                Json::Arr(vec![Json::obj([
                    ("name", Json::str("n")),
                    ("type", Json::str("Z"))
                ])])
            );
            let Json::Arr(operands) = &when["operands"] else {
                panic!()
            };
            assert_eq!(operands.len(), 2);
            let guard = wire(reference(&operands[0]));
            assert_eq!(guard["kind"], Json::str("source"));
            let Json::Obj(location) = &guard["location"] else {
                panic!()
            };
            let Json::Arr(span) = &location["span"] else {
                panic!()
            };
            let (Json::Nat(start), Json::Nat(end)) = (&span[0], &span[1]) else {
                panic!()
            };
            assert_eq!(
                &p.shared_inputs().sources().law().bytes()[*start as usize..*end as usize],
                guard_text.as_bytes()
            );
            let negation = wire(reference(&operands[1]));
            assert_eq!(negation["operation"], Json::str("not"));
        }
        assert!(cases > 0);
    }
}

#[test]
fn guarded_numeric_residuals_use_typed_boolean_maps_and_keep_raw_equations() {
    use crate::observed::observable_layout::Reading;
    use crate::{canonical::Json, types::Type};
    for ty in ["Z", "Q"] {
        for body in ["n=1", "1=0"] {
            let p = single_part(&format!(
                "law required reflexive(c:Part,n:{ty}) when n=0:{body};"
            ));
            let env = Environment::with_prepared(&p, &quiet()).unwrap();
            let mut g = graph(&p);
            let plan = prepare(
                &env,
                &mut g,
                p.shared_inputs(),
                &p.requests().requests()[0],
                &quiet(),
            )
            .unwrap();
            let layout = plan.polynomial.as_ref().unwrap();
            assert!(layout.data.complete);
            let reference = |value: &Json| {
                let Json::Obj(fields) = value else { panic!() };
                let Json::Str(id) = &fields["node"] else {
                    panic!()
                };
                NodeRef(id.strip_prefix('n').unwrap().parse().unwrap())
            };
            let wire = |r: NodeRef| {
                let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
                    panic!()
                };
                let value = v.wire();
                let Json::Obj(ref fields) = value else {
                    panic!()
                };
                fields.clone()
            };
            let mut checked = 0;
            for object in &layout.data.objects {
                for coordinate in &object.coordinates {
                    let super::super::observable_layout::Source::Polynomial(q) = &coordinate.source
                    else {
                        panic!()
                    };
                    if q.guard==crate::observed::object_equation_presentation::EquationGuard::OutsideObject {continue;}
                    checked += 1;
                    let nu = coordinate.value(Reading::Nu).unwrap();
                    let epsilon = coordinate.value(Reading::Epsilon).unwrap();
                    let residual = coordinate.value(Reading::Residual).unwrap();
                    assert_ne!(residual, nu);
                    assert_ne!(residual, epsilon);
                    let Some(Payload::Construction(v)) = &g.get(residual).unwrap().payload else {
                        panic!()
                    };
                    let D::PolynomialLaw(data) = &v.data else {
                        panic!()
                    };
                    assert!(data.guarded_parameter_family());
                    assert!(data.parameter_difference(&quiet()).unwrap().is_none());
                    for r in [nu, epsilon, residual] {
                        env.recheck_node(&g, g.get(r).unwrap(), r.0).unwrap();
                    }
                    let residual = wire(residual);
                    let Json::Arr(terms) = &residual["terms"] else {
                        panic!()
                    };
                    let [Json::Obj(term)] = terms.as_slice() else {
                        panic!()
                    };
                    let coefficient = reference(&term["coefficient"]);
                    assert_eq!(
                        g.get(coefficient).unwrap().ty,
                        NodeType::Expression(q.ty.clone())
                    );
                    let multiply = wire(coefficient);
                    assert_eq!(multiply["operation"], Json::str("multiply"));
                    let Json::Arr(operands) = &multiply["operands"] else {
                        panic!()
                    };
                    let [indicator, _] = operands.as_slice() else {
                        panic!()
                    };
                    let indicator = reference(indicator);
                    assert_eq!(
                        g.get(indicator).unwrap().ty,
                        NodeType::Expression(q.ty.clone())
                    );
                    let compose = wire(indicator);
                    assert_eq!(compose["operation"], Json::str("compose"));
                    let Json::Arr(operands) = &compose["operands"] else {
                        panic!()
                    };
                    let [guard, map] = operands.as_slice() else {
                        panic!()
                    };
                    let guard = reference(guard);
                    assert_eq!(g.get(guard).unwrap().ty, NodeType::Expression(Type::Bool));
                    assert_eq!(
                        crate::observed::law_evaluation::origin(&g, q.instance)
                            .unwrap()
                            .unwrap()
                            .guard_reference,
                        Some(guard)
                    );
                    let map = reference(map);
                    assert_eq!(g.get(map).unwrap().ty, NodeType::Construction(T::StateMap));
                    let map = wire(map);
                    assert_eq!(map["kind"], Json::str("finite"));
                    let source = wire(reference(&map["source"]));
                    assert_eq!(source["type"], Type::Bool.wire());
                    let target = wire(reference(&map["target"]));
                    assert_eq!(target["type"], q.ty.wire());
                    let Json::Arr(pairs) = &map["pairs"] else {
                        panic!()
                    };
                    assert_eq!(pairs.len(), 2);
                    for (pair, (boolean, number)) in pairs.iter().zip([(false, "0"), (true, "1")]) {
                        let Json::Arr(pair) = pair else { panic!() };
                        let [from, to] = pair.as_slice() else {
                            panic!()
                        };
                        assert_eq!(g.scalar(reference(from)).unwrap(), &Scalar::Bool(boolean));
                        let expected =
                            crate::observed::numeric::literal(number, &q.ty, &quiet()).unwrap();
                        assert_eq!(g.scalar(reference(to)).unwrap(), &expected);
                    }
                    let source=crate::observed::object_equation_presentation::parameter_source_on_guard_fiber(
                        &p.shared_inputs(),plan.architecture.witness.readings(),q.position.instance,&[],&quiet()
                    ).unwrap().unwrap();
                    assert!(source.guard.dynamic());
                    assert!(!source.guard.zero_at(q.position.object, &quiet()).unwrap());
                }
            }
            assert!(checked > 0);
            let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &quiet())
                .unwrap()
                .unwrap();
            assert!(
                circuits
                    .iter()
                    .flat_map(|d| &d.cases)
                    .all(|c| c.when.is_none())
            );
            assert!(circuits.iter().any(|d| !d.cases.is_empty()));
        }
    }
}

#[test]
fn guarded_numeric_families_keep_existing_finite_parameter_bindings() {
    use crate::observed::{
        object_equation_presentation::EquationGuard, observable_layout::Reading,
    };
    let p =
        single_part("law required reflexive(c:Part,n:Z,b:Bool) when if b then n=0 else false:n=1;");
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    let layout = plan.polynomial.as_ref().unwrap();
    assert!(layout.data.complete);
    let mut applicable = false;
    let mut actual_position = None;
    let mut outside = false;
    for object in &layout.data.objects {
        for coordinate in &object.coordinates {
            let super::super::observable_layout::Source::Polynomial(q) = &coordinate.source else {
                panic!()
            };
            if q.guard == EquationGuard::OutsideObject {
                continue;
            }
            let origin = crate::observed::law_evaluation::origin(&g, q.instance)
                .unwrap()
                .unwrap();
            let binding = origin.bindings.iter().find(|b| b.name == "b").unwrap();
            let canonical = crate::observed::law_evaluation::origin(&g, coordinate.index)
                .unwrap()
                .unwrap();
            let canonical = canonical.bindings.iter().find(|b| b.name == "b").unwrap();
            assert_eq!(
                g.scalar(canonical.value).unwrap(),
                g.scalar(binding.value).unwrap()
            );
            match q.guard {
                EquationGuard::AlwaysFalse => {
                    outside = true;
                    assert_eq!(g.scalar(binding.value).unwrap(), &Scalar::Bool(false));
                    assert!(coordinate.value(Reading::Epsilon).is_none());
                }
                EquationGuard::Undetermined => {
                    applicable = true;
                    actual_position.get_or_insert(q.position);
                    assert_eq!(g.scalar(binding.value).unwrap(), &Scalar::Bool(true));
                    assert!(origin.guarded_family);
                    let r = coordinate.value(Reading::Residual).unwrap();
                    let Some(Payload::Construction(value)) = &g.get(r).unwrap().payload else {
                        panic!()
                    };
                    let D::PolynomialLaw(data) = &value.data else {
                        panic!()
                    };
                    assert!(data.guarded_parameter_family());
                    env.recheck_node(&g, g.get(r).unwrap(), r.0).unwrap();
                }
                _ => panic!("unexpected guard {:?}", q.guard),
            }
        }
    }
    assert!(applicable && outside);
    let position = actual_position.unwrap();
    let readings = plan.architecture.witness.readings();
    let names = readings.instances()[position.instance]
        .declaration()
        .parameters
        .iter()
        .map(|(name, _)| (name.clone(), name.clone()))
        .collect::<Vec<_>>();
    for source_value in [false, true] {
        let source = vec![("b".into(), Scalar::Bool(source_value))];
        let target = vec![("b".into(), Scalar::Bool(true))];
        let family = crate::observed::environment::numeric_law_function::compare_bound(
            &p.shared_inputs(),
            [readings, readings],
            [position, position],
            &names,
            [&source, &target],
            &quiet(),
        )
        .unwrap();
        assert_eq!(family.applicable, Some(source_value));
        assert_eq!(family.equivalent, Some(source_value));
        assert_eq!(family.value_equal, Some(source_value));
        if !source_value {
            let point = family.value_example.as_ref().unwrap();
            assert!(point.bindings.contains(&("n".into(), Scalar::Z(0.into()))));
            assert!(point.bindings.contains(&("b".into(), Scalar::Bool(false))));
            assert_eq!(point.left, Scalar::Z(0.into()));
            assert_eq!(point.right, Scalar::Z((-1).into()));
        }
    }
    let answer = crate::observed::build_result::retain_plan(
        &env,
        &mut g,
        plan,
        &p.requests().requests()[0],
        &quiet(),
    )
    .unwrap();
    assert_eq!(answer.status, Decision::Established);
    assert!(answer.outputs.contains_key("algebra"));
}

#[test]
fn affine_guard_missing_coefficient_keeps_observation_reason_and_constructed_object() {
    for (guard, unsupported) in [
        ("n=c.quantity", false),
        ("n=c.quantity and n=0", false),
        ("(n-c.quantity)*(n-c.quantity)=0", true),
    ] {
        let inputs = fixture::inputs(
            true,
            false,
            &format!("law required guarded(c:Part,n:Z) when {guard}:n=1;"),
        );
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["b=build(Selected,on=@v/root)"],
            &quiet(),
        )
        .unwrap();
        let p = PreparedObserved {
            inputs,
            requests,
            object: None,
        };
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.contains_key("object"));
        assert!(!answer.outputs.contains_key("algebra"));
        assert!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)
                    && r.missing.iter().any(|f| f.snapshot == "v"
                        && f.subject == "q"
                        && f.field.as_deref() == Some("Family.Part.quantity")))
        );
        // 別の対象で係数が観測済みなら、非線形guardの算法理由も独立に残る。
        assert_eq!(
            answer
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. })),
            unsupported,
            "{guard}"
        );
    }
}

#[test]
fn nonlinear_guard_keeps_the_original_algorithm_reason_and_partial_object() {
    for (ty, guard) in [
        ("Z", "n*n=0"),
        ("Q", "n*n=0"),
        ("Z", "n=1 and n*n=0"),
        ("Z", "let a=n in a*a=0"),
        ("Z", "let a=n*n in a=0"),
    ] {
        let p = single_part(&format!(
            "law required guarded(c:Part,n:{ty}) when {guard}:1=0;"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Undetermined, "{ty}: {guard}");
        assert!(answer.outputs.contains_key("object"));
        assert!(!answer.outputs.contains_key("algebra"));
        let reasons = answer.reasons.iter().filter(|reason| matches!(&reason.kind,
            ReasonKind::UnsupportedAlgorithm { operand_types, .. } if operand_types.contains(&if ty == "Z" { crate::types::Type::Z } else { crate::types::Type::Q }))).collect::<Vec<_>>();
        assert!(!reasons.is_empty(), "{ty}: {guard}");
        assert!(reasons.iter().all(|reason| !reason.dependencies.is_empty()
            && reason.location.is_some()
            && reason.missing.is_empty()));
    }
}

#[test]
fn cancelled_polynomial_guard_uses_the_required_affine_algorithm() {
    for (guard, status) in [
        ("n*n-n*n=0", Decision::Established),
        ("n*n-n*n=1", Decision::Established),
        ("let a=n*n in a-a=0", Decision::Established),
        ("(let a=n*n in a)-(let a=n*n in a)=0", Decision::Established),
    ] {
        let p = single_part(&format!(
            "law required guarded(c:Part,n:Z) when {guard}:0=0;"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, status, "{guard}");
        assert!(answer.outputs.contains_key("algebra"));
        assert!(
            !answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        );
    }
}

#[test]
fn wrapped_nonlinear_numeric_guards_keep_their_original_algorithm_reason() {
    for (helper, guard) in [
        ("view square(x:Z):Z=x*x;", "square(n)=0"),
        ("view nonlinear(x:Z):Bool=x*x=0;", "nonlinear(n)"),
        ("view echo(x:Z):Z=x;", "echo(n*n)=0"),
        ("", "(if true then n*n else 0)=0"),
        ("", "(match true {_=>n*n;})=0"),
        ("", "(match n {x=>x*x;})=0"),
        ("", "match n*n {x=>x=0;}"),
        ("", "if false then false else n*n=0"),
    ] {
        let p = single_part(&format!(
            "{helper} law required guarded(c:Part,n:Z) when {guard}:1=0;"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Undetermined, "{guard}");
        assert!(answer.outputs.contains_key("object"));
        assert!(!answer.outputs.contains_key("algebra"));
        assert!(
            answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. })),
            "{guard}"
        );
        assert!(
            !answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::Missing)),
            "{guard}"
        );
    }
}

#[test]
fn selected_nonlinear_guards_do_not_require_unselected_missing_observations() {
    for guard in [
        "(if true then n*n else c.quantity)=0",
        "if false then c.quantity=0 else n*n=0",
    ] {
        let inputs = fixture::inputs(
            true,
            false,
            &format!("law required guarded(c:Part,n:Z) when {guard}:1=0;"),
        );
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["b=build(Selected,on=@v/root)"],
            &quiet(),
        )
        .unwrap();
        let p = PreparedObserved {
            inputs,
            requests,
            object: None,
        };
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Undetermined, "{guard}");
        assert!(answer.outputs.contains_key("object"));
        assert!(
            answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. })),
            "{guard}"
        );
        assert!(
            !answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::Missing)),
            "{guard}"
        );
    }
}

#[test]
fn unsupported_numeric_guard_conditions_keep_typed_reasons_and_partial_objects() {
    for (ty, guard) in [
        ("Z", "n>0"),
        ("Q", "n>0"),
        ("Z", "n!=0"),
        ("Z", "n*n=0 or n*n=1"),
        ("Z", "n=0 or n=1"),
        ("Z", "n*n=0 implies n*n=1"),
        ("Z", "not(n*n=0)"),
        ("Z", "not(n=0)"),
    ] {
        let p = single_part(&format!(
            "law required guarded(c:Part,n:{ty}) when {guard}:1=0;"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Undetermined, "{guard}");
        assert!(answer.outputs.contains_key("object"));
        assert!(!answer.outputs.contains_key("algebra"));
        assert!(answer.reasons.iter().any(|r| matches!(&r.kind, ReasonKind::UnsupportedAlgorithm {operand_types,..} if operand_types.contains(&if ty=="Z" {crate::types::Type::Z} else {crate::types::Type::Q}))), "{guard}");
        assert!(
            !answer
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Missing)),
            "{guard}"
        );
    }
}

#[test]
fn numeric_guard_boundary_simplifications_keep_affine_and_constant_conditions() {
    for (guard, body) in [
        ("not(not(n=0))", "n=0"),
        ("n=0 or n=0", "n=0"),
        ("n=0 implies n=0", "0=0"),
        ("n*n-n*n>0", "1=0"),
        ("n*n-n*n>=0", "0=0"),
        ("(n*n-n*n=0) or n*n=1", "0=0"),
        ("(n*n-n*n=1) and n*n=1", "1=0"),
    ] {
        let p = single_part(&format!(
            "law required guarded(c:Part,n:Z) when {guard}:{body};"
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        let answer = crate::observed::build_result::retain_plan(
            &env,
            &mut g,
            plan,
            &p.requests().requests()[0],
            &quiet(),
        )
        .unwrap();
        assert_eq!(answer.status, Decision::Established, "{guard}");
        assert!(answer.outputs.contains_key("algebra"));
        assert!(
            !answer
                .reasons
                .iter()
                .any(|reason| matches!(reason.kind, ReasonKind::UnsupportedAlgorithm { .. })),
            "{guard}"
        );
    }
}
