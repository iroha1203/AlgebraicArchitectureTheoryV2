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
        &mut quiet(),
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
    for (ty, tuple) in [("Z", false), ("Q", false), ("Z", true), ("Q", true)] {
        let parameter_type = if tuple {
            format!("({ty},{ty})")
        } else {
            ty.to_owned()
        };
        for (body, truth) in [("n=n", true), ("n=n+1", false), ("n=0", false)] {
            let expression = if tuple {
                body.replace("n", "(n.0+n.1)")
            } else {
                body.to_owned()
            };
            let p = single_part(&format!(
                "law required reflexive(c:Part,n:{parameter_type}):{expression};"
            ));
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            let mut g = graph(&p);
            let plan = prepare(
                &env,
                &mut g,
                p.shared_inputs(),
                &p.requests().requests()[0],
                &mut quiet(),
            )
            .unwrap();
            let table = plan.laws.as_ref().unwrap();
            let circuits =
                crate::observed::build_circuit_plan::closed(&env, &g, &plan, &mut quiet())
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
}

fn single_part(body: &str) -> PreparedObserved {
    use crate::observed::input::{InputSources, check_inputs};
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
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
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
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let mut g = graph(&p);
        let plan = prepare(
            &env,
            &mut g,
            p.shared_inputs(),
            &p.requests().requests()[0],
            &mut quiet(),
        )
        .unwrap();
        let comparisons =
            crate::observed::build_compare::compare(&env, &g, &plan, &mut quiet()).unwrap();
        assert_eq!(comparisons.len(), 1, "{body}");
        assert_eq!(comparisons[0].equal, Some(expected), "{body}");
    }
}

#[test]
fn closed_circuits_use_the_actual_component_residual_and_keep_reject_cases() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    let circuits = crate::observed::build_circuit_plan::closed(&env, &g, &plan, &mut quiet())
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
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    assert!(
        crate::observed::build_circuit_plan::closed(&env, &g, &plan, &mut quiet())
            .unwrap()
            .is_none()
    );
}

#[test]
fn native_build_answer_contains_rechecked_algebra_and_component_circuits() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
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
    use crate::observed::input::{InputSources, check_inputs};
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
    let old = &initial.definitions().vocabularies["Family"].digest;
    let new = &defs.vocabularies["Family"].digest;
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
            &mut quiet(),
        )
        .unwrap(),
    );
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &["b=build(Selected,on=@v/root)"],
        &mut quiet(),
    )
    .unwrap();
    let p = PreparedObserved {
        inputs,
        requests,
        object: None,
    };
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
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
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let answer = crate::observed::build_result::evaluate(
        &p,
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
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
fn four_stops_keep_a_completed_object_without_publishing_unfinished_algebra() {
    for mode in 0..4 {
        for at in [1, 6] {
            let mut armed = false;
            let mut seen = 0;
            let mut control = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    armed |= point == Checkpoint::ObjectLawCircuits;
                    if armed && point == Checkpoint::NativeResultNode {
                        seen += 1;
                    }
                    let stop = seen >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && mode == 0),
                        memory_mib: u128::from(stop && mode == 1),
                        signal: (stop && mode >= 2).then_some(if mode == 2 {
                            crate::result::Signal::Int
                        } else {
                            crate::result::Signal::Term
                        }),
                    }
                },
            );
            let p = prepared(false);
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            let mut g = Graph::new(&control);
            g.requests = p.requests().requests().to_vec();
            let answer = crate::observed::build_result::evaluate(
                &p,
                &env,
                &mut g,
                &p.requests().requests()[0],
                &mut control,
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
}

#[test]
fn one_build_uses_the_same_native_objects_laws_patterns_equations_and_invariants() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
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
        crate::observed::build_compare::compare(&env, &g, &plan, &mut quiet())
            .unwrap()
            .is_empty()
    ); // この入力の全3対象は完全patternがそれぞれ異なる。
    plan.boundary
        .recheck(&env, &g, g.nodes.len(), &mut quiet())
        .unwrap();
    assert!(env.architecture_ref().is_none());
}

#[test]
fn source_validation_rejects_context_reference_order_and_original_node_changes_together() {
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
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
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let result = if matches!(mode, 4 | 5) {
            let mut inputs = boundary.inputs().to_vec();
            inputs.push(NodeRef(g.nodes.len() + usize::from(mode == 5)));
            Boundary::capture(
                &fresh,
                &g,
                plan.architecture.reference,
                inputs,
                &mut quiet(),
            )
            .map(|_| ())
        } else {
            boundary.recheck(&fresh, &g, g.nodes.len(), &mut quiet())
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
        .recheck(&env, &g, g.nodes.len(), &mut quiet())
        .unwrap();
}

#[test]
fn outside_polynomial_keeps_the_original_symbolic_difference_without_an_evaluated_epsilon() {
    use crate::observed::observable_layout::{Placed, Reading, Source};
    let p = prepared(false);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    let layout = plan.polynomial.as_ref().unwrap();
    let checked = layout.checked(&env, &g, &mut quiet()).unwrap();
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
            .at(1, 1, Reading::Epsilon, 0, &layout.data.anchor, &mut quiet())
            .unwrap(),
        Placed::Uncomputed { .. }
    ));
    let Placed::Value { reference, .. } = checked
        .at(
            1,
            1,
            Reading::Residual,
            0,
            &layout.data.anchor,
            &mut quiet(),
        )
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
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
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
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut g = graph(&p);
    let plan = prepare(
        &env,
        &mut g,
        p.shared_inputs(),
        &p.requests().requests()[0],
        &mut quiet(),
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
    let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
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
fn required_numeric_tuple_missing_needed_rechecks_original_answers() {
    for tuple in [false, true] {
        let (ty, term) = if tuple {
            ("(Z,(Z,Z))", "pair.0")
        } else {
            ("Z", "pair")
        };
        let more = if tuple { "(Z,Z)" } else { "Z" };
        let inputs=fixture::inputs(true,false,&format!("law required balanced(pair:{ty},c:Part,last:Z,more:{more}):{term}+c.quantity={term};"));
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &[
                "b=build(Selected,on=@v/root)",
                "c=check(Selected.balanced,on=$b.object,c=@v/q)",
                "n=needed($c)",
            ],
            &mut quiet(),
        )
        .unwrap();
        let p = PreparedObserved {
            inputs,
            requests,
            object: None,
        };
        let result = crate::observed::evaluate_observed(p, &mut quiet()).unwrap();
        let env = Environment::with_prepared(&result.prepared, &mut quiet()).unwrap();
        let mut g = Graph::new(&quiet());
        g.nodes = result.nodes.clone();
        g.contexts = result.contexts.clone();
        g.requests = result.prepared.requests().requests().to_vec();
        g.checked_answers = result.answers.iter().cloned().enumerate().collect();
        g.frames = result.frames.clone();
        g.instances = result.instances.clone();
        g.iterations = result.iterations.clone();
        g.cases = result.cases.clone();
        g.universal_witnesses = result.universal_witnesses.clone();
        for index in 0..2 {
            env.validate_answer(&g, &g.requests[index], &result.answers[index])
                .unwrap();
        }
        g.active = crate::observed::call::Context {
            request: 2,
            ..Default::default()
        };
        let request = g.requests[2].clone();
        let (answer, stop) =
            crate::observed::needed::evaluate(&mut g, &env, &request, &mut quiet()).unwrap();
        assert!(stop.is_none());
        assert!(answer.outputs.contains_key("plan"));
        assert_ne!(result.status(), "error");
        let index = g
            .nodes
            .iter()
            .position(|n| matches!(n.payload, Some(Payload::CompletionPair { .. })))
            .unwrap();
        let saved = g.contexts[index];
        g.contexts[index].request = 2;
        let fresh = Environment::with_prepared(&result.prepared, &mut quiet()).unwrap();
        assert!(fresh.recheck_node(&g, &g.nodes[index], index).is_err());
        g.contexts[index] = saved;
        let template = g.nodes[index].arguments[0];
        let ordinal = g
            .universal_witnesses
            .iter()
            .position(|w| w.template == template && w.ordinal == 0)
            .unwrap();
        let saved = g.universal_witnesses[ordinal].caller;
        g.universal_witnesses[ordinal].caller.request = 2;
        let fresh = Environment::with_prepared(&result.prepared, &mut quiet()).unwrap();
        assert!(fresh.recheck_node(&g, &g.nodes[index], index).is_err());
        g.universal_witnesses[ordinal].caller = saved;
    }
}
