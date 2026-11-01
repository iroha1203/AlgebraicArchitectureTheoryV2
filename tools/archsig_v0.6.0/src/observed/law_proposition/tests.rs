use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
use crate::types::Type;
use std::sync::Arc;
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
use crate::control::quiet;
fn prepared(body: &str) -> PreparedObserved {
    let inputs = fixture::inputs(false, false, body);
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
fn replay(p: &PreparedObserved, source: &Graph) -> Result<(), ValidationFailure> {
    let env = Environment::with_prepared(p, &mut quiet())?;
    let mut g = Graph::new(&quiet());
    g.requests = source.requests.clone();
    g.frames = source.frames.clone();
    g.instances = source.instances.clone();
    g.iterations = source.iterations.clone();
    g.cases = source.cases.clone();
    g.universal_witnesses = source.universal_witnesses.clone();
    g.checked_answers = source.checked_answers.clone();
    for (i, node) in source.nodes.iter().enumerate() {
        g.active = source.contexts[i];
        env.validate(&g, node)?;
        g.push(node.clone())?;
    }
    Ok(())
}
#[test]
fn native_law_propositions_keep_actual_truth_and_refutation_in_each_object() {
    let p = prepared("law required zero(c:Part):c.quantity=0;");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
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
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut quiet(),
    )
    .unwrap();
    let mut templates = 0;
    let mut rows = 0;
    for (object, d) in ds.iter().enumerate() {
        for o in &d.originals {
            let row = frames::origin(&g, o.reference).unwrap().unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
                panic!("subject")
            };
            let who = subject.clone();
            let reading = check(
                &env,
                &mut g,
                o.reference,
                objects.architectures[object],
                &mut quiet(),
            )
            .unwrap();
            assert_eq!(reading.origin, o.reference);
            assert_eq!(
                reading.answer.is_some(),
                object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q")
            );
            if let Some(answer) = reading.answer {
                assert_eq!(
                    answer.status,
                    if who == "p" {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
                let claim = answer.claim.unwrap();
                assert!(matches!(
                    g.nodes[claim.0].payload,
                    Some(Payload::Proposition { .. })
                ));
                assert_eq!(answer.outputs.get("proposition"), Some(&claim));
                assert!(!answer.evidence.is_empty());
                assert_eq!(g.contexts[claim.0].instance, reading.instance);
                assert_eq!(
                    answer.evidence.iter().any(|r| matches!(
                        g.nodes[r.0].payload,
                        Some(Payload::Counterexample { .. })
                    )),
                    who == "q"
                );
                assert!(answer.reasons.is_empty());
                assert!(row.ready);
                assert!(row.body_allowed);
                if o.row.is_some() {
                    rows += 1;
                } else {
                    templates += 1;
                }
            }
        }
    }
    assert_eq!((templates, rows), (4, 4));
    replay(&p, &g).unwrap();
}

#[test]
fn native_false_guard_proposition_keeps_unread_body_and_conditional_truth() {
    let p = prepared("law required inactive(c:Part) when false:c.quantity=0;");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
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
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &mut quiet(),
    )
    .unwrap();
    let mut runs = 0;
    for (object, d) in ds.iter().enumerate() {
        for r in &d.readings {
            let reading = check(
                &env,
                &mut g,
                r.instance,
                objects.architectures[object],
                &mut quiet(),
            )
            .unwrap();
            if let Some(answer) = reading.answer {
                assert_eq!(answer.status, Decision::Established);
                assert!(answer.evidence.is_empty());
                assert!(answer.reasons.is_empty());
                let e = answer.outputs["evaluation"];
                let Some(Payload::Evaluation {
                    value,
                    parts,
                    applicability,
                    ..
                }) = &g.nodes[e.0].payload
                else {
                    panic!("evaluation")
                };
                assert_eq!(*applicability, "not_applicable");
                assert_eq!(g.boolean(*value).unwrap(), Some(true));
                assert_eq!(parts.len(), 2);
                assert!(parts[1].children.is_empty());
                assert!(parts[1].value.is_none());
                runs += 1;
            }
        }
    }
    assert_eq!(runs, 4);
    replay(&p, &g).unwrap();
}

fn from_inputs(inputs: Arc<crate::input::CheckedInputs>) -> PreparedObserved {
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
fn start(p: &PreparedObserved) -> (Graph, NodeRef, Vec<NodeRef>) {
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
    (g, a.reference, objects.architectures)
}
fn rows(p: &PreparedObserved, g: &mut Graph, a: NodeRef) -> Vec<Vec<NodeRef>> {
    crate::observed::polynomial_law_diagram::retain_family(g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .into_iter()
        .map(|d| d.readings.iter().map(|r| r.instance).collect())
        .collect()
}
fn who(g: &Graph, r: NodeRef) -> String {
    let row = frames::origin(g, r).unwrap().unwrap();
    let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
        panic!("subject")
    };
    subject.clone()
}
fn replay_nodes(
    p: &PreparedObserved,
    source: &Graph,
    nodes: Vec<Node>,
) -> Result<(), ValidationFailure> {
    let mut bad = copy_graph(source, &quiet());
    bad.nodes = nodes.into();
    replay(p, &bad)
}
fn copy_graph(g: &Graph, c: &Control) -> Graph {
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
#[allow(dead_code)]
mod finite_fixture {
    include!("../../../tests/common/finite_law_family_data.rs");
}
#[test]
fn native_finite_propositions_keep_all_boolean_rows_and_their_counterexamples() {
    let p = from_inputs(finite_fixture::inputs(
        false,
        "law required bit(c:Part,b:Bool):(c.quantity=0)=b;",
    ));
    let (mut g, a, objects) = start(&p);
    let ds = crate::observed::finite_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.originals.len(), 4);
        for r in &d.originals {
            let person = who(&g, r.row);
            let origin = frames::origin(&g, r.row).unwrap().unwrap();
            let Scalar::Bool(bit) = g.scalar(origin.bindings[1].value).unwrap() else {
                panic!("bit")
            };
            let expected = (person == "p") == *bit;
            let got = check(&env, &mut g, r.row, objects[object], &mut quiet()).unwrap();
            if let Some(answer) = got.answer {
                assert_eq!(
                    answer.status,
                    if expected {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
                assert_eq!(
                    answer.evidence.iter().any(|r| matches!(
                        g.nodes[r.0].payload,
                        Some(Payload::Counterexample { .. })
                    )),
                    !expected
                );
                let claim = answer.claim.unwrap();
                let Some(Payload::Proposition { instance }) = &g.nodes[claim.0].payload else {
                    panic!("proposition")
                };
                let Some(Payload::LawInstance { bindings, .. }) = &g.nodes[instance.0].payload
                else {
                    panic!("instance")
                };
                assert_eq!(bindings.len(), 2);
                assert_eq!(
                    g.scalar(bindings[1].value).unwrap(),
                    &Scalar::Bool(person == "p" && expected || person != "p" && !expected)
                );
                count += 1;
            }
        }
    }
    assert_eq!(count, 8);
    replay(&p, &g).unwrap();
}
#[test]
fn native_unknown_guard_and_body_propositions_keep_missing_without_invented_evidence() {
    for body in [
        "law required guarded(c:Part) when c.quantity=0:c.quantity=1;",
        "law required missing(c:Part):c.quantity=0;",
    ] {
        let p = from_inputs(fixture::inputs(true, false, body));
        let (mut g, a, objects) = start(&p);
        let rs = rows(&p, &mut g, a);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let mut count = 0;
        for (object, rs) in rs.iter().enumerate() {
            for r in rs {
                let person = who(&g, *r);
                let got = check(&env, &mut g, *r, objects[object], &mut quiet()).unwrap();
                if let Some(answer) = got.answer {
                    if person == "q" {
                        assert_eq!(answer.status, Decision::Undetermined);
                        assert!(answer.evidence.is_empty());
                        let e = answer.outputs["evaluation"];
                        let Some(Payload::Evaluation {
                            value,
                            applicability,
                            ..
                        }) = &g.nodes[e.0].payload
                        else {
                            panic!("evaluation")
                        };
                        assert!(value.is_none());
                        assert_eq!(
                            *applicability,
                            if body.contains("when") {
                                "undetermined"
                            } else {
                                "applicable"
                            }
                        );
                        assert!(answer.reasons.iter().any(|r| {
                            r.missing.iter().any(|f| {
                                f.subject == "q"
                                    && f.field.as_deref() == Some("Family.Part.quantity")
                            })
                        }));
                        count += 1;
                    }
                }
            }
        }
        assert_eq!(count, 2);
        replay(&p, &g).unwrap();
    }
}
#[test]
fn native_tuple_proposition_evidence_preserves_both_original_typed_operands() {
    let p = from_inputs(fixture::inputs(
        false,
        true,
        "law required pair(c:Part):c.quantity=(0,rat(1,2));",
    ));
    let (mut g, a, objects) = start(&p);
    let rs = rows(&p, &mut g, a);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for (object, rs) in rs.iter().enumerate() {
        for r in rs {
            let person = who(&g, *r);
            let got = check(&env, &mut g, *r, objects[object], &mut quiet()).unwrap();
            if let Some(answer) = got.answer {
                assert_eq!(
                    answer.status,
                    if person == "p" {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
                let evaluation = answer.outputs["evaluation"];
                let Some(Payload::Evaluation { parts, .. }) = &g.nodes[evaluation.0].payload else {
                    panic!("evaluation")
                };
                assert_eq!(parts[0].children.len(), 2);
                for child in &parts[0].children {
                    assert_eq!(
                        g.nodes[child.0].ty,
                        NodeType::Evaluation(Type::Tuple(vec![Type::Z, Type::Q]))
                    );
                }
                let evidence = answer.evidence[0];
                let Some(Payload::EvaluationEvidence { lhs, rhs, .. }) =
                    &g.nodes[evidence.0].payload
                else {
                    panic!("evidence")
                };
                assert_eq!(
                    g.scalar(*rhs).unwrap().ty(),
                    Type::Tuple(vec![Type::Z, Type::Q])
                );
                assert_eq!(
                    g.scalar(*lhs).unwrap().ty(),
                    Type::Tuple(vec![Type::Z, Type::Q])
                );
                assert_ne!(lhs, rhs);
                count += 1;
            }
        }
    }
    assert_eq!(count, 4);
    replay(&p, &g).unwrap();
}
#[test]
fn native_propositions_use_actual_object_quantification_and_original_helpers() {
    for (extra, body, by_object) in [
        ("view amount(c:Part):Z=c.quantity;", "amount(c)>=0", false),
        ("", "forall x:Part.x.quantity=0", true),
        (
            "",
            "forall f in list<Path<Part,Part>>[identity(c)].source(f)=c",
            false,
        ),
    ] {
        let p = prepared(&format!("{extra}law required tested(c:Part):{body};"));
        let (mut g, a, objects) = start(&p);
        let rs = rows(&p, &mut g, a);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let mut count = 0;
        let objects_checked = if by_object { rs.len() } else { 1 };
        for (object, rs) in rs.iter().enumerate().take(objects_checked) {
            for r in rs {
                let got = check(&env, &mut g, *r, objects[object], &mut quiet())
                    .unwrap_or_else(|e| panic!("{body} object {object}: {e:?}"));
                if let Some(answer) = got.answer {
                    assert_eq!(
                        answer.status,
                        if !by_object || object == 1 {
                            Decision::Established
                        } else {
                            Decision::Refuted
                        }
                    );
                    let eval = answer.outputs["evaluation"];
                    let Some(Payload::Evaluation { environment, .. }) = &g.nodes[eval.0].payload
                    else {
                        panic!("evaluation")
                    };
                    assert_eq!(*environment, Some(objects[object]));
                    if by_object {
                        assert!(
                            answer
                                .scope
                                .quantifiers
                                .iter()
                                .any(|q| q.name == "x" && q.domain.is_some())
                        );
                    }
                    count += 1;
                }
            }
        }
        assert_eq!(count, if by_object { 4 } else { 2 });
        replay(&p, &g).unwrap();
    }
}
#[test]
fn native_propositions_reject_forged_truth_evidence_role_binding_and_environment() {
    let p = prepared("law required zero(c:Part):c.quantity=0;");
    let (mut g, a, objects) = start(&p);
    let rs = rows(&p, &mut g, a);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let q = *rs[0].iter().find(|r| who(&g, **r) == "q").unwrap();
    let answer = check(&env, &mut g, q, objects[0], &mut quiet())
        .unwrap()
        .answer
        .unwrap();
    assert_eq!(answer.status, Decision::Refuted);
    let claim = answer.claim.unwrap();
    let counter = *answer
        .evidence
        .iter()
        .find(|r| matches!(g.nodes[r.0].payload, Some(Payload::Counterexample { .. })))
        .unwrap();
    for mode in 0..2 {
        let mut nodes = g.nodes.clone();
        if mode == 0 {
            nodes[claim.0].judgment.as_mut().unwrap().status = Decision::Established;
        } else {
            let Some(Payload::Counterexample { left, right, .. }) = &mut nodes[counter.0].payload
            else {
                panic!()
            };
            *right = *left;
        }
        assert!(replay_nodes(&p, &g, nodes.into_vec()).is_err(), "forgery {mode}");
    }
    replay(&p, &g).unwrap();
}
#[test]
fn native_unbounded_parameter_uses_universal_proposition_without_finite_samples() {
    let parameter_type = Type::Tuple(vec![Type::Z, Type::Tuple(vec![Type::Z, Type::Z])]);
    let p = prepared("law required unbounded(c:Part,k:(Z,(Z,Z))):c.quantity=k.0+k.1.1;");
    let (mut g, a, objects) = start(&p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for (object, d) in ds.iter().enumerate().take(2) {
        assert!(d.unavailable.is_none());
        for o in &d.originals {
            assert!(o
                .parameters
                .iter()
                .any(|(n, t)| n == "k" && t == &parameter_type));
            let before = g.nodes.len();
            let r = check(&env, &mut g, o.reference, objects[object], &mut quiet()).unwrap();
            if frames::origin(&g, o.reference).unwrap().unwrap().outside {
                assert!(r.answer.is_none() && r.instance.is_none());
                assert_eq!(g.nodes.len(), before);
            } else {
                let answer = r.answer.unwrap();
                assert!(r.instance.is_some());
                assert_eq!(
                    g.get(answer.claim.unwrap())
                        .unwrap()
                        .judgment
                        .as_ref()
                        .unwrap()
                        .status,
                    Decision::Refuted
                );
                assert!(g.nodes.len() > before);
                let quantifier = answer
                    .scope
                    .quantifiers
                    .iter()
                    .find(|q| q.name == "k" && q.ty == parameter_type)
                    .unwrap();
                assert!(
                    matches!(&g.get(quantifier.domain.unwrap()).unwrap().payload,Some(Payload::TypeDomain{ty}) if *ty==parameter_type)
                );
            }
        }
    }
    replay(&p, &g).unwrap();
}

#[test]
fn native_law_proposition_interrupt_keeps_completed_evidence_and_exact_prefix() {
    use crate::control::Checkpoint;
    use std::{cell::Cell, rc::Rc};
    let p = prepared("law required zero(c:Part):c.quantity=0;");
    let (mut initial, a, objects) = start(&p);
    let rs = rows(&p, &mut initial, a);
    let root = *rs[0].iter().find(|r| who(&initial, **r) == "q").unwrap();
    let seen = Rc::new(Cell::new(0));
    let counter = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::FiniteIteration {
            counter.set(counter.get() + 1)
        }
        None
    });
    let mut complete = copy_graph(&initial, &c);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let whole = check(&env, &mut complete, root, objects[0], &mut c).unwrap();
    assert_eq!(whole.answer.unwrap().status, Decision::Refuted);
    let total = seen.get();
    assert!(total > 50);
    let mut retained_evidence = false;
    let mut retained_complete = false;
    for at in [2 * total / 3, total - 5, total] {
        let seen = Rc::new(Cell::new(0));
        let counter = seen.clone();
        let mut c = Control::new(move |point| {
            if point == Checkpoint::FiniteIteration {
                counter.set(counter.get() + 1)
            }
            let stop = counter.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = copy_graph(&initial, &c);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            matches!(
                check(&env, &mut g, root, objects[0], &mut c),
                Err(ValidationFailure::Stop(_))
            ),
            "point {at}"
        );
        assert_eq!(g.active, initial.active);
        assert!(env.architecture_ref().is_none());
        assert!(g.nodes.len() <= complete.nodes.len());
        assert_eq!(g.nodes, &complete.nodes[..g.nodes.len()]);
        assert_eq!(g.contexts, &complete.contexts[..g.nodes.len()]);
        retained_evidence |= g.nodes.len() < complete.nodes.len()
            && g.nodes[initial.nodes.len()..]
                .iter()
                .any(|n| n.ty == NodeType::Evidence);
        retained_complete |= g.nodes.len() == complete.nodes.len();
        replay(&p, &g).unwrap();
    }
    assert!(retained_evidence);
    assert!(retained_complete);
}

#[test]
fn native_guarded_numeric_quantifiers_keep_guard_body_and_conditional_judgments() {
    let p = from_inputs(fixture::inputs(
        true,
        false,
        "law required tested(c:Part) when c.quantity=0:forall k:Z.k=0;",
    ));
    let (mut g, a, objects) = start(&p);
    let rs = rows(&p, &mut g, a);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for r in &rs[0] {
        let person = who(&g, *r);
        let answer = check(&env, &mut g, *r, objects[0], &mut quiet())
            .unwrap_or_else(|e| panic!("{person}: {e:?}"))
            .answer
            .unwrap();
        assert_eq!(
            answer.status,
            if person == "p" {
                Decision::Refuted
            } else {
                Decision::Undetermined
            }
        );
        let eval = answer.outputs["evaluation"];
        let Some(Payload::Evaluation {
            applicability,
            parts,
            ..
        }) = &g.nodes[eval.0].payload
        else {
            panic!("evaluation")
        };
        assert_eq!(
            *applicability,
            if person == "q" {
                "undetermined"
            } else {
                "applicable"
            }
        );
        assert_eq!(parts.len(), 2);
        count += 1;
    }
    assert_eq!(count, 2);
    replay(&p, &g).unwrap();
}

#[test]
fn native_false_guard_body_source_never_becomes_a_regular_or_universal_evaluation() {
    for body in ["c.quantity=0", "forall k:Z.k=0"] {
        let p = from_inputs(fixture::inputs(
            true,
            false,
            &format!("law required skipped(c:Part) when false:{body};"),
        ));
        let (mut g, a, objects) = start(&p);
        let rs = rows(&p, &mut g, a);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let mut count = 0;
        for (object, rs) in rs.iter().enumerate() {
            for r in rs {
                let before = g.nodes.len();
                let result = check(&env, &mut g, *r, objects[object], &mut quiet()).unwrap();
                if let Some(answer) = result.answer {
                    assert_eq!(answer.status, Decision::Established);
                    assert!(answer.reasons.is_empty());
                    assert!(g.nodes[before..].iter().all(|n| {
                        n.support
                            .iter()
                            .all(|f| f.field.as_deref() != Some("Family.Part.quantity"))
                    }));
                    let Some(Payload::Proposition { instance }) =
                        g.nodes[answer.claim.unwrap().0].payload
                    else {
                        panic!("prop")
                    };
                    let Some(Payload::LawInstance { body: source, .. }) =
                        g.nodes[instance.0].payload
                    else {
                        panic!("instance")
                    };
                    let Some(Payload::Evaluation { parts, .. }) =
                        &g.nodes[answer.outputs["evaluation"].0].payload
                    else {
                        panic!("eval")
                    };
                    let guard = parts[0].children[0];
                    let mut forged = g.nodes[guard.0].clone();
                    let Some(Payload::Evaluation {
                        expression, parts, ..
                    }) = &mut forged.payload
                    else {
                        panic!("guard")
                    };
                    let old = *expression;
                    *expression = source;
                    let Some(Payload::Expression { location, .. }) = &g.nodes[source.0].payload
                    else {
                        panic!("source")
                    };
                    parts[0].location = location.clone();
                    for r in &mut forged.arguments {
                        if *r == old {
                            *r = source
                        }
                    }
                    let mut active = copy_graph(&g, &quiet());
                    active.active = g.contexts[guard.0];
                    assert!(env.validate(&active, &forged).is_err(), "{body}");
                    let origin = frames::origin(&g, *r).unwrap().unwrap();
                    let declaration = &p.inputs().law().declarations[&origin.declaration];
                    let request = active.requests[0].clone();
                    let before = active.nodes.len();
                    assert!(
                        crate::observed::evaluate::instance_expression(
                            &env,
                            &mut active,
                            &mut quiet(),
                            &request,
                            declaration,
                            result.instance.unwrap(),
                            origin.body
                        )
                        .is_err()
                    );
                    assert_eq!(active.nodes.len(), before);
                    count += 1;
                }
            }
        }
        assert_eq!(count, 4);
        replay(&p, &g).unwrap();
    }
}
#[test]
fn native_self_equality_proposition_keeps_unobserved_operands_and_normalization() {
    let p = from_inputs(fixture::inputs(
        true,
        false,
        "law required reflexive(c:Part):c.quantity=c.quantity;",
    ));
    let (mut g, a, objects) = start(&p);
    let rs = rows(&p, &mut g, a);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for (object, rs) in rs.iter().enumerate() {
        for r in rs {
            let person = who(&g, *r);
            let result = check(&env, &mut g, *r, objects[object], &mut quiet()).unwrap();
            if let Some(answer) = result.answer {
                assert_eq!(answer.status, Decision::Established);
                if person == "q" {
                    assert!(answer.scope.completions);
                    let evaluation = answer.outputs["evaluation"];
                    let Some(Payload::Evaluation { parts, value, .. }) =
                        &g.nodes[evaluation.0].payload
                    else {
                        panic!("eval")
                    };
                    assert_eq!(g.boolean(*value).unwrap(), Some(true));
                    assert_eq!(parts[0].children.len(), 2);
                    for child in &parts[0].children {
                        let Some(Payload::Evaluation { value, .. }) = &g.nodes[child.0].payload
                        else {
                            panic!("child")
                        };
                        assert!(value.is_none());
                    }
                    assert!(!g.nodes[evaluation.0].evidence.is_empty());
                    assert!(!answer.evidence.is_empty());
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 2);
    replay(&p, &g).unwrap();
}
#[test]
fn native_law_proposition_roles_and_original_declarations_are_preserved() {
    let p = prepared(
        "law required zero(c:Part):c.quantity=0;law optional nonnegative(c:Part):c.quantity>=0;",
    );
    let (mut g, a, objects) = start(&p);
    let rs = rows(&p, &mut g, a);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut count = 0;
    for (object, rs) in rs.iter().enumerate() {
        for r in rs {
            let person = who(&g, *r);
            let origin = frames::origin(&g, *r).unwrap().unwrap();
            let optional = origin.declaration.ends_with(".nonnegative");
            let result = check(&env, &mut g, *r, objects[object], &mut quiet()).unwrap();
            if let Some(answer) = result.answer {
                assert_eq!(
                    answer.status,
                    if optional || person == "p" {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
                let Some(Payload::Proposition { instance }) =
                    g.nodes[answer.claim.unwrap().0].payload
                else {
                    panic!("prop")
                };
                let Some(Payload::LawInstance { name, role, .. }) = &g.nodes[instance.0].payload
                else {
                    panic!("instance")
                };
                assert_eq!(name, &origin.declaration);
                assert_eq!(*role, if optional { "optional" } else { "required" });
                count += 1;
            }
        }
    }
    assert_eq!(count, 8);
    replay(&p, &g).unwrap();
}
