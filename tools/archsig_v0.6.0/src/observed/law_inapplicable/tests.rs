use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
#[allow(dead_code)]
mod finite_fixture {
    include!("../../../tests/common/finite_law_reading_data.rs");
}
use crate::control::quiet;
fn prepared(inputs: Arc<crate::input::CheckedInputs>) -> PreparedObserved {
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
fn start(p: &PreparedObserved) -> (Graph, NodeRef, Vec<NodeRef>) {
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
    (g, a.reference, objects.architectures)
}
fn replay(p: &PreparedObserved, source: &Graph) -> Result<(), ValidationFailure> {
    let env = Environment::with_prepared(p, &quiet())?;
    let mut g = Graph::new(&quiet());
    g.requests = source.requests.clone();
    g.frames = source.frames.clone();
    g.instances = source.instances.clone();
    g.iterations = source.iterations.clone();
    g.cases = source.cases.clone();
    g.universal_witnesses = source.universal_witnesses.clone();
    g.checked_answers = source.checked_answers.clone();
    for (i, n) in source.nodes.iter().enumerate() {
        g.active = source.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(())
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::OutsideLaw(d) = &v.data else {
        panic!("outside")
    };
    d
}
fn assert_outside(g: &Graph, a: &Answer, origin: NodeRef, architecture: NodeRef) {
    assert_eq!(a.status, Decision::Established);
    assert!(a.evidence.is_empty());
    assert!(a.reasons.is_empty());
    let e = a.outputs["evaluation"];
    let q = a.claim.unwrap();
    assert_eq!(a.outputs["proposition"], q);
    assert_eq!(g.nodes[e.0].ty, NodeType::Evaluation(Type::Bool));
    assert_eq!(g.nodes[q.0].ty, NodeType::Proposition);
    let d = data(g, e);
    assert_eq!(d.origin, origin);
    assert_eq!(d.architecture, architecture);
    let Kind::Evaluation { value } = d.kind else {
        panic!("evaluation")
    };
    assert_eq!(g.boolean(Some(value)).unwrap(), Some(true));
    let Json::Obj(ref w) = d.wire() else {
        panic!("record")
    };
    assert_eq!(w["applicability"], Json::str("not_applicable"));
    let Json::Arr(parts) = &w["parts"] else {
        panic!("parts")
    };
    assert_eq!(parts.len(), 1);
    let Json::Obj(body) = &parts[0] else {
        panic!("body")
    };
    assert_eq!(body["children"], Json::Arr(vec![]));
    assert!(!body.contains_key("value"));
    assert!(!body.contains_key("residual"));
    assert!(matches!(data(g,q).kind,Kind::Proposition {evaluation} if evaluation==e));
    assert_eq!(
        g.nodes[q.0].judgment.as_ref().unwrap().status,
        Decision::Established
    );
    let wire = g.nodes[q.0].wire(q.0, &g.nodes[..q.0]);
    let Json::Obj(ref node) = wire else {
        panic!("node record")
    };
    let Json::Obj(ref payload) = node["value"] else {
        panic!("proposition record")
    };
    assert_eq!(
        payload.keys().map(String::as_str).collect::<Vec<_>>(),
        vec!["operands", "predicate", "quantifiers"]
    );
    assert_eq!(payload["predicate"], Json::str("law_holds"));
    assert_eq!(payload["operands"], Json::Arr(vec![origin.wire()]));
    let Json::Obj(ref scope) = node["scope"] else {
        panic!("scope record")
    };
    assert_eq!(payload["quantifiers"], scope["quantifiers"]);
}
#[test]
fn polynomial_outside_law_keeps_original_rows_roles_and_unread_body_in_every_object() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, a, objects) = start(&p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap();
    let mut templates = 0;
    let mut rows = 0;
    for (object, d) in ds.iter().enumerate() {
        for o in &d.originals {
            let row = frames::origin(&g, o.reference).unwrap().unwrap();
            let before = g.nodes.len();
            let answer = check(&env, &mut g, o.reference, objects[object], &quiet()).unwrap();
            assert_eq!(answer.is_some(), row.outside);
            if let Some(answer) = answer {
                assert!(!row.ready);
                assert!(!row.body_allowed);
                assert_eq!(row.bindings.len(), 1);
                assert!(
                    matches!(g.scalar(row.bindings[0].value).unwrap(), Scalar::Subject { subject, .. } if subject == if object == 1 { "q" } else { "p" })
                );
                assert_outside(&g, &answer, o.reference, objects[object]);
                assert_eq!(g.nodes.len(), before + 3);
                if o.row.is_some() {
                    rows += 1;
                } else {
                    templates += 1;
                }
            } else {
                assert_eq!(g.nodes.len(), before);
            }
        }
    }
    assert_eq!((templates, rows), (4, 4));
    replay(&p, &g).unwrap();
}
#[test]
fn finite_outside_law_preserves_missing_body_without_changing_inside_evaluation() {
    let p = prepared(finite_fixture::inputs(
        true,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, a, objects) = start(&p);
    let ds =
        crate::observed::finite_law_diagram::retain_family(&mut g, p.shared_inputs(), a, &quiet())
            .unwrap()
            .unwrap();
    let mut count = 0;
    for (object, d) in ds.iter().enumerate() {
        for o in &d.originals {
            let row = frames::origin(&g, o.row).unwrap().unwrap();
            let before = g.nodes.len();
            let answer = check(&env, &mut g, o.row, objects[object], &quiet()).unwrap();
            assert_eq!(answer.is_some(), row.outside);
            if let Some(answer) = answer {
                assert_outside(&g, &answer, o.row, objects[object]);
                assert_eq!(g.nodes.len(), before + 3);
                count += 1;
            } else {
                assert_eq!(g.nodes.len(), before);
                if row.ready {
                    let ordinary = crate::observed::law_proposition::check(
                        &env,
                        &mut g,
                        o.row,
                        objects[object],
                        &quiet(),
                    )
                    .unwrap()
                    .answer
                    .unwrap();
                    let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap()
                    else {
                        panic!("subject")
                    };
                    assert_eq!(
                        ordinary.status,
                        if subject == "q" {
                            Decision::Undetermined
                        } else {
                            Decision::Established
                        }
                    );
                }
            }
        }
    }
    assert_eq!(count, 2);
    replay(&p, &g).unwrap();
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
fn outside(p: &PreparedObserved) -> (Graph, NodeRef, Vec<NodeRef>, NodeRef, NodeRef) {
    let (mut g, a, objects) = start(p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap();
    let origin = ds[1]
        .originals
        .iter()
        .find(|o| frames::origin(&g, o.reference).unwrap().unwrap().outside)
        .unwrap()
        .reference;
    let inside = ds[1]
        .originals
        .iter()
        .find(|o| frames::origin(&g, o.reference).unwrap().unwrap().ready)
        .unwrap()
        .reference;
    (g, origin, objects, a, inside)
}
#[test]
fn outside_law_rejects_inside_origin_other_object_truth_scope_binding_and_request_forgery() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, origin, objects, _, inside) = outside(&p);
    assert!(check(&env, &mut g, origin, objects[2], &quiet()).is_err());
    let a = check(&env, &mut g, origin, objects[1], &quiet())
        .unwrap()
        .unwrap();
    let e = a.outputs["evaluation"];
    let q = a.claim.unwrap();
    let Kind::Evaluation { value } = data(&g, e).kind else {
        panic!()
    };
    for mode in 0..10 {
        let mut bad = copy_graph(&g, &quiet());
        let r = if mode == 2 {
            value
        } else if mode == 3 {
            q
        } else {
            e
        };
        if mode == 3 {
            bad.nodes[r.0].judgment.as_mut().unwrap().status = Decision::Refuted;
        } else if mode == 9 {
            bad.requests[0].id = "other".into();
        } else {
            let Some(Payload::Construction(v)) = &mut bad.nodes[r.0].payload else {
                panic!()
            };
            let D::OutsideLaw(d) = &mut v.data else {
                panic!()
            };
            match mode {
                0 => d.origin = inside,
                1 => d.architecture = objects[2],
                2 => d.kind = Kind::Value(Scalar::Bool(false)),
                4 => d.body = inside,
                5 => d.bindings.clear(),
                6 => d.support.clear(),
                7 => d.scope.readings.clear(),
                8 => d.kind = Kind::Evaluation { value: q },
                _ => unreachable!(),
            }
            let args = d.arguments();
            let support = d.support.clone();
            let scope = d.scope.clone();
            bad.nodes[r.0].arguments = args;
            bad.nodes[r.0].support = support;
            bad.nodes[r.0].scope = scope;
        }
        assert!(replay(&p, &bad).is_err(), "mode {mode}");
    }
    let other = prepared(fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=1;",
    ));
    assert!(replay(&other, &g).is_err());
    replay(&p, &g).unwrap();
}
#[test]
fn outside_law_keeps_false_unknown_guard_and_unbounded_body_unread() {
    for guard in ["false", "c.quantity=0"] {
        let p = prepared(fixture::inputs(
            true,
            false,
            &format!("law required tested(c:Part) when {guard}:forall k:Z.k=0;"),
        ));
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let (mut g, origin, objects, _, _) = outside(&p);
        let before = g.nodes.len();
        let a = check(&env, &mut g, origin, objects[1], &quiet())
            .unwrap()
            .unwrap();
        assert_outside(&g, &a, origin, objects[1]);
        assert_eq!(g.nodes.len(), before + 3);
        assert!(
            g.nodes[before..]
                .iter()
                .all(|n| matches!(n.payload, Some(Payload::Construction(_))))
        );
        replay(&p, &g).unwrap();
    }
}
#[test]
fn finite_outside_law_keeps_every_boolean_binding_and_guard_independently() {
    let p = prepared(finite_fixture::inputs(
        true,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, a, objects) = start(&p);
    let ds =
        crate::observed::finite_law_diagram::retain_family(&mut g, p.shared_inputs(), a, &quiet())
            .unwrap()
            .unwrap();
    let mut values = vec![];
    for (i, d) in ds.iter().enumerate() {
        for o in &d.originals {
            let row = frames::origin(&g, o.row).unwrap().unwrap();
            let answer = check(&env, &mut g, o.row, objects[i], &quiet()).unwrap();
            assert_eq!(answer.is_some(), row.outside);
            if let Some(answer) = answer {
                assert_outside(&g, &answer, o.row, objects[i]);
                values.push((i, g.scalar(row.bindings[1].value).unwrap().clone()));
            }
        }
    }
    assert_eq!(
        values,
        vec![
            (1, Scalar::Bool(false)),
            (1, Scalar::Bool(true)),
            (2, Scalar::Bool(false)),
            (2, Scalar::Bool(true))
        ]
    );
    replay(&p, &g).unwrap();
}
#[test]
fn outside_law_interrupt_keeps_exact_completed_prefix_and_final_proposition() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let (initial, origin, objects, _, _) = outside(&p);
    let seen = Rc::new(Cell::new(0));
    let counter = seen.clone();
    let c = Control::new(move |point| {
        if point == Checkpoint::ObjectEvaluation {
            counter.set(counter.get() + 1)
        }
        None
    });
    let mut complete = copy_graph(&initial, &c);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    assert!(
        check(&env, &mut complete, origin, objects[1], &c)
            .unwrap()
            .is_some()
    );
    let total = seen.get();
    assert_eq!(total, 5);
    let mut final_retained = false;
    for at in 1..=total {
        let seen = Rc::new(Cell::new(0));
        let counter = seen.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::ObjectEvaluation {
                counter.set(counter.get() + 1)
            }
            let stop = counter.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = copy_graph(&initial, &c);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(matches!(
            check(&env, &mut g, origin, objects[1], &c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.active, initial.active);
        assert!(env.state.architecture_ref().is_none());
        assert_eq!(g.nodes, &complete.nodes[..g.nodes.len()]);
        assert_eq!(g.contexts, &complete.contexts[..g.nodes.len()]);
        final_retained |= g.nodes.len() == complete.nodes.len();
        replay(&p, &g).unwrap();
    }
    assert!(final_retained);
}

#[test]
fn outside_law_self_and_future_refs_fail_before_recursive_recheck() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, origin, objects, _, _) = outside(&p);
    let answer = check(&env, &mut g, origin, objects[1], &quiet())
        .unwrap()
        .unwrap();
    let e = answer.outputs["evaluation"];
    let mut results = vec![];
    for mode in 0..4 {
        let armed = Rc::new(Cell::new(false));
        let arm = armed.clone();
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let control = Control::new(move |point| {
            if arm.get() && point == Checkpoint::FiniteIteration {
                count.set(count.get() + 1)
            }
            (arm.get() && count.get() >= 200).then_some(crate::result::Signal::Int)
        });
        let mut bad = copy_graph(&g, &control);
        let Some(Payload::Construction(v)) = &mut bad.nodes[e.0].payload else {
            panic!()
        };
        let D::OutsideLaw(d) = &mut v.data else {
            panic!()
        };
        match mode {
            0 => d.origin = e,
            1 => d.architecture = e,
            2 => d.origin = NodeRef(e.0 + 1),
            _ => d.architecture = NodeRef(e.0 + 1),
        };
        let args = d.arguments();
        bad.nodes[e.0].arguments = args;
        let env = Environment::with_prepared(&p, &control).unwrap();
        armed.set(true);
        let result = env.recheck_node(&bad, &bad.nodes[e.0], e.0);
        results.push(result);
    }
    for (mode, result) in results.iter().enumerate() {
        assert!(
            matches!(result, Err(ValidationFailure::Internal(_))),
            "mode {mode}: should reject invalid Ref, got {result:?}"
        );
    }
}

#[test]
fn unbound_integer_parameter_keeps_its_quantifier_in_outside_propositions() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required unbounded(c:Part,k:Z):c.quantity=k;",
    ));
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let (mut g, a, objects) = start(&p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap();
    let mut original_count = 0;
    for (object, d) in ds.iter().enumerate() {
        assert!(d.unavailable.is_none());
        for o in &d.originals {
            assert!(o.parameters.iter().any(|(n, t)| n == "k" && t == &Type::Z));
            assert!(o.row.is_none(), "無限域を有限の代入行にしない");
            let outside = crate::observed::law_evaluation::origin(&g, o.reference)
                .unwrap()
                .unwrap()
                .outside;
            let before = g.nodes.len();
            let answer = check(&env, &mut g, o.reference, objects[object], &quiet()).unwrap();
            assert_eq!(answer.is_some(), outside);
            if let Some(answer) = answer {
                assert_outside(&g, &answer, o.reference, objects[object]);
                assert_eq!(
                    g.nodes[answer.claim.unwrap().0].scope.quantifiers,
                    g.nodes[o.reference.0].scope.quantifiers
                );
            } else {
                assert_eq!(g.nodes.len(), before);
            }
            original_count += 1;
        }
    }
    assert!(original_count > 0);
    replay(&p, &g).unwrap();
}
