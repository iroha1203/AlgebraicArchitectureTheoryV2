use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/polynomial_law_family_data.rs");
}
use archsig_common::control::quiet;
fn prepared(body: &str) -> PreparedObserved {
    let inputs = fixture::inputs(false, false, body);
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
fn initial(p: &PreparedObserved) -> (Graph, NodeRef, Vec<NodeRef>) {
    let c = quiet();
    let env = Environment::with_prepared(p, &c).unwrap();
    let mut g = Graph::new(&c);
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &c,
    )
    .unwrap();
    assert!(a.complete);
    let components = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a.reference,
        &c,
    )
    .unwrap()
    .unwrap();
    (g, a.reference, components.architectures)
}
#[test]
fn native_polynomial_law_rows_use_the_regular_evaluator_and_each_object_environment() {
    let p = prepared("law required zero(c:Part):c.quantity=0;");
    let (mut g, a, objects) = initial(&p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap();
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut completed = 0;
    for (object, d) in ds.iter().enumerate() {
        for reading in &d.readings {
            let row = origin(&g, reading.instance).unwrap().unwrap();
            let who = match g.scalar(row.bindings[0].value).unwrap() {
                Scalar::Subject { subject, .. } => subject.clone(),
                _ => panic!("subject"),
            };
            let applied = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            let e = evaluate(&env, &mut g, reading.instance, objects[object], &quiet()).unwrap();
            assert_eq!(e.body.is_some(), applied);
            assert_eq!(e.instance.is_some(), applied);
            if let Some(body) = e.body {
                let n = &g.nodes[body.0];
                let Some(Payload::Evaluation {
                    expression,
                    value,
                    environment,
                    ..
                }) = &n.payload
                else {
                    panic!("ordinary Evaluation")
                };
                assert_eq!(g.boolean(*value).unwrap(), Some(who == "p"));
                assert_eq!(*environment, Some(objects[object]));
                assert!(matches!(
                    g.nodes[expression.0].payload,
                    Some(Payload::Expression { .. })
                ));
                assert_eq!(g.contexts[body.0].instance, e.instance);
                completed += 1;
            }
        }
    }
    assert_eq!(completed, 4);
}

#[allow(dead_code)]
mod finite_fixture {
    include!("../../../../../tests/common/finite_law_family_data.rs");
}
fn inputs_prepared(inputs: Arc<archsig_input::input::CheckedInputs>) -> PreparedObserved {
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
fn replay(
    p: &PreparedObserved,
    source: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let env = Environment::with_prepared(p, &quiet())?;
    let mut g = Graph::new(&quiet());
    g.requests = source.requests.clone();
    g.checked_answers = source.checked_answers.clone();
    g.frames = source.frames.clone();
    g.iterations = source.iterations.clone();
    g.instances = source.instances.clone();
    g.cases = source.cases.clone();
    g.universal_witnesses = source.universal_witnesses.clone();
    for (index, node) in nodes.iter().enumerate() {
        g.active = source.contexts[index];
        env.validate(&g, node)?;
        g.push(node.clone())?;
    }
    Ok(g)
}
fn truth(g: &Graph, r: NodeRef) -> Option<bool> {
    let Some(Payload::Evaluation { value, .. }) = &g.nodes[r.0].payload else {
        panic!("Evaluation")
    };
    g.boolean(*value).unwrap()
}
fn polynomial_origins(g: &mut Graph, p: &PreparedObserved, a: NodeRef) -> Vec<Vec<NodeRef>> {
    crate::observed::polynomial_law_diagram::retain_family(g, p.shared_inputs(), a, &quiet())
        .unwrap()
        .into_iter()
        .map(|d| d.readings.iter().map(|r| r.instance).collect())
        .collect()
}
#[test]
fn native_finite_rows_keep_all_bool_bindings_in_regular_expression_evaluations() {
    let p = inputs_prepared(finite_fixture::inputs(
        false,
        "law required bit(c:Part,b:Bool):(c.quantity=0)=b;",
    ));
    let (mut g, a, objects) = initial(&p);
    let ds =
        crate::observed::finite_law_diagram::retain_family(&mut g, p.shared_inputs(), a, &quiet())
            .unwrap()
            .unwrap();
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut count = 0;
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.originals.len(), 4);
        for o in &d.originals {
            let row = origin(&g, o.row).unwrap().unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
                panic!("subject")
            };
            let who = subject.clone();
            let Scalar::Bool(bit) = g.scalar(row.bindings[1].value).unwrap() else {
                panic!("Bool")
            };
            let bit = *bit;
            let applies = object == 0 || (object == 1 && who == "p") || (object == 2 && who == "q");
            let e = evaluate(&env, &mut g, o.row, objects[object], &quiet()).unwrap();
            assert_eq!(e.body.is_some(), applies);
            if let Some(body) = e.body {
                assert_eq!(truth(&g, body), Some((who == "p") == bit));
                count += 1;
            }
        }
    }
    assert_eq!(count, 8);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_false_guard_keeps_guard_evaluation_and_never_evaluates_missing_body() {
    let p = inputs_prepared(fixture::inputs(
        true,
        false,
        "law required off(c:Part) when false:c.quantity=0;",
    ));
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let before = g.nodes.len();
    let mut guards = 0;
    for (object, rs) in rows.iter().enumerate() {
        for r in rs {
            let e = evaluate(&env, &mut g, *r, objects[object], &quiet()).unwrap();
            assert!(e.body.is_none());
            if let Some(guard) = e.guard {
                assert_eq!(truth(&g, guard), Some(false));
                guards += 1;
            }
        }
    }
    assert_eq!(guards, 4);
    for n in &g.nodes[before..] {
        assert!(
            !n.support
                .iter()
                .any(|f| f.field.as_deref() == Some("Family.Part.quantity"))
        );
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_missing_guard_and_body_keep_unknown_values_and_actual_missing_locations() {
    let p = inputs_prepared(fixture::inputs(
        true,
        false,
        "law required guarded(c:Part) when c.quantity=0:c.quantity=1;",
    ));
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut missing = 0;
    for (object, rs) in rows.iter().enumerate() {
        for r in rs {
            let row = origin(&g, *r).unwrap().unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
                panic!("subject")
            };
            let who = subject.clone();
            let e = evaluate(&env, &mut g, *r, objects[object], &quiet()).unwrap();
            if let Some(body) = e.body {
                if who == "q" {
                    assert_eq!(truth(&g, body), None);
                    assert_eq!(truth(&g, e.guard.unwrap()), None);
                    assert!(g.nodes[body.0].reasons.iter().any(|r| {
                        r.missing.iter().any(|f| {
                            f.subject == "q" && f.field.as_deref() == Some("Family.Part.quantity")
                        })
                    }));
                    missing += 1;
                } else {
                    assert_eq!(truth(&g, e.guard.unwrap()), Some(true));
                    assert_eq!(truth(&g, body), Some(false));
                }
            }
        }
    }
    assert_eq!(missing, 2);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_tuple_body_preserves_both_typed_operand_evaluations_and_source_occurrences() {
    let p = inputs_prepared(fixture::inputs(
        false,
        true,
        "law required pair(c:Part):c.quantity=(0,rat(1,2));",
    ));
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut count = 0;
    for (object, rs) in rows.iter().enumerate() {
        for r in rs {
            let row = origin(&g, *r).unwrap().unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
                panic!("subject")
            };
            let who = subject.clone();
            let e = evaluate(&env, &mut g, *r, objects[object], &quiet()).unwrap();
            if let Some(body) = e.body {
                assert_eq!(truth(&g, body), Some(who == "p"));
                let Some(Payload::Evaluation {
                    expression, parts, ..
                }) = &g.nodes[body.0].payload
                else {
                    panic!("Evaluation")
                };
                let Some(Payload::Expression {
                    location: archsig_common::issue::Location::Law { span },
                    bindings,
                    ..
                }) = &g.nodes[expression.0].payload
                else {
                    panic!("source")
                };
                assert_eq!(*span, p.inputs().law().exprs()[row.body].span);
                assert_eq!(bindings.len(), 1);
                assert_eq!(parts[0].children.len(), 2);
                for child in &parts[0].children {
                    assert_eq!(
                        g.nodes[child.0].ty,
                        NodeType::Evaluation(Type::Tuple(vec![Type::Z, Type::Q]))
                    );
                }
                count += 1;
            }
        }
    }
    assert_eq!(count, 4);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_term_path_and_unbounded_quantifiers_keep_original_domains_and_instance_contexts() {
    for (body, expected) in [
        (
            "forall f in list<Term<(Z)->Z>>[fn(x:Z)=>x,fn(x:Z)=>x+1].f(0)>=0",
            true,
        ),
        ("forall k:Z.k=0", false),
    ] {
        let p = prepared(&format!("law required quantified(c:Part):{body};"));
        let (mut g, a, objects) = initial(&p);
        let rows = polynomial_origins(&mut g, &p, a);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut count = 0;
        for r in &rows[0] {
            let e = evaluate(&env, &mut g, *r, objects[0], &quiet()).unwrap();
            let b = e.body.unwrap();
            assert_eq!(truth(&g, b), Some(expected));
            assert!(
                g.nodes[b.0]
                    .scope
                    .quantifiers
                    .iter()
                    .any(|q| q.name == if body.contains("forall k") { "k" } else { "f" })
            );
            count += 1;
        }
        assert_eq!(count, 2);
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn native_law_frames_reject_parameter_domain_context_and_origin_forgery() {
    let p = prepared(
        "law required same(c:Part):c.quantity=c.quantity;law optional other(c:Part):true;",
    );
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let e = evaluate(&env, &mut g, rows[0][0], objects[0], &quiet()).unwrap();
    let index = e.instance.unwrap();
    let record = g.instances[index].clone();
    let (_, member) = frame_value(&g, record.member).unwrap();
    let Kind::Member { bindings, .. } = &member.kind else {
        panic!("member")
    };
    let parameter = bindings[0];
    let mut nodes = g.nodes.clone();
    let Some(Payload::Construction(v)) = &mut nodes[parameter.0].payload else {
        panic!("native")
    };
    let D::LawFrame(d) = &mut v.data else {
        panic!("frame")
    };
    let Kind::Parameter { value, .. } = &mut d.kind else {
        panic!()
    };
    *value = Scalar::Bool(true);
    assert!(replay(&p, &g, &nodes).is_err(), "frame mutation");
    let mut bad = prefix_graph(&g, &quiet());
    bad.instances[index].source = rows[0][1];
    assert!(replay(&p, &bad, &bad.nodes).is_err(), "record mutation");
    assert!(evaluate(&env, &mut g, rows[1][0], objects[0], &quiet()).is_err());
    replay(&p, &g, &g.nodes).unwrap();
}
fn prefix_graph(g: &Graph, c: &Control) -> Graph {
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
#[test]
fn native_guard_order_and_false_guard_cannot_be_bypassed_by_direct_body_evaluation() {
    for guard in ["true", "false"] {
        let p = prepared(&format!(
            "law required guarded(c:Part) when {guard}:c.quantity=0;"
        ));
        let (mut g, a, objects) = initial(&p);
        let rows = polynomial_origins(&mut g, &p, a);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let e = evaluate(&env, &mut g, rows[0][0], objects[0], &quiet()).unwrap();
        let index = e.instance.unwrap();
        let row = origin(&g, e.origin).unwrap().unwrap();
        let request = g.requests[0].clone();
        let decl = &p.inputs().law().declarations()[&row.declaration];
        if guard == "false" {
            let before = g.nodes.len();
            assert!(
                super::super::evaluate::instance_expression(
                    &env,
                    &mut g,
                    &quiet(),
                    &request,
                    decl,
                    index,
                    row.body
                )
                .is_err()
            );
            assert_eq!(g.nodes.len(), before);
        } else {
            let domain = g.instances[index].domain;
            let mut early = prefix_graph(&g, &quiet());
            early.nodes.truncate(domain.0 + 1);
            early.contexts.truncate(domain.0 + 1);
            let before = early.nodes.len();
            assert!(
                super::super::evaluate::instance_expression(
                    &env,
                    &mut early,
                    &quiet(),
                    &request,
                    decl,
                    index,
                    row.body
                )
                .is_err()
            );
            assert_eq!(early.nodes.len(), before);
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}
#[test]
fn native_named_view_calls_use_the_same_instance_object_and_original_call_frames() {
    let p = prepared("view plus(c:Part):Z=c.quantity+1;law required chosen(c:Part):plus(c)=1;");
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut count = 0;
    for (object, rs) in rows.iter().enumerate() {
        for r in rs {
            let row = origin(&g, *r).unwrap().unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(row.bindings[0].value).unwrap() else {
                panic!()
            };
            let who = subject.clone();
            let e = evaluate(&env, &mut g, *r, objects[object], &quiet()).unwrap();
            if let Some(body) = e.body {
                assert_eq!(truth(&g, body), Some(who == "p"));
                assert!(
                    g.contexts
                        .iter()
                        .any(|c| c.instance == e.instance && c.frame.is_some())
                );
                count += 1;
            }
        }
    }
    assert_eq!(count, 4);
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_unanchored_helpers_stay_out_of_axes_and_symbolic_parameters_keep_their_domain() {
    let p = prepared("law required always():true;");
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    // root/owned参照へ適用しないhelperは、独立の観測軸へ追加しない。
    assert!(rows.iter().all(Vec::is_empty));
    assert_eq!(objects.len(), 3);
    replay(&p, &g, &g.nodes).unwrap();
    let p = prepared("law required unbounded(c:Part,k:Z):c.quantity=k;");
    let (mut g, a, objects) = initial(&p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &quiet(),
    )
    .unwrap();
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    for (object, d) in ds.iter().enumerate() {
        assert!(d.unavailable.is_none());
        for o in &d.originals {
            assert!(o.parameters.iter().any(|(n, t)| n == "k" && t == &Type::Z));
            assert!(o.row.is_none(), "無限域を有限の代入行にしない");
            let applies = origin(&g, o.reference).unwrap().unwrap().ready;
            let before = g.nodes.len();
            let e = evaluate(&env, &mut g, o.reference, objects[object], &quiet()).unwrap();
            assert_eq!(e.instance.is_some(), applies);
            assert_eq!(e.body.is_some(), applies);
            assert!(e.guard.is_none());
            if !applies {
                assert_eq!(g.nodes.len(), before);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn native_numeric_law_frames_evaluate_the_requested_guard_and_body() {
    for guard in ["true", "false", "k=k"] {
        let p = prepared(&format!(
            "law required family(c:Part,k:Z) when {guard}:k=k;"
        ));
        let (mut g, a, objects) = initial(&p);
        let rows = polynomial_origins(&mut g, &p, a);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let mut checked = 0;
        for (object, rows) in rows.iter().enumerate() {
            for row in rows {
                let e = evaluate(&env, &mut g, *row, objects[object], &quiet()).unwrap();
                if let Some(actual) = e.guard {
                    assert_eq!(truth(&g, actual), Some(guard != "false"));
                    assert_eq!(e.body.is_some(), guard != "false");
                    if let Some(body) = e.body {
                        assert_eq!(truth(&g, body), Some(true));
                    }
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 4);
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn native_law_expression_interrupt_keeps_exact_completed_dag_prefix_and_restore_context() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared("law required zero(c:Part):c.quantity=0;");
    let (mut initial, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut initial, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let root = rows[0][0];
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let probe = Control::new(move |point| {
        if point == Checkpoint::Expression {
            count.set(count.get() + 1)
        }
        None
    });
    let mut complete = prefix_graph(&initial, &probe);
    evaluate(&env, &mut complete, root, objects[0], &probe).unwrap();
    let total = seen.get();
    assert!(total >= 3);
    let mut retained_evaluation = false;
    let mut retained_complete_post_stop = false;
    for at in 1..=total {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::Expression {
                count.set(count.get() + 1)
            }
            let stop = count.get() >= at;
            stop.then_some(archsig_input::result::Signal::Int)
        });
        let mut g = prefix_graph(&initial, &c);
        assert!(matches!(
            evaluate(&env, &mut g, root, objects[0], &c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.active, initial.active);
        assert!(env.state.architecture_ref().is_none());
        assert!(g.nodes.len() >= initial.nodes.len() && g.nodes.len() <= complete.nodes.len());
        assert_eq!(g.nodes.len(), g.contexts.len());
        retained_complete_post_stop |= g.nodes.len() == complete.nodes.len();
        retained_evaluation |= g.nodes.len() < complete.nodes.len()
            && g.nodes[initial.nodes.len()..]
                .iter()
                .any(|n| matches!(n.payload, Some(Payload::Evaluation { .. })));
        for (index, node) in g.nodes.iter().enumerate() {
            let other = &complete.nodes[index];
            assert_eq!(
                (
                    &node.ty,
                    &node.rule,
                    &node.arguments,
                    &node.support,
                    &node.scope,
                    &node.reasons
                ),
                (
                    &other.ty,
                    &other.rule,
                    &other.arguments,
                    &other.support,
                    &other.scope,
                    &other.reasons
                )
            );
            match (&node.payload, &other.payload) {
                (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                    assert_eq!(a.wire(), b.wire())
                }
                _ => assert_eq!(node, other),
            }
            assert_eq!(g.contexts[index], complete.contexts[index]);
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
    assert!(retained_evaluation);
    assert!(retained_complete_post_stop);
}

#[test]
fn native_reference_quantifiers_use_each_objects_actual_domain_even_for_identical_bindings() {
    let p = prepared("law required all(c:Part):forall x:Part.x.quantity=0;");
    let (mut g, a, objects) = initial(&p);
    let rows = polynomial_origins(&mut g, &p, a);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut evaluated = 0;
    for (object, rs) in rows.iter().enumerate() {
        for r in rs {
            let e = evaluate(&env, &mut g, *r, objects[object], &quiet()).unwrap();
            if let Some(body) = e.body {
                assert_eq!(truth(&g, body), Some(object == 1));
                let q = g.nodes[body.0]
                    .scope
                    .quantifiers
                    .iter()
                    .find(|q| q.name == "x")
                    .unwrap();
                let Some(Payload::Domain { ty, elements }) = &g.nodes[q.domain.unwrap().0].payload
                else {
                    panic!("actual Domain")
                };
                assert_eq!(ty, &Type::Ref("Family.Part".into()));
                let names = elements
                    .iter()
                    .map(|r| match g.scalar(*r).unwrap() {
                        Scalar::Subject { subject, .. } => subject.as_str(),
                        _ => panic!("subject"),
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    names,
                    if object == 0 {
                        vec!["p", "q"]
                    } else if object == 1 {
                        vec!["p"]
                    } else {
                        vec!["q"]
                    }
                );
                evaluated += 1;
            }
        }
    }
    assert_eq!(evaluated, 4);
    replay(&p, &g, &g.nodes).unwrap();
}
