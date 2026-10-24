use super::*;
use crate::observed::input::CheckedInputs;
use crate::observed::{
    PreparedObserved,
    control::{Limits, Usage},
    request::resolve_native_for_test,
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/polynomial_law_family_data.rs");
}
#[allow(dead_code)]
mod finite_fixture {
    include!("../../tests/common/finite_law_family_data.rs");
}
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn prepared(inputs: Arc<CheckedInputs>, root: &str) -> PreparedObserved {
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), &[&ask], &mut quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, NodeRef) {
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = super::super::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut quiet(),
    )
    .unwrap();
    (g, a.reference)
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
fn replay(p: &PreparedObserved, g: &Graph) -> Result<(), ValidationFailure> {
    let env = Environment::with_prepared(p, &mut quiet())?;
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
        env.validate(&prefix, n)?;
        prefix.push(n.clone())?;
    }
    Ok(())
}
fn table(p: &PreparedObserved) -> (Graph, Arc<Table>) {
    let (mut g, a) = start(p);
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let t = crate::observed::law_table::retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    (g, Arc::new(t))
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let D::PredicateInvariant(d) = &v.data else {
        panic!()
    };
    d
}
fn field(g: &Graph, r: NodeRef, name: &str) -> Option<Json> {
    let Json::Obj(ref w) = data(g, r).wire() else {
        panic!()
    };
    w.get(name).cloned()
}
fn reference(v: &Json) -> NodeRef {
    let Json::Obj(v) = v else { panic!() };
    let Json::Str(n) = &v["node"] else { panic!() };
    NodeRef(n.strip_prefix('n').unwrap().parse().unwrap())
}
fn value(g: &Graph, r: NodeRef) -> Option<bool> {
    field(g, r, "value").map(|v| g.boolean(Some(reference(&v))).unwrap().unwrap())
}
fn named(g: &Graph, r: NodeRef, name: &str) -> String {
    let o = frames::origin(g, r).unwrap().unwrap();
    let b = o.bindings.iter().find(|b| b.name == name).unwrap();
    let Scalar::Subject { subject, .. } = g.scalar(b.value).unwrap() else {
        panic!()
    };
    subject.clone()
}
#[test]
fn original_roles_instances_all_objects_and_conditional_boolean_values_are_preserved() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "view ahead(c:Part):Z=c.quantity;law required zero(c:Part):c.quantity=0;law optional same(c:Part,d:Part):c.quantity=d.quantity;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &mut quiet()).unwrap();
    assert_eq!(out.len(), 6);
    assert_eq!(out[0].instance, 2);
    assert!(out.iter().any(|i| i.instance >= 6));
    assert_eq!(t.objects.len(), 3);
    let mut required = 0;
    let mut optional = 0;
    for inv in &out {
        assert_eq!(inv.evaluations.len(), 3);
        assert_eq!(
            g.get(inv.invariant).unwrap().ty,
            NodeType::Construction(T::Invariant)
        );
        assert_eq!(
            field(&g, inv.invariant, "kind"),
            Some(Json::str("predicate"))
        );
        assert_eq!(field(&g, inv.invariant, "instance"), Some(inv.law.wire()));
        assert!(field(&g, inv.invariant, "selected").is_none());
        let Some(Payload::Construction(v)) = &g.get(inv.law).unwrap().payload else {
            panic!()
        };
        let Json::Obj(ref w) = v.wire() else { panic!() };
        let o = frames::origin(&g, inv.law).unwrap().unwrap();
        let c = named(&g, inv.law, "c");
        let same = o.declaration.ends_with(".same");
        if same {
            assert_eq!(w["role"], Json::str("optional"));
            optional += 1;
        } else {
            assert_eq!(w["role"], Json::str("required"));
            required += 1;
        }
        for (object, e) in inv.evaluations.iter().enumerate() {
            let matches = object == 0
                || (c == if object == 1 { "p" } else { "q" }
                    && (!same || named(&g, inv.law, "d") == c));
            let expected = !matches
                || if same {
                    c == named(&g, inv.law, "d")
                } else {
                    c == "p"
                };
            assert_eq!(value(&g, *e), Some(expected));
            assert_eq!(
                field(&g, *e, "environment"),
                Some(t.objects[object].architecture.wire())
            );
            let expression = reference(&field(&g, *e, "expression").unwrap());
            let Some(Payload::Construction(v)) = &g.get(expression).unwrap().payload else {
                panic!()
            };
            let Json::Obj(ref w) = v.wire() else { panic!() };
            assert_eq!(w["kind"], Json::str("object_reading"));
            assert_eq!(w["object"], t.objects[object].object.wire());
            assert_eq!(w["declaration"], Json::str(&o.declaration));
        }
    }
    assert_eq!((required, optional), (2, 4));
    replay(&p, &g).unwrap();
}
#[test]
fn parameter_function_keeps_all_guarded_rows_and_suppresses_the_forall_aggregate_value() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &mut quiet()).unwrap();
    assert_eq!(out.len(), 2);
    for inv in &out {
        assert_eq!(
            field(&g, inv.invariant, "parameters"),
            Some(Json::Arr(vec![Json::obj([
                ("name", Json::str("b")),
                ("type", Type::Bool.wire())
            ])]))
        );
        let c = named(&g, inv.law, "c");
        for (object, e) in inv.evaluations.iter().enumerate() {
            assert_eq!(value(&g, *e), None);
            let Json::Arr(ref parts) = field(&g, *e, "parts").unwrap() else {
                panic!()
            };
            let Json::Obj(part) = &parts[0] else { panic!() };
            let native =
                t.objects[object].evaluations[out.iter().position(|x| x.law == inv.law).unwrap()];
            let Some(Payload::Construction(v)) = &g.get(native).unwrap().payload else {
                panic!()
            };
            let D::LawFamily(d) = &v.data else { panic!() };
            let super::super::law_family::Kind::Evaluation { rows, .. } = &d.kind else {
                panic!()
            };
            assert_eq!(rows.len(), 2);
            assert_eq!(
                part["children"],
                refs(&rows.iter().map(|r| r.evaluation).collect::<Vec<_>>())
            );
            let outside = object != 0 && c != if object == 1 { "p" } else { "q" };
            assert_eq!(
                field(&g, *e, "applicability"),
                Some(Json::str(if outside {
                    "not_applicable"
                } else {
                    "applicable"
                }))
            );
            for (i, row) in rows.iter().enumerate() {
                assert_eq!(
                    g.get(row.proposition)
                        .unwrap()
                        .judgment
                        .as_ref()
                        .unwrap()
                        .status,
                    if outside || i == 0 || c == "p" {
                        Decision::Established
                    } else {
                        Decision::Refuted
                    }
                );
            }
        }
    }
    replay(&p, &g).unwrap();
}
#[test]
fn missing_quantity_and_false_guard_keep_the_actual_slots_and_vacuous_truth_distinct() {
    let p = prepared(
        fixture::inputs(
            true,
            false,
            "law required zero(c:Part):c.quantity=0;law optional skip(c:Part) when false:forall k:Z.k=0;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &mut quiet()).unwrap();
    assert_eq!(out.len(), 4);
    let mut missing = 0;
    for inv in &out {
        let o = frames::origin(&g, inv.law).unwrap().unwrap();
        let c = named(&g, inv.law, "c");
        for (object, e) in inv.evaluations.iter().enumerate() {
            let applies = object == 0 || c == if object == 1 { "p" } else { "q" };
            if o.declaration.ends_with(".skip") {
                assert_eq!(value(&g, *e), Some(true));
                assert_eq!(
                    field(&g, *e, "applicability"),
                    Some(Json::str("not_applicable"))
                );
            } else if c == "q" && applies {
                assert_eq!(value(&g, *e), None);
                assert!(
                    g.get(*e)
                        .unwrap()
                        .reasons
                        .iter()
                        .flat_map(|r| &r.missing)
                        .any(|f| f.subject == "q"
                            && f.field.as_deref() == Some("Family.Part.quantity"))
                );
                missing += 1;
            } else {
                assert_eq!(value(&g, *e), Some(true));
            }
        }
    }
    assert_eq!(missing, 2);
    replay(&p, &g).unwrap();
}
#[test]
fn private_records_and_source_tables_reject_other_instances_objects_and_coverage_changes() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required first(c:Part):c.quantity=0;law optional second(c:Part):c.quantity=0;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &mut quiet()).unwrap();
    assert_eq!(out.len(), 4);
    let last = out.last().unwrap();
    for target in [last.evaluations[0], last.invariant] {
        for mode in 0..14 {
            let mut bad = copy_graph(&g, &quiet());
            let n = &mut bad.nodes[target.0];
            match mode {
                0 => {
                    n.arguments.pop();
                }
                1 => n.arguments.reverse(),
                2 => n.support.clear(),
                3 => n.scope = Scope::default(),
                4 => {
                    n.judgment = Some(Judgment {
                        status: Decision::Established,
                        evidence: vec![],
                        reasons: vec![],
                    })
                }
                5 => n.ty = NodeType::Construction(T::SignatureAxis),
                _ => {
                    let Some(Payload::Construction(v)) = &mut n.payload else {
                        panic!()
                    };
                    let D::PredicateInvariant(d) = &mut v.data else {
                        panic!()
                    };
                    let s = Arc::make_mut(&mut d.source);
                    match mode {
                        6 => {
                            let Json::Obj(w) = &mut d.part.wire else {
                                panic!()
                            };
                            w.insert("instance".into(), out[0].law.wire());
                        }
                        7 => {
                            let Json::Obj(w) = &mut d.part.wire else {
                                panic!()
                            };
                            w.remove(if w.contains_key("values") {
                                "values"
                            } else {
                                "parts"
                            });
                        }
                        8 => {
                            d.part.arguments.push(target);
                        }
                        9 => s.base += 1,
                        10 => {
                            Arc::make_mut(&mut s.table).indices.reverse();
                        }
                        11 => {
                            Arc::make_mut(&mut s.table).objects.reverse();
                        }
                        12 => {
                            s.outputs.pop();
                        }
                        13 => {
                            let column = s.table.indices.len() - 1;
                            let t = Arc::make_mut(&mut s.table);
                            t.objects[0].evaluations[column] = t.objects[0].evaluations[0];
                            t.objects[0].holds[column] = t.objects[0].holds[0];
                        }
                        _ => unreachable!(),
                    }
                    s.parts[d.index] = d.part.clone();
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
    let foreign = prepared(
        fixture::inputs(
            false,
            false,
            "law required first(c:Part):c.quantity=1;law optional second(c:Part):c.quantity=0;",
        ),
        "root",
    );
    let fresh = Environment::with_prepared(&foreign, &mut quiet()).unwrap();
    assert!(
        fresh
            .recheck_node(&g, g.get(last.invariant).unwrap(), last.invariant.0)
            .is_err()
    );
    replay(&p, &g).unwrap();
}
#[test]
fn a_later_build_reads_saved_predicates_without_regenerating_or_rebinding_them() {
    let mut p = prepared(
        fixture::inputs(false, false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    p.requests = resolve_native_for_test(
        p.inputs.law(),
        p.inputs.archmap(),
        &[
            "b=build(Selected,on=@v/root)",
            "later=build(Selected,on=@v/r2)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &mut quiet()).unwrap();
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
    for inv in &out {
        for r in inv.evaluations.iter().copied().chain([inv.invariant]) {
            assert!(fresh.recheck_node(&g, g.get(r).unwrap(), r.0).is_ok());
        }
    }
    let before = copy_graph(&g, &quiet());
    assert!(retain(&env, &mut g, t.clone(), &mut quiet()).is_err());
    assert_eq!(g.nodes, before.nodes);
    assert_eq!(g.contexts, before.contexts);
    assert_eq!(g.instances, before.instances);
    assert_eq!(g.active, before.active);
    for mode in 0..3 {
        let mut bad = copy_graph(&g, &quiet());
        let r = out[0].invariant;
        match mode {
            0 => bad.requests[0].id = "foreign".into(),
            1 => bad.contexts[r.0].request = 1,
            2 => bad.contexts[r.0].frame = Some(0),
            _ => unreachable!(),
        };
        let fresh = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(
            fresh.recheck_node(&bad, bad.get(r).unwrap(), r.0).is_err(),
            "mode{mode}"
        );
    }
}
#[test]
fn four_stops_keep_exact_completed_predicate_evaluation_and_invariant_prefixes() {
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let (initial, t) = table(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let native = Rc::new(RefCell::new(vec![]));
    let points = native.clone();
    let mut c = Control::new(Limits::default(), move |checkpoint| {
        seen.set(seen.get() + 1);
        if checkpoint == Checkpoint::NativeResultNode {
            points.borrow_mut().push(seen.get());
        }
        Usage::default()
    });
    let mut full = copy_graph(&initial, &c);
    let out = retain(&env, &mut full, t.clone(), &mut c).unwrap();
    assert_eq!(out.len(), 4);
    let total = count.get();
    assert!(total > 20);
    assert!(native.borrow().len() > 2);
    let early = native.borrow()[1];
    let mut partial = false;
    for mode in 0..4 {
        for at in [1, early, total / 2, total - 3, total - 2, total - 1, total] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |_| {
                    seen.set(seen.get() + 1);
                    let hit = seen.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(mode == 0 && hit),
                        memory_mib: u128::from(mode == 1 && hit),
                        signal: if hit && mode == 2 {
                            Some(crate::result::Signal::Int)
                        } else if hit && mode == 3 {
                            Some(crate::result::Signal::Term)
                        } else {
                            None
                        },
                    }
                },
            );
            let mut g = copy_graph(&initial, &c);
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            let result = retain(&env, &mut g, t.clone(), &mut c);
            assert!(
                matches!(result, Err(ValidationFailure::Stop(_))),
                "mode{mode}/at{at}: {result:?}"
            );
            assert_eq!(g.active, initial.active);
            assert!(env.architecture_ref().is_none());
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
            replay(&p, &g).unwrap();
        }
    }
    assert!(partial);
}
