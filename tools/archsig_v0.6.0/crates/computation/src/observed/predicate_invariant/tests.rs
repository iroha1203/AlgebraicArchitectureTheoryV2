use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
use archsig_input::input::CheckedInputs;
#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/polynomial_law_family_data.rs");
}
#[allow(dead_code)]
mod finite_fixture {
    include!("../../../../../tests/common/finite_law_family_data.rs");
}
use archsig_common::control::quiet;
fn prepared(inputs: Arc<CheckedInputs>, root: &str) -> PreparedObserved {
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests =
        resolve_native_for_test(inputs.law(), inputs.archmap(), &[&ask], &quiet()).unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn start(p: &PreparedObserved) -> (Graph, NodeRef) {
    let env = Environment::with_prepared(p, &quiet()).unwrap();
    let mut g = Graph::new(&quiet());
    g.requests = p.requests().requests().to_vec();
    let a = super::super::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &quiet(),
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
    let env = Environment::with_prepared(p, &quiet())?;
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
    let env = Environment::with_prepared(p, &quiet()).unwrap();
    let t = crate::observed::law_table::retain(&env, &mut g, p.shared_inputs(), a, &quiet())
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
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &quiet()).unwrap();
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
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &quiet()).unwrap();
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
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &quiet()).unwrap();
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
        &quiet(),
    )
    .unwrap();
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &quiet()).unwrap();
    g.active.request = 1;
    assert!(
        crate::observed::architecture_result::build(
            p.shared_inputs(),
            &env,
            &mut g,
            &p.requests().requests()[1],
            &quiet()
        )
        .unwrap()
        .complete
    );
    let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
    for inv in &out {
        for r in inv.evaluations.iter().copied().chain([inv.invariant]) {
            assert!(fresh.recheck_node(&g, g.get(r).unwrap(), r.0).is_ok());
        }
    }
    let before = copy_graph(&g, &quiet());
    assert!(retain(&env, &mut g, t.clone(), &quiet()).is_err());
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
        let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(
            fresh.recheck_node(&bad, bad.get(r).unwrap(), r.0).is_err(),
            "mode{mode}"
        );
    }
}
#[test]
fn interrupt_stops_keep_exact_completed_predicate_evaluation_and_invariant_prefixes() {
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
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let native = Rc::new(RefCell::new(vec![]));
    let points = native.clone();
    let c = Control::new(move |checkpoint| {
        seen.set(seen.get() + 1);
        if checkpoint == Checkpoint::NativeResultNode {
            points.borrow_mut().push(seen.get());
        }
        None
    });
    let mut full = copy_graph(&initial, &c);
    let out = retain(&env, &mut full, t.clone(), &c).unwrap();
    assert_eq!(out.len(), 4);
    let total = count.get();
    assert!(total > 20);
    assert!(native.borrow().len() > 2);
    let early = native.borrow()[1];
    let mut partial = false;
    for at in [early, total / 2] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let c = Control::new(move |_| {
            seen.set(seen.get() + 1);
            (seen.get() >= at).then_some(archsig_input::result::Signal::Int)
        });
        let mut g = copy_graph(&initial, &c);
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        let result = retain(&env, &mut g, t.clone(), &c);
        assert!(
            matches!(result, Err(ValidationFailure::Stop(_))),
            "at{at}: {result:?}"
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
        if at == total / 2 {
            replay(&p, &g).unwrap();
        }
    }
    assert!(partial);
}
#[test]
fn saved_table_self_and_later_references_fail_before_recursive_or_interrupted_validation() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required first(c:Part):c.quantity=0;law optional second(c:Part):c.quantity=0;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t.clone(), &quiet()).unwrap();
    let first = out[0].evaluations[0];
    let last = out.last().unwrap();
    for (target, mode) in [
        (first, 0),
        (last.invariant, 3),
        (last.invariant, 7),
        (first, 6),
    ] {
        let mut bad = copy_graph(&g, &quiet());
        // The original Table now belongs only to the actual first/Whole producer.
        // Rechecking a later projection must reject tampering through that edge too.
        let Some(Payload::Construction(v)) = &mut bad.nodes[first.0].payload else {
            panic!()
        };
        let D::PredicateInvariant(d) = &mut v.data else {
            panic!()
        };
        let Origin::Whole(source) = &mut d.origin else {
            panic!("whole producer")
        };
        let s = Arc::make_mut(source);
        let t = Arc::make_mut(&mut s.table);
        let r = match mode {
            0 | 3 => target,
            6 => last.invariant,
            7 => NodeRef(g.nodes.len() + 1),
            _ => unreachable!(),
        };
        match mode {
            0 | 6 | 7 => t.objects[0].evaluations[0] = r,
            3 => t.objects[0].architecture = r,
            _ => unreachable!(),
        }
        let calls = Rc::new(Cell::new(0));
        let seen = calls.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            (seen.get() >= 10_000).then_some(archsig_input::result::Signal::Int)
        });
        let fresh = Environment::with_prepared(&p, &control).unwrap();
        let result = fresh.recheck_node(&bad, bad.get(target).unwrap(), target.0);
        assert!(
            matches!(result, Err(ValidationFailure::Internal(_))),
            "target{target:?}/mode{mode}: {result:?}"
        );
        assert!(
            calls.get() < 10_000,
            "rejected by metadata, not interruption"
        );
    }
    for r in [NodeRef(g.nodes.len()), NodeRef(g.nodes.len() + 1)] {
        let mut t = (*t).clone();
        t.objects[0].evaluations[0] = r;
        let before = copy_graph(&g, &quiet());
        let env = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(matches!(
            retain(&env, &mut g, Arc::new(t), &quiet()),
            Err(ValidationFailure::Internal(_))
        ));
        assert_eq!(g.nodes, before.nodes);
        assert_eq!(g.contexts, before.contexts);
        assert_eq!(g.active, before.active);
    }
}

#[test]
fn projection_dependencies_share_one_cold_whole_and_preserve_public_arguments() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional same(c:Part,d:Part):c.quantity=d.quantity;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let base = g.nodes.len();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    assert!(!out.is_empty());
    let first = NodeRef(base);
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    crate::observed::data::observe_iterations(move |_, _, phase, _| {
        if phase == "predicate_whole_compute" {
            seen.set(seen.get() + 1);
        }
    });
    let cold = Environment::with_prepared(&p, &quiet()).unwrap();
    // Start at a projection, not at the Whole: its actual dependency must authenticate it.
    let last = out.last().unwrap().invariant;
    cold.recheck_node(&g, g.get(last).unwrap(), last.0).unwrap();
    for at in base..g.nodes.len() {
        let n = &g.nodes[at];
        let d = data(&g, NodeRef(at));
        if at == base {
            assert!(matches!(d.origin, Origin::Whole(_)));
            assert!(n.arguments.iter().all(|reference| reference.0 < base));
        } else {
            assert!(
                matches!(d.origin, Origin::Projection { first: actual, .. } if actual == first)
            );
            assert!(n.arguments.contains(&first));
        }
        let Json::Obj(ref wire) = n.wire(at, &g.nodes[..at]) else {
            panic!("node wire")
        };
        assert_eq!(wire["arguments"], refs(d.public_arguments()));
        cold.recheck_node(&g, n, at).unwrap();
    }
    crate::observed::data::clear_iteration_observer();
    assert_eq!(
        count.get(),
        1,
        "all parts must project one independently checked whole"
    );
    replay(&p, &g).unwrap();
}

#[test]
fn projections_reject_wrong_producer_position_metadata_and_changed_whole() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional same(c:Part,d:Part):c.quantity=d.quantity;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let old_base = g.nodes.len();
    retain(&env, &mut g, t.clone(), &quiet()).unwrap();
    let base = g.nodes.len();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    let target = out.last().unwrap().invariant;
    for mode in 0..6 {
        let mut bad = copy_graph(&g, &quiet());
        let mut d = data(&bad, target).clone();
        match mode {
            0 | 1 | 2 | 3 => {
                let Origin::Projection { first, .. } = &mut d.origin else {
                    panic!("projection")
                };
                *first = match mode {
                    0 => target,
                    1 => NodeRef(g.nodes.len() + 1),
                    2 => NodeRef(base + 1),
                    _ => NodeRef(old_base),
                };
                if matches!(mode, 2 | 3) {
                    // Keep the arithmetic position valid: reject the actual wrong
                    // producer/extent, not merely an inconsistent base+index.
                    d.index = target.0 - first.0;
                }
            }
            4 => d.index += 1,
            5 => d.part.scope.readings.clear(),
            _ => unreachable!(),
        }
        bad.nodes[target.0] = d.node();
        let cold = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(
            cold.recheck_node(&bad, bad.get(target).unwrap(), target.0)
                .is_err(),
            "mode{mode}"
        );
    }
    // A checked projection must lose success after COW changes to its real producer.
    let warm = Environment::with_prepared(&p, &quiet()).unwrap();
    let mut bad = copy_graph(&g, &quiet());
    warm.recheck_node(&bad, bad.get(target).unwrap(), target.0)
        .unwrap();
    let mut whole = data(&bad, NodeRef(base)).clone();
    let Origin::Whole(source) = &mut whole.origin else {
        panic!("whole")
    };
    Arc::make_mut(source)
        .parts
        .last_mut()
        .unwrap()
        .scope
        .readings
        .clear();
    bad.nodes[base] = whole.node();
    assert!(
        warm.recheck_node(&bad, bad.get(target).unwrap(), target.0)
            .is_err()
    );
}

#[test]
fn projection_architecture_clones_are_values_not_physical_identity_certificates() {
    let p = prepared(
        fixture::inputs(false, false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    let target = out.last().unwrap().invariant;
    let mut d = data(&g, target).clone();
    let Origin::Projection { architecture, .. } = &mut d.origin else {
        panic!("projection")
    };
    *architecture = Arc::new(architecture.as_ref().clone());
    g.nodes[target.0] = d.node();
    let cold = Environment::with_prepared(&p, &quiet()).unwrap();
    cold.recheck_node(&g, g.get(target).unwrap(), target.0)
        .unwrap();
}

#[test]
fn interrupted_projection_authentication_keeps_graph_and_retries_whole_cold() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(
        fixture::inputs(false, false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    let target = out.last().unwrap().invariant;
    let before = g.nodes.clone();
    let armed = Rc::new(Cell::new(false));
    let observed = armed.clone();
    crate::observed::data::observe_iterations(move |_, _, phase, _| {
        if phase == "predicate_whole_compute" {
            observed.set(true);
        }
    });
    let control = Control::new(move |_| armed.get().then_some(archsig_input::result::Signal::Term));
    let cold = Environment::with_prepared(&p, &control).unwrap();
    let result = cold.recheck_node(&g, g.get(target).unwrap(), target.0);
    crate::observed::data::clear_iteration_observer();
    assert!(matches!(result, Err(ValidationFailure::Stop(_))));
    assert_eq!(g.nodes, before);
    let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
    fresh
        .recheck_node(&g, g.get(target).unwrap(), target.0)
        .unwrap();
}

fn refactor_predicate_supports(g: &mut Graph, base: usize, flat: bool) {
    let mut whole = data(g, NodeRef(base)).clone();
    let Origin::Whole(source) = &mut whole.origin else {
        panic!("whole")
    };
    let source = Arc::make_mut(source);
    for part in &mut source.parts {
        part.support = if flat {
            Support::from(part.support.materialize_for_test())
        } else {
            Support::concat([Support::default(), part.support.clone()])
        };
    }
    whole.part = source.parts[0].clone();
    g.nodes[base] = whole.node();
    for at in base + 1..g.nodes.len() {
        let mut projection = data(g, NodeRef(at)).clone();
        projection.part.support = if flat {
            Support::from(projection.part.support.materialize_for_test())
        } else {
            Support::concat([Support::default(), projection.part.support.clone()])
        };
        g.nodes[at] = projection.node();
    }
    for at in base..g.nodes.len() {
        let original = g.nodes[at].support.clone();
        // Node top support deliberately differs from its own native payload too.
        g.nodes[at].support = if flat {
            Support::concat([Support::default(), original])
        } else {
            Support::from(original.materialize_for_test())
        };
    }
}

#[test]
fn cold_and_warm_authenticate_old_flat_and_alternative_native_part_supports() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional same(c:Part,d:Part):c.quantity=d.quantity;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let base = g.nodes.len();
    retain(&env, &mut g, t, &quiet()).unwrap();
    for flat in [true, false] {
        let mut changed = copy_graph(&g, &quiet());
        refactor_predicate_supports(&mut changed, base, flat);
        let target = NodeRef(changed.nodes.len() - 1);
        assert!(
            !data(&changed, target)
                .part
                .support
                .same_recipe(&data(&g, target).part.support)
        );
        assert!(
            !changed.nodes[target.0]
                .support
                .same_recipe(&data(&changed, target).part.support)
        );
        let cold = Environment::with_prepared(&p, &quiet()).unwrap();
        for _ in 0..2 {
            for at in base..changed.nodes.len() {
                cold.recheck_node(&changed, &changed.nodes[at], at).unwrap();
                assert_eq!(
                    changed.nodes[at].wire(at, &changed.nodes[..at]),
                    g.nodes[at].wire(at, &g.nodes[..at])
                );
            }
        }
        replay(&p, &changed).unwrap();
    }
}

#[test]
fn equivalent_support_does_not_hide_coordinated_fact_or_value_forgery() {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional same(c:Part,d:Part):c.quantity=d.quantity;",
        ),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let base = g.nodes.len();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    for (wrong_fact, wrong_value) in [(true, false), (false, true), (true, true)] {
        let mut bad = copy_graph(&g, &quiet());
        refactor_predicate_supports(&mut bad, base, true);
        let mut whole = data(&bad, NodeRef(base)).clone();
        let Origin::Whole(source) = &mut whole.origin else {
            panic!("whole")
        };
        let source = Arc::make_mut(source);
        let index = if wrong_value {
            source
                .parts
                .iter()
                .position(|part| {
                    matches!(&part.wire,
                Json::Obj(wire) if wire.contains_key("value"))
                })
                .unwrap()
        } else {
            out.last().unwrap().invariant.0 - base
        };
        if wrong_value {
            let Json::Obj(wire) = &mut source.parts[index].wire else {
                panic!("value")
            };
            let original = reference(&wire["value"]);
            let original = g.boolean(Some(original)).unwrap().unwrap();
            let opposite = g.nodes[..base].iter().position(|node|
                matches!(node.payload, Some(Payload::Scalar(Scalar::Bool(value))) if value != original)
            ).map(NodeRef).unwrap();
            wire.insert("value".into(), opposite.wire());
            source.parts[index].arguments.push(opposite);
            source.parts[index].arguments.sort_by_key(|r| r.0);
            source.parts[index].arguments.dedup();
        }
        if wrong_fact {
            let mut facts = source.parts[index].support.materialize_for_test();
            facts.push(Fact::from(archsig_input::archmap::FactData {
                snapshot: "v".into(),
                subject: "forged".into(),
                field: None,
                atom: None,
            }));
            source.parts[index].support = Support::from(facts);
        }
        source.arguments =
            whole_arguments(&source.table, &source.parts, source.base, &quiet()).unwrap();
        let local = source.parts[index].clone();
        whole.part = source.parts[0].clone();
        bad.nodes[base] = whole.node();
        let target = NodeRef(base + index);
        if index != 0 {
            let mut projection = data(&bad, target).clone();
            projection.part = local;
            bad.nodes[target.0] = projection.node();
        }
        let cold = Environment::with_prepared(&p, &quiet()).unwrap();
        assert!(
            matches!(
                cold.recheck_node(&bad, bad.get(target).unwrap(), target.0),
                Err(ValidationFailure::Internal(_))
            ),
            "wrong_fact={wrong_fact}/wrong_value={wrong_value}"
        );
    }
}

#[test]
fn native_part_semantic_support_comparison_obeys_control_without_changing_graph() {
    let p = prepared(
        fixture::inputs(false, false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (mut g, t) = table(&p);
    let env = Environment::with_prepared(&p, &quiet()).unwrap();
    let out = retain(&env, &mut g, t, &quiet()).unwrap();
    let target = out.last().unwrap().invariant;
    let original = data(&g, target).part.clone();
    let mut alternate = original.clone();
    alternate.support = Support::concat([Support::default(), original.support.clone()]);
    assert!(!alternate.support.same_recipe(&original.support));
    let control = Control::new(|_| Some(archsig_input::result::Signal::Term));
    let before = g.nodes.clone();
    assert!(matches!(
        alternate.matches_with_support(&original, &control),
        Err(ValidationFailure::Stop(_))
    ));
    assert_eq!(g.nodes, before);
    let fresh = Environment::with_prepared(&p, &quiet()).unwrap();
    fresh
        .recheck_node(&g, g.get(target).unwrap(), target.0)
        .unwrap();
}
