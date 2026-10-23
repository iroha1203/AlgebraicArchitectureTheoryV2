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
fn subject(g: &Graph, r: NodeRef, name: &str) -> String {
    let o = frames::origin(g, r).unwrap().unwrap();
    let b = o.bindings.iter().find(|b| b.name == name).unwrap();
    let Scalar::Subject { subject, .. } = g.scalar(b.value).unwrap() else {
        panic!()
    };
    subject.clone()
}
const LAWS: &str = "law required zero(c:Part):c.quantity=0;law optional bit(c:Part,b:Bool) when b:c.quantity=0;law required same(c:Part,d:Part):c.quantity=d.quantity;";
#[test]
fn all_laws_and_objects_keep_common_order_roles_bindings_and_actual_judgments() {
    let p = prepared(fixture::inputs(false, false, LAWS), "root");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(t.indices.len(), 8);
    assert_eq!(t.objects.len(), 3);
    let mut required = 0;
    let mut optional = 0;
    for r in &t.indices {
        let Some(Payload::Construction(v)) = &g.get(*r).unwrap().payload else {
            panic!()
        };
        let crate::canonical::Json::Obj(ref w) = v.wire() else {
            panic!()
        };
        match &w["role"] {
            crate::canonical::Json::Str(role) if role == "required" => required += 1,
            crate::canonical::Json::Str(role) if role == "optional" => optional += 1,
            _ => panic!(),
        }
    }
    assert_eq!((required, optional), (6, 2));
    for (object, row) in t.objects.iter().enumerate() {
        assert_eq!(row.origins.len(), 8);
        assert_eq!(row.evaluations.len(), 8);
        assert_eq!(row.holds.len(), 8);
        for (i, r) in row.origins.iter().enumerate() {
            let o = frames::origin(&g, *r).unwrap().unwrap();
            let b = frames::origin(&g, t.indices[i]).unwrap().unwrap();
            assert_eq!(o.declaration, b.declaration);
            assert_eq!(o.object, object);
            assert_eq!(o.bindings.len(), b.bindings.len());
            for (x, y) in o.bindings.iter().zip(&b.bindings) {
                assert_eq!((&x.name, &x.ty), (&y.name, &y.ty));
                assert_eq!(g.scalar(x.value).unwrap(), g.scalar(y.value).unwrap());
            }
            let c = subject(&g, *r, "c");
            let outside = object != 0
                && (c != if object == 1 { "p" } else { "q" }
                    || o.bindings.iter().find(|b| b.name == "d").is_some_and(|_| {
                        subject(&g, *r, "d") != if object == 1 { "p" } else { "q" }
                    }));
            let truth = outside
                || if o.declaration.ends_with(".same") {
                    c == subject(&g, *r, "d")
                } else {
                    c == "p"
                };
            assert_eq!(
                g.get(row.holds[i])
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
            if !truth {
                assert!(!g.get(row.holds[i]).unwrap().evidence.is_empty());
            }
        }
    }
    assert!(t.scope.readings.contains("Selected"));
    assert!(t.scope.snapshots.contains("v"));
    assert!(t.scope.assignments);
    assert!(
        t.scope
            .quantifiers
            .iter()
            .any(|q| q.name == "b" && q.domain.is_some())
    );
    t.recheck(&env, &g, &mut quiet()).unwrap();
    replay(&p, &g).unwrap();
}
#[test]
fn finite_fields_and_finite_parameter_families_use_real_domain_evaluations() {
    let p = prepared(
        finite_fixture::inputs(
            false,
            "law required zero(c:Part):c.quantity=0;law optional every(c:Part,n:Fp(2)):c.quantity=n;",
        ),
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(t.indices.len(), 4);
    assert_eq!(t.objects.len(), 3);
    for (object, row) in t.objects.iter().enumerate() {
        for (i, r) in row.origins.iter().enumerate() {
            let c = subject(&g, *r, "c");
            let o = frames::origin(&g, *r).unwrap().unwrap();
            let outside = object != 0 && c != if object == 1 { "p" } else { "q" };
            let truth = outside || (!o.declaration.ends_with(".every") && c == "p");
            assert_eq!(
                g.get(row.holds[i])
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
    }
    t.recheck(&env, &g, &mut quiet()).unwrap();
    replay(&p, &g).unwrap();
}
#[test]
fn missing_readings_remain_real_undetermined_cells_with_original_reasons() {
    let p = prepared(
        fixture::inputs(
            true,
            false,
            "law required zero(c:Part):c.quantity=0;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(t.indices.len(), 4);
    let mut missing = 0;
    for (object, row) in t.objects.iter().enumerate() {
        for (i, r) in row.origins.iter().enumerate() {
            let c = subject(&g, *r, "c");
            let q = c == "q" && (object == 0 || object == 2);
            let n = g.get(row.holds[i]).unwrap();
            assert_eq!(
                n.judgment.as_ref().unwrap().status,
                if q {
                    Decision::Undetermined
                } else {
                    Decision::Established
                }
            );
            if q {
                assert!(n.reasons.iter().any(|r| r.missing.iter().any(
                    |f| f.subject == "q" && f.field.as_deref() == Some("Family.Part.quantity")
                )));
                missing += 1;
            }
        }
    }
    assert_eq!(missing, 4);
    assert!(!t.reasons.is_empty());
    t.recheck(&env, &g, &mut quiet()).unwrap();
    replay(&p, &g).unwrap();
}
#[test]
fn an_empty_law_or_reference_family_keeps_every_object_and_no_fake_evaluation() {
    for (body, root, objects) in [
        ("", "root", 3),
        ("law required zero(c:Part):c.quantity=0;", "r2", 1),
    ] {
        let p = prepared(fixture::inputs(false, false, body), root);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let (mut g, a) = start(&p);
        let before = g.nodes.len();
        let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .unwrap();
        assert!(t.indices.is_empty());
        assert_eq!(t.objects.len(), objects);
        assert!(
            t.objects
                .iter()
                .all(|r| r.origins.is_empty() && r.evaluations.is_empty() && r.holds.is_empty())
        );
        assert!(g.nodes[before..].iter().all(|n| !matches!(
            n.payload,
            Some(Payload::Evaluation { .. } | Payload::Proposition { .. })
        )));
        t.recheck(&env, &g, &mut quiet()).unwrap();
        replay(&p, &g).unwrap();
    }
}
#[test]
fn guarded_unread_bodies_and_tuple_values_keep_the_original_whole_judgments() {
    for (tuple, body) in [
        (
            false,
            "law required skip(c:Part) when false:forall k:Z.k=0;",
        ),
        (
            true,
            "law required reflexive(c:Part):c.quantity=c.quantity;",
        ),
    ] {
        let p = prepared(fixture::inputs(false, tuple, body), "root");
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let (mut g, a) = start(&p);
        let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .unwrap();
        assert_eq!(t.indices.len(), 2);
        assert!(
            t.objects.iter().flat_map(|r| &r.holds).all(|r| g
                .get(*r)
                .unwrap()
                .judgment
                .as_ref()
                .unwrap()
                .status
                == Decision::Established)
        );
        if !tuple {
            for row in &t.objects {
                for r in &row.evaluations {
                    if let Some(Payload::Evaluation { parts, .. }) = &g.get(*r).unwrap().payload {
                        let b = parts.last().unwrap();
                        assert!(b.value.is_none() && b.children.is_empty());
                    }
                }
            }
        }
        t.recheck(&env, &g, &mut quiet()).unwrap();
        replay(&p, &g).unwrap();
    }
}
#[test]
fn an_uncomputed_numeric_family_never_becomes_a_completed_table_or_mathematical_false() {
    let p = prepared(
        fixture::inputs(false, false, "law required later(c:Part,k:Z):c.quantity=k;"),
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let before = g.nodes.len();
    assert!(
        retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .is_none()
    );
    assert!(g.nodes.len() > before);
    assert!(!g.nodes[before..].iter().any(|n| n.judgment.is_some()));
    assert_eq!(g.active, g.context_at(a.0));
    replay(&p, &g).unwrap();
}
fn sample() -> (PreparedObserved, Graph, Table) {
    let p = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=0;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let t = retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    (p, g, t)
}
#[test]
fn table_recheck_rejects_coverage_order_wrong_sources_metadata_and_future_refs() {
    let (p, g, t) = sample();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for mode in 0..25 {
        let mut bad = t.clone();
        match mode {
            0 => {
                bad.indices.pop();
            }
            1 => bad.indices.reverse(),
            2 => bad.indices[1] = bad.indices[0],
            3 => {
                bad.objects.pop();
            }
            4 => bad.objects.reverse(),
            5 => bad.objects[0].object = bad.objects[1].object,
            6 => bad.objects[0].architecture = bad.objects[1].architecture,
            7 => bad.objects[0].origins.reverse(),
            8 => {
                bad.objects[0].evaluations.pop();
            }
            9 => {
                bad.objects[0].holds.pop();
            }
            10 => bad.objects[0].evaluations[0] = bad.objects[0].evaluations[1],
            11 => bad.objects[0].holds[0] = bad.objects[0].holds[1],
            12 => {
                bad.objects[0].evaluations[0] = bad.objects[1].evaluations[0];
                bad.objects[0].holds[0] = bad.objects[1].holds[0];
            }
            13 => bad.objects[0].origins[0] = bad.indices[1],
            14 => bad.support.clear(),
            15 => bad.scope.snapshots.clear(),
            16 => bad.scope.quantifiers.clear(),
            17 => bad.scope.assignments = false,
            18 => bad.component_source = bad.objects[1].object,
            19 => bad.architecture = bad.objects[1].architecture,
            20 => bad.indices[0] = NodeRef(g.nodes.len()),
            21 => bad.objects[0].evaluations[0] = NodeRef(g.nodes.len() + 1),
            22 => bad.objects[0].holds[0] = bad.indices[0],
            23 => {
                bad.objects[0].origins.pop();
            }
            24 => bad.objects[0].origins[0] = bad.objects[0].holds[0],
            _ => unreachable!(),
        };
        assert!(bad.recheck(&env, &g, &mut quiet()).is_err(), "mode {mode}");
    }
    let other = prepared(
        fixture::inputs(
            false,
            false,
            "law required zero(c:Part):c.quantity=1;law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let other_env = Environment::with_prepared(&other, &mut quiet()).unwrap();
    assert!(t.recheck(&other_env, &g, &mut quiet()).is_err());
    t.recheck(&env, &g, &mut quiet()).unwrap();
}
#[test]
fn graph_evaluation_and_proposition_forgery_is_rejected_before_table_acceptance() {
    let (p, g, t) = sample();
    for future in [false, true] {
        let mut bad = copy_graph(&g, &quiet());
        let row = &t.objects[0];
        let r = *row
            .evaluations
            .iter()
            .find(|r| {
                matches!(
                    g.get(**r).unwrap().payload,
                    Some(Payload::Evaluation { .. })
                )
            })
            .unwrap();
        let invalid = NodeRef(r.0 + usize::from(future));
        let Some(Payload::Evaluation { expression, .. }) = &mut bad.nodes[r.0].payload else {
            panic!()
        };
        *expression = invalid;
        bad.nodes[r.0].arguments.push(invalid);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(matches!(
            t.recheck(&env, &bad, &mut quiet()),
            Err(ValidationFailure::Internal(_))
        ));
    }
    let mut bad = copy_graph(&g, &quiet());
    let status = &mut bad.nodes[t.objects[0].holds[0].0]
        .judgment
        .as_mut()
        .unwrap()
        .status;
    *status = if *status == Decision::Established {
        Decision::Refuted
    } else {
        Decision::Established
    };
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    assert!(t.recheck(&env, &bad, &mut quiet()).is_err());
    replay(&p, &g).unwrap();
}
#[test]
fn four_stops_leave_exact_completed_dag_prefix_and_no_completed_table() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(
        fixture::inputs(false, false, "law required truth(c:Part):true;"),
        "root",
    );
    let (initial, a) = start(&p);
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::ObjectEvaluation {
            count.set(count.get() + 1)
        }
        Usage::default()
    });
    let mut full = copy_graph(&initial, &c);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    retain(&env, &mut full, p.shared_inputs(), a, &mut c)
        .unwrap()
        .unwrap();
    let total = seen.get();
    assert!(total > 4);
    let mut points = vec![1, total / 4, total / 2, 3 * total / 4, total - 1, total];
    points.sort();
    points.dedup();
    let mut partial = false;
    let mut complete = false;
    for mode in 0..4 {
        for &at in &points {
            let seen = Rc::new(Cell::new(0));
            let count = seen.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::ObjectEvaluation {
                        count.set(count.get() + 1)
                    }
                    let stop = count.get() >= at;
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
            let mut g = copy_graph(&initial, &c);
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            assert!(matches!(
                retain(&env, &mut g, p.shared_inputs(), a, &mut c),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.active, initial.active);
            assert!(env.architecture_ref().is_none());
            // 別実行の内部SourceはArc identityが異なる。公開DAGと各由来の再検査を照合する。
            assert_eq!(&g.nodes[..initial.nodes.len()], &initial.nodes);
            assert!(g.nodes.len() <= full.nodes.len());
            for (i, node) in g.nodes.iter().enumerate() {
                assert_eq!(
                    node.wire(i, &g.nodes[..i]),
                    full.nodes[i].wire(i, &full.nodes[..i])
                );
            }
            assert_eq!(g.contexts, &full.contexts[..g.nodes.len()]);
            partial |= g.nodes.len() > initial.nodes.len() && g.nodes.len() < full.nodes.len();
            complete |= g.nodes.len() == full.nodes.len();
            replay(&p, &g).unwrap();
        }
    }
    assert!(partial);
    assert!(complete);
}

#[test]
fn unknown_ownership_keeps_a_pending_architecture_and_never_completes_the_table() {
    use crate::observed::input::{InputBytes, InputSources, check_inputs};
    let original = fixture::inputs(false, false, "law required truth(c:Part):true;");
    let source = original.sources();
    let map = String::from_utf8(source.archmap().bytes().to_vec()).unwrap();
    let missing = map.replace(r#"{"id":"oq","subject":"q","field":"Family.Part.owner","value":["v","root"],"origin":"model"},"#, "");
    assert_ne!(missing, map);
    let inputs = Arc::new(
        check_inputs(
            InputSources::new(
                source.definitions().to_vec(),
                source.law().clone(),
                InputBytes::new("archmap", missing.into_bytes()),
            ),
            &mut quiet(),
        )
        .unwrap(),
    );
    let p = prepared(inputs, "root");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    assert!(
        matches!(&g.get(a).unwrap().payload, Some(Payload::Construction(v)) if matches!(&v.data,D::Pending{ty:T::Architecture,..}))
    );
    assert!(!g.get(a).unwrap().reasons.is_empty());
    let before = g.nodes.clone();
    assert!(matches!(
        retain(&env, &mut g, p.shared_inputs(), a, &mut quiet()),
        Err(ValidationFailure::Internal(_))
    ));
    assert_eq!(g.nodes, before);
    assert_eq!(g.active, g.context_at(a.0));
    replay(&p, &g).unwrap();
}
