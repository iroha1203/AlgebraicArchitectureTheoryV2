use crate::input::CheckedInputs;
use super::super::law_table;
use super::*;
use crate::{
    control::{Limits, Usage},
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../tests/common/polynomial_law_family_data.rs");
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
#[allow(dead_code)]
fn subject(g: &Graph, r: NodeRef, name: &str) -> String {
    let o = super::super::law_evaluation::origin(g, r).unwrap().unwrap();
    let b = o.bindings.iter().find(|b| b.name == name).unwrap();
    let Scalar::Subject { subject, .. } = g.scalar(b.value).unwrap() else {
        panic!()
    };
    subject.clone()
}

fn sample(
    missing: bool,
    tuple: bool,
    body: &str,
    root: &str,
) -> (PreparedObserved, Graph, Arc<Table>, Layout) {
    from_inputs(fixture::inputs(missing, tuple, body), root)
}
fn from_inputs(
    inputs: Arc<CheckedInputs>,
    root: &str,
) -> (PreparedObserved, Graph, Arc<Table>, Layout) {
    let p = prepared(inputs, root);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a) = start(&p);
    let table = Arc::new(
        law_table::retain(&env, &mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .unwrap(),
    );
    let layout = retain(&env, &g, table.clone(), &mut quiet()).unwrap();
    (p, g, table, layout)
}
fn polynomial(g: &Graph, r: NodeRef) -> Vec<(crate::canonical::Json, Vec<crate::canonical::Json>)> {
    use crate::canonical::Json;
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let Json::Obj(ref fields) = v.wire() else {
        panic!()
    };
    let Json::Arr(terms) = &fields["terms"] else {
        panic!()
    };
    terms
        .iter()
        .map(|term| {
            let Json::Obj(t) = term else { panic!() };
            let Json::Arr(powers) = &t["powers"] else {
                panic!()
            };
            let position = g
                .nodes
                .iter()
                .enumerate()
                .find_map(|(i, _)| (NodeRef(i).wire() == t["coefficient"]).then_some(NodeRef(i)))
                .unwrap();
            (g.scalar(position).unwrap().wire(), powers.clone())
        })
        .collect()
}
#[test]
fn mixed_z_q_fp_components_share_factors_and_place_only_at_the_root_atom() {
    use crate::input::{InputSources, check_inputs};
    let original = fixture::inputs(
        false,
        true,
        "law required self(c:Part):c.quantity=c.quantity;law optional again(c:Part):c.quantity=c.quantity;",
    );
    let s = original.sources();
    let definition = String::from_utf8(s.definitions()[0].bytes().to_vec())
        .unwrap()
        .replace(r#"["Tuple","Z","Q"]"#, r#"["Tuple","Z","Q",["Fp","2"]]"#);
    assert_ne!(definition.as_bytes(), s.definitions()[0].bytes());
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let old = &original.definitions().vocabularies["Family"].digest;
    let digest = &defs.vocabularies["Family"].digest;
    let law = String::from_utf8(s.law().bytes().to_vec())
        .unwrap()
        .replace(old, digest);
    let map = String::from_utf8(s.archmap().bytes().to_vec())
        .unwrap()
        .replace(old, digest)
        .replace(
            r#""value":["0",["1","2"]]"#,
            r#""value":["0",["1","2"],"0"]"#,
        )
        .replace(
            r#""value":["1",["3","2"]]"#,
            r#""value":["1",["3","2"],"1"]"#,
        );
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
    let (p, g, t, l) = from_inputs(inputs, "root");
    assert_eq!(l.data.factors.len(), 3);
    assert_eq!(l.data.indices, t.indices);
    assert_eq!(l.data.indices.len(), 4);
    assert_eq!(l.data.objects.len(), 3);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete()); // 対象外の生差は未評価のまま、記号表示と条件付き零を保持。
    assert_eq!(
        l.data.anchor,
        Fact {
            snapshot: "v".into(),
            subject: "root".into(),
            field: None,
            atom: None
        }
    );
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.object, t.objects[object].object);
        assert_eq!(row.architecture, t.objects[object].architecture);
        assert_eq!(row.coordinates.len(), 12);
        for (i, q) in row.coordinates.iter().enumerate() {
            let expected = match q.polynomial().unwrap().ty {
                crate::types::Type::Z => 0,
                crate::types::Type::Q => 1,
                crate::types::Type::Fp(_) => 2,
                _ => panic!(),
            };
            assert!(polynomial(&g, q.polynomial().unwrap().nu.unwrap()).is_empty());
            assert_eq!(
                q.polynomial().unwrap().epsilon.is_none(),
                q.polynomial().unwrap().guard == EquationGuard::OutsideObject
            );
            assert_eq!(q.polynomial().unwrap().component, [expected]);
            assert_eq!(q.factor, Some(expected));
            assert_eq!(q.polynomial().unwrap().ring, Some(l.data.factors[expected]));
            for factor in 0..3 {
                for atom in checked.atoms {
                    let v = checked
                        .at(object, i, Reading::Residual, factor, atom, &mut quiet())
                        .unwrap();
                    if atom == &l.data.anchor && factor == expected {
                        let Placed::Value { ring, reference } = v else {
                            panic!()
                        };
                        assert_eq!(ring, l.data.factors[expected]);
                        assert_eq!(Some(reference), q.polynomial().unwrap().residual);
                        assert!(polynomial(&g, reference).is_empty());
                    } else {
                        assert_eq!(
                            v,
                            Placed::Zero {
                                ring: l.data.factors[factor]
                            }
                        );
                    }
                }
            }
        }
    }
    replay(&p, &g).unwrap();
}
#[test]
fn a_complete_refuted_equation_is_not_confused_with_an_unfinished_layout() {
    use crate::canonical::Json;
    let (p, g, t, l) = sample(
        false,
        false,
        "law required contradiction(r:Root):0=1;",
        "r2",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    assert_eq!(l.data.factors.len(), 1);
    assert_eq!(l.data.objects.len(), 1);
    assert_eq!(l.data.objects[0].coordinates.len(), 1);
    assert_eq!(
        g.get(t.objects[0].holds[0])
            .unwrap()
            .judgment
            .as_ref()
            .unwrap()
            .status,
        Decision::Refuted
    );
    for reading in [Reading::Nu, Reading::Epsilon, Reading::Residual] {
        let Placed::Value { ring, reference } = checked
            .at(0, 0, reading, 0, &l.data.anchor, &mut quiet())
            .unwrap()
        else {
            panic!()
        };
        assert_eq!(ring, l.data.factors[0]);
        assert_eq!(
            polynomial(&g, reference),
            [(Json::Str("-1".into()), vec![])]
        );
    }
    replay(&p, &g).unwrap();
}
#[test]
fn non_applicable_rows_keep_raw_epsilon_absent_and_real_residual_zero() {
    let (p, g, _, l) = sample(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    let mut outside = 0;
    for (object, row) in l.data.objects.iter().enumerate() {
        for (i, q) in row.coordinates.iter().enumerate() {
            if q.polynomial().unwrap().guard == EquationGuard::OutsideObject {
                outside += 1;
                assert!(
                    q.polynomial().unwrap().nu.is_some()
                        && q.polynomial().unwrap().epsilon.is_none()
                );
                assert!(matches!(
                    checked
                        .at(object, i, Reading::Nu, 0, &l.data.anchor, &mut quiet())
                        .unwrap(),
                    Placed::Value { .. }
                ));
                assert_eq!(
                    checked
                        .at(object, i, Reading::Epsilon, 0, &l.data.anchor, &mut quiet())
                        .unwrap(),
                    Placed::Uncomputed {
                        ring: l.data.factors[0]
                    }
                );
                let Placed::Value { reference, .. } = checked
                    .at(
                        object,
                        i,
                        Reading::Residual,
                        0,
                        &l.data.anchor,
                        &mut quiet(),
                    )
                    .unwrap()
                else {
                    panic!()
                };
                assert!(polynomial(&g, reference).is_empty());
            }
        }
    }
    assert_eq!(outside, 2);
    assert!(checked.is_complete());
    replay(&p, &g).unwrap();
}
#[test]
fn missing_quantities_and_unavailable_presentations_retain_every_position_without_defaulting() {
    for body in [
        "law required zero(c:Part):c.quantity=0;",
        "law required bounded(c:Part):c.quantity<=0;",
    ] {
        let (p, g, _, l) = sample(true, false, body, "root");
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let checked = l.checked(&env, &g, &mut quiet()).unwrap();
        assert!(!checked.is_complete());
        assert_eq!(l.data.indices.len(), 2);
        assert_eq!(l.data.objects.len(), 3);
        assert!(
            l.data
                .objects
                .iter()
                .all(|o| !o.coordinates.is_empty() || o.unavailable.is_some())
        );
        assert!(!l.data.reasons.is_empty());
        if body.contains("<=") {
            assert!(l.data.factors.is_empty());
            assert!(
                l.data
                    .objects
                    .iter()
                    .flat_map(|r| &r.coordinates)
                    .all(|q| q.factor.is_none())
            );
        } else {
            let q = l.data.objects[0]
                .coordinates
                .iter()
                .position(|q| subject(&g, q.polynomial().unwrap().instance, "c") == "q")
                .unwrap();
            assert_eq!(
                checked
                    .at(0, q, Reading::Epsilon, 0, &l.data.anchor, &mut quiet())
                    .unwrap(),
                Placed::Uncomputed {
                    ring: l.data.factors[0]
                }
            );
        }
        replay(&p, &g).unwrap();
    }
}
#[test]
fn finite_parameter_rows_keep_bindings_cases_and_symbolic_global_indices() {
    let (p, g, t, l) = sample(
        false,
        false,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    assert_eq!(l.data.indices.len(), 2);
    assert_eq!(l.data.objects[0].coordinates.len(), 4);
    let ds = t.diagrams().unwrap();
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.coordinates.len(), ds[object].coordinates.len());
        for (q, source) in row.coordinates.iter().zip(&ds[object].coordinates) {
            assert_eq!(q.polynomial().unwrap(), source);
            assert!(l.data.indices.contains(&q.index));
            if object == 0 {
                let o = super::super::law_evaluation::origin(&g, q.polynomial().unwrap().instance)
                    .unwrap()
                    .unwrap();
                let b = o.bindings.iter().find(|b| b.name == "b").unwrap();
                assert_eq!(
                    g.scalar(b.value).unwrap(),
                    &Scalar::Bool(q.polynomial().unwrap().row == Some(1))
                );
            }
        }
    }
    assert!(
        l.data
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "b" && q.domain.is_some())
    );
    replay(&p, &g).unwrap();
}
#[test]
fn the_empty_family_is_an_empty_block_product_with_all_objects_and_the_actual_universe() {
    let (p, g, _, l) = sample(false, false, "", "root");
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    assert!(l.data.factors.is_empty() && l.data.indices.is_empty());
    assert_eq!(l.data.objects.len(), 3);
    assert!(
        l.data
            .objects
            .iter()
            .all(|o| o.coordinates.is_empty() && o.presentations.is_empty())
    );
    assert!(checked.atoms.contains(&l.data.anchor));
    assert_eq!(checked.atoms.len(), 8); // root, r2, p, q と4つのfield Atom。

    assert!(
        checked
            .at(0, 0, Reading::Residual, 0, &l.data.anchor, &mut quiet())
            .is_err()
    );
    replay(&p, &g).unwrap();
}
#[test]
fn layout_and_underlying_table_tampering_is_rejected() {
    let (p, g, table, l) = sample(
        false,
        true,
        "law required self(c:Part):c.quantity=c.quantity;law optional again(c:Part):c.quantity=c.quantity;",
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    for mode in 0..26 {
        let mut b = l.clone();
        match mode {
            0 => b.data.factors.reverse(),
            1 => {
                b.data.factors.pop();
            }
            2 => b.data.factors.push(b.data.factors[0]),
            3 => b.data.anchor.subject = "p".into(),
            4 => b.data.universe = b.data.architecture,
            5 => b.data.indices.reverse(),
            6 => {
                b.data.indices.pop();
            }
            7 => b.data.objects.reverse(),
            8 => {
                b.data.objects.pop();
            }
            9 => b.data.objects[0].coordinates.reverse(),
            10 => {
                b.data.objects[0].coordinates.pop();
            }
            11 => b.data.objects[0].coordinates[0].factor = Some(1),
            12 => b.data.objects[0].coordinates[0].factor = Some(20),
            13 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .component = vec![1]
            }
            14 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .row = Some(20)
            }
            15 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .case = 20
            }
            16 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .nu = Some(NodeRef(g.nodes.len()))
            }
            17 => b.data.objects[0].coordinates[0].index = b.data.indices[1],
            18 => b.data.support.clear(),
            19 => b.data.scope.snapshots.clear(),
            20 => b.data.complete = !b.data.complete,
            21 => b.data.objects[0].presentations.clear(),
            22 => b.data.objects[0].architecture = b.data.objects[1].architecture,
            23 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .position
                    .object = 1
            }
            24 => {
                b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .epsilon = b.data.objects[0].coordinates[0]
                    .polynomial_mut()
                    .unwrap()
                    .residual
            }
            25 => {
                let mut t = (*table).clone();
                t.indices.reverse();
                b.table = Arc::new(t);
            }
            _ => unreachable!(),
        }
        // epsilonとresidualが同じRefである場合は、他Lawの評価へ明示的に差し替える。
        if mode == 24 {
            b.data.objects[0].coordinates[0]
                .polynomial_mut()
                .unwrap()
                .epsilon = Some(table.objects[0].holds[0]);
        }
        assert!(b.recheck(&env, &g, &mut quiet()).is_err(), "mode {mode}");
    }
    let mut bad = copy_graph(&g, &quiet());
    bad.nodes[l.data.factors[0].0]
        .arguments
        .push(NodeRef(l.data.factors[0].0));
    assert!(l.recheck(&env, &bad, &mut quiet()).is_err());
    let other = prepared(
        fixture::inputs(
            false,
            true,
            "law required self(c:Part):c.quantity=c.quantity;",
        ),
        "root",
    );
    let foreign = Environment::with_prepared(&other, &mut quiet()).unwrap();
    assert!(l.recheck(&foreign, &g, &mut quiet()).is_err());
    l.recheck(&env, &g, &mut quiet()).unwrap();
}
#[test]
fn checked_placement_rejects_foreign_atoms_indices_and_coordinates() {
    let (p, g, _, l) = sample(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
        "root",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    let foreign = Fact {
        snapshot: "other".into(),
        ..l.data.anchor.clone()
    };
    assert!(
        checked
            .at(0, 0, Reading::Nu, 0, &foreign, &mut quiet())
            .is_err()
    );
    assert!(
        checked
            .at(30, 0, Reading::Nu, 0, &l.data.anchor, &mut quiet())
            .is_err()
    );
    assert!(
        checked
            .at(0, 30, Reading::Nu, 0, &l.data.anchor, &mut quiet())
            .is_err()
    );
    assert!(
        checked
            .at(0, 0, Reading::Nu, 30, &l.data.anchor, &mut quiet())
            .is_err()
    );
}
#[test]
fn four_stops_do_not_return_a_layout_or_mutate_the_finished_graph() {
    use std::{cell::Cell, rc::Rc};
    let (p, g, t, l) = sample(false, false, "law required zero(r:Root):0=0;", "r2");
    let seen = Rc::new(Cell::new(0));
    let counter = seen.clone();
    let mut c = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::EquationPresentation {
            counter.set(counter.get() + 1)
        }
        Usage::default()
    });
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let full = retain(&env, &g, t.clone(), &mut c).unwrap();
    assert_eq!(full.data, l.data);
    let total = seen.get();
    assert!(total > 4);
    for mode in 0..4 {
        for at in [1, total / 2, total - 1, total] {
            let seen = Rc::new(Cell::new(0));
            let counter = seen.clone();
            let mut c = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::EquationPresentation {
                        counter.set(counter.get() + 1)
                    }
                    let stop = counter.get() >= at;
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
            let before = g.nodes.clone();
            let contexts = g.contexts.clone();
            let active = g.active;
            let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
            assert!(matches!(
                retain(&env, &g, t.clone(), &mut c),
                Err(ValidationFailure::Stop(_))
            ));
            assert_eq!(g.nodes, before);
            assert_eq!(g.contexts, contexts);
            assert_eq!(g.active, active);
            assert!(env.architecture_ref().is_none());
            replay(&p, &g).unwrap();
        }
    }
}
