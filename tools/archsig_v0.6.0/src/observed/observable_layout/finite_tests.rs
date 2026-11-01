use super::*;
use crate::{
    input::CheckedInputs,
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/finite_law_family_data.rs");
}
#[allow(dead_code)]
mod polynomial_fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
use crate::control::quiet;
fn prepared(inputs: Arc<CheckedInputs>) -> PreparedObserved {
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
fn start(p: &PreparedObserved) -> (Graph, Arc<Table>) {
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
    let table =
        super::super::law_table::retain(&env, &mut g, p.shared_inputs(), a.reference, &mut quiet())
            .unwrap()
            .unwrap();
    (g, Arc::new(table))
}
fn copy(g: &Graph, c: &Control) -> Graph {
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
fn replay(p: &PreparedObserved, g: &Graph) {
    let env = Environment::with_prepared(p, &mut quiet()).unwrap();
    let mut prefix = copy(g, &quiet());
    prefix.nodes.clear();
    prefix.contexts.clear();
    for (i, n) in g.nodes.iter().enumerate() {
        prefix.active = g.contexts[i];
        env.validate(&prefix, n).unwrap();
        prefix.push(n.clone()).unwrap();
    }
}
fn sample(missing: bool, body: &str) -> (PreparedObserved, Graph, Layout) {
    let p = prepared(fixture::inputs(missing, body));
    let (mut g, t) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let l = retain_finite(&env, &mut g, t, p.shared_inputs(), &mut quiet())
        .unwrap()
        .unwrap();
    (p, g, l)
}
fn finite(q: &Coordinate) -> &FiniteCoordinate {
    let Source::Finite(q) = &q.source else {
        panic!()
    };
    q
}
fn subject(g: &Graph, q: &FiniteCoordinate) -> String {
    let b = q.original.bindings.iter().find(|b| b.name == "c").unwrap();
    let Scalar::Subject { subject, .. } = g.scalar(b.value).unwrap() else {
        panic!()
    };
    subject.clone()
}
fn values(g: &Graph, r: NodeRef) -> Vec<String> {
    use crate::canonical::Json;
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let Json::Obj(ref object) = v.wire() else {
        panic!()
    };
    let Json::Arr(ref values) = object["values"] else {
        panic!()
    };
    values
        .iter()
        .map(|value| {
            let Json::Obj(value) = value else { panic!() };
            let Json::Str(id) = &value["node"] else {
                panic!()
            };
            let r = NodeRef(id.strip_prefix('n').unwrap().parse().unwrap());
            let Scalar::Z(n) = g.scalar(r).unwrap() else {
                panic!()
            };
            n.to_string()
        })
        .collect()
}
const LAWS: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
#[test]
fn every_finite_column_uses_the_real_shared_z_to_d_function_and_whole_law_judgment() {
    let (p, g, l) = sample(false, LAWS);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    assert_eq!(l.data.factors.len(), 1);
    assert_eq!(l.data.indices.len(), 4);
    assert_eq!(l.data.objects.len(), 3);
    assert_eq!(checked.atoms.len(), 8);
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.status, EquationPresentationStatus::Ready);
        assert_eq!(row.coordinates.len(), 4);
        for (i, q) in row.coordinates.iter().enumerate() {
            let f = finite(q);
            let c = subject(&g, f);
            let origin = super::super::law_evaluation::origin(&g, f.original.row)
                .unwrap()
                .unwrap();
            let applicable = object == 0 || c == if object == 1 { "p" } else { "q" };
            let expected = if !applicable {
                ["0", "0", "0", "0"]
            } else {
                match (origin.declaration.as_str(), c.as_str()) {
                    ("Selected.zero", "p") => ["0", "0", "1", "1"],
                    ("Selected.zero", "q") => ["0", "1", "0", "1"],
                    ("Selected.one", "p") => ["1", "1", "0", "0"],
                    ("Selected.one", "q") => ["1", "0", "1", "0"],
                    _ => panic!(),
                }
            };
            assert_eq!(values(&g, f.value.nu), expected);
            assert_eq!(q.factor, Some(0));
            assert!(l.data.indices.contains(&q.index));
            assert_eq!(f.object, object);
            let violated = applicable
                && ((origin.declaration.ends_with("zero") && c == "q")
                    || (origin.declaration.ends_with("one") && c == "p"));
            if !applicable {
                assert!(f.value.epsilon.is_none());
            }
            let e = f.epsilon.unwrap();
            assert_eq!(values(&g, e), vec![if violated { "1" } else { "0" }; 4]);
            let index = l.data.indices.iter().position(|r| *r == q.index).unwrap();
            assert_eq!(
                g.get(l.table.objects[object].holds[index])
                    .unwrap()
                    .judgment
                    .as_ref()
                    .unwrap()
                    .status,
                if violated {
                    Decision::Refuted
                } else {
                    Decision::Established
                }
            );
            for atom in checked.atoms {
                let got = checked
                    .at(object, i, Reading::Residual, 0, atom, &mut quiet())
                    .unwrap();
                assert_eq!(
                    got,
                    if atom == &l.data.anchor {
                        Placed::Value {
                            ring: l.data.factors[0],
                            reference: e,
                        }
                    } else {
                        Placed::Zero {
                            ring: l.data.factors[0],
                        }
                    }
                );
            }
            assert_eq!(
                checked
                    .at(object, i, Reading::Epsilon, 0, &l.data.anchor, &mut quiet())
                    .unwrap(),
                checked
                    .at(
                        object,
                        i,
                        Reading::Residual,
                        0,
                        &l.data.anchor,
                        &mut quiet()
                    )
                    .unwrap()
            );
        }
    }
    // 同じ法則の全node再検査は欠測の表(missing_observations_...)が代表する。
}
#[test]
fn finite_value_parameters_keep_every_binding_guard_row_and_quantified_global_index() {
    let (p, g, l) = sample(
        false,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    assert_eq!(l.data.indices.len(), 2);
    assert!(
        l.data
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "b" && q.domain.is_some())
    );
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.coordinates.len(), 4);
        for q in &row.coordinates {
            let f = finite(q);
            let c = subject(&g, f);
            let b = f.original.bindings.iter().find(|b| b.name == "b").unwrap();
            let Scalar::Bool(on) = g.scalar(b.value).unwrap() else {
                panic!()
            };
            let applicable = object == 0 || c == if object == 1 { "p" } else { "q" };
            let expected = if !*on || !applicable {
                ["0", "0", "0", "0"]
            } else if c == "p" {
                ["0", "0", "1", "1"]
            } else {
                ["0", "1", "0", "1"]
            };
            assert_eq!(values(&g, f.value.nu), expected);
            let origin = super::super::law_evaluation::origin(&g, q.index)
                .unwrap()
                .unwrap();
            assert_eq!(origin.bindings.len(), 1);
            assert_eq!(f.original.bindings.len(), 2);
        }
    }
    let Plan::Finite(plan) = &l.plan else {
        panic!()
    };
    for d in plan.diagrams().unwrap() {
        for r in d.readings {
            if r.reading.guard == Some(false) {
                assert!(r.body.is_none());
                assert_eq!(r.reading.holds, Some(true));
            }
        }
    }
    replay(&p, &g);
}
#[test]
fn finite_indicator_includes_the_guard_and_does_not_claim_to_be_the_polynomial_difference() {
    let (p, g, l) = sample(
        false,
        "law required guarded(c:Part) when c.quantity=0:c.quantity=1;",
    );
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(checked.is_complete());
    for (object, row) in l.data.objects.iter().enumerate() {
        for q in &row.coordinates {
            let f = finite(q);
            let c = subject(&g, f);
            let applies = object == 0 || c == if object == 1 { "p" } else { "q" };
            let expected = if !applies {
                ["0", "0", "0", "0"]
            } else if c == "p" {
                ["1", "1", "0", "0"]
            } else {
                ["1", "0", "1", "0"]
            };
            assert_eq!(values(&g, f.value.nu), expected);
            assert_eq!(
                values(&g, f.epsilon.unwrap()),
                vec![if applies && c == "p" { "1" } else { "0" }; 4]
            );
        }
    }
    let Plan::Finite(plan) = &l.plan else {
        panic!()
    };
    assert!(
        plan.diagrams()
            .unwrap()
            .iter()
            .flat_map(|d| &d.readings)
            .any(|r| r.reading.guard == Some(false) && r.body.is_none())
    );
    replay(&p, &g);
}
#[test]
fn missing_observations_keep_uncomputed_indicator_values_and_original_reasons() {
    let (p, g, l) = sample(true, LAWS);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let checked = l.checked(&env, &g, &mut quiet()).unwrap();
    assert!(!checked.is_complete());
    assert_eq!(l.data.objects.len(), 3);
    let mut unknown = 0;
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.coordinates.len(), 4);
        for (i, q) in row.coordinates.iter().enumerate() {
            let f = finite(q);
            let missing = subject(&g, f) == "q" && (object == 0 || object == 2);
            if missing {
                unknown += 1;
                assert!(f.epsilon.is_none());
                assert_eq!(
                    checked
                        .at(
                            object,
                            i,
                            Reading::Residual,
                            0,
                            &l.data.anchor,
                            &mut quiet()
                        )
                        .unwrap(),
                    Placed::Uncomputed {
                        ring: l.data.factors[0]
                    }
                );
            }
        }
    }
    assert_eq!(unknown, 4);
    assert!(
        l.data
            .reasons
            .iter()
            .flat_map(|r| &r.missing)
            .any(|f| f.subject == "q" && f.field.as_deref() == Some("Family.Part.quantity"))
    );
    replay(&p, &g);
}
#[test]
fn an_unavailable_finite_plan_does_not_change_the_table_or_create_a_completed_layout() {
    let p = prepared(polynomial_fixture::inputs(
        false,
        false,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let (mut g, t) = start(&p);
    let before = g.nodes.clone();
    let contexts = g.contexts.clone();
    let active = g.active;
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    assert!(
        retain_finite(&env, &mut g, t, p.shared_inputs(), &mut quiet())
            .unwrap()
            .is_none()
    );
    assert_eq!(g.nodes, before);
    assert_eq!(g.contexts, contexts);
    assert_eq!(g.active, active);
    replay(&p, &g);
}
#[test]
fn an_empty_law_family_keeps_the_empty_block_product_and_all_objects_without_a_fake_finite_factor()
{
    let p = prepared(fixture::inputs(false, ""));
    let (mut g, t) = start(&p);
    let before = g.nodes.clone();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let l = retain_finite(&env, &mut g, t, p.shared_inputs(), &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(g.nodes, before);
    assert!(l.data.factors.is_empty() && l.data.indices.is_empty());
    assert_eq!(l.data.objects.len(), 3);
    assert!(l.data.objects.iter().all(|o| o.coordinates.is_empty()));
    assert!(l.checked(&env, &g, &mut quiet()).unwrap().is_complete());
    replay(&p, &g);
}
#[test]
fn finite_construction_interrupt_keeps_the_exact_finished_node_prefix_and_request_context() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(fixture::inputs(
        false,
        "law required zero(c:Part):c.quantity=0;",
    ));
    let (initial, t) = start(&p);
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::NativeResultNode {
            count.set(count.get() + 1)
        }
        None
    });
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut full = copy(&initial, &c);
    retain_finite(&env, &mut full, t.clone(), p.shared_inputs(), &mut c)
        .unwrap()
        .unwrap();
    let total = seen.get();
    assert!(total > 4);
    // 計画用checkpointでなく、実nodeの転記直前・直後で止める。
    let mut partial = false;
    let mut end = false;
    for at in [total / 2, total] {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let probes = Rc::new(Cell::new(0));
        let samples = probes.clone();
        let mut c = Control::new(move |point| {
            samples.set(samples.get() + 1);
            if point == Checkpoint::NativeResultNode {
                count.set(count.get() + 1)
            }
            let stop = count.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let mut g = copy(&initial, &c);
        let expected = crate::result::Signal::Int;
        assert!(matches!(
            retain_finite(&env, &mut g, t.clone(), p.shared_inputs(), &mut c),
            Err(ValidationFailure::Stop(reason)) if reason == expected
        ));
        assert_eq!(seen.get(), at);
        let frozen = probes.get();
        assert_eq!(c.checkpoint(Checkpoint::NativeResultNode), Err(expected));
        assert_eq!(probes.get(), frozen);
        assert_eq!(g.active, initial.active);
        assert!(env.state.architecture_ref().is_none());
        assert_eq!(&g.nodes[..initial.nodes.len()], &initial.nodes);
        assert!(g.nodes.len() <= full.nodes.len());
        for (i, n) in g.nodes.iter().enumerate() {
            assert_eq!(
                n.wire(i, &g.nodes[..i]),
                full.nodes[i].wire(i, &full.nodes[..i])
            );
        }
        assert_eq!(g.contexts, &full.contexts[..g.nodes.len()]);
        partial |= g.nodes.len() > initial.nodes.len() && g.nodes.len() < full.nodes.len();
        end |= g.nodes.len() == full.nodes.len();
        replay(&p, &g);
    }
    assert!(partial);
    assert!(end);
}

#[test]
fn boolean_fields_use_the_finite_indicator_with_original_boolean_operands() {
    use crate::input::{InputSources, check_inputs};
    // The Law is checked only after changing the shared definition and its digest.
    let source = fixture::inputs(false, "");
    let bytes = source.sources();
    let definition = String::from_utf8(bytes.definitions()[0].bytes().to_vec())
        .unwrap()
        .replace(r#"["Fp","2"]"#, r#""Bool""#);
    assert_ne!(definition.as_bytes(), bytes.definitions()[0].bytes());
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let old = &source.definitions().vocabularies["Family"].digest;
    let digest = &defs.vocabularies["Family"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Family version \"1\" digest \"{digest}\";law required on(c:Part):c.quantity=true;}}"
    );
    let map = String::from_utf8(bytes.archmap().bytes().to_vec())
        .unwrap()
        .replace(old, digest)
        .replace(r#""value":"0""#, r#""value":false"#)
        .replace(r#""value":"1""#, r#""value":true"#);
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
    let p = prepared(inputs);
    let (mut g, t) = start(&p);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let l = retain_finite(&env, &mut g, t, p.shared_inputs(), &mut quiet())
        .unwrap()
        .unwrap();
    assert!(l.checked(&env, &g, &mut quiet()).unwrap().is_complete());
    assert_eq!(l.data.factors.len(), 1);
    assert_eq!(l.data.indices.len(), 2);
    for (object, row) in l.data.objects.iter().enumerate() {
        assert_eq!(row.coordinates.len(), 2);
        for q in &row.coordinates {
            let f = finite(q);
            let c = subject(&g, f);
            let applies = object == 0 || c == if object == 1 { "p" } else { "q" };
            let expected = if !applies {
                ["0", "0", "0", "0"]
            } else if c == "p" {
                ["1", "1", "0", "0"]
            } else {
                ["1", "0", "1", "0"]
            };
            assert_eq!(values(&g, f.value.nu), expected);
            assert_eq!(
                values(&g, f.epsilon.unwrap()),
                vec![if applies && c == "p" { "1" } else { "0" }; 4]
            );
            assert_eq!(
                g.get(f.value.lhs).unwrap().ty,
                NodeType::Expression(crate::types::Type::Bool)
            );
            assert_eq!(
                g.get(f.value.rhs).unwrap().ty,
                NodeType::Expression(crate::types::Type::Bool)
            );
        }
    }
    replay(&p, &g);
}
