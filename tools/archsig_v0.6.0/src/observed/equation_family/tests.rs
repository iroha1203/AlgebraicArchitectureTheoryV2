use super::*;
use crate::{
    input::CheckedInputs,
    observed::{PreparedObserved, law_table, observable_layout, request::resolve_native_for_test},
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
fn start(p: &PreparedObserved, finite: bool) -> (Graph, Arc<Layout>) {
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
    let table = Arc::new(
        law_table::retain(&env, &mut g, p.shared_inputs(), a.reference, &mut quiet())
            .unwrap()
            .unwrap(),
    );
    let layout = if finite {
        observable_layout::retain_finite(&env, &mut g, table, p.shared_inputs(), &mut quiet())
            .unwrap()
            .unwrap()
    } else {
        observable_layout::retain(&env, &g, table, &mut quiet()).unwrap()
    };
    (g, Arc::new(layout))
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
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.get(r).unwrap().payload else {
        panic!()
    };
    let D::EquationFamily(d) = &v.data else {
        panic!()
    };
    d
}
fn field<'a>(j: &'a Json, name: &str) -> &'a Json {
    let Json::Obj(o) = j else { panic!() };
    &o[name]
}
#[test]
fn finite_family_keeps_all_original_rows_presentations_and_refuted_laws() {
    let p = prepared(
        fixture::inputs(false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (mut g, l) = start(&p, true);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let old = g.nodes.len();
    let r = retain(&env, &mut g, l.clone(), &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(r, NodeRef(old));
    assert_eq!(g.nodes.len(), old + 1);
    let d = data(&g, r);
    let t = l.law_table();
    assert_eq!(d.output.indices, t.indices);
    assert_eq!(d.output.indices.len(), 2);
    assert_eq!(d.output.factors, l.data.factors);
    assert_eq!(d.output.factors.len(), 1);
    assert_eq!(d.output.universe, l.data.universe);
    assert_eq!(d.output.anchor, l.data.anchor);
    assert!(d.output.anchor.field.is_none() && d.output.anchor.atom.is_none());
    assert_eq!(d.output.objects.len(), 3);
    assert_eq!(d.output.coordinates.len(), 2);
    for (i, o) in d.output.objects.iter().enumerate() {
        assert_eq!(o.object, t.objects[i].object);
        assert_eq!(o.evaluations, t.objects[i].evaluations);
        assert_eq!(o.holds, t.objects[i].holds);
        assert_eq!(
            o.presentations,
            l.data.objects[i]
                .presentations
                .iter()
                .map(|r| r.unwrap())
                .collect::<Vec<_>>()
        );
        assert_eq!(o.holds.len(), 2);
        assert_eq!(o.presentations.len(), 1);
    }
    assert!(
        d.output.objects[0].holds.iter().any(|r| g
            .get(*r)
            .unwrap()
            .judgment
            .as_ref()
            .unwrap()
            .status
            == Decision::Refuted)
    );
    assert!(
        d.output.objects[0].holds.iter().any(|r| g
            .get(*r)
            .unwrap()
            .judgment
            .as_ref()
            .unwrap()
            .status
            == Decision::Established)
    );
    for (q, s) in d
        .output
        .coordinates
        .iter()
        .zip(&l.data.objects[0].coordinates)
    {
        let CoordinateSource::Finite(s) = &s.source else {
            panic!()
        };
        assert_eq!(q.instance, s.value.instance);
        assert_eq!(q.component, s.value.component);
        assert_eq!(q.factor, 0);
        assert_eq!(
            g.get(s.value.lhs).unwrap().ty,
            NodeType::Expression(crate::types::Type::Fp("2".into()))
        );
        assert_eq!(
            g.get(s.value.rhs).unwrap().ty,
            NodeType::Expression(crate::types::Type::Fp("2".into()))
        );
    }
    let n = g.get(r).unwrap();
    assert_eq!(n.ty, NodeType::Construction(T::EquationFamily));
    assert_eq!(n.rule, Rule::Construction("equation_family"));
    assert!(n.judgment.is_none());
    assert_eq!(n.arguments, d.arguments());
    assert!(n.arguments.iter().all(|r| r.0 < old));
    assert_eq!(n.support, l.data.support);
    assert_eq!(n.scope, l.data.scope);
    let wire = d.wire();
    let Json::Obj(fields) = &wire else { panic!() };
    assert_eq!(fields.len(), 4);
    assert_eq!(field(&wire, "indices"), &refs(&t.indices));
    assert_eq!(field(&wire, "observable_factors"), &refs(&l.data.factors));
    assert_eq!(
        field(field(&wire, "embedding"), "universe"),
        &l.data.universe.wire()
    );
    assert_eq!(
        field(field(&wire, "embedding"), "anchor"),
        &l.data.anchor.wire()
    );
    let Json::Arr(rows) = field(&wire, "objects") else {
        panic!()
    };
    for (i, row) in rows.iter().enumerate() {
        assert_eq!(field(row, "object"), &t.objects[i].object.wire());
        assert_eq!(field(row, "evaluations"), &refs(&t.objects[i].evaluations));
        assert_eq!(field(row, "holds"), &refs(&t.objects[i].holds));
    }
    env.recheck_node(&g, n, r.0).unwrap();
    replay(&p, &g);
}
#[test]
fn finite_parameter_coordinates_keep_actual_bindings_and_symbolic_whole_scope() {
    let p = prepared(
        fixture::inputs(
            false,
            "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
        ),
        "root",
    );
    let (mut g, l) = start(&p, true);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = retain(&env, &mut g, l.clone(), &mut quiet())
        .unwrap()
        .unwrap();
    let d = data(&g, r);
    assert_eq!(d.output.indices.len(), 2);
    assert_eq!(d.output.coordinates.len(), 4);
    let mut parameters = vec![];
    for q in &d.output.coordinates {
        let o = crate::observed::law_evaluation::origin(&g, q.instance)
            .unwrap()
            .unwrap();
        assert!(o.declaration.ends_with(".bit"));
        let b = o.bindings.iter().find(|b| b.name == "b").unwrap();
        parameters.push((
            o.bindings
                .iter()
                .find(|b| b.name == "c")
                .map(|b| g.scalar(b.value).unwrap().clone())
                .unwrap(),
            g.scalar(b.value).unwrap().clone(),
        ));
    }
    assert_eq!(parameters.len(), 4);
    for subject in ["p", "q"] {
        for b in [false, true] {
            assert_eq!(
                parameters
                    .iter()
                    .filter(
                        |(s, v)| matches!(s,Scalar::Subject{subject:s,..} if s==subject)
                            && *v == Scalar::Bool(b)
                    )
                    .count(),
                1
            );
        }
    }
    assert!(
        g.get(r)
            .unwrap()
            .scope
            .quantifiers
            .iter()
            .any(|q| q.name == "b" && q.domain.is_some())
    );
    assert!(d.output.objects.iter().all(|o| o.holds.len() == 2));
    replay(&p, &g);
}
#[test]
fn polynomial_family_preserves_integer_ring_and_actual_epsilon_even_when_refuted() {
    let p = prepared(
        polynomial_fixture::inputs(
            false,
            false,
            "law required yes(c:Root):0=0;law optional no(c:Root):0=1;",
        ),
        "r2",
    );
    let (mut g, l) = start(&p, false);
    assert!(l.data.complete);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = retain(&env, &mut g, l.clone(), &mut quiet())
        .unwrap()
        .unwrap();
    let d = data(&g, r);
    assert_eq!(d.output.indices.len(), 2);
    assert_eq!(d.output.objects.len(), 1);
    assert_eq!(d.output.coordinates.len(), 2);
    assert_eq!(d.output.factors.len(), 1);
    for (q, source) in d
        .output
        .coordinates
        .iter()
        .zip(&l.data.objects[0].coordinates)
    {
        let CoordinateSource::Polynomial(s) = &source.source else {
            panic!()
        };
        assert_eq!(q.instance, s.instance);
        assert_eq!(q.component, s.component);
        assert_eq!(q.factor, 0);
        assert_eq!(
            g.get(s.lhs).unwrap().ty,
            NodeType::Expression(crate::types::Type::Z)
        );
        assert!(s.nu.is_some() && s.epsilon.is_some() && s.residual.is_some());
    }
    let mut refuted = 0;
    for (index, r) in d.output.indices.iter().enumerate() {
        let origin = crate::observed::law_evaluation::origin(&g, *r)
            .unwrap()
            .unwrap();
        let failed = origin.declaration == "Selected.no";
        assert!(failed || origin.declaration == "Selected.yes");
        let n = g.get(d.output.objects[0].holds[index]).unwrap();
        assert_eq!(
            n.judgment.as_ref().unwrap().status,
            if failed {
                Decision::Refuted
            } else {
                Decision::Established
            }
        );
        if failed {
            assert!(!n.evidence.is_empty());
            refuted += 1;
        }
    }
    assert_eq!(refuted, 1);
    replay(&p, &g);
}
#[test]
fn empty_family_keeps_all_objects_and_empty_block_product() {
    let p = prepared(fixture::inputs(false, ""), "root");
    let (mut g, l) = start(&p, true);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = retain(&env, &mut g, l, &mut quiet()).unwrap().unwrap();
    let d = data(&g, r);
    assert_eq!(d.output.objects.len(), 3);
    assert!(
        d.output.indices.is_empty()
            && d.output.coordinates.is_empty()
            && d.output.factors.is_empty()
    );
    for o in &d.output.objects {
        assert!(o.evaluations.is_empty() && o.holds.is_empty() && o.presentations.is_empty());
    }
    replay(&p, &g);
}
#[test]
fn missing_and_unfinished_presentations_do_not_publish_a_completed_family() {
    for finite in [false, true] {
        let inputs = if finite {
            fixture::inputs(true, "law required zero(c:Part):c.quantity=0;")
        } else {
            polynomial_fixture::inputs(true, false, "law required zero(c:Part):c.quantity=0;")
        };
        let p = prepared(inputs, "root");
        let (mut g, l) = start(&p, finite);
        assert!(!l.data.complete);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let old = copy(&g, &quiet());
        assert!(retain(&env, &mut g, l, &mut quiet()).unwrap().is_none());
        assert_eq!(g.nodes, old.nodes);
        assert_eq!(g.contexts, old.contexts);
        assert_eq!(g.active, old.active);
        assert!(
            !g.nodes
                .iter()
                .any(|n| n.ty == NodeType::Construction(T::EquationFamily))
        );
        replay(&p, &g);
    }
}
#[test]
fn interrupt_keeps_the_completed_graph_prefix_and_original_request_context() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(
        fixture::inputs(false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (initial, l) = start(&p, true);
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut c = Control::new(move |point| {
        if matches!(
            point,
            Checkpoint::EquationPresentation | Checkpoint::NativeResultNode
        ) {
            seen.set(seen.get() + 1)
        }
        None
    });
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut full = copy(&initial, &c);
    let r = retain(&env, &mut full, l.clone(), &mut c).unwrap().unwrap();
    assert_eq!(r.0, initial.nodes.len());
    let total = count.get();
    assert!(total > 4);
    let mut finished = false;
    for at in [total / 2, total] {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut c = Control::new(move |point| {
            if matches!(
                point,
                Checkpoint::EquationPresentation | Checkpoint::NativeResultNode
            ) {
                count.set(count.get() + 1)
            }
            let stop = count.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = copy(&initial, &c);
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        assert!(matches!(
            retain(&env, &mut g, l.clone(), &mut c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.active, initial.active);
        assert!(env.state.architecture_ref().is_none());
        assert!(g.nodes.len() <= full.nodes.len());
        for (i, n) in g.nodes.iter().enumerate() {
            assert_eq!(
                n.wire(i, &g.nodes[..i]),
                full.nodes[i].wire(i, &full.nodes[..i])
            );
        }
        assert_eq!(g.contexts, &full.contexts[..g.nodes.len()]);
        finished |= g.nodes.len() == full.nodes.len();
        if at < total {
            replay(&p, &g);
        }
    }
    assert!(finished);
}

#[test]
fn tuple_integer_rational_components_keep_distinct_factors_and_original_field_slots() {
    use crate::input::{InputSources, check_inputs};
    let original = polynomial_fixture::inputs(false, true, "");
    let bytes = original.sources();
    let definition = String::from_utf8(bytes.definitions()[0].bytes().to_vec()).unwrap()
        .replace(r#""fields":[],"alignments":[]"#, r#""fields":[{"name":"amount","type":["Tuple","Z","Q"],"meaning":"成分値。"}],"alignments":[]"#);
    assert_ne!(definition.as_bytes(), bytes.definitions()[0].bytes());
    let defs =
        crate::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let old = &original.definitions().vocabularies()["Family"].digest;
    let digest = &defs.vocabularies()["Family"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Family version \"1\" digest \"{digest}\";law required pair(r:Root):r.amount=(0,0);}}"
    );
    let map=String::from_utf8(bytes.archmap().bytes().to_vec()).unwrap().replace(old,digest)
        .replace(r#""atoms":["#, r#""atoms":[{"id":"amount","subject":"r2","field":"Family.Root.amount","value":["1",["1","2"]],"origin":"model"},"#);
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
    let p = prepared(inputs, "r2");
    let (mut g, l) = start(&p, false);
    assert!(l.data.complete);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = retain(&env, &mut g, l.clone(), &mut quiet())
        .unwrap()
        .unwrap();
    let d = data(&g, r);
    assert_eq!(d.output.indices.len(), 1);
    assert_eq!(d.output.objects.len(), 1);
    assert_eq!(d.output.coordinates.len(), 2);
    assert_eq!(d.output.factors.len(), 2);
    assert_ne!(d.output.factors[0], d.output.factors[1]);
    assert_eq!(d.output.objects[0].presentations.len(), 2);
    for (i, q) in d.output.coordinates.iter().enumerate() {
        assert_eq!(q.instance, d.output.coordinates[0].instance);
        assert_eq!(q.component, [i]);
        assert_eq!(q.factor, i);
        let CoordinateSource::Polynomial(source) = &l.data.objects[0].coordinates[i].source else {
            panic!()
        };
        assert_eq!(source.component, [i]);
        assert_eq!(source.ring, Some(d.output.factors[i]));
        assert_eq!(
            g.get(source.lhs).unwrap().ty,
            NodeType::Expression(if i == 0 {
                crate::types::Type::Z
            } else {
                crate::types::Type::Q
            })
        );
    }
    assert!(
        g.get(r)
            .unwrap()
            .support
            .iter()
            .any(|f| f.subject == "r2" && f.field.as_deref() == Some("Family.Root.amount"))
    );
    assert_eq!(
        g.get(d.output.objects[0].holds[0])
            .unwrap()
            .judgment
            .as_ref()
            .unwrap()
            .status,
        Decision::Refuted
    );
    replay(&p, &g);
}

#[test]
fn family_recheck_rejects_equal_architecture_clones_and_altered_requests_or_contexts() {
    let p = prepared(
        fixture::inputs(false, "law required zero(c:Part):c.quantity=0;"),
        "root",
    );
    let (mut g, l) = start(&p, true);
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let r = retain(&env, &mut g, l.clone(), &mut quiet())
        .unwrap()
        .unwrap();
    let n = g.get(r).unwrap();
    let mut forged = n.clone();
    let Some(Payload::Construction(value)) = &mut forged.payload else {
        panic!()
    };
    let Witness::Architecture(a) = &mut value.witness else {
        panic!()
    };
    *a = Arc::new((**a).clone());
    assert!(env.recheck_node(&g, &forged, r.0).is_err());
    let mut changed = copy(&g, &quiet());
    changed.requests[0].id = "other".into();
    assert!(env.recheck_node(&changed, n, r.0).is_err());
    let mut changed = copy(&g, &quiet());
    changed.contexts[r.0].instance = Some(usize::MAX);
    assert!(env.recheck_node(&changed, n, r.0).is_err());
    let mut changed = copy(&g, &quiet());
    changed.active.request = 1;
    let old = changed.nodes.len();
    assert!(retain(&env, &mut changed, l, &mut quiet()).is_err());
    assert_eq!(changed.nodes.len(), old);
    assert!(env.recheck_node(&g, n, r.0 + 1).is_err());
    replay(&p, &g);
}
