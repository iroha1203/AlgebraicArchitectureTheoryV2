use super::*;
use crate::{
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/polynomial_law_family_data.rs");
}
#[allow(dead_code)]
mod finite_fixture {
    include!("../../../tests/common/finite_law_reading_data.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
fn prepared(inputs: Arc<crate::input::CheckedInputs>) -> PreparedObserved {
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
    for (i, n) in source.nodes.iter().enumerate() {
        g.active = source.contexts[i];
        env.validate(&g, n)?;
        g.push(n.clone())?;
    }
    Ok(())
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
fn native(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::LawInstantiation(d) = &v.data else {
        panic!("instantiation")
    };
    d
}
fn poly(
    p: &PreparedObserved,
) -> (
    Graph,
    Vec<NodeRef>,
    Vec<crate::observed::polynomial_law_diagram::Diagram>,
) {
    let (mut g, a, objects) = start(p);
    let ds = crate::observed::polynomial_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap();
    (g, objects, ds)
}
fn candidates(
    g: &Graph,
    ds: &[crate::observed::polynomial_law_diagram::Diagram],
) -> Vec<(NodeRef, NodeRef, usize)> {
    let mut pairs = vec![];
    for base in &ds[0].originals {
        let b = frames::origin(g, base.reference).unwrap().unwrap();
        if !b.ready {
            continue;
        }
        for (object, d) in ds.iter().enumerate().skip(1) {
            for target in d.originals.iter().filter(|target| target.row.is_none()) {
                let t = frames::origin(g, target.reference).unwrap().unwrap();
                if t.outside
                    && b.declaration == t.declaration
                    && t.bindings.iter().all(|f| {
                        b.bindings.iter().any(|v| {
                            v.name == f.name
                                && v.ty == f.ty
                                && g.scalar(v.value).unwrap() == g.scalar(f.value).unwrap()
                        })
                    })
                {
                    pairs.push((base.reference, target.reference, object));
                }
            }
        }
    }
    pairs
}
#[test]
fn polynomial_complete_bindings_specialize_every_outside_template_and_keep_unread_body() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    let pairs = candidates(&g, &ds);
    assert_eq!(pairs.len(), 4);
    let mut values = vec![];
    for (base, template, object) in pairs {
        let b = frames::origin(&g, base).unwrap().unwrap();
        let t = frames::origin(&g, template).unwrap().unwrap();
        assert_eq!(t.bindings.len(), 1);
        assert_eq!(b.bindings.len(), 2);
        let before = g.nodes.len();
        let row = instantiate(&env, &mut g, base, template, objects[object], &mut quiet()).unwrap();
        assert_eq!(g.nodes.len(), before + 1);
        let d = native(&g, row);
        assert_eq!(
            (d.base, d.template, d.architecture),
            (base, template, objects[object])
        );
        let Some(Payload::Construction(base_value)) = &g.nodes[base.0].payload else {
            panic!()
        };
        assert_eq!(d.wire(), base_value.wire());
        assert_eq!(g.nodes[row.0].ty, NodeType::LawInstance);
        assert_eq!(
            g.nodes[row.0].scope.quantifiers,
            g.nodes[base.0].scope.quantifiers
        );
        let inst = frames::origin(&g, row).unwrap().unwrap();
        assert_eq!(inst.object, object);
        assert!(inst.outside);
        assert!(!inst.ready);
        assert!(!inst.body_allowed);
        assert_eq!(inst.bindings, b.bindings);
        assert_eq!(inst.body, b.body);
        assert_eq!(inst.guard, b.guard);
        let answer = crate::observed::law_inapplicable::check(
            &env,
            &mut g,
            row,
            objects[object],
            &mut quiet(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(answer.status, Decision::Established);
        assert_eq!(g.nodes.len(), before + 4);
        assert!(
            g.nodes[before..]
                .iter()
                .all(|n| matches!(n.payload, Some(Payload::Construction(_))))
        );
        let Some(Payload::Construction(v)) = &g.nodes[answer.outputs["evaluation"].0].payload
        else {
            panic!()
        };
        let Json::Obj(ref wire) = v.wire() else {
            panic!()
        };
        assert_eq!(wire["applicability"], Json::str("not_applicable"));
        assert_eq!(wire["expression"], b.body_reference.wire());
        assert_eq!(wire["environment"], objects[object].wire());
        let Json::Arr(parts) = &wire["parts"] else {
            panic!()
        };
        let Json::Obj(body) = &parts[0] else { panic!() };
        assert!(!body.contains_key("value"));
        assert!(!body.contains_key("residual"));
        values.push((object, g.scalar(b.bindings[1].value).unwrap().clone()));
        assert!(
            frames::prepare_instance(&env, &mut g, row, objects[object], &mut quiet())
                .unwrap()
                .is_none()
        );
    }
    values.sort_by_key(|(o, b)| (*o, matches!(b, Scalar::Bool(true))));
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
fn closed_finite_scalar_products_roles_and_guards_keep_original_specialization() {
    for body in [
        "law required bit(c:Part,b:Bool,d:Bool) when false:c.quantity=0;",
        "law required bit(c:Part,b:Fp(2)):c.quantity=0;",
    ] {
        let p = prepared(fixture::inputs(true, false, body));
        let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
        let (mut g, objects, ds) = poly(&p);
        let pairs = candidates(&g, &ds);
        assert!(!pairs.is_empty(), "{body}");
        for (base, template, object) in pairs {
            let row =
                instantiate(&env, &mut g, base, template, objects[object], &mut quiet()).unwrap();
            let answer = crate::observed::law_inapplicable::check(
                &env,
                &mut g,
                row,
                objects[object],
                &mut quiet(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(answer.status, Decision::Established);
        }
        replay(&p, &g).unwrap();
    }
}
#[test]
fn finite_native_rows_use_scalar_identity_across_separately_retained_objects() {
    let p = prepared(finite_fixture::inputs(
        true,
        "law optional bit(c:Part,b:Bool) when b:c.quantity=0;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, a, objects) = start(&p);
    let ds = crate::observed::finite_law_diagram::retain_family(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let mut count = 0;
    for (object, d) in ds.iter().enumerate().skip(1) {
        for target in &d.originals {
            let t = frames::origin(&g, target.row).unwrap().unwrap();
            if !t.outside {
                continue;
            }
            let base = ds[0]
                .originals
                .iter()
                .find(|o| {
                    let b = frames::origin(&g, o.row).unwrap().unwrap();
                    b.ready
                        && b.bindings
                            .iter()
                            .zip(&t.bindings)
                            .all(|(x, y)| g.scalar(x.value).unwrap() == g.scalar(y.value).unwrap())
                })
                .unwrap()
                .row;
            let row = instantiate(
                &env,
                &mut g,
                base,
                target.row,
                objects[object],
                &mut quiet(),
            )
            .unwrap();
            assert!(
                crate::observed::law_inapplicable::check(
                    &env,
                    &mut g,
                    row,
                    objects[object],
                    &mut quiet()
                )
                .unwrap()
                .is_some()
            );
            count += 1;
        }
    }
    assert_eq!(count, 4);
    replay(&p, &g).unwrap();
}
fn first() -> (PreparedObserved, Graph, Vec<NodeRef>, NodeRef, NodeRef) {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required bit(c:Part,b:Bool) when b:c.quantity=0;law optional other(c:Part,b:Bool):c.quantity=1;",
    ));
    let (g, objects, ds) = poly(&p);
    let (base, target, _) = candidates(&g, &ds)
        .into_iter()
        .find(|(_, _, o)| *o == 1)
        .unwrap();
    (p, g, objects, base, target)
}
#[test]
fn self_and_future_dependencies_are_rejected_before_recursive_recheck() {
    let (p, mut g, objects, base, target) = first();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let row = instantiate(&env, &mut g, base, target, objects[1], &mut quiet()).unwrap();
    for mode in 0..6 {
        let mut bad = copy_graph(&g, &quiet());
        let Some(Payload::Construction(v)) = &mut bad.nodes[row.0].payload else {
            panic!()
        };
        let D::LawInstantiation(d) = &mut v.data else {
            panic!()
        };
        let invalid = NodeRef(row.0 + usize::from(mode >= 3));
        match mode % 3 {
            0 => d.base = invalid,
            1 => d.template = invalid,
            _ => d.architecture = invalid,
        };
        bad.nodes[row.0].arguments = d.arguments();
        assert!(
            matches!(
                env.recheck_node(&bad, &bad.nodes[row.0], row.0),
                Err(ValidationFailure::Internal(_))
            ),
            "mode {mode}"
        );
    }
}
#[test]
fn unbound_integer_specialization_preserves_the_original_symbolic_family() {
    let p = prepared(fixture::inputs(
        false,
        false,
        "law required unbounded(c:Part,k:Z):c.quantity=k;",
    ));
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let (mut g, objects, ds) = poly(&p);
    assert!(ds.iter().all(|d| d.unavailable.is_none()));
    assert!(ds.iter().flat_map(|d| &d.originals).all(|o| o.row.is_none() && o.parameters == vec![("k".into(), crate::types::Type::Z)]));
    for base in &ds[0].originals {
        for target in &ds[1].originals {
            let source = frames::origin(&g, base.reference).unwrap().unwrap();
            let target_origin = frames::origin(&g, target.reference).unwrap().unwrap();
            let valid = target_origin.outside && target_origin.bindings.iter().all(|fixed| source.bindings.iter().any(|b| b.name == fixed.name && b.ty == fixed.ty && g.scalar(b.value).unwrap() == g.scalar(fixed.value).unwrap()));
            let before = g.nodes.len();
            let result = instantiate(&env, &mut g, base.reference, target.reference, objects[1], &mut quiet());
            assert_eq!(result.is_ok(), valid);
            if let Ok(row) = result {
                assert_eq!(g.nodes.len(), before + 1);
                assert_eq!(g.nodes[row.0].scope.quantifiers, g.nodes[base.reference.0].scope.quantifiers);
                let specialized = frames::origin(&g, row).unwrap().unwrap();
                assert!(specialized.outside && !specialized.ready && !specialized.body_allowed);
                assert_eq!(specialized.bindings, source.bindings);
                assert_eq!(specialized.body, source.body);
                let Some(Payload::Construction(original)) = &g.nodes[base.reference.0].payload else { panic!("original") };
                assert_eq!(native(&g, row).wire(), original.wire());
            } else {
                assert_eq!(g.nodes.len(), before);
            }
        }
    }
    replay(&p, &g).unwrap();
}
#[test]
fn interrupt_retains_only_the_completed_specialization_prefix() {
    use std::{cell::Cell, rc::Rc};
    let (p, initial, objects, base, target) = first();
    let env = Environment::with_prepared(&p, &mut quiet()).unwrap();
    let mut complete = copy_graph(&initial, &quiet());
    instantiate(&env, &mut complete, base, target, objects[1], &mut quiet()).unwrap();
    for at in [2, 3] {
        let seen = Rc::new(Cell::new(0));
        let counter = seen.clone();
        let mut c = Control::new(move |point| {
            if point == Checkpoint::ObjectEvaluation {
                counter.set(counter.get() + 1)
            }
            let stop = counter.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = copy_graph(&initial, &c);
        assert!(matches!(
            instantiate(&env, &mut g, base, target, objects[1], &mut c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.active, initial.active);
        assert_eq!(g.nodes, &complete.nodes[..g.nodes.len()]);
        assert_eq!(g.contexts, &complete.contexts[..g.nodes.len()]);
        assert_eq!(g.nodes.len(), initial.nodes.len() + usize::from(at == 3));
        replay(&p, &g).unwrap();
    }
}
