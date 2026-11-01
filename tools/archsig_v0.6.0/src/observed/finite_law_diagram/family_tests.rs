use super::*;
use crate::{
    observed::{PreparedObserved, request::resolve_native_for_test},
};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/finite_law_family_data.rs");
}
fn quiet() -> Control {
    Control::unlimited()
}
fn prepared(missing: bool, body: &str, root: &str) -> PreparedObserved {
    let inputs = fixture::inputs(missing, body);
    let ask = format!("b=build(Selected,on=@v/{root})");
    let requests = resolve_native_for_test(
        inputs.law(),
        inputs.archmap(),
        &[ask.as_str()],
        &mut quiet(),
    )
    .unwrap();
    PreparedObserved {
        inputs,
        requests,
        object: None,
    }
}
fn built(p: &PreparedObserved) -> (Graph, NodeRef) {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c).unwrap();
    let mut g = Graph::new(&c);
    g.requests = p.requests().requests().to_vec();
    let a = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[0],
        &mut c,
    )
    .unwrap();
    assert!(a.complete, "{:?}", a.reasons);
    (g, a.reference)
}
fn replay(
    p: &PreparedObserved,
    original: &Graph,
    nodes: &[Node],
) -> Result<Graph, ValidationFailure> {
    let mut c = quiet();
    let env = Environment::with_prepared(p, &mut c)?;
    let mut g = Graph::new(&c);
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    for (index, node) in nodes.iter().enumerate() {
        g.active = original.contexts[index];
        env.validate(&g, node)?;
        g.push(node.clone())?;
    }
    Ok(g)
}
fn data(g: &Graph, r: NodeRef) -> &Data {
    let Some(Payload::Construction(v)) = &g.nodes[r.0].payload else {
        panic!("native")
    };
    let D::FiniteLaw(d) = &v.data else {
        panic!("finite")
    };
    d
}
fn values(g: &Graph, r: NodeRef) -> Vec<String> {
    let Part::Function { values, .. } = data(g, r).part() else {
        panic!("function")
    };
    values
        .iter()
        .map(|r| match g.scalar(*r).unwrap() {
            Scalar::Z(n) => n.to_string(),
            _ => panic!("Z"),
        })
        .collect()
}
const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
#[test]
fn all_standard_objects_share_the_same_native_domain_ring_and_evaluation() {
    let p = prepared(false, BODY, "root");
    let (mut g, a) = built(&p);
    let before = g.nodes.len();
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(ds.len(), 3);
    let source = &data(&g, ds[0].ring).source;
    assert_eq!(
        source
            .architecture
            .readings()
            .objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["root", "p", "q"]
    );
    assert_eq!(source.owned_outputs.as_ref().unwrap().len(), 2);
    for (object, d) in ds.iter().enumerate() {
        for (coordinate, column) in d.columns.iter().enumerate() {
            let original = d.originals.iter().find(|o| o.column == *column).unwrap();
            let Part::LawInstance { name, .. } = data(&g, original.row).part() else {
                panic!("instance")
            };
            let binding = original.bindings.iter().find(|b| b.name == "c").unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(binding.value).unwrap() else {
                panic!("subject")
            };
            let applicable =
                object == 0 || (object == 1 && subject == "p") || (object == 2 && subject == "q");
            let expected = if !applicable {
                ["0", "0", "0", "0"]
            } else {
                match (name.as_str(), subject.as_str()) {
                    ("Selected.zero", "p") => ["0", "0", "1", "1"],
                    ("Selected.zero", "q") => ["0", "1", "0", "1"],
                    ("Selected.one", "p") => ["1", "1", "0", "0"],
                    ("Selected.one", "q") => ["1", "0", "1", "0"],
                    _ => panic!("original law and binding"),
                }
            };
            assert_eq!(
                values(&g, d.nu[coordinate]),
                expected,
                "object {object} {name} {subject}"
            );
        }
        assert_eq!(
            (d.domain, d.ring, d.target, d.evaluation),
            (ds[0].domain, ds[0].ring, ds[0].target, ds[0].evaluation)
        );
        assert_eq!(d.points, ds[0].points);
        assert!(d.evaluation.is_some());
        assert_eq!(d.nu.len(), 4);
        assert_eq!(d.originals.len(), 4);
        assert!(Arc::ptr_eq(source, &data(&g, d.required).source));
        let Part::Equation(crate::observed::equation_presentation_node::Part::Presentation {
            domain,
            ring,
            coordinates,
            ..
        }) = data(&g, d.presentation.unwrap()).part()
        else {
            panic!("presentation")
        };
        assert_eq!((*domain, *ring), (ds[0].domain, ds[0].ring));
        assert_eq!(coordinates.len(), 4);
        for (q, nu) in coordinates.iter().zip(&d.nu) {
            assert_eq!(q.nu, *nu);
        }
    }
    let parts = &source.parts;
    assert_eq!(
        parts
            .iter()
            .filter(|p| matches!(p, Part::Domain { .. }))
            .count(),
        1
    );
    assert_eq!(
        parts
            .iter()
            .filter(|p| matches!(p, Part::FunctionRing { .. }))
            .count(),
        1
    );
    assert_eq!(
        parts
            .iter()
            .filter(|p| matches!(p, Part::Evaluation { .. }))
            .count(),
        1
    );
    let Part::Domain { elements, .. } = data(&g, ds[0].domain).part() else {
        panic!("domain")
    };
    assert_eq!(elements.len(), 4);
    for (index, node) in g.nodes.iter().enumerate().skip(before) {
        assert!(node.arguments.iter().all(|r| r.0 < index));
    }
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn shared_finite_family_preserves_parameter_rows_known_values_and_original_missing_slots() {
    use crate::observed::equation_presentation_node::Part as E;
    for missing in [false, true] {
        let p = prepared(
            missing,
            "law required grid(c:Part,n:Fp(2)):c.quantity=n;",
            "root",
        );
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .unwrap();
        assert_eq!(ds.len(), 3);
        assert_eq!(ds[0].evaluation.is_none(), missing);
        let Part::Equation(E::Presentation { coordinates, .. }) =
            data(&g, ds[0].presentation.unwrap()).part()
        else {
            panic!("presentation")
        };
        assert_eq!(coordinates.len(), 4);
        let mut rows = std::collections::BTreeSet::new();
        for original in &ds[0].originals {
            let subject = original.bindings.iter().find(|b| b.name == "c").unwrap();
            let parameter = original.bindings.iter().find(|b| b.name == "n").unwrap();
            let Scalar::Subject { subject, .. } = g.scalar(subject.value).unwrap() else {
                panic!("subject")
            };
            let Scalar::Fp { value, .. } = g.scalar(parameter.value).unwrap() else {
                panic!("parameter")
            };
            rows.insert((subject.clone(), value.to_string()));
            let q = coordinates
                .iter()
                .find(|q| q.instance == original.row)
                .unwrap();
            assert_eq!(q.epsilon.is_none(), missing && subject == "q");
            if let Some(epsilon) = q.epsilon {
                let observed = if subject == "p" { "0" } else { "1" };
                let expected = if observed == value.to_string() {
                    "0"
                } else {
                    "1"
                };
                assert!(values(&g, epsilon).iter().all(|v| v == expected));
            }
        }
        assert_eq!(
            rows,
            std::collections::BTreeSet::from([
                ("p".into(), "0".into()),
                ("p".into(), "1".into()),
                ("q".into(), "0".into()),
                ("q".into(), "1".into())
            ])
        );
        if missing {
            for d in &ds {
                assert_eq!(d.ring, ds[0].ring);
                assert!(
                    g.nodes[d.presentation.unwrap().0]
                        .reasons
                        .iter()
                        .any(|r| r.kind == ReasonKind::Missing
                            && r.missing.iter().any(|f| f.subject == "q"
                                && f.field.as_deref() == Some("Family.Part.quantity")
                                && f.atom.is_none()))
                );
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn family_source_rejects_missing_reordered_duplicated_and_replaced_object_outputs() {
    let p = prepared(false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let original = data(&g, ds[0].ring).source.clone();
    for kind in 0..9 {
        let mut changed = (*original).clone();
        match kind {
            0 => {
                changed.owned_outputs.as_mut().unwrap().pop();
            }
            1 => changed.owned_outputs.as_mut().unwrap().swap(0, 1),
            2 => {
                let duplicate = changed.owned_outputs.as_ref().unwrap()[0].clone();
                changed.owned_outputs.as_mut().unwrap().push(duplicate);
            }
            3 => changed.owned_outputs.as_mut().unwrap()[0].ring = changed.outputs.required,
            4 => changed.owned_outputs.as_mut().unwrap()[0].domain = changed.outputs.required,
            5 => changed.owned_outputs.as_mut().unwrap()[0].nu.reverse(),
            6 => changed.outputs.points.reverse(),
            7 => changed.object = 1,
            _ => changed.base = changed.base.checked_add(1).unwrap(),
        }
        assert!(
            changed
                .recheck(p.inputs(), &original.architecture, 0, &mut quiet())
                .is_err(),
            "source {kind}"
        );
        let mut nodes = g.nodes.clone();
        let Some(Payload::Construction(v)) = &mut nodes[ds[0].ring.0].payload else {
            panic!("native")
        };
        let D::FiniteLaw(value) = &mut v.data else {
            panic!("finite")
        };
        value.source = Arc::new(changed);
        assert!(replay(&p, &g, &nodes).is_err(), "graph {kind}");
    }
    let missing = prepared(true, BODY, "root");
    assert!(
        original
            .recheck(missing.inputs(), &original.architecture, 0, &mut quiet())
            .is_err()
    );
    assert!(retain_family(&mut g, p.shared_inputs(), NodeRef(usize::MAX), &mut quiet()).is_err());
    replay(&p, &g, &g.nodes).unwrap();
}
#[test]
fn an_empty_law_family_keeps_the_real_base_and_all_owned_objects_without_coordinates() {
    for (root, count) in [("root", 3), ("r2", 1)] {
        let p = prepared(false, "", root);
        let (mut g, a) = built(&p);
        let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
            .unwrap()
            .unwrap();
        assert_eq!(ds.len(), count);
        for d in &ds {
            assert_eq!(d.ring, ds[0].ring);
            assert!(
                d.originals.is_empty()
                    && d.nu.is_empty()
                    && d.epsilon.is_empty()
                    && d.operands.is_empty()
            );
            let Part::Ideal { generators, .. } = data(&g, d.required).part() else {
                panic!("ideal")
            };
            assert!(generators.is_empty());
        }
        assert_eq!(
            data(&g, ds[0].ring)
                .source
                .architecture
                .construction()
                .root()
                .subject,
            root
        );
        replay(&p, &g, &g.nodes).unwrap();
    }
}
fn prefix(original: &Graph, c: &Control) -> Graph {
    let mut g = Graph::new(c);
    g.nodes = original.nodes.clone();
    g.contexts = original.contexts.clone();
    g.frames = original.frames.clone();
    g.iterations = original.iterations.clone();
    g.instances = original.instances.clone();
    g.cases = original.cases.clone();
    g.universal_witnesses = original.universal_witnesses.clone();
    g.active = original.active;
    g.requests = original.requests.clone();
    g.checked_answers = original.checked_answers.clone();
    g
}
#[test]
fn interrupt_keeps_only_finished_shared_basis_and_object_prefixes() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, BODY, "root");
    let (initial, a) = built(&p);
    let before = initial.nodes.len();
    let mut complete = prefix(&initial, &quiet());
    let ds = retain_family(&mut complete, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    for at in [
        2 * (ds[1].presentation.unwrap().0 - before + 1),
        2 * (ds[2].presentation.unwrap().0 - before + 1),
    ] {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut c = Control::new(move |point| {
            if point == Checkpoint::NativeResultNode {
                count.set(count.get() + 1);
            }
            let stop = count.get() >= at;
            stop.then_some(crate::result::Signal::Int)
        });
        let mut g = prefix(&initial, &c);
        assert!(matches!(
            retain_family(&mut g, p.shared_inputs(), a, &mut c),
            Err(ValidationFailure::Stop(_))
        ));
        assert_eq!(g.nodes.len(), before + at.div_ceil(2));
        assert_eq!(g.nodes.len(), g.contexts.len());
        for (left, right) in g.nodes.iter().zip(&complete.nodes) {
            assert_eq!(
                (
                    &left.ty,
                    &left.rule,
                    &left.arguments,
                    &left.support,
                    &left.scope,
                    &left.reasons,
                    &left.judgment
                ),
                (
                    &right.ty,
                    &right.rule,
                    &right.arguments,
                    &right.support,
                    &right.scope,
                    &right.reasons,
                    &right.judgment
                )
            );
            match (&left.payload, &right.payload) {
                (Some(Payload::Construction(a)), Some(Payload::Construction(b))) => {
                    assert_eq!(a.wire(), b.wire())
                }
                _ => assert_eq!(left, right),
            }
        }
        replay(&p, &g, &g.nodes).unwrap();
    }
}

#[test]
fn shared_family_rejects_foreign_root_request_input_and_cached_witness_without_appending() {
    let mut p = prepared(false, BODY, "root");
    p.requests = resolve_native_for_test(
        p.inputs().law(),
        p.inputs().archmap(),
        &["b=build(Selected,on=@v/root)", "c=build(Selected,on=@v/r2)"],
        &mut quiet(),
    )
    .unwrap();
    let (mut g, a) = built(&p);
    let mut c = quiet();
    let env = Environment::with_prepared(&p, &mut c).unwrap();
    g.active.request = 1;
    let before = g.nodes.len();
    assert!(retain_family(&mut g, p.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let other = crate::observed::architecture_result::build(
        p.shared_inputs(),
        &env,
        &mut g,
        &p.requests().requests()[1],
        &mut c,
    )
    .unwrap();
    assert!(other.complete);
    let second = retain_family(&mut g, p.shared_inputs(), other.reference, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(second.len(), 1);
    assert_eq!(
        data(&g, second[0].ring)
            .source
            .architecture
            .construction()
            .root()
            .subject,
        "r2"
    );
    g.active.request = 0;
    let first = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let Some(Payload::Construction(value)) = &g.nodes[first[0].ring.0].payload else {
        panic!("native")
    };
    env.recheck_finite_law_diagram(&g, value).unwrap();
    let mut foreign = (**value).clone();
    foreign.witness = Witness::Architecture(data(&g, second[0].ring).source.architecture.clone());
    assert!(env.recheck_finite_law_diagram(&g, &foreign).is_err());
    let missing = prepared(true, BODY, "root");
    let before = g.nodes.len();
    assert!(retain_family(&mut g, missing.shared_inputs(), a, &mut quiet()).is_err());
    assert_eq!(g.nodes.len(), before);
    let objects = crate::observed::object_component_diagram::retain(
        &mut g,
        p.shared_inputs(),
        a,
        &mut quiet(),
    )
    .unwrap()
    .unwrap();
    let before = g.nodes.len();
    assert!(
        retain_family(
            &mut g,
            p.shared_inputs(),
            objects.architectures[1],
            &mut quiet()
        )
        .is_err()
    );
    assert_eq!(g.nodes.len(), before);
    replay(&p, &g, &g.nodes).unwrap();
}
