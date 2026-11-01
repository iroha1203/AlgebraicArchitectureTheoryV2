use super::*;
use crate::observed::{PreparedObserved, request::resolve_native_for_test};
#[allow(dead_code)]
mod fixture {
    include!("../../../tests/common/finite_law_reading_data.rs");
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
fn value(g: &Graph, r: Option<NodeRef>) -> Option<bool> {
    r.map(|r| match g.scalar(r).unwrap() {
        Scalar::Bool(v) => *v,
        _ => panic!("Bool"),
    })
}
fn row<'a>(g: &Graph, d: &'a Diagram, name: &str, subject: &str) -> &'a LawReading {
    d.readings.iter().find(|r|{
        let Part::LawInstance{name:n,bindings,..}=data(g,r.instance).part() else{panic!("instance")};
        n==name&&bindings.iter().any(|b|matches!(g.scalar(b.value).unwrap(),Scalar::Subject{subject:s,..}if s==subject))
    }).unwrap()
}
const BODY: &str = "law required zero(c:Part):c.quantity=0;law optional one(c:Part):c.quantity=1;";
#[test]
fn observed_law_body_and_conditional_values_keep_every_object_and_original_row() {
    let p = prepared(false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    assert_eq!(ds.len(), 3);
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 4);
        for (name, subject, body) in [
            ("Selected.zero", "p", true),
            ("Selected.zero", "q", false),
            ("Selected.one", "p", false),
            ("Selected.one", "q", true),
        ] {
            let r = row(&g, d, name, subject);
            let applies =
                object == 0 || (object == 1 && subject == "p") || (object == 2 && subject == "q");
            assert_eq!(r.reading.application, Some(applies));
            assert_eq!(value(&g, r.body), applies.then_some(body));
            assert_eq!(value(&g, r.holds), Some(!applies || body));
            assert_eq!(r.reading.body, value(&g, r.body));
            assert_eq!(r.reading.holds, value(&g, r.holds));
            assert!(!r.reading.condition_failed && !r.reading.condition_pending);
            for reference in [r.body, r.holds].into_iter().flatten() {
                let Part::ObservedBoolean { origin, .. } = data(&g, reference).part() else {
                    panic!("observed")
                };
                assert_eq!(*origin, r.instance);
                assert!(r.instance.0 < reference.0);
                assert!(g.nodes[reference.0].arguments.contains(&r.instance));
                assert!(!g.nodes[reference.0].scope.assignments);
            }
        }
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn false_guard_keeps_conditional_true_without_creating_body_or_missing_epsilon() {
    let p = prepared(
        true,
        "law required off(c:Part) when false:c.quantity=1;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    for (object, d) in ds.iter().enumerate() {
        for subject in ["p", "q"] {
            let r = row(&g, d, "Selected.off", subject);
            assert_eq!(value(&g, r.holds), Some(true));
            assert!(r.body.is_none());
            assert_eq!(
                r.reading.guard,
                (object == 0 || (object == 1 && subject == "p") || (object == 2 && subject == "q"))
                    .then_some(false)
            );
            assert!(
                !r.reading
                    .positions
                    .iter()
                    .any(|f| f.field.as_deref() == Some("Family.Part.quantity"))
            );
        }
    }
    let Part::Equation(crate::observed::equation_presentation_node::Part::Presentation {
        coordinates,
        ..
    }) = data(&g, ds[0].presentation.unwrap()).part()
    else {
        panic!("presentation")
    };
    let original = row(&g, &ds[0], "Selected.off", "q");
    assert!(
        coordinates
            .iter()
            .filter(|q| q.instance == original.instance)
            .all(|q| q.epsilon.is_none())
    );
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn missing_guard_and_body_are_unknown_and_never_false_or_zero() {
    let p = prepared(
        true,
        "law required guarded(c:Part) when c.quantity=0:c.quantity=1;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let known = row(&g, &ds[0], "Selected.guarded", "p");
    assert_eq!(value(&g, known.body), Some(false));
    assert_eq!(value(&g, known.holds), Some(false));
    let unknown = row(&g, &ds[0], "Selected.guarded", "q");
    assert_eq!(unknown.reading.guard, None);
    assert!(unknown.body.is_none() && unknown.holds.is_none());
    assert!(unknown.reading.positions.iter().any(|f| f.subject == "q"
        && f.field.as_deref() == Some("Family.Part.quantity")
        && f.atom.is_none()));
    assert_eq!(
        value(&g, row(&g, &ds[1], "Selected.guarded", "q").holds),
        Some(true)
    );
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn missing_self_equality_separates_finite_constant_from_unobserved_body() {
    let p = prepared(
        true,
        "law required reflexive(c:Part):c.quantity=c.quantity;",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let r = row(&g, &ds[0], "Selected.reflexive", "q");
    assert!(r.body.is_none());
    assert!(r.holds.is_none());
    let coordinate = ds[0]
        .columns
        .iter()
        .position(|column| *column == r.column)
        .unwrap();
    let Part::Function { values, .. } = data(&g, ds[0].epsilon[coordinate].unwrap()).part() else {
        panic!("backend epsilon")
    };
    assert!(
        values
            .iter()
            .all(|r| matches!(g.scalar(*r).unwrap(),Scalar::Z(v)if v==&0.into()))
    );
    let Part::Equation(crate::observed::equation_presentation_node::Part::Presentation {
        coordinates,
        evaluation,
        ..
    }) = data(&g, ds[0].presentation.unwrap()).part()
    else {
        panic!("presentation")
    };
    assert!(evaluation.is_none());
    assert!(coordinates.iter().any(|q| q.instance == r.instance));
    assert!(
        coordinates
            .iter()
            .filter(|q| q.instance == r.instance)
            .all(|q| q.epsilon.is_none())
    );
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn parameter_rows_keep_distinct_actual_bool_values_and_do_not_use_a_display_witness() {
    let p = prepared(
        false,
        "law required choose(c:Part,b:Bool):c.quantity=(if b then 0 else 1);",
        "root",
    );
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    for (object, d) in ds.iter().enumerate() {
        assert_eq!(d.readings.len(), 4);
        let mut keys = vec![];
        for r in &d.readings {
            let Part::LawInstance { bindings, .. } = data(&g, r.instance).part() else {
                panic!("instance")
            };
            let Scalar::Subject { subject, .. } = g
                .scalar(bindings.iter().find(|b| b.name == "c").unwrap().value)
                .unwrap()
            else {
                panic!("subject")
            };
            let Scalar::Bool(b) = g
                .scalar(bindings.iter().find(|b| b.name == "b").unwrap().value)
                .unwrap()
            else {
                panic!("Bool")
            };
            let applies =
                object == 0 || (object == 1 && subject == "p") || (object == 2 && subject == "q");
            let expected = (subject == "p") == *b;
            assert_eq!(value(&g, r.body), applies.then_some(expected));
            assert_eq!(value(&g, r.holds), Some(!applies || expected));
            keys.push((subject.as_str(), *b));
        }
        keys.sort();
        assert_eq!(keys, [("p", false), ("p", true), ("q", false), ("q", true)]);
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn source_and_graph_reject_bool_value_role_origin_metadata_and_output_tampering() {
    let p = prepared(false, BODY, "root");
    let (mut g, a) = built(&p);
    let ds = retain_family(&mut g, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    let original = data(&g, ds[0].ring).source.clone();
    let reference = ds[0].readings[0].holds.unwrap();
    for kind in 0..7 {
        let mut changed = (*original).clone();
        if kind < 4 {
            let Part::ObservedBoolean {
                origin,
                body,
                value,
                support,
                ..
            } = &mut changed.parts[reference.0 - changed.base]
            else {
                panic!("observed")
            };
            match kind {
                0 => {
                    let Scalar::Bool(v) = value else {
                        panic!("Bool")
                    };
                    *v = !*v;
                }
                1 => *body = !*body,
                2 => *origin = ds[0].originals[1].row,
                _ => support.clear(),
            }
        } else {
            match kind {
                4 => changed.outputs.readings.swap(0, 1),
                5 => changed.outputs.readings[0].reading.holds = None,
                _ => changed.owned_outputs.as_mut().unwrap()[0]
                    .readings
                    .pop()
                    .map(|_| ())
                    .unwrap(),
            }
        }
        assert!(
            changed
                .recheck(p.inputs(), &original.architecture, 0, &mut quiet())
                .is_err(),
            "source {kind}"
        );
        let mut nodes = g.nodes.clone();
        let Some(Payload::Construction(v)) = &mut nodes[reference.0].payload else {
            panic!("native")
        };
        let D::FiniteLaw(d) = &mut v.data else {
            panic!("finite")
        };
        d.source = Arc::new(changed);
        assert!(replay(&p, &g, &nodes).is_err(), "graph {kind}");
    }
    replay(&p, &g, &g.nodes).unwrap();
}

#[test]
fn raw_reading_rejects_other_inputs_and_preserves_pending_and_failed_owned_conditions() {
    let body = "view amount(r:Root,c:Part[r]):Fp(2)=c.quantity;law required typed(c:Part):amount(c.choice,c)=c.quantity;";
    for (choice, pending, failed) in [
        (Some("root"), false, false),
        (None, true, false),
        (Some("r2"), false, true),
    ] {
        let inputs = fixture::conditional_inputs(choice, body);
        let mut p = prepared(false, BODY, "root");
        p.inputs = inputs;
        p.requests = resolve_native_for_test(
            p.inputs().law(),
            p.inputs().archmap(),
            &["b=build(Selected,on=@v/root)"],
            &mut quiet(),
        )
        .unwrap();
        let mut c = quiet();
        let env = Environment::with_prepared(&p, &mut c).unwrap();
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
        let origin = &a.witness;
        assert_eq!(a.complete, choice.is_some());
        let full =
            finite_automatic_law_family(p.inputs(), origin.readings(), &mut quiet()).unwrap();
        let f = full.family().unwrap();
        let mut found = false;
        for (column, _) in f.columns().iter().enumerate() {
            let original = f.instance_source(column).unwrap().0;
            if f.column_object_identity(column).unwrap().subject().subject != "root"
                || !original
                    .bindings()
                    .iter()
                    .any(|b| b.subject().subject == "q")
            {
                continue;
            }
            let reading = f.observed_law(p.inputs(), column, &mut quiet()).unwrap();
            found = true;
            assert_eq!(reading.condition_pending, pending);
            assert_eq!(reading.condition_failed, failed);
            assert_eq!(reading.holds, (!pending && !failed).then_some(true));
            assert!(
                f.observed_law(prepared(true, BODY, "root").inputs(), column, &mut quiet())
                    .is_err()
            );
        }
        assert!(found);
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
fn observed_law_booleans_stop_with_exact_finished_prefixes_on_interrupt() {
    use std::{cell::Cell, rc::Rc};
    let p = prepared(false, BODY, "root");
    let (initial, a) = built(&p);
    let before = initial.nodes.len();
    let mut complete = prefix(&initial, &quiet());
    let ds = retain_family(&mut complete, p.shared_inputs(), a, &mut quiet())
        .unwrap()
        .unwrap();
    for at in [
        2 * (ds[1].readings[0].holds.unwrap().0 - before + 1),
        2 * (ds[2].readings[0].holds.unwrap().0 - before + 1),
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
