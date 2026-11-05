use super::*;
use crate::observed::result::Graph;
use archsig_common::control::{Checkpoint, Signal};
use std::{cell::RefCell, rc::Rc};

// Frozen previous slice-input helper. The oracle owns the old raw clone row.
fn legacy_domain(
    b: &mut Builder<'_>,
    ty: &Type,
    values: &[Scalar],
    c: &Control,
) -> Result<(NodeRef, Vec<(Scalar, NodeRef)>), ValidationFailure> {
    let mut elements = vec![];
    for value in values {
        c.checkpoint(archsig_common::control::Checkpoint::Localize)?;
        if !elements.iter().any(|(v, _)| v == value) {
            elements.push((value.clone(), change_result::value(b, value)?));
        }
    }
    let domain = domain(b, ty, &elements.iter().map(|(_, r)| *r).collect::<Vec<_>>())?;
    Ok((domain, elements))
}
fn row(items: &[bool], flag: bool) -> Scalar {
    Scalar::Tuple(vec![
        Scalar::Set {
            element: Type::Bool,
            items: items.iter().map(|v| Scalar::Bool(*v)).collect(),
        },
        Scalar::Bool(flag),
    ])
}
fn wire_values(values: &[(Scalar, NodeRef)]) -> Vec<(String, NodeRef)> {
    values
        .iter()
        .map(|(v, r)| (v.wire().canonical(), *r))
        .collect()
}
fn wire_parts(parts: &[crate::observed::build_result::Part]) -> Vec<String> {
    parts.iter().map(|p| p.wire().canonical()).collect()
}

#[test]
fn borrowed_image_rows_keep_legacy_parts_and_local_wire_representatives() {
    let c = Control::unlimited();
    let old_graph = Graph::new(&c);
    let new_graph = Graph::new(&c);
    let mut old_builder = Builder {
        g: &old_graph,
        base: 0,
        parts: vec![],
    };
    let mut new_builder = Builder {
        g: &new_graph,
        base: 0,
        parts: vec![],
    };
    let first = row(&[true, false], false);
    assert_eq!(
        change_result::value(&mut old_builder, &first).unwrap(),
        NodeRef(0)
    );
    assert_eq!(
        change_result::value(&mut new_builder, &first).unwrap(),
        NodeRef(0)
    );
    let projected = vec![
        row(&[], false),
        row(&[true], true),
        row(&[false, true], false),
    ];
    let before = projected
        .iter()
        .map(|v| v.wire().canonical())
        .collect::<Vec<_>>();
    let points = [2, 0, 2, 1];
    // Explicit old clone sequence, independent of the new point-index iterator.
    let old_values = vec![
        row(&[false, true], false),
        row(&[], false),
        row(&[false, true], false),
        row(&[true], true),
    ];
    let ty = projected[0].ty();
    let (old_domain, old_values) = legacy_domain(&mut old_builder, &ty, &old_values, &c).unwrap();
    let (new_domain, new_values) = scalar_domain(
        &mut new_builder,
        &ty,
        points.iter().map(|point| &projected[*point]),
        &c,
    )
    .unwrap();
    assert_eq!(new_domain, old_domain);
    assert_eq!(wire_values(&new_values), wire_values(&old_values));
    assert_eq!(
        new_values.iter().map(|(_, r)| *r).collect::<Vec<_>>(),
        vec![NodeRef(0), NodeRef(1), NodeRef(2)]
    );
    assert_eq!(new_values[0].0.wire().canonical(), "[[false,true],false]");
    assert_eq!(
        new_builder.parts[0].wire().canonical(),
        "[[true,false],false]"
    );
    assert_eq!(new_builder.parts, old_builder.parts);
    assert_eq!(
        wire_parts(&new_builder.parts),
        wire_parts(&old_builder.parts)
    );
    assert_eq!(
        projected
            .iter()
            .map(|v| v.wire().canonical())
            .collect::<Vec<_>>(),
        before
    );
}

type DomainResult = Result<(NodeRef, Vec<(Scalar, NodeRef)>), Signal>;
fn run_domain(
    borrowed: bool,
    projected: &[Scalar],
    points: &[usize],
    control: &Control,
) -> (DomainResult, Vec<crate::observed::build_result::Part>) {
    let graph = Graph::new(control);
    let mut builder = Builder {
        g: &graph,
        base: 0,
        parts: vec![],
    };
    let ty = Type::Tuple(vec![Type::Set(Box::new(Type::Bool)), Type::Bool]);
    let result = if borrowed {
        scalar_domain(
            &mut builder,
            &ty,
            points.iter().map(|point| &projected[*point]),
            control,
        )
    } else {
        let values = points
            .iter()
            .map(|point| projected[*point].clone())
            .collect::<Vec<_>>();
        legacy_domain(&mut builder, &ty, &values, control)
    }
    .map_err(|failure| match failure {
        ValidationFailure::Stop(signal) => signal,
        other => panic!("{other:?}"),
    });
    (result, builder.parts)
}

#[test]
fn borrowed_image_rows_keep_empty_results_checkpoint_order_and_stopped_parts() {
    let projected = vec![
        row(&[], false),
        row(&[true], true),
        row(&[false, true], false),
    ];
    for points in [vec![], vec![2, 0, 2, 1]] {
        let trace = |borrowed| {
            let seen = Rc::new(RefCell::new(Vec::<Checkpoint>::new()));
            let observed = seen.clone();
            let control = Control::new(move |point| {
                observed.borrow_mut().push(point);
                None
            });
            let (result, parts) = run_domain(borrowed, &projected, &points, &control);
            assert!(result.is_ok());
            let visits = seen.borrow().clone();
            (result, parts, visits)
        };
        let (old_result, old_parts, old_trace) = trace(false);
        let (new_result, new_parts, new_trace) = trace(true);
        assert_eq!(new_result, old_result);
        assert_eq!(new_parts, old_parts);
        assert_eq!(wire_parts(&new_parts), wire_parts(&old_parts));
        assert_eq!(new_trace, old_trace);
        if !points.is_empty() {
            assert!(!old_trace.is_empty());
        }
        for signal in [Signal::Int, Signal::Term] {
            for at in 1..=old_trace.len() {
                let stop = || {
                    let mut visits = 0;
                    Control::new(move |_| {
                        visits += 1;
                        (visits == at).then_some(signal)
                    })
                };
                let (old_result, old_parts) = run_domain(false, &projected, &points, &stop());
                let (new_result, new_parts) = run_domain(true, &projected, &points, &stop());
                assert_eq!(new_result, Err(signal));
                assert_eq!(old_result, Err(signal));
                assert_eq!(new_parts, old_parts);
                assert_eq!(wire_parts(&new_parts), wire_parts(&old_parts));
            }
        }
    }
}
