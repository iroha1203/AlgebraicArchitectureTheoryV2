use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/internal_paths.rs");
}
fn example(view: &str) -> ObservedEvaluation {
    let ask = format!("current=evaluate(Walk.{view},e=@v/e)");
    let r = evaluate_observed_bytes(
        fixture::input("normal", "r1"),
        &["seed=evaluate(Walk.seed)", "prior=check(Walk.prior)", &ask],
        &mut named_call_quiet(),
    )
    .unwrap();
    assert!(
        matches!(r.status(), "complete" | "partial"),
        "{:?}",
        r.issues
    );
    assert_eq!(r.answers[1].status, Decision::Refuted);
    r
}
fn environment(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn path_mut(n: &mut Node) -> &mut super::super::super::path_value::PathValue {
    let Some(Payload::Scalar(Scalar::Path(p))) = &mut n.payload else {
        panic!("Path")
    };
    p
}
fn path_index(r: &ObservedEvaluation) -> usize {
    r.nodes
        .iter()
        .position(
            |n| matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p)))if p.step.is_some()),
        )
        .unwrap()
}
fn fact(snapshot: &str, subject: &str, field: Option<&str>) -> Fact {
    Fact {
        snapshot: snapshot.into(),
        subject: subject.into(),
        field: field.map(|f| format!("Paths.Node.{f}")),
        atom: field.map(|f| format!("{subject}-{f}")),
    }
}
#[test]
fn internal_path_action_is_exact_on_all_42_original_atoms_and_external_identity() {
    let r = example("step");
    let Some(Payload::Scalar(Scalar::Path(p))) = &r.nodes[path_index(&r)].payload else {
        panic!()
    };
    let step = p.step.as_ref().unwrap();
    assert_eq!(step.carrier.len(), 42);
    assert_eq!(step.images.len(), 42);
    let mut expected = vec![];
    for (snapshot, subjects) in [
        (
            "v",
            vec!["A", "p", "q", "r", "e", "alias", "self", "different"],
        ),
        ("w", vec!["A", "p"]),
    ] {
        for subject in subjects {
            expected.push(Fact {
                snapshot: snapshot.into(),
                subject: subject.into(),
                field: None,
                atom: None,
            });
            if subject == "A" {
                continue;
            }
            let (entity, fields) = if ["p", "q", "r"].contains(&subject) {
                ("Node", vec!["owner", "mark", "link", "links", "members"])
            } else {
                ("Hop", vec!["owner", "from", "to"])
            };
            for field in fields {
                expected.push(Fact {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: Some(format!("Paths.{entity}.{field}")),
                    atom: Some(format!("{subject}-{field}")),
                });
            }
        }
    }
    expected.sort();
    assert_eq!(step.carrier, expected);
    for (a, b) in step.carrier.iter().zip(&step.images) {
        let image = if a.snapshot == "v" && a.subject == "p" {
            Fact {
                snapshot: "v".into(),
                subject: "q".into(),
                field: a.field.clone(),
                atom: a.atom.as_ref().map(|s| s.replacen("p-", "q-", 1)),
            }
        } else {
            a.clone()
        };
        assert_eq!(b, &image, "{a:?}");
    }
    for fixed in [
        fact("w", "p", None),
        fact("w", "p", Some("links")),
        fact("v", "A", None),
        fact("v", "r", Some("members")),
    ] {
        let i = step.carrier.iter().position(|f| f == &fixed).unwrap();
        assert_eq!(step.images[i], fixed);
    }
    assert_eq!(
        p.object(),
        Scalar::Subject {
            snapshot: "v".into(),
            subject: "p".into(),
            entity: "Paths.Node".into()
        }
    );
    assert_eq!(
        p.target(),
        Scalar::Subject {
            snapshot: "v".into(),
            subject: "q".into(),
            entity: "Paths.Node".into()
        }
    );
    assert_eq!(
        step.generator,
        Scalar::Subject {
            snapshot: "v".into(),
            subject: "e".into(),
            entity: "Paths.Hop".into()
        }
    );
}
fn reject_node(r: &ObservedEvaluation, index: usize, bad: Node) {
    assert_ne!(bad, r.nodes[index]);
    let mut graph = rebuild_for_origin_and_support_recheck(r, &r.nodes[..index]).unwrap();
    graph.active = r.contexts[index];
    let e = environment(r);
    e.validate(&graph, &r.nodes[index]).unwrap();
    let checked = e.validate(&graph, &bad);
    assert!(
        matches!(checked, Err(ValidationFailure::Internal(_))),
        "cached {index}: {checked:?}; rule {:?}; type {:?}",
        bad.rule,
        bad.ty
    );
    assert!(
        matches!(
            environment(r).validate(&graph, &bad),
            Err(ValidationFailure::Internal(_))
        ),
        "fresh {index}"
    );
    e.validate(&graph, &r.nodes[index]).unwrap();
    let mut all = r.nodes.clone();
    all[index] = bad;
    assert!(
        matches!(
            rebuild_for_origin_and_support_recheck(r, &all),
            Err(ValidationFailure::Internal(_))
        ),
        "whole {index}"
    );
}
fn changed_path() {
    let r = example("maybe");
    let i = path_index(&r);
    for kind in [0, 1, 2] {
        let mut bad = r.nodes[i].clone();
        match kind {
            0 => {
                path_mut(&mut bad).step.as_mut().unwrap().carrier.pop();
            }
            1 => {
                let s = path_mut(&mut bad).step.as_mut().unwrap();
                s.images[0] = s.carrier[0].clone();
                let j = s
                    .carrier
                    .iter()
                    .position(|f| f == &fact("v", "p", None))
                    .unwrap();
                s.images[j] = s.carrier[j].clone();
            }
            2 => path_mut(&mut bad).step.as_mut().unwrap().carrier[0].snapshot = "foreign".into(),
            _ => panic!(),
        }
        reject_node(&r, i, bad);
    }
}
#[test]
fn internal_path_recheck_rejects_carrier_image_and_foreign_atom_mutations() {
    changed_path();
}
fn stopped() {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input("normal", "r1");
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "current=evaluate(Walk.maybe,e=@v/e)",
        "later=evaluate(Walk.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert!(matches!(normal.status(), "complete" | "partial"));
    let reason = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &mut control).unwrap();
    let result = evaluate_observed_with_validator(prepared, &mut control, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, actual, _| {
                if ctx.request == 2 && actual == "path_action" && !s.replace(true) {
                    a.set(true)
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let result = result.unwrap();
    assert!(seen.get());
    assert_eq!(result.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(reason));
    assert!(result.nodes.len() < normal.nodes.len());
    assert_eq!(
        result.frames.as_slice(),
        &normal.frames[..result.frames.len()]
    );
    assert_eq!(
        result.iterations.as_slice(),
        &normal.iterations[..result.iterations.len()]
    );
    assert_eq!(
        result.instances.as_slice(),
        &normal.instances[..result.instances.len()]
    );
    assert_eq!(result.cases.as_slice(), &normal.cases[..result.cases.len()]);
    assert_eq!(
        result.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..result.universal_witnesses.len()]
    );
    assert_eq!(&result.answers[..2], &normal.answers[..2]);
    for a in &result.answers[2..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&reason))
        );
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result.wire();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(reason));
}
#[test]
fn internal_path_action_cancel_keeps_all_tables_prior_answers_and_frozen_probe() {
    stopped();
}
