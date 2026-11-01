use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/composed_paths.rs");
}
use crate::control::quiet;
fn example(bad: bool) -> ObservedEvaluation {
    let current = if bad {
        "current=evaluate(Walk.join,e=@v/e,f=@v/self)"
    } else {
        "current=evaluate(Walk.triple,s=@v/self,e=@v/e,f=@v/next)"
    };
    let r = evaluate_observed_bytes(
        fixture::input(false, "r1"),
        &[
            "seed=evaluate(Walk.seed)",
            "prior=check(Walk.prior)",
            current,
        ],
        &mut quiet(),
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
        &mut quiet(),
    )
    .unwrap()
}
fn composed_index(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().filter(|(_,n)|matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p)))if p.step.as_ref().is_some_and(|s|s.word_tail.len()==2))).map(|(i,_)|i).next().unwrap()
}
#[test]
fn then_full_46_atom_action_composes_outside_original_source_family() {
    let r = example(false);
    let i = composed_index(&r);
    let Some(Payload::Scalar(Scalar::Path(p))) = &r.nodes[i].payload else {
        panic!()
    };
    let step = p.step.as_ref().unwrap();
    assert_eq!(step.carrier.len(), 46);
    assert_eq!(step.images.len(), 46);
    let mut expected = Vec::new();
    for (snapshot, subjects) in [
        (
            "v",
            vec![
                "A",
                "p",
                "q",
                "r",
                "e",
                "alias",
                "self",
                "different",
                "next",
            ],
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
    let mut moved = 0;
    for (a, b) in step.carrier.iter().zip(&step.images) {
        let image = if a.snapshot == "v" && ["p", "q"].contains(&a.subject.as_str()) {
            moved += 1;
            Fact {
                snapshot: "v".into(),
                subject: "r".into(),
                field: a.field.clone(),
                atom: a
                    .atom
                    .as_ref()
                    .map(|id| format!("r-{}", id.split_once('-').unwrap().1)),
            }
        } else {
            a.clone()
        };
        assert_eq!(b, &image, "{a:?}");
    }
    assert_eq!(moved, 12); // pの元F外であるqの6元も第二操作で移る。
    let names = std::iter::once(&step.generator)
        .chain(&step.word_tail)
        .map(|g| {
            let Scalar::Subject { subject, .. } = g else {
                panic!()
            };
            subject.as_str()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["self", "e", "next"]);
}
fn reject(r: &ObservedEvaluation, i: usize, bad: Node) {
    assert_ne!(bad, r.nodes[i]);
    let mut graph = rebuild_for_origin_and_support_recheck(r, &r.nodes[..i]).unwrap();
    graph.active = r.contexts[i];
    let e = environment(r);
    e.validate(&graph, &r.nodes[i]).unwrap();
    let checked = e.validate(&graph, &bad);
    assert!(
        matches!(checked, Err(ValidationFailure::Internal(_))),
        "cached {checked:?}"
    );
    assert!(matches!(
        environment(r).validate(&graph, &bad),
        Err(ValidationFailure::Internal(_))
    ));
    e.validate(&graph, &r.nodes[i]).unwrap();
    let mut all = r.nodes.clone();
    all[i] = bad;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(r, &all),
        Err(ValidationFailure::Internal(_))
    ));
}
#[test]
fn then_typed_endpoint_counterexample_recheck_rejects_fabricated_values_and_evidence() {
    let r = example(true);
    let proof = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::PathCounterexample { .. })))
        .unwrap();
    for kind in 0..4 {
        let mut bad = r.nodes[proof].clone();
        match kind {
            0 => {
                let Some(Payload::PathCounterexample { left, right, .. }) = &mut bad.payload else {
                    panic!()
                };
                std::mem::swap(left, right);
            }
            1 => {
                bad.arguments.remove(1);
            }
            2 => bad.support.clear(),
            3 => {
                let Some(Payload::PathCounterexample { facts, .. }) = &mut bad.payload else {
                    panic!()
                };
                facts.clear();
            }
            _ => panic!(),
        };
        reject(&r, proof, bad);
    }
    let i = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::PathCondition { .. })))
        .unwrap();
    let mut bad = r.nodes[i].clone();
    bad.judgment.as_mut().unwrap().status = Decision::Established;
    reject(&r, i, bad);
    let Some(Payload::PathCounterexample { left, .. }) = &r.nodes[proof].payload else {
        panic!()
    };
    let i = left.0;
    let mut bad = r.nodes[i].clone();
    bad.payload = Some(Payload::Scalar(Scalar::Bool(true)));
    bad.ty = NodeType::Value(Type::Bool);
    reject(&r, i, bad);
}
fn stop() {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(false, "r1");
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "current=evaluate(Walk.triple,s=@v/self,e=@v/e,f=@v/next)",
        "later=evaluate(Walk.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert!(matches!(normal.status(), "complete" | "partial"));
    let reason = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, op, _| {
                if ctx.request == 2 && op == "path_compose" && !s.replace(true) {
                    a.set(true)
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let r = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(r.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(reason));
    assert!(r.nodes.len() < normal.nodes.len());
    assert_eq!(r.frames.as_slice(), &normal.frames[..r.frames.len()]);
    assert_eq!(
        r.iterations.as_slice(),
        &normal.iterations[..r.iterations.len()]
    );
    assert_eq!(
        r.instances.as_slice(),
        &normal.instances[..r.instances.len()]
    );
    assert_eq!(r.cases.as_slice(), &normal.cases[..r.cases.len()]);
    assert_eq!(
        r.universal_witnesses.as_slice(),
        &normal.universal_witnesses[..r.universal_witnesses.len()]
    );
    assert_eq!(&r.answers[..2], &normal.answers[..2]);
    for a in &r.answers[2..] {
        assert_eq!(a.status, Decision::Undetermined);
        assert!(a.outputs.is_empty() && a.claim.is_none() && a.evidence.is_empty());
        assert!(
            a.reasons
                .iter()
                .any(|r| matches!(&r.kind,ReasonKind::Stop(s)if s==&reason))
        );
    }
    r.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(reason));
}
#[test]
fn then_actual_composition_cancel_keeps_all_tables_and_prior_answers() {
    stop();
}
