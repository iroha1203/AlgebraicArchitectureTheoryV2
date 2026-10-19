use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/composed_paths.rs");
}
fn quiet() -> Control {
    named_call_quiet()
}
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
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
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
fn path_mut(n: &mut Node) -> &mut super::super::super::path_value::PathValue {
    let Some(Payload::Scalar(Scalar::Path(p))) = &mut n.payload else {
        panic!()
    };
    p
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
fn changes(kinds: &[usize]) {
    let r = example(false);
    let i = composed_index(&r);
    for &kind in kinds {
        let mut bad = r.nodes[i].clone();
        match kind {
            0 => path_mut(&mut bad).step.as_mut().unwrap().word_tail.clear(),
            1 => path_mut(&mut bad)
                .step
                .as_mut()
                .unwrap()
                .word_tail
                .swap(0, 1),
            2 => path_mut(&mut bad).step.as_mut().unwrap().word_tail[0] = Scalar::Bool(true),
            3 => {
                let s = path_mut(&mut bad).step.as_mut().unwrap();
                s.word_tail.push(s.generator.clone());
            }
            4 => {
                path_mut(&mut bad).step.as_mut().unwrap().generator = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "alias".into(),
                    entity: "Paths.Hop".into(),
                }
            }
            5 => {
                let s = path_mut(&mut bad).step.as_mut().unwrap();
                let j = s
                    .carrier
                    .iter()
                    .position(|f| f.snapshot == "v" && f.subject == "q" && f.field.is_none())
                    .unwrap();
                s.images[j] = s.carrier[j].clone();
            }
            6 => bad.arguments.swap(0, 1),
            7 => {
                bad.arguments.remove(1);
            }
            8 => bad.arguments.swap(2, 3),
            9 => bad.support.clear(),
            10 => bad.scope.snapshots.clear(),
            11 => {
                let Rule::Input {
                    location: Location::Law { span },
                    ..
                } = &mut bad.rule
                else {
                    panic!()
                };
                span.0 += 1;
            }
            12 => bad.ty = NodeType::Value(Type::Bool),
            13 => path_mut(&mut bad).reading = "Other".into(),
            _ => panic!(),
        };
        reject(&r, i, bad);
    }
}
#[test]
fn then_cached_and_fresh_recheck_rejects_erased_reordered_extra_and_ill_typed_word() {
    changes(&[0, 1, 2, 3, 4]);
}
#[test]
fn then_recheck_rejects_reextended_action_wrong_operands_and_endpoints() {
    changes(&[5, 6, 7, 8]);
}
#[test]
fn then_recheck_rejects_original_source_reading_support_scope_and_type() {
    changes(&[9, 10, 11, 12, 13]);
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
#[test]
fn then_resident_success_cache_rejects_changed_call_frame_and_reaccepts_restored_frame() {
    let r = evaluate_observed_bytes(
        fixture::input(false, "r1"),
        &["x=evaluate(Walk.join_nested,e=@v/e,f=@v/next)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let i=r.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p)))if p.step.as_ref().is_some_and(|s|s.word_tail.len()==1))).unwrap();
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..i]).unwrap();
    graph.active = r.contexts[i];
    let frame = r.contexts[i].frame.unwrap();
    let saved = graph.frames[frame].clone();
    assert_eq!(saved.arguments.len(), 2);
    let e = environment(&r);
    e.validate(&graph, &r.nodes[i]).unwrap();
    graph.frames[frame].arguments.swap(0, 1);
    assert!(matches!(
        e.validate(&graph, &r.nodes[i]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        environment(&r).validate(&graph, &r.nodes[i]),
        Err(ValidationFailure::Internal(_))
    ));
    graph.frames[frame] = saved;
    e.validate(&graph, &r.nodes[i]).unwrap();
}
fn stop(stage: &'static str, kind: usize, unknown: bool) {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(unknown, "r1");
    let current = if unknown {
        "current=evaluate(Walk.right_unit,e=@v/e)"
    } else {
        "current=evaluate(Walk.triple,s=@v/self,e=@v/e,f=@v/next)"
    };
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        current,
        "later=evaluate(Walk.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut quiet()).unwrap();
    assert!(matches!(normal.status(), "complete" | "partial"));
    let (limits, usage, reason) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            super::super::super::control::Usage::default()
        }
    });
    let prepared = prepare_observed(input, &asks, &mut c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, op, _| {
                if ctx.request == 2
                    && op == stage
                    && (!unknown || ctx.case.is_some())
                    && !s.replace(true)
                {
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
    assert_eq!(c.stop_reason(), Some(reason.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert!(r.nodes.len() < normal.nodes.len());
    assert_eq!(r.nodes.as_slice(), &normal.nodes[..r.nodes.len()]);
    assert_eq!(r.contexts.as_slice(), &normal.contexts[..r.contexts.len()]);
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
    if unknown {
        assert!(r.answers[2].reasons.iter().any(|r| !r.missing.is_empty()));
    }
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r.wire();
    assert_eq!(c.checkpoint(Checkpoint::Expression), Err(reason));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn then_actual_composition_cancel_keeps_all_tables_and_prior_answers() {
    stop("path_compose", 0, false);
}
#[test]
fn then_actual_word_time_stop_keeps_all_tables_and_frozen_probe() {
    stop("path_word", 1, false);
}
#[test]
fn then_actual_recheck_memory_stop_keeps_all_tables_and_frozen_probe() {
    stop("path_composition_recheck", 2, false);
}
#[test]
fn then_completion_composition_cancel_keeps_original_missing_and_prefix() {
    stop("path_compose", 0, true);
}
