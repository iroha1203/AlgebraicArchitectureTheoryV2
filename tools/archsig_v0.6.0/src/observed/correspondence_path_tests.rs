use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/correspondence_paths.rs");
}
fn quiet() -> Control {
    named_call_quiet()
}
fn example(bad: bool) -> ObservedEvaluation {
    let current = if bad {
        "current=evaluate(Reservations.step,m=@v/m)"
    } else {
        "current=evaluate(Reservations.step,m=@v/m)"
    };
    let r = evaluate_observed_bytes(
        fixture::input(if bad { "bad_endpoint" } else { "normal" }, "r1"),
        &[
            "seed=evaluate(Reservations.seed)",
            "prior=check(Reservations.prior)",
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
fn path_index(r: &ObservedEvaluation) -> usize {
    r.nodes.iter().enumerate().filter(|(_,n)|matches!(&n.payload,Some(Payload::Scalar(Scalar::Path(p)))if p.step.as_ref().is_some_and(|s|s.word_tail.is_empty()))).map(|(i,_)|i).next().unwrap()
}
fn path_mut(n: &mut Node) -> &mut super::super::super::path_value::PathValue {
    let Some(Payload::Scalar(Scalar::Path(p))) = &mut n.payload else {
        panic!()
    };
    p
}
#[test]
fn correspondence_action_maps_all_41_original_atoms_and_collapses_exact_external_complement() {
    let r = example(false);
    let i = path_index(&r);
    let Some(Payload::Scalar(Scalar::Path(p))) = &r.nodes[i].payload else {
        panic!()
    };
    let step = p.step.as_ref().unwrap();
    let mut expected = vec![];
    for (name, ty, fields) in [
        ("A", "Reservations.System", vec![]),
        ("B", "Reservations.System", vec![]),
        ("p", "Reservations.State", vec!["owner", "free", "held"]),
        ("q", "Reservations.State", vec!["owner", "free", "held"]),
        ("r", "Reservations.State", vec!["owner", "free", "held"]),
        ("s", "Reservations.State", vec!["owner", "free", "held"]),
        ("e", "Reservations.Reserve", vec!["owner", "from", "to"]),
        ("f", "Reservations.Reserve", vec!["owner", "from", "to"]),
        (
            "m",
            "Reservations.Migration",
            vec!["from", "to", "states", "reserves"],
        ),
        (
            "alias",
            "Reservations.Migration",
            vec!["from", "to", "states", "reserves"],
        ),
        (
            "self",
            "Reservations.Migration",
            vec!["from", "to", "states", "reserves"],
        ),
    ] {
        expected.push(Fact {
            snapshot: "v".into(),
            subject: name.into(),
            field: None,
            atom: None,
        });
        for field in fields {
            expected.push(Fact {
                snapshot: "v".into(),
                subject: name.into(),
                field: Some(format!("{ty}.{field}")),
                atom: Some(format!("{name}-{field}")),
            });
        }
    }
    expected.sort();
    assert_eq!(expected.len(), 41);
    assert_eq!(step.carrier, expected);
    let images: Vec<_> = expected
        .iter()
        .map(|f| {
            let target = match f.subject.as_str() {
                "A" => Some("B"),
                "p" => Some("r"),
                "q" => Some("s"),
                "e" => Some("f"),
                _ => None,
            };
            if let Some(target) = target {
                let mut f = f.clone();
                f.subject = target.into();
                if let Some(field) = &f.field {
                    f.atom = Some(format!("{target}-{}", field.rsplit('.').next().unwrap()));
                }
                f
            } else {
                Fact {
                    snapshot: "v".into(),
                    subject: "B".into(),
                    field: None,
                    atom: None,
                }
            }
        })
        .collect();
    assert_eq!(step.images, images);
    assert_eq!(
        step.carrier
            .iter()
            .zip(&step.images)
            .filter(|(a, b)| a != b)
            .count(),
        40
    );
    assert_eq!(
        step.generator,
        Scalar::Subject {
            snapshot: "v".into(),
            subject: "m".into(),
            entity: "Reservations.Migration".into()
        }
    );
    assert!(step.word_tail.is_empty());
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
fn correspondence_recheck_rejects_fabricated_action_generator_endpoints_source_scope_and_support() {
    let r = example(false);
    let i = path_index(&r);
    for kind in 0..10 {
        let mut bad = r.nodes[i].clone();
        match kind {
            0 => {
                let p = path_mut(&mut bad);
                let s = p.step.as_mut().unwrap();
                let at = s
                    .carrier
                    .iter()
                    .position(|f| f.subject == "alias" && f.field.is_none())
                    .unwrap();
                s.images[at] = s.carrier[at].clone();
            }
            1 => {
                let s = path_mut(&mut bad).step.as_mut().unwrap();
                s.generator = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "alias".into(),
                    entity: "Reservations.Migration".into(),
                };
            }
            2 => {
                path_mut(&mut bad).step.as_mut().unwrap().target = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "A".into(),
                    entity: "Reservations.System".into(),
                };
            }
            3 => bad.support.clear(),
            4 => bad.scope.snapshots.clear(),
            5 => bad.arguments.swap(0, 1),
            6 => {
                bad.arguments.remove(1);
            }
            7 => {
                let s = path_mut(&mut bad).step.as_mut().unwrap();
                s.word_tail.push(s.generator.clone());
            }
            8 => path_mut(&mut bad).reading = "Other".into(),
            _ => {
                let Rule::Input {
                    location: Location::Law { span },
                    ..
                } = &mut bad.rule
                else {
                    panic!()
                };
                span.0 += 1;
            }
        }
        reject(&r, i, bad);
    }
}
#[test]
fn correspondence_condition_counterexample_recheck_rejects_changed_operands_and_fact_provenance() {
    let r = example(true);
    let (i, n) = r
        .nodes
        .iter()
        .enumerate()
        .find(|(_, n)| matches!(n.payload, Some(Payload::PathCounterexample { .. })))
        .unwrap();
    for kind in 0..3 {
        let mut bad = n.clone();
        match kind {
            0 => {
                let Some(Payload::PathCounterexample { left, right, .. }) = &mut bad.payload else {
                    panic!()
                };
                std::mem::swap(left, right);
            }
            1 => bad.support.clear(),
            _ => {
                let Some(Payload::PathCounterexample { facts, .. }) = &mut bad.payload else {
                    panic!()
                };
                facts.clear();
            }
        }
        reject(&r, i, bad);
    }
}
fn stop(stage: &'static str, kind: usize, unknown: bool) {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(
        if unknown {
            "missing_arrow_map"
        } else {
            "normal"
        },
        "r1",
    );
    let current = if unknown {
        "current=evaluate(Reservations.right,m=@v/m)"
    } else {
        "current=evaluate(Reservations.step,m=@v/m)"
    };
    let asks = [
        "seed=evaluate(Reservations.seed)",
        "prior=check(Reservations.prior)",
        current,
        "later=evaluate(Reservations.seed)",
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
fn correspondence_actual_action_cancel_preserves_all_tables_and_prior_answers() {
    stop("correspondence_action", 0, false);
}
#[test]
fn correspondence_actual_action_time_preserves_all_tables_and_probe_freeze() {
    stop("correspondence_action", 1, false);
}
#[test]
fn correspondence_actual_recheck_memory_preserves_all_tables_and_probe_freeze() {
    stop("path_scalar_recheck", 2, false);
}
#[test]
fn correspondence_shared_completion_action_cancel_keeps_missing_and_prefix() {
    stop("correspondence_action", 0, true);
}
#[allow(dead_code)]
mod aligned {
    use crate as archsig;
    include!("../../tests/common/aligned_paths.rs");
}
#[test]
fn correspondence_aligned_full_action_keeps_external_existence_but_collapses_its_field() {
    let r = evaluate_observed_bytes(
        aligned::input(false),
        &["x=evaluate(Flow.step,m=@v/m)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let i = path_index(&r);
    let Some(Payload::Scalar(Scalar::Path(p))) = &r.nodes[i].payload else {
        panic!()
    };
    let step = p.step.as_ref().unwrap();
    let mut expected = vec![];
    for (name, ty, fields) in [
        ("A", "Flow.Left", vec![]),
        ("B", "Flow.Right", vec![]),
        ("z", "Flow.External", vec!["qty"]),
        ("p", "Flow.LNode", vec!["owner", "qty", "refs", "external"]),
        ("q", "Flow.LNode", vec!["owner", "qty", "refs", "external"]),
        (
            "r",
            "Flow.RNode",
            vec!["owner", "amount", "targets", "outside"],
        ),
        ("m", "Flow.Move", vec!["from", "to", "nodes"]),
    ] {
        expected.push(Fact {
            snapshot: "v".into(),
            subject: name.into(),
            field: None,
            atom: None,
        });
        for field in fields {
            expected.push(Fact {
                snapshot: "v".into(),
                subject: name.into(),
                field: Some(format!("{ty}.{field}")),
                atom: Some(format!("{name}-{field}")),
            });
        }
    }
    expected.sort();
    assert_eq!(expected.len(), 23);
    assert_eq!(step.carrier, expected);
    let images: Vec<_> = expected
        .iter()
        .map(|f| {
            if f.subject == "z" && f.field.is_none() {
                return f.clone();
            }
            let mut out = Fact {
                snapshot: "v".into(),
                subject: "B".into(),
                field: None,
                atom: None,
            };
            if ["p", "q"].contains(&f.subject.as_str()) {
                out.subject = "r".into();
                if let Some(field) = &f.field {
                    let moved = match field.rsplit('.').next().unwrap() {
                        "owner" => "owner",
                        "qty" => "amount",
                        "refs" => "targets",
                        "external" => "outside",
                        _ => panic!(),
                    };
                    out.field = Some(format!("Flow.RNode.{moved}"));
                    out.atom = Some(format!("r-{moved}"));
                }
            }
            out
        })
        .collect();
    assert_eq!(step.images, images);
    assert_eq!(
        expected.iter().zip(&images).filter(|(a, b)| a != b).count(),
        21
    );
}
#[test]
fn correspondence_resident_cache_rejects_actual_call_frame_argument_loss_and_restores() {
    let r = evaluate_observed_bytes(
        fixture::input("normal", "r1"),
        &["x=evaluate(Reservations.nested,m=@v/m)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let i = r
        .nodes
        .iter()
        .enumerate()
        .find(|(i, n)| {
            r.contexts[*i].frame.is_some()
                && matches!(n.payload, Some(Payload::Scalar(Scalar::Path(_))))
        })
        .unwrap()
        .0;
    let mut g = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..i]).unwrap();
    g.active = r.contexts[i];
    let frame = r.contexts[i].frame.unwrap();
    let saved = g.frames[frame].clone();
    assert_eq!(saved.arguments.len(), 1);
    let e = environment(&r);
    e.validate(&g, &r.nodes[i]).unwrap();
    g.frames[frame].arguments.clear();
    assert!(matches!(
        e.validate(&g, &r.nodes[i]),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        environment(&r).validate(&g, &r.nodes[i]),
        Err(ValidationFailure::Internal(_))
    ));
    g.frames[frame] = saved;
    e.validate(&g, &r.nodes[i]).unwrap();
}
