use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/internal_paths.rs");
}
fn example(mode: &str, view: &str) -> ObservedEvaluation {
    let ask = format!("current=evaluate(Walk.{view},e=@v/e)");
    let r = evaluate_observed_bytes(
        fixture::input(mode, "r1"),
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
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
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
    let r = example("normal", "step");
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
fn changed_path(kinds: &[usize]) {
    let r = example("normal", "maybe");
    let i = path_index(&r);
    for &kind in kinds {
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
            3 => {
                path_mut(&mut bad).step.as_mut().unwrap().generator = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "alias".into(),
                    entity: "Paths.Hop".into(),
                }
            }
            4 => {
                path_mut(&mut bad).step.as_mut().unwrap().target = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "r".into(),
                    entity: "Paths.Node".into(),
                }
            }
            5 => path_mut(&mut bad).step.as_mut().unwrap().target = Scalar::Bool(true),
            6 => path_mut(&mut bad).reading = "Other".into(),
            7 => path_mut(&mut bad).subject = "q".into(),
            8 => bad.support.clear(),
            9 => bad.scope.snapshots.clear(),
            10 => bad.arguments.clear(),
            11 => bad.arguments.swap(1, 2),
            12 => bad.arguments[0] = bad.arguments[1],
            13 => {
                let Rule::Input {
                    location: Location::Law { span },
                    ..
                } = &mut bad.rule
                else {
                    panic!()
                };
                span.0 += 1;
            }
            14 => bad.ty = NodeType::Value(Type::Bool),
            15 => path_mut(&mut bad).step = None,
            _ => panic!(),
        }
        reject_node(&r, i, bad);
    }
}
#[test]
fn internal_path_recheck_rejects_carrier_image_and_foreign_atom_mutations() {
    changed_path(&[0, 1, 2]);
}
#[test]
fn internal_path_recheck_rejects_generator_endpoints_and_malformed_target_without_panic() {
    changed_path(&[3, 4, 5, 7, 15]);
}
#[test]
fn internal_path_recheck_rejects_support_scope_reading_original_span_and_type() {
    changed_path(&[6, 8, 9, 13, 14]);
}
#[test]
fn internal_path_recheck_rejects_missing_reordered_and_wrong_producer_edges() {
    changed_path(&[10, 11, 12]);
}
#[test]
fn internal_path_container_recheck_rejects_another_existing_ref_and_nested_value() {
    let r = example("normal", "maybe");
    let i=r.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Scalar(Scalar::Option{value:Some(p),..}))if matches!(p.as_ref(),Scalar::Path(_)))).unwrap();
    let mut bad = r.nodes[i].clone();
    bad.arguments.clear();
    reject_node(&r, i, bad);
    let mut bad = r.nodes[i].clone();
    bad.arguments[0] = r.nodes[path_index(&r)].arguments[1];
    reject_node(&r, i, bad);
    let mut bad = r.nodes[i].clone();
    let Some(Payload::Scalar(Scalar::Option { value: Some(p), .. })) = &mut bad.payload else {
        panic!()
    };
    let Scalar::Path(p) = p.as_mut() else {
        panic!()
    };
    p.subject = "q".into();
    reject_node(&r, i, bad);
}
#[test]
fn internal_path_cached_recheck_rejects_missing_call_argument_and_restores_frame() {
    let r = example("normal", "maybe");
    let i = path_index(&r);
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..i]).unwrap();
    graph.active = r.contexts[i];
    let frame = r.contexts[i].frame.unwrap();
    assert_eq!(graph.frames[frame].arguments.len(), 1);
    let e = environment(&r);
    e.validate(&graph, &r.nodes[i]).unwrap();
    let saved = graph.frames[frame].clone();
    graph.frames[frame].arguments.clear();
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
#[test]
fn internal_path_condition_recheck_rejects_counterexample_structure_support_and_source() {
    let r = example("mismatch", "step");
    let i = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::PathCounterexample { .. })))
        .unwrap();
    for kind in 0..4 {
        let mut bad = r.nodes[i].clone();
        match kind {
            0 => {
                let Some(Payload::PathCounterexample { left, right, .. }) = &mut bad.payload else {
                    panic!()
                };
                std::mem::swap(left, right);
            }
            1 => bad.support.clear(),
            2 => {
                bad.arguments.remove(0);
            }
            3 => {
                let Some(Payload::PathCounterexample { facts, .. }) = &mut bad.payload else {
                    panic!()
                };
                facts.clear();
            }
            _ => unreachable!(),
        };
        reject_node(&r, i, bad);
    }
    let i = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::PathCondition { .. })))
        .unwrap();
    let mut bad = r.nodes[i].clone();
    bad.judgment.as_mut().unwrap().status = Decision::Established;
    reject_node(&r, i, bad);
    let mut bad = r.nodes[i].clone();
    bad.evidence.clear();
    reject_node(&r, i, bad);
}
fn stopped(stage: &'static str, kind: usize, unknown: bool) {
    use std::{cell::Cell, rc::Rc};
    let input = fixture::input(if unknown { "missing_to" } else { "normal" }, "r1");
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "current=evaluate(Walk.maybe,e=@v/e)",
        "later=evaluate(Walk.seed)",
    ];
    let normal = evaluate_observed_bytes(input.clone(), &asks, &mut named_call_quiet()).unwrap();
    assert!(matches!(normal.status(), "complete" | "partial"));
    let (limits, usage, reason) = reservations_private_stop_usage(kind);
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            super::super::super::control::Usage::default()
        }
    });
    let prepared = prepare_observed(input, &asks, &mut control).unwrap();
    let result = evaluate_observed_with_validator(prepared, &mut control, |e, g, q, answer| {
        e.validate_answer(g, q, answer)?;
        if q.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, actual, _| {
                if ctx.request == 2
                    && actual == stage
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
    let result = result.unwrap();
    assert!(seen.get(), "{stage}");
    assert_eq!(result.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(reason.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert!(result.nodes.len() < normal.nodes.len());
    assert_eq!(result.nodes.as_slice(), &normal.nodes[..result.nodes.len()]);
    assert_eq!(
        result.contexts.as_slice(),
        &normal.contexts[..result.contexts.len()]
    );
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
    if unknown {
        assert!(
            result.answers[2]
                .reasons
                .iter()
                .any(|r| !r.missing.is_empty())
        );
    }
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result.wire();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(reason));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn internal_path_action_cancel_keeps_all_tables_prior_answers_and_frozen_probe() {
    stopped("path_action", 0, false);
}
#[test]
fn internal_path_endpoint_time_stop_keeps_all_tables_prior_answers_and_frozen_probe() {
    stopped("path_endpoints", 1, false);
}
#[test]
fn internal_path_scalar_recheck_memory_stop_keeps_all_tables_and_frozen_probe() {
    stopped("path_scalar_recheck", 2, false);
}
#[test]
fn internal_path_completion_endpoint_cancel_keeps_original_missing_and_prefix() {
    stopped("path_endpoints", 0, true);
}
