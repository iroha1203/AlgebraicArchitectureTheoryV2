use super::*;
use crate::observed::{
    construction_result::ConstructionData as D,
    control::{Limits, Usage},
    public_compare::Part,
};
use std::{cell::Cell, rc::Rc};
mod fixture {
    use crate as archsig;
    include!("../../tests/common/public_path_compose.rs");
}
const E: &str = fixture::E;
const ALIAS: &str = "alias=evaluate(Walk.step,e=@v/alias)";
const WORD: &str = "a=compare($e.value,to=$alias.value,kind=word)";
const ACTION: &str = "a=compare($e.value,to=$alias.value,kind=action)";
fn example(qs: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        fixture::input(false, "compare-unit"),
        qs,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn comparison_recheck_rejects_forged_records_propositions_and_metadata() {
    let r = example(&[E, ALIAS, WORD]);
    let record = r.answers[2].outputs["comparison"].0;
    let claim = r.answers[2].outputs["proposition"].0;
    for kind in 0..8 {
        let target = if kind >= 6 { claim } else { record };
        completion_mutation(&r, target, |nodes| {
            let n = &mut nodes[target];
            match kind {
                3 => n.support.clear(),
                4 => n.scope.readings.clear(),
                5 => n.scope.completions = true,
                6 => n.judgment.as_mut().unwrap().status = Decision::Established,
                7 => n.evidence.clear(),
                _ => {
                    let Some(Payload::Construction(v)) = &mut n.payload else {
                        panic!()
                    };
                    let D::Comparison(Part::Comparison {
                        kind: k,
                        left,
                        right,
                    }) = &mut v.data
                    else {
                        panic!()
                    };
                    match kind {
                        0 => *k = "action".into(),
                        1 => *left = *right,
                        _ => std::mem::swap(left, right),
                    }
                }
            }
        });
    }
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let env = Environment::with_prepared(r.prepared(), &mut Control::unlimited()).unwrap();
    for kind in 0..6 {
        let mut a = r.answers[2].clone();
        match kind {
            0 => {
                a.outputs.remove("comparison");
            }
            1 => a.status = Decision::Established,
            2 => a.scope.snapshots.clear(),
            3 => a.evidence.clear(),
            4 => {
                a.outputs
                    .insert("proposition".into(), r.answers[0].outputs["value"]);
            }
            _ => a.reasons.push(Reason::internal("a", "forged".into())),
        }
        assert!(env
            .validate_answer(&graph, &r.prepared().requests().requests()[2], &a)
            .is_err());
    }
}
#[test]
fn comparison_recheck_rejects_counterexample_and_endpoint_condition_forgery() {
    let r = example(&[
        E,
        fixture::F,
        fixture::C,
        "d=evaluate(Walk.step,e=@v/different)",
        "a=compare($c.operation,to=$d.value,kind=action)",
    ]);
    let proof = r.answers[4].evidence[0].0;
    for kind in 0..3 {
        completion_mutation(&r, proof, |nodes| {
            let Some(Payload::Construction(v)) = &mut nodes[proof].payload else {
                panic!()
            };
            let D::Comparison(Part::Evidence { left, right, facts }) = &mut v.data else {
                panic!()
            };
            match kind {
                0 => *left = *right,
                1 => facts.clear(),
                _ => facts[0].subject = "p".into(),
            }
        });
    }
    let bad = example(&[E, fixture::F, "a=compare($e.value,to=$f.value,kind=action)"]);
    let claim = bad.answers[2].outputs["proposition"].0;
    let condition=bad.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Comparison(Part::Endpoints{..})))).unwrap();
    for kind in 0..3 {
        let target = if kind == 0 { claim } else { condition };
        completion_mutation(&bad, target, |nodes| {
            if kind == 0 {
                let ReasonKind::ConditionFailed { construction, .. } =
                    &mut nodes[target].judgment.as_mut().unwrap().reasons[0].kind
                else {
                    panic!()
                };
                *construction = "compose";
            } else if kind == 1 {
                nodes[target].judgment.as_mut().unwrap().status = Decision::Established;
            } else {
                let Some(Payload::Construction(v)) = &mut nodes[target].payload else {
                    panic!()
                };
                let D::Comparison(Part::Endpoints { left, right }) = &mut v.data else {
                    panic!()
                };
                *left = *right;
            }
        });
    }
}
#[test]
fn comparison_rechecks_current_inputs_requests_and_original_typed_refs() {
    let r = example(&[E, ALIAS, WORD]);
    let index = r.answers[2].outputs["comparison"].0;
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let prepared = prepare_observed(
        fixture::input(false, "changed-source"),
        &[E, ALIAS, WORD],
        &mut Control::unlimited(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
    assert!(env.recheck_node(&graph, &r.nodes[index], index).is_err());
    let prepared = prepare_observed(
        fixture::input(false, "compare-unit"),
        &[E, ALIAS, ACTION],
        &mut Control::unlimited(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
    graph.requests = prepared.requests().requests().to_vec();
    assert!(env.recheck_node(&graph, &r.nodes[index], index).is_err());
}
fn stopping(at: usize, mode: usize, point: Checkpoint) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    (
        Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= at;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: match (stop, mode) {
                        (true, 2) => Some(crate::result::Signal::Int),
                        (true, 3) => Some(crate::result::Signal::Term),
                        _ => None,
                    },
                }
            },
        ),
        count,
    )
}
#[test]
fn completed_comparison_transfer_stops_keep_checked_decisions_and_evidence() {
    for (q, status, record) in [
        (WORD, Decision::Refuted, true),
        (ACTION, Decision::Established, true),
        (
            "a=compare($e.value,to=$e.value,kind=action)",
            Decision::Established,
            true,
        ),
        (
            "a=compare($e.value,to=$alias.value,kind=action)",
            Decision::Refuted,
            false,
        ),
    ] {
        // The last case supplies next:q→r as the second Path, so the source condition fails.
        let second = if !record {
            fixture::F.replace("f=", "alias=")
        } else {
            ALIAS.into()
        };
        let qs = [E, second.as_str(), q];
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::NativeResultNode {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let prepared = prepare_observed(
            fixture::input(false, "compare-unit"),
            &qs,
            &mut Control::unlimited(),
        )
        .unwrap();
        let normal = evaluate_observed(prepared, &mut probe).unwrap();
        assert_eq!(normal.answers[2].status, status);
        let total = count.get();
        assert!(total >= 2);
        for at in [1, total] {
            for mode in 0..4 {
                let (mut control, count) = stopping(at, mode, Checkpoint::NativeResultNode);
                let prepared = prepare_observed(
                    fixture::input(false, "compare-unit"),
                    &qs,
                    &mut Control::unlimited(),
                )
                .unwrap();
                let stopped = evaluate_observed(prepared, &mut control).unwrap();
                assert_ne!(stopped.status(), "error", "{:?}", stopped.issues);
                let a = &stopped.answers[2];
                assert_eq!(a.status, status);
                assert_eq!(a.outputs.contains_key("comparison"), record);
                assert_eq!(a.evidence.len(), usize::from(status == Decision::Refuted));
                rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn operation_comparisons_keep_completed_native_decisions_at_the_final_checkpoint() {
    let sources = || {
        InputSources::from_bytes(
            vec![include_bytes!("../../tests/fixtures/reservations.atoms.json").to_vec()],
            include_bytes!("../../tests/fixtures/public-compose.law").to_vec(),
            include_bytes!("../../tests/fixtures/configuration-operation.archmap.json").to_vec(),
        )
    };
    let qs = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "a=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let r = evaluate_observed_bytes(sources(), &qs, &mut Control::unlimited()).unwrap();
    assert_eq!(r.status(), "complete");
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let op =
        crate::observed::public_compose::op(&graph, r.answers[0].outputs["operation"]).unwrap();
    for action in [false, true] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::ConfigurationOperation {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        if action {
            assert!(op
                .action_difference(r.prepared().inputs(), op, &mut probe)
                .unwrap()
                .is_none());
        } else {
            assert!(op
                .word_equal(r.prepared().inputs(), op, &mut probe)
                .unwrap());
        }
        let total = count.get();
        assert!(total > 10);
        for mode in 0..4 {
            let (mut c, count) = stopping(total, mode, Checkpoint::ConfigurationOperation);
            if action {
                let mut retained = None;
                let failure = op
                    .action_difference_retained(r.prepared().inputs(), op, &mut c, |v| {
                        retained = Some(v.cloned())
                    })
                    .unwrap_err();
                assert!(matches!(
                    failure,
                    crate::construction::ConstructionFailure::Stopped(_)
                ));
                assert_eq!(retained, Some(None));
            } else {
                let mut retained = None;
                let failure = op
                    .word_equal_retained(r.prepared().inputs(), op, &mut c, |v| retained = Some(v))
                    .unwrap_err();
                assert!(matches!(
                    failure,
                    crate::construction::ConstructionFailure::Stopped(_)
                ));
                assert_eq!(retained, Some(true));
            }
            assert_eq!(count.get(), total);
            assert!(c.checkpoint(Checkpoint::ConfigurationOperation).is_err());
            assert_eq!(count.get(), total);
        }
    }
}
#[test]
fn comparison_computation_stops_keep_only_completed_decisions_and_never_probe_after_stop() {
    for q in [
        "a=compare($e.value,to=$e.value,kind=word)",
        "a=compare($e.value,to=$alias.value,kind=action)",
    ] {
        let prefix = example(&[E, ALIAS]);
        let prepared = prepare_observed(
            fixture::input(false, "compare-unit"),
            &[E, ALIAS, q],
            &mut Control::unlimited(),
        )
        .unwrap();
        let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
        let graph = || {
            let mut g = rebuild_for_origin_and_support_recheck(&prefix, &prefix.nodes).unwrap();
            g.requests = prepared.requests().requests().to_vec();
            g.active = crate::observed::call::Context {
                request: 2,
                frame: None,
                iteration: None,
                instance: None,
                case: None,
            };
            g
        };
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::FiniteIteration {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let a = crate::observed::public_compare::evaluate(
            &prepared,
            &env,
            &mut graph(),
            &prepared.requests().requests()[2],
            &mut probe,
        )
        .unwrap();
        assert_eq!(a.status, Decision::Established);
        let total = count.get();
        assert!(total > 5);
        for at in [1, total / 2, total] {
            for mode in 0..4 {
                let (mut c, count) = stopping(at, mode, Checkpoint::FiniteIteration);
                let mut g = graph();
                let answer = crate::observed::public_compare::evaluate(
                    &prepared,
                    &env,
                    &mut g,
                    &prepared.requests().requests()[2],
                    &mut c,
                );
                if at == total {
                    let a = answer.unwrap();
                    assert_eq!(a.status, Decision::Established);
                    assert!(a.outputs.contains_key("comparison"));
                    assert!(!a.reasons.is_empty());
                    env.validate_answer(&g, &prepared.requests().requests()[2], &a)
                        .unwrap();
                } else {
                    assert!(matches!(answer, Err(ValidationFailure::Stop(_))));
                    assert!(g.nodes.iter().all(|n|!matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.witness,crate::observed::construction_result::Witness::Compare(_)))));
                }
                assert_eq!(count.get(), at);
                assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn action_refutation_computation_stops_keep_the_point_and_both_images_together() {
    let qs = [
        E,
        fixture::F,
        fixture::C,
        "d=evaluate(Walk.step,e=@v/different)",
        "a=compare($c.operation,to=$d.value,kind=action)",
    ];
    let prefix = example(&qs[..4]);
    let prepared = prepare_observed(
        fixture::input(false, "compare-unit"),
        &qs,
        &mut Control::unlimited(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
    let graph = || {
        let mut g = rebuild_for_origin_and_support_recheck(&prefix, &prefix.nodes).unwrap();
        g.requests = prepared.requests().requests().to_vec();
        g.active = crate::observed::call::Context {
            request: 4,
            frame: None,
            iteration: None,
            instance: None,
            case: None,
        };
        g
    };
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut probe = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::FiniteIteration {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let normal = crate::observed::public_compare::evaluate(
        &prepared,
        &env,
        &mut graph(),
        &prepared.requests().requests()[4],
        &mut probe,
    )
    .unwrap();
    assert_eq!(normal.status, Decision::Refuted);
    let total = count.get();
    assert!(total > 5);
    for at in [1, total / 2, total - 1, total] {
        for mode in 0..4 {
            let (mut c, count) = stopping(at, mode, Checkpoint::FiniteIteration);
            let mut g = graph();
            let result = crate::observed::public_compare::evaluate(
                &prepared,
                &env,
                &mut g,
                &prepared.requests().requests()[4],
                &mut c,
            );
            if at == total {
                let a = result.unwrap();
                assert_eq!(a.status, Decision::Refuted);
                let Some(Payload::Construction(v)) = &g.get(a.evidence[0]).unwrap().payload else {
                    panic!()
                };
                let D::Comparison(Part::Evidence { facts, .. }) = &v.data else {
                    panic!()
                };
                assert_eq!(
                    facts.iter().map(|f| f.subject.as_str()).collect::<Vec<_>>(),
                    ["q", "r", "q"]
                );
                assert!(facts
                    .iter()
                    .all(|f| f.snapshot == "v" && f.field.is_none() && f.atom.is_none()));
                env.validate_answer(&g, &prepared.requests().requests()[4], &a)
                    .unwrap();
            } else {
                assert!(
                    matches!(result, Err(ValidationFailure::Stop(_))),
                    "反例未完成の停止では比較を確定しない: {result:?}"
                );
                assert!(g.nodes.iter().all(|n|!matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.witness,crate::observed::construction_result::Witness::Compare(_)))));
            }
            assert_eq!(count.get(), at);
            assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
            assert_eq!(count.get(), at);
        }
    }
}
mod primitive {
    use crate as archsig;
    include!("../../tests/common/compare_values.rs");
}
fn primitive_example(qs: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(primitive::input(false, ""), qs, &mut Control::unlimited())
        .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn value_comparison_recheck_rejects_source_values_raw_scope_refs_and_false_proofs() {
    let r = primitive_example(&[
        "n=evaluate(Values.vinteger,s=@v/a)",
        "m=evaluate(Values.vpair,s=@v/a)",
        "a=compare($n.value,to=$m.value[0],kind=value)",
        "raw=compare(@v/a,to=@v/a,kind=value)",
    ]);
    let record = r.answers[2].outputs["comparison"].0;
    let claim = r.answers[2].claim.unwrap().0;
    let evidence = r.answers[2].evidence[0].0;
    let raw = r.answers[3].outputs["comparison"].0;
    let Some(Payload::Construction(v)) = &r.nodes[raw].payload else {
        panic!()
    };
    let D::Comparison(Part::Comparison { left, .. }) = v.data else {
        panic!()
    };
    for case in 0..10 {
        let target = match case {
            0 => r.answers[0].outputs["value"].0,
            1..=3 => record,
            4..=5 => claim,
            6 => evidence,
            _ => raw,
        };
        completion_mutation(&r, target, |nodes| {
            let target = if case >= 7 { left.0 } else { target };
            match case {
                0 => nodes[target].payload = Some(Payload::Scalar(Scalar::Z(0.into()))),
                1 => nodes[target].support.clear(),
                2 => nodes[target].scope.snapshots.clear(),
                3 => {
                    let Some(Payload::Construction(v)) = &mut nodes[target].payload else {
                        panic!()
                    };
                    let D::Comparison(Part::Comparison { kind, .. }) = &mut v.data else {
                        panic!()
                    };
                    *kind = "word".into();
                }
                4 => nodes[target].judgment.as_mut().unwrap().status = Decision::Established,
                5 => nodes[target].evidence.clear(),
                6 => {
                    let Some(Payload::Construction(v)) = &mut nodes[target].payload else {
                        panic!()
                    };
                    let D::Comparison(Part::Evidence { left, right, .. }) = &mut v.data else {
                        panic!()
                    };
                    *left = *right;
                }
                7 => {
                    nodes[target].scope.readings.insert("Values".into());
                }
                8 => nodes[target].support.clear(),
                _ => {
                    nodes[target].payload = Some(Payload::Scalar(Scalar::Subject {
                        snapshot: "w".into(),
                        subject: "a".into(),
                        entity: "Values.Sample".into(),
                    }))
                }
            }
        });
    }
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let changed = primitive::input(false, "");
    let bytes = String::from_utf8(changed.archmap().bytes().to_vec())
        .unwrap()
        .replace("有限モデル", "変更モデル");
    let changed = InputSources::from_bytes(
        vec![changed.definitions()[0].bytes().to_vec()],
        changed.law().bytes().to_vec(),
        bytes.into_bytes(),
    );
    let qs = [
        "n=evaluate(Values.vinteger,s=@v/a)",
        "m=evaluate(Values.vpair,s=@v/a)",
        "a=compare($n.value,to=$m.value[0],kind=value)",
        "raw=compare(@v/a,to=@v/a,kind=value)",
    ];
    let prepared = prepare_observed(changed, &qs, &mut Control::unlimited()).unwrap();
    let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
    assert!(env.recheck_node(&graph, &r.nodes[record], record).is_err());
    let mut wrong = r.prepared().requests().requests()[3].clone();
    wrong.head = Selector::Subject {
        snapshot: "v".into(),
        subject: "b".into(),
    };
    let env = Environment::with_prepared(r.prepared(), &mut Control::unlimited()).unwrap();
    assert!(env.validate_answer(&graph, &wrong, &r.answers[3]).is_err());
}
#[test]
fn ground_value_computation_stops_keep_only_complete_equalities_and_counterexamples() {
    for (right, decision) in [("@v/a", Decision::Established), ("@v/b", Decision::Refuted)] {
        let q = format!("a=compare(@v/a,to={right},kind=value)");
        let prefix = primitive_example(&[]);
        let prepared = prepare_observed(
            primitive::input(false, ""),
            &[q.as_str()],
            &mut Control::unlimited(),
        )
        .unwrap();
        let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
        let graph = || {
            let mut g = rebuild_for_origin_and_support_recheck(&prefix, &prefix.nodes).unwrap();
            g.requests = prepared.requests().requests().to_vec();
            g
        };
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::FiniteIteration {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let a = crate::observed::public_compare::evaluate(
            &prepared,
            &env,
            &mut graph(),
            &prepared.requests().requests()[0],
            &mut probe,
        )
        .unwrap();
        assert_eq!(a.status, decision);
        let total = count.get();
        assert!(total >= 4);
        for at in [1, total / 2, total - 1, total] {
            for mode in 0..4 {
                let (mut c, count) = stopping(at, mode, Checkpoint::FiniteIteration);
                let mut g = graph();
                let outcome = crate::observed::public_compare::evaluate(
                    &prepared,
                    &env,
                    &mut g,
                    &prepared.requests().requests()[0],
                    &mut c,
                );
                if at >= total - 1 {
                    let a = outcome.unwrap();
                    assert_eq!(a.status, decision);
                    assert!(a.outputs.contains_key("comparison"));
                    assert_eq!(a.evidence.len(), usize::from(decision == Decision::Refuted));
                    env.validate_answer(&g, &prepared.requests().requests()[0], &a)
                        .unwrap();
                } else {
                    assert!(matches!(outcome, Err(ValidationFailure::Stop(_))));
                    assert!(g.nodes.iter().all(|n|!matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.witness,crate::observed::construction_result::Witness::Compare(_)))));
                }
                assert_eq!(count.get(), at);
                assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn ground_value_transfer_stops_keep_the_complete_original_evidence() {
    for (to, decision) in [("@v/a", Decision::Established), ("@v/b", Decision::Refuted)] {
        let q = format!("a=compare(@v/a,to={to},kind=value)");
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::NativeResultNode {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        evaluate_observed_bytes(primitive::input(false, ""), &[q.as_str()], &mut probe).unwrap();
        let total = count.get();
        assert!(total >= 2);
        for at in [1, total] {
            for mode in 0..4 {
                let (mut c, count) = stopping(at, mode, Checkpoint::NativeResultNode);
                let r = evaluate_observed_bytes(primitive::input(false, ""), &[q.as_str()], &mut c)
                    .unwrap();
                assert_eq!(r.status(), "interrupted", "{:?}", r.issues);
                assert_eq!(r.answers[0].status, decision);
                assert!(r.answers[0].outputs.contains_key("comparison"));
                assert_eq!(
                    r.answers[0].evidence.len(),
                    usize::from(decision == Decision::Refuted)
                );
                rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn nested_ground_equality_retains_only_the_finished_outer_result_before_the_final_stop() {
    let value = |last| Scalar::List {
        element: Type::Tuple(vec![Type::Bool, Type::Z]),
        items: (0..8)
            .map(|i| {
                Scalar::Tuple(vec![
                    Scalar::Bool(false),
                    Scalar::Z((if i == 7 { last } else { i }).into()),
                ])
            })
            .collect(),
    };
    for (right, expected) in [(7, true), (9, false)] {
        let left = value(7);
        let right = value(right);
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let probe = Control::new(Limits::default(), move |p| {
            if p == Checkpoint::FiniteIteration {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        assert_eq!(
            crate::observed::data::equal(&left, &right, &probe).unwrap(),
            expected
        );
        let total = count.get();
        assert!(total > 20);
        for at in [1, total / 2, total - 1, total] {
            for mode in 0..4 {
                let (c, count) = stopping(at, mode, Checkpoint::FiniteIteration);
                let mut retained = None;
                let outcome = crate::observed::data::equal_retained(&left, &right, &c, |v| {
                    retained = Some(v)
                });
                assert!(matches!(outcome, Err(ValidationFailure::Stop(_))));
                assert_eq!(retained, if at == total { Some(expected) } else { None });
                assert_eq!(count.get(), at);
                assert!(c.clone().checkpoint(Checkpoint::FiniteIteration).is_err());
                assert_eq!(count.get(), at);
            }
        }
    }
}
#[test]
fn raw_subject_comparison_rechecks_its_request_context_even_for_an_identical_value() {
    let mut r = primitive_example(&[
        "prior=compare(@v/a,to=@v/a,kind=value)",
        "current=compare(@v/a,to=@v/a,kind=value)",
    ]);
    let record = r.answers[1].outputs["comparison"].0;
    let Some(Payload::Construction(v)) = &r.nodes[record].payload else {
        panic!()
    };
    let D::Comparison(Part::Comparison { left, .. }) = v.data else {
        panic!()
    };
    assert_eq!(r.contexts[left.0].request, 1);
    r.contexts[left.0].request = 0;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&r, &r.nodes),
        Err(ValidationFailure::Internal(_))
    ));
}
