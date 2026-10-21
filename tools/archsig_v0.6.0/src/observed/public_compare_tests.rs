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
