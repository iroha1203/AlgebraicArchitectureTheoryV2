use super::*;
use crate::{
    control::{Limits, Usage},
    observed::{construction_result::ConstructionData as D, public_compare::Part},
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
    r
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
    assert_eq!(r.answers[4].status, Decision::Refuted);
    // 反例の再検査の代表: 反例の事実を落とすと核が拒否する。
    let proof = r.answers[4].evidence[0].0;
    rejects_mutated_prefix(&r, proof, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[proof].payload else {
            panic!()
        };
        let D::Comparison(Part::Evidence { facts, .. }) = &mut v.data else {
            panic!()
        };
        facts.clear();
    });
    // 端点条件の判断を反転すると核が拒否する。
    let bad = example(&[E, fixture::F, "a=compare($e.value,to=$f.value,kind=action)"]);
    assert_eq!(bad.answers[2].status, Decision::Refuted);
    let condition=bad.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Comparison(Part::Endpoints{..})))).unwrap();
    rejects_mutated_prefix(&bad, condition, |nodes| {
        nodes[condition].judgment.as_mut().unwrap().status = Decision::Established;
    });
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
        // 停止の種類と位置は代表1つ(最初の転記点での time 停止)だけを見る。
        let (mut control, _) = stopping(1, 0, Checkpoint::NativeResultNode);
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
        {
            let (mut c, _) = stopping(total, 0, Checkpoint::ConfigurationOperation);
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
    assert_eq!(r.answers[2].status, Decision::Refuted);
    assert_eq!(r.answers[3].status, Decision::Established);
    // 判断の再検査の代表: 値比較の命題の判断を反転すると核が拒否する。
    let claim = r.answers[2].claim.unwrap().0;
    rejects_mutated_prefix(&r, claim, |nodes| {
        nodes[claim].judgment.as_mut().unwrap().status = Decision::Established
    });
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
        for at in [1, total] {
            {
                let (mut c, _) = stopping(at, 0, Checkpoint::FiniteIteration);
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
        let (mut c, _) = stopping(1, 0, Checkpoint::NativeResultNode);
        let r =
            evaluate_observed_bytes(primitive::input(false, ""), &[q.as_str()], &mut c).unwrap();
        assert_eq!(r.status(), "interrupted", "{:?}", r.issues);
        assert_eq!(r.answers[0].status, decision);
        assert!(r.answers[0].outputs.contains_key("comparison"));
        assert_eq!(
            r.answers[0].evidence.len(),
            usize::from(decision == Decision::Refuted)
        );
        rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
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
        let mut completed_at = None;
        assert_eq!(
            crate::observed::data::equal_retained(&left, &right, &probe, |answer| {
                assert_eq!(answer, expected);
                assert!(completed_at.replace(count.get()).is_none());
            })
            .unwrap(),
            expected
        );
        let total = count.get();
        let completed_at = completed_at.unwrap();
        assert!(completed_at > 1 && completed_at < total);
        // 完成通知の直前・直後を検査する。外側へ戻るpostは複数あり得る。
        for at in [1, completed_at, completed_at + 1, total] {
            {
                let (c, _) = stopping(at, 0, Checkpoint::FiniteIteration);
                let mut retained = None;
                let outcome = crate::observed::data::equal_retained(&left, &right, &c, |v| {
                    retained = Some(v)
                });
                assert!(matches!(outcome, Err(ValidationFailure::Stop(_))));
                assert_eq!(
                    retained,
                    if at > completed_at {
                        Some(expected)
                    } else {
                        None
                    }
                );
            }
        }
    }
}

#[test]
fn dynamic_value_type_conditions_recheck_both_original_producers_and_their_evidence() {
    let r = evaluate_observed_bytes(
        primitive::input(false, "view flagged():Packet=Flag(false);"),
        &[
            "full=evaluate(Values.vpacket,s=@v/a)",
            "flag=evaluate(Values.flagged)",
            "c=compare($full.value[0],to=$flag.value[0],kind=value)",
            "plan=needed($c)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", r.issues);
    assert_eq!(r.answers[2].status, Decision::Undetermined);
    assert_eq!(r.answers[3].status, Decision::Established);
    let condition=r.nodes.iter().position(|n|matches!(&n.rule,Rule::ProjectionCheck{parameter,part:ProjectionCheckPart::Condition} if parameter=="head/to")).unwrap();
    rejects_mutated_prefix(&r, condition, |nodes| {
        nodes[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
}
#[test]
fn dynamic_value_type_condition_stops_never_publish_an_unchecked_comparison() {
    let input = || primitive::input(false, "view flagged():Packet=Flag(false);");
    let qs = [
        "full=evaluate(Values.vpacket,s=@v/a)",
        "flag=evaluate(Values.flagged)",
        "c=compare($full.value[0],to=$flag.value[0],kind=value)",
        "plan=needed($c)",
    ];
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut probe = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::Projection {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let prepared=||prepare_observed(input(),&qs,&mut Control::unlimited()).unwrap();
    let normal = evaluate_observed(prepared(), &mut probe).unwrap();
    assert_eq!(normal.status(), "partial");
    let total = count.get();
    assert!(total > 5);
    let (mut c, _) = stopping(total / 2, 0, Checkpoint::Projection);
    let r = evaluate_observed(prepared(), &mut c).unwrap();
    assert_eq!(r.status(), "interrupted", "{:?}", r.issues);
    assert!(!r.answers[2].outputs.contains_key("comparison"));
    assert_ne!(r.answers[2].status, Decision::Established);
    assert_ne!(r.answers[2].status, Decision::Refuted);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}
#[path = "public_term_compare_tests.rs"]
mod term_cases;

#[path = "public_relation_sources_tests.rs"]
mod relation_sources_tests;
