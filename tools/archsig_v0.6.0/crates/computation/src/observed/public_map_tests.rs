use super::*;
use crate::observed::construction_result::ConstructionData as D;
const D_BYTES: &[u8] = include_bytes!("../../../../tests/fixtures/reservations.atoms.json");
const L_BYTES: &[u8] = include_bytes!("../../../../tests/fixtures/reservations.law");
const A_BYTES: &str = include_str!("../../../../tests/fixtures/reservations.archmap.json");
const MAP_ASK: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";
fn inputs(map: &str) -> InputSources {
    InputSources::from_bytes(
        vec![D_BYTES.to_vec()],
        L_BYTES.to_vec(),
        map.as_bytes().to_vec(),
    )
}
fn example(map: &str) -> ObservedEvaluation {
    let result =
        evaluate_observed_bytes(inputs(map), &[MAP_ASK], &Control::unlimited()).unwrap();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    result
}
fn changed_native(
    result: &ObservedEvaluation,
    select: impl Fn(&D) -> bool,
    change: impl Fn(&mut D),
) {
    let i = result
        .nodes
        .iter()
        .position(|n| matches!(&n.payload,Some(Payload::Construction(v)) if select(&v.data)))
        .unwrap();
    completion_mutation(result, i, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[i].payload else {
            unreachable!()
        };
        change(&mut v.data);
    });
}
#[test]
fn native_counterexamples_reject_changed_facts_bindings_and_evidence_coverage() {
    let map = A_BYTES
        .lines()
        .map(|line| {
            if line.contains("\"id\": \"m-states\"") {
                line.replace("[\"v\", \"r\"]", "[\"v\", \"temp\"]")
                    .replace("[\"v\", \"s\"]", "[\"v\", \"r\"]")
                    .replace("[\"v\", \"temp\"]", "[\"v\", \"s\"]")
            } else {
                line.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let result = example(&map);
    assert_eq!(result.answers[0].status, Decision::Refuted);
    changed_native(
        &result,
        |d| matches!(d, D::Counterexample { .. }),
        |d| {
            if let D::Counterexample { facts, .. } = d {
                facts.clear();
            }
        },
    );
    changed_native(
        &result,
        |d| matches!(d, D::Counterexample { .. }),
        |d| {
            if let D::Counterexample { subject, left, .. } = d {
                *subject = *left;
            }
        },
    );
    let claim = result.answers[0].claim.unwrap().0;
    completion_mutation(&result, claim, |nodes| {
        nodes[claim].evidence.pop();
        nodes[claim].judgment.as_mut().unwrap().evidence.pop();
    });
}
#[test]
fn native_map_stops_latch_without_discarding_checked_maps_or_resuming_computation() {
    use std::{cell::Cell, rc::Rc};
    for point in [
        Checkpoint::ConfigurationMap,
        Checkpoint::ConfigurationOperation,
        Checkpoint::NativeResultNode,
    ] {
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let probe = Control::new(move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            None
        });
        let original = evaluate_observed_bytes(inputs(A_BYTES), &[MAP_ASK], &probe).unwrap();
        assert_eq!(original.status(), "complete");
        let total = count.get();
        assert!(total > 0);
        // 停止の種類は共通の停止処理を通るので SIGINT 停止だけを見る。
        for at in [1, (total / 2).max(1), total] {
            let count = Rc::new(Cell::new(0usize));
            let seen = count.clone();
            let control = Control::new(move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                (seen.get() >= at).then_some(archsig_input::result::Signal::Int)
            });
            let result =
                evaluate_observed_bytes(inputs(A_BYTES), &[MAP_ASK], &control).unwrap();
            assert_eq!(
                result.status(),
                "interrupted",
                "{point:?}/{at}: {:?}",
                result.issues
            );
            assert!(
                !result
                    .issues
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Internal(_))),
                "{:?}",
                result.issues
            );
            assert!(control.stop_reason().is_some());
            if at == total {
                assert!(
                    result.answers[0].outputs.contains_key("map"),
                    "{point:?}: {:?}",
                    result.answers
                );
                assert_eq!(result.answers[0].status, Decision::Established);
                if matches!(
                    point,
                    Checkpoint::NativeResultNode | Checkpoint::ConfigurationOperation
                ) {
                    assert!(result.answers[0].outputs.contains_key("operation"));
                }
                rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
            }
        }
    }
}
