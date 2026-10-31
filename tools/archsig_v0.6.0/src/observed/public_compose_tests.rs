use super::*;
use crate::observed::PrepareFailure;
use crate::{
    control::{Limits, Usage},
    observed::{
        construction_result::{ConstructionData as D, Witness},
        public_compose::Part,
    },
};
use std::{cell::Cell, rc::Rc};
const DEFINITIONS: &[u8] = include_bytes!("../../tests/fixtures/reservations.atoms.json");
const LAW: &[u8] = include_bytes!("../../tests/fixtures/public-compose.law");
const MAP: &str = include_str!("../../tests/fixtures/configuration-operation.archmap.json");
const ASKS: [&str; 3] = [
    "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
    "n=map(Reservations.Migration,on=@v/n,reading=Reservations)",
    "c=compose($m.operation,then=$n.operation)",
];
fn sources(map: &str) -> InputSources {
    InputSources::from_bytes(
        vec![DEFINITIONS.to_vec()],
        LAW.to_vec(),
        map.as_bytes().to_vec(),
    )
}
fn example(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(sources(MAP), asks, &mut Control::unlimited()).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
#[test]
fn composition_rechecks_actual_inputs_requests_and_refutation_proof() {
    let r = example(&ASKS);
    assert_eq!(r.answers[2].status, Decision::Established);
    let bad = example(&[
        ASKS[0],
        "bad=compose($m.operation,then=$m.operation)",
        "blocked=compose($bad.operation,then=$m.operation)",
        "plan=needed($blocked)",
    ]);
    assert_eq!(bad.answers[1].status, Decision::Refuted);
    // 判断の再検査の代表: 端点条件の判断を反転すると核が拒否する。
    let condition=bad.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Composition(Part::Endpoints{..})))).unwrap();
    rejects_mutated_prefix(&bad, condition, |nodes| {
        nodes[condition].judgment.as_mut().unwrap().status = Decision::Established
    });
}
#[test]
fn native_and_transfer_composition_stops_preserve_only_checked_operations() {
    for point in [
        Checkpoint::ConfigurationOperation,
        Checkpoint::NativeResultNode,
    ] {
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut probe = Control::new(Limits::default(), move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let prepared = prepare_observed(sources(MAP), &ASKS, &mut Control::unlimited()).unwrap();
        let normal = evaluate_observed(prepared, &mut probe).unwrap();
        assert_eq!(normal.status(), "complete");
        let total = count.get();
        assert!(total > 10);
        // 停止の種類は time だけ、位置は完了直前の1点だけを見る。
        let at = total - 1;
        let seen = Rc::new(Cell::new(0usize));
        let mut c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: None,
            },
            move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= at;
                Usage {
                    elapsed_ms: u128::from(stop),
                    ..Usage::default()
                }
            },
        );
        let prepared = prepare_observed(sources(MAP), &ASKS, &mut Control::unlimited()).unwrap();
        let stopped = evaluate_observed(prepared, &mut c).unwrap();
        assert_ne!(stopped.status(), "error", "{:?}", stopped.issues);
        let graph = rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
        let a = &stopped.answers[2];
        if point == Checkpoint::NativeResultNode {
            assert_eq!(a.status, Decision::Established);
            assert!(a.outputs.contains_key("operation"));
            let result = graph.get(a.outputs["operation"]).unwrap();
            assert!(
                matches!(&result.payload,Some(Payload::Construction(v)) if matches!(v.witness,Witness::Compose(_)))
            );
        } else {
            assert!(!a.outputs.contains_key("operation"));
        }
    }
}
#[test]
fn compose_resolution_keeps_forward_dependency_priority_and_empty_cycle_results() {
    let prepared = prepare_observed(
        sources(MAP),
        &[ASKS[2], ASKS[1], ASKS[0]],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(prepared.requests().evaluation_order(), &[1, 2, 0]);
    let failed = prepare_observed(
        sources(MAP),
        &[
            ASKS[0],
            "a=compose($b.operation,then=$m.operation)",
            "b=compose($a.operation,then=$m.operation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let wire = failed.wire().unwrap();
    let crate::canonical::Json::Obj(ref wire) = wire else {
        panic!()
    };
    assert_eq!(wire["nodes"], crate::canonical::Json::Arr(vec![]));
    assert_eq!(wire["answers"], crate::canonical::Json::Arr(vec![]));
    let PrepareFailure::Requests {
        failure: crate::observed::request::ResolveFailure::Invalid { requests, .. },
        ..
    } = failed
    else {
        panic!("循環の静的不正")
    };
    assert!(
        requests
            .iter()
            .any(|r| r.id == "a" && r.dependencies.contains(&"b".into()))
    );
    assert!(
        requests
            .iter()
            .any(|r| r.id == "b" && r.dependencies.contains(&"a".into()))
    );
}
