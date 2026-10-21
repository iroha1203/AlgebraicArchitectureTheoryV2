use super::*;
use crate::observed::PrepareFailure;
use crate::observed::{
    construction_result::{ConstructionData as D, Witness},
    control::{Limits, Usage},
    public_compose::Part,
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
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
#[test]
fn composed_dag_rejects_forged_actions_words_names_endpoints_conditions_and_scope() {
    let r = example(&ASKS);
    let original = r.answers[2].outputs["operation"].0;
    for kind in 0..10 {
        let target = if kind == 0 {
            r.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(&v.data,D::Composition(Part::Action{..})))).unwrap()
        } else {
            original
        };
        completion_mutation(&r, target, |nodes| {
            let n = &mut nodes[target];
            match kind {
                0 => {
                    let Some(Payload::Construction(v)) = &mut n.payload else {
                        panic!()
                    };
                    let D::Composition(Part::Action { images, .. }) = &mut v.data else {
                        panic!()
                    };
                    images.reverse();
                }
                1..=6 => {
                    let Some(Payload::Construction(v)) = &mut n.payload else {
                        panic!()
                    };
                    let D::Composition(Part::Operation {
                        source,
                        target,
                        candidate,
                        map,
                        action,
                        preservation,
                        left,
                        right,
                        word,
                    }) = &mut v.data
                    else {
                        panic!()
                    };
                    match kind {
                        1 => word.reverse(),
                        2 => std::mem::swap(left, right),
                        3 => std::mem::swap(source, target),
                        4 => *candidate = *map,
                        5 => *action = *source,
                        _ => *preservation = *map,
                    }
                }
                7 => n.support.clear(),
                8 => n.scope.readings.clear(),
                _ => n.scope.completions = true,
            }
        });
    }
    let label = r.nodes.iter().position(|n| matches!(&n.payload,
        Some(Payload::Construction(v)) if matches!(&v.witness, Witness::Compose(_))
            && matches!(v.data, D::ConstructionLabel(_)))).unwrap();
    completion_mutation(&r, label, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[label].payload else { panic!() };
        v.data = D::ConstructionLabel(Scalar::Text("compose".into()));
    });
    let mut control = Control::unlimited();
    let env = Environment::with_prepared(r.prepared(), &mut control).unwrap();
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    for kind in 0..4 {
        let mut a = r.answers[2].clone();
        match kind {
            0 => a.outputs.remove("map").map(|_| ()).unwrap(),
            1 => a.status = Decision::Refuted,
            2 => a.scope.snapshots.clear(),
            _ => {
                a.outputs
                    .insert("operation".into(), r.answers[0].outputs["operation"]);
            }
        }
        assert!(
            env.validate_answer(&graph, &r.prepared().requests().requests()[2], &a)
                .is_err()
        );
    }
}
#[test]
fn composition_rechecks_actual_inputs_requests_and_refutation_proof() {
    let r = example(&ASKS);
    let last = r.answers[2].outputs["operation"].0;
    let mut control = Control::unlimited();
    let altered = MAP.replace("\"value\":\"2\"", "\"value\":\"99\"");
    assert_ne!(altered, MAP);
    let prepared = prepare_observed(sources(&altered), &ASKS, &mut control).unwrap();
    let env = Environment::with_prepared(&prepared, &mut control).unwrap();
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    assert!(env.recheck_node(&graph, &r.nodes[last], last).is_err());
    let prepared = prepare_observed(
        sources(MAP),
        &[
            ASKS[0],
            ASKS[1],
            "c=compose($n.operation,then=$m.operation)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    let env = Environment::with_prepared(&prepared, &mut Control::unlimited()).unwrap();
    graph.requests = prepared.requests().requests().to_vec();
    assert!(env.recheck_node(&graph, &r.nodes[last], last).is_err());
    let bad = example(&[
        ASKS[0],
        "bad=compose($m.operation,then=$m.operation)",
        "blocked=compose($bad.operation,then=$m.operation)",
        "plan=needed($blocked)",
    ]);
    assert_eq!(bad.answers[1].status, Decision::Refuted);
    let claim = bad.answers[1].outputs["proposition"].0;
    completion_mutation(&bad, claim, |nodes| {
        let reason = &mut nodes[claim].judgment.as_mut().unwrap().reasons[0];
        let ReasonKind::ConditionFailed { construction, .. } = &mut reason.kind else { panic!() };
        *construction = "compose";
    });
    let proof = bad.answers[1].evidence[0].0;
    completion_mutation(&bad, proof, |nodes| {
        let Some(Payload::Construction(v)) = &mut nodes[proof].payload else {
            panic!()
        };
        let D::Composition(Part::Evidence { left, right }) = &mut v.data else {
            panic!()
        };
        *left = *right;
    });
    let condition=bad.nodes.iter().position(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,D::Composition(Part::Endpoints{..})))).unwrap();
    completion_mutation(&bad, condition, |nodes| {
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
        for at in [total - 1, total] {
            for mode in 0..4 {
                let count = Rc::new(Cell::new(0usize));
                let seen = count.clone();
                let mut c = Control::new(
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
                );
                let prepared =
                    prepare_observed(sources(MAP), &ASKS, &mut Control::unlimited()).unwrap();
                let stopped = evaluate_observed(prepared, &mut c).unwrap();
                assert_ne!(stopped.status(), "error", "{:?}", stopped.issues);
                assert_eq!(count.get(), at);
                rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
                let a = &stopped.answers[2];
                if point == Checkpoint::NativeResultNode || at == total {
                    assert_eq!(a.status, Decision::Established);
                    assert!(a.outputs.contains_key("operation"));
                    let graph =
                        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
                    let result = graph.get(a.outputs["operation"]).unwrap();
                    assert!(
                        matches!(&result.payload,Some(Payload::Construction(v)) if matches!(v.witness,Witness::Compose(_)))
                    );
                } else {
                    assert!(!a.outputs.contains_key("operation"));
                }
                assert_eq!(count.get(), at);
            }
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
