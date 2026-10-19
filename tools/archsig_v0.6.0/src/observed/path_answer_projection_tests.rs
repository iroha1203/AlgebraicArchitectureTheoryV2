use super::*;
#[allow(dead_code)]
mod fixture {
    use crate as archsig;
    include!("../../tests/common/path_answer_projections.rs");
}
const ASK: &[&str] = &[
    "seed=evaluate(Walk.seed)",
    "prior=check(Walk.prior)",
    "first=evaluate(Walk.join,e=@v/e,f=@v/next)",
    "other=evaluate(Walk.join,e=@v/e,f=@v/next)",
    "foreign=evaluate(Walk.keep_node,x=$other.value.target)",
    "take=evaluate(Walk.keep_node,x=$first.evaluation.value.target)",
    "kept=evaluate(Walk.keep,p=$first.value)",
];
fn result() -> ObservedEvaluation {
    let r = evaluate_observed_bytes(fixture::composed(false, "r1"), ASK, &mut named_call_quiet())
        .unwrap();
    assert_eq!(r.status(), "complete");
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
fn env(r: &ObservedEvaluation) -> Environment<'_> {
    Environment::with_requests(
        r.prepared.inputs(),
        r.prepared.requests().requests(),
        &mut named_call_quiet(),
    )
    .unwrap()
}
fn source(r: &ObservedEvaluation, answer: usize) -> usize {
    let Some(Payload::Evaluation { expression, .. }) =
        &r.nodes[r.answers[answer].outputs["evaluation"].0].payload
    else {
        panic!()
    };
    expression.0
}
#[test]
fn path_answer_component_equal_foreign_ref_is_not_the_original_selection() {
    let r = result();
    let at = source(&r, 5);
    let selected = r.answers[5].outputs["value"];
    let foreign = r.answers[4].outputs["value"];
    let mut shape = rebuild_for_origin_and_support_recheck(&r, &r.nodes[..at]).unwrap();
    assert_ne!(selected, foreign);
    assert!(selected.0 < at && foreign.0 < at);
    assert_eq!(
        shape.get(selected).unwrap().ty,
        shape.get(foreign).unwrap().ty
    );
    assert_eq!(
        shape.scalar(selected).unwrap(),
        shape.scalar(foreign).unwrap()
    );
    let change = |nodes: &mut [Node]| {
        let Some(Payload::Expression { bindings, .. }) = &mut nodes[at].payload else {
            panic!()
        };
        assert_eq!(bindings[0].value, selected);
        bindings[0].value = foreign;
        for reference in &mut nodes[at].arguments {
            if *reference == selected {
                *reference = foreign;
            }
        }
    };
    let mut changed = r.nodes.clone();
    change(&mut changed);
    shape.active = r.contexts[at];
    shape
        .push(changed[at].clone())
        .expect("同型・同値・既出の別Refは形検査を通る");
    completion_mutation(&r, at, change);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
}

#[test]
fn path_answer_component_same_environment_rechecks_producer_requests_values_and_restoration() {
    let r = result();
    let mut graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let environment = env(&r);
    let target = r.answers[5].outputs["evaluation"].0;
    let producer = r.answers[2].outputs["value"].0;
    let selected = r.answers[5].outputs["value"].0;
    let original_requests = graph.requests.clone();
    let original_registry = graph.checked_answers.clone();
    for variant in 0..7 {
        environment
            .recheck_node(&graph, &graph.nodes[target], target)
            .unwrap();
        match variant {
            0 => {
                let Some(Payload::Scalar(Scalar::Path(path))) = &mut graph.nodes[producer].payload
                else {
                    panic!()
                };
                path.step.as_mut().unwrap().target = Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    entity: "Paths.Node".into(),
                };
            }
            1 => {
                let Some(Payload::Scalar(Scalar::Path(path))) = &mut graph.nodes[producer].payload
                else {
                    panic!()
                };
                let step = path.step.as_mut().unwrap();
                assert_eq!(step.word_tail.len(), 1);
                std::mem::swap(&mut step.generator, &mut step.word_tail[0]);
            }
            2 => {
                let Selector::Answer { path, .. } = &mut graph.requests[5].arguments[0].value
                else {
                    panic!()
                };
                *path.last_mut().unwrap() =
                    crate::observed::projection::ProjectionStep::Field("source".into());
            }
            3 => {
                let other = graph
                    .checked_answers
                    .iter()
                    .find(|(index, _)| *index == 3)
                    .unwrap()
                    .1
                    .outputs
                    .clone();
                let producer = graph
                    .checked_answers
                    .iter_mut()
                    .find(|(index, _)| *index == 2)
                    .unwrap();
                assert_ne!(producer.1.outputs, other);
                producer.1.outputs = other;
            }
            4 => {
                let Some(Payload::Scalar(Scalar::Subject { subject, .. })) =
                    &mut graph.nodes[selected].payload
                else {
                    panic!()
                };
                assert_eq!(subject, "r");
                *subject = "p".into();
            }
            5 => {
                assert!(graph.nodes[selected].scope.snapshots.contains("v"));
                graph.nodes[selected].scope.snapshots.clear();
            }
            6 => graph.contexts[source(&r, 5)].request = 4,
            _ => unreachable!(),
        }
        assert!(
            matches!(
                environment.recheck_node(&graph, &graph.nodes[target], target),
                Err(ValidationFailure::Internal(_))
            ),
            "variant {variant}"
        );
        assert!(
            matches!(
                env(&r).recheck_node(&graph, &graph.nodes[target], target),
                Err(ValidationFailure::Internal(_))
            ),
            "fresh variant {variant}"
        );
        graph.nodes = r.nodes.clone();
        graph.contexts = r.contexts.clone();
        graph.requests = original_requests.clone();
        graph.checked_answers = original_registry.clone();
        environment
            .recheck_node(&graph, &graph.nodes[target], target)
            .unwrap();
    }
}

#[test]
fn path_answer_condition_rejects_forged_inapplicability_for_a_valid_component() {
    let asks = [
        "seed=evaluate(Walk.seed)",
        "p=evaluate(Walk.join,e=@v/e,f=@v/next)",
        "take=evaluate(Walk.keep_hop,e=$p.value.generators[2])",
        "later=evaluate(Walk.seed)",
    ];
    let r = evaluate_observed_bytes(
        fixture::composed(false, "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    assert_eq!(r.answers[2].status, Decision::Undetermined);
    let graph = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    let environment = env(&r);
    let request = &r.prepared.requests().requests()[2];
    environment
        .validate_answer(&graph, request, &r.answers[2])
        .unwrap();
    let actual = r
        .nodes
        .iter()
        .position(|node| {
            matches!(
                node.rule,
                Rule::ProjectionCheck {
                    part: ProjectionCheckPart::Actual,
                    ..
                }
            )
        })
        .unwrap();
    completion_mutation(&r, actual, |nodes| {
        nodes[actual].payload = Some(Payload::Scalar(Scalar::Bool(true)))
    });
    let mut changed = r.answers[2].clone();
    changed
        .reasons
        .retain(|reason| !matches!(reason.kind, ReasonKind::ConditionFailed { .. }));
    assert_ne!(changed, r.answers[2]);
    assert!(matches!(
        environment.validate_answer(&graph, request, &changed),
        Err(ValidationFailure::Internal(_))
    ));
    environment
        .validate_answer(&graph, request, &r.answers[2])
        .unwrap();
    // 元の検査済みSelectorを有効な位置へ変えた別batchに、旧反証を移せない。
    let valid = [
        asks[0],
        asks[1],
        "take=evaluate(Walk.keep_hop,e=$p.value.generators[1])",
        asks[3],
    ];
    let valid = evaluate_observed_bytes(
        fixture::composed(false, "r1"),
        &valid,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(valid.status(), "complete");
    let graph = rebuild_for_origin_and_support_recheck(&valid, &valid.nodes).unwrap();
    let environment = env(&valid);
    let request = &valid.prepared.requests().requests()[2];
    environment
        .validate_answer(&graph, request, &valid.answers[2])
        .unwrap();
    environment
        .validate_answer(&graph, request, &valid.answers[2])
        .unwrap();
    // 旧反証のRefが全て存在する同じgraphで、検査済み元Selectorだけを
    // 有効な位置へ替える。未知Refの拒否を反証再検査の代用にしない。
    let mut hybrid = rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    hybrid.requests = valid.prepared.requests().requests().to_vec();
    hybrid.active = r.contexts[actual];
    let Signature::View { params, .. } =
        &valid.prepared.inputs().law().declarations["Walk.keep_hop"].signature
    else {
        panic!()
    };
    assert!(matches!(
        environment
            .answer_binding(&hybrid, &request.arguments[0].value, params[0].span)
            .unwrap(),
        crate::observed::environment::AnswerBinding::Reference(_)
    ));
    for reason in &r.answers[2].reasons {
        for reference in &reason.dependencies {
            assert!(reference.0 < hybrid.nodes.len());
        }
        if let ReasonKind::ConditionFailed { condition, .. } = reason.kind {
            assert!(condition.0 < hybrid.nodes.len());
            assert_eq!(hybrid.get(condition).unwrap().ty, NodeType::Proposition);
        }
    }
    assert!(matches!(
        environment.recheck_node(&hybrid, &hybrid.nodes[actual], actual),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(matches!(
        environment.validate_answer(&hybrid, request, &r.answers[2]),
        Err(ValidationFailure::Internal(_))
    ));
    hybrid.requests = r.prepared.requests().requests().to_vec();
    env(&r)
        .recheck_node(&hybrid, &hybrid.nodes[actual], actual)
        .unwrap();
    env(&r)
        .validate_answer(&hybrid, &r.prepared.requests().requests()[2], &r.answers[2])
        .unwrap();
}

fn stop(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "p=evaluate(Walk.join,e=@v/e,f=@v/next)",
        "take=evaluate(Walk.keep_node,x=$p.value.target)",
        "later=evaluate(Walk.seed)",
    ];
    let normal = evaluate_observed_bytes(
        fixture::composed(false, "r1"),
        &asks,
        &mut named_call_quiet(),
    )
    .unwrap();
    assert_eq!(normal.status(), "complete");
    let Signature::View { params, .. } =
        &normal.prepared.inputs().law().declarations["Walk.keep_node"].signature
    else {
        panic!()
    };
    let span = params[0].span;
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
    let armed = Rc::new(Cell::new(false));
    let phase = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let mut control = Control::new(limits, move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(fixture::composed(false, "r1"), &asks, &mut control).unwrap();
    let mut copy = control.clone();
    let stopped = evaluate_observed_with_validator(
        prepared,
        &mut control,
        |environment, graph, request, answer| {
            environment.validate_answer(graph, request, answer)?;
            if request.id == "p" {
                let (a, ph, s) = (armed.clone(), phase.clone(), seen.clone());
                data::observe_iterations(move |at, context, operation, _| {
                    if at == span
                        && context.request == 3
                        && operation == "answer_projection_check_step"
                        && (!recheck || ph.get())
                    {
                        assert_eq!(s.get(), 0);
                        s.set(1);
                        a.set(true);
                    }
                });
            }
            if recheck && request.id == "take" {
                let fresh = Environment::with_requests(
                    normal.prepared.inputs(),
                    normal.prepared.requests().requests(),
                    &mut copy,
                )?;
                phase.set(true);
                let result = fresh.validate_answer(graph, request, answer);
                phase.set(false);
                result?;
            }
            Ok(())
        },
    )
    .unwrap();
    data::clear_iteration_observer();
    assert_eq!(seen.get(), 1);
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(Some(probes.get()), frozen.get());
    assert_eq!(
        format!("{:?}", stopped.nodes),
        format!("{:?}", &normal.nodes[..stopped.nodes.len()])
    );
    assert_eq!(stopped.contexts, normal.contexts[..stopped.contexts.len()]);
    assert_eq!(&stopped.answers[..3], &normal.answers[..3]);
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    assert!(stopped.answers[1].claim.is_some() && !stopped.answers[1].evidence.is_empty());
    for index in 3..5 {
        if recheck && index == 3 {
            assert_eq!(stopped.answers[index].status, normal.answers[index].status);
            assert_eq!(
                stopped.answers[index].outputs,
                normal.answers[index].outputs
            );
            assert_eq!(stopped.answers[index].claim, normal.answers[index].claim);
            assert_eq!(
                stopped.answers[index].evidence,
                normal.answers[index].evidence
            );
        } else {
            assert_eq!(stopped.answers[index].status, Decision::Undetermined);
            assert!(stopped.answers[index].outputs.is_empty());
        }
        let reason = stopped.answers[index]
            .reasons
            .iter()
            .find(|reason| matches!(&reason.kind, ReasonKind::Stop(actual) if actual == &expected))
            .unwrap();
        assert_eq!(reason.request, stopped.answers[index].id);
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!()
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    assert_eq!(control.checkpoint(Checkpoint::Expression), Err(expected));
    assert_eq!(Some(probes.get()), frozen.get());
}
#[test]
fn path_answer_projection_actual_walk_stop_keeps_verified_prefix_and_independent_answers() {
    stop(false)
}
#[test]
fn path_answer_projection_fresh_recheck_stop_preserves_verified_current_and_freezes() {
    stop(true)
}
