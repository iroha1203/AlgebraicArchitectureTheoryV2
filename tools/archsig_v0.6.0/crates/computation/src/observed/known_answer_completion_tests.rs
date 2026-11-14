fn assert_known_answer_raw(result: &ObservedEvaluation) {
    let graph = rebuild_for_origin_and_support_recheck(result, &result.nodes).unwrap();
    let control = quiet();
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    for (request, answer) in result
        .prepared
        .requests()
        .requests()
        .iter()
        .zip(&result.answers)
    {
        environment
            .validate_answer(&graph, request, answer)
            .unwrap();
    }
}

#[test]
fn known_answers_keep_original_scope_missing_applicability_and_typed_values_without_extra_completions()
 {
    for (body, kind, status, applicability) in [
        (
            "view current(s:Sample):Unit=if s.o=none<Bool> then unit else unit;",
            "evaluate",
            Decision::Established,
            "applicable",
        ),
        (
            "law required current(s:Sample):false and s.o=none<Bool>;",
            "check",
            Decision::Refuted,
            "applicable",
        ),
        (
            "law required current(s:Sample) when false:s.o=none<Bool>;",
            "check",
            Decision::Established,
            "not_applicable",
        ),
        (
            "law required current(s:Sample) when s.o=none<Bool>:true;",
            "check",
            Decision::Established,
            "undetermined",
        ),
        (
            "view current(s:Sample):Term<(Z)->Z>=let unused=s.o in fn(x:Z)=>x;",
            "evaluate",
            Decision::Established,
            "applicable",
        ),
    ] {
        let body = body.replace(">=", "> =");
        let ask = format!("current={kind}(Calc.current,s=@v/sample)");
        let result = evaluate_observed_bytes(
            finite_completion_fixture(&body, false),
            &[&ask, "plan=needed($current)"],
            &quiet(),
        )
        .unwrap();
        assert_eq!(
            result.answers[0].status, status,
            "{body}: {:?}",
            result.issues
        );
        assert!(
            result.cases.is_empty(),
            "a checked determinate Answer needs no second whole derivation"
        );
        assert!(
            !result
                .nodes
                .iter()
                .any(|node| matches!(node.payload, Some(Payload::CompletionSeed { .. })))
        );
        let answer = &result.answers[0];
        let root = answer.outputs["evaluation"];
        let node = &result.nodes[root.0];
        assert_eq!(answer.scope, node.scope);
        assert!(answer.scope.completions);
        let Some(Payload::Evaluation {
            applicability: actual,
            value: Some(value),
            ..
        }) = &node.payload
        else {
            panic!("determinate original Evaluation")
        };
        assert_eq!(*actual, applicability);
        assert!(answer.reasons.iter().any(|r| {
            r.missing
                .iter()
                .any(|f| f.field.as_deref() == Some("ClosedValue.Sample.o"))
        }));
        if status == Decision::Refuted {
            assert!(answer.claim.is_some());
            assert!(answer.evidence.iter().any(|r| matches!(
                result.nodes[r.0].payload,
                Some(Payload::Counterexample { .. })
            )));
        } else if body.contains("Unit") {
            assert_eq!(data_scalar_at(&result, value.0), &Scalar::Unit);
        } else if body.contains("Term<") {
            let Scalar::Term(term) = data_scalar_at(&result, value.0) else {
                panic!("typed function value")
            };
            assert_eq!(
                term.apply(
                    &[Scalar::Z(7.into())],
                    result.prepared.inputs().law(),
                    &quiet()
                )
                .unwrap(),
                Scalar::Z(7.into())
            );
        } else {
            assert_eq!(data_scalar_at(&result, value.0), &Scalar::Bool(true));
        }
        let plan = result.answers[1].outputs["plan"];
        assert!(
            matches!(&result.nodes[plan.0].payload,Some(Payload::ObservationPlan{requirements,blockers,..})if requirements.is_empty()&&blockers.is_empty())
        );
        assert_known_answer_raw(&result);
        recheck_mutation(&result, |nodes| nodes[root.0].scope.completions = false);
    }
}

#[test]
fn known_family_and_pending_implication_keep_whole_claim_and_original_missing() {
    let family = finite_family_example(
        "law required ensured(s:Sample) when s.p:true;",
        &["all=check(Calc.ensured)"],
        true,
    );
    assert_eq!(family.answers[0].status, Decision::Established);
    assert!(family.answers[0].claim.is_some());
    assert!(family.cases.is_empty());
    assert!(
        family.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert!(family.answers[0].evidence.iter().any(|r| matches!(
        family.nodes[r.0].payload,
        Some(Payload::FiniteExhaustion { .. })
    )));
    assert_known_answer_raw(&family);
    let pending = evaluate_observed_bytes(
        partial_call_fixture::missing_reference_input(),
        &["implication=check(Reservations.pcSkipImpliesLaw,a=@v/B,e=@v/e)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(
        pending.answers[0].status,
        Decision::Established,
        "{:?}",
        pending.issues
    );
    assert!(pending.cases.is_empty());
    assert!(
        pending.answers[0]
            .reasons
            .iter()
            .any(|r| matches!(r.kind, ReasonKind::Missing))
    );
    assert_known_answer_raw(&pending);
}

#[test]
fn unknown_correlated_answers_still_require_complete_assignments_and_needed_reasons() {
    for (body, known) in [
        ("view current(s:Sample):Bool=s.o=s.o;", true),
        ("view current(s:Sample):Option<Bool>=s.o;", false),
    ] {
        let body = body.replace(">=", "> =");
        let result = evaluate_observed_bytes(
            finite_completion_fixture(&body, false),
            &[
                "current=evaluate(Calc.current,s=@v/sample)",
                "plan=needed($current)",
            ],
            &quiet(),
        )
        .unwrap();
        assert_eq!(result.cases.len(), 3);
        let answer = &result.answers[0];
        assert_eq!(
            answer.status,
            if known {
                Decision::Established
            } else {
                Decision::Undetermined
            }
        );
        if known {
            assert_eq!(
                data_scalar_at(&result, answer.outputs["value"].0),
                &Scalar::Bool(true)
            );
            assert!(answer.evidence.iter().any(|r|matches!(&result.nodes[r.0].payload,Some(Payload::FiniteExhaustion{checked:3,instances,..})if instances.len()==3)));
        } else {
            assert!(!answer.outputs.contains_key("value"));
            assert!(answer.evidence.iter().any(|r| matches!(
                result.nodes[r.0].payload,
                Some(Payload::CompletionPair { .. })
            )));
        }
        let plan = result.answers[1].outputs["plan"];
        assert!(
            matches!(&result.nodes[plan.0].payload,Some(Payload::ObservationPlan{requirements,..})if requirements.len()==usize::from(!known))
        );
        assert_known_answer_raw(&result);
    }
}

#[test]
fn known_answer_post_validation_stop_keeps_checked_counterexample_and_missing() {
    use std::sync::{
        Arc,
        atomic::{AtomicI32, Ordering},
    };
    for signal in [Signal::Int, Signal::Term] {
        let flag = Arc::new(AtomicI32::new(0));
        let control = Control::from_signal_flag(flag.clone(), 1, 2);
        let input = finite_completion_fixture(
            "view seed():Unit=unit; law required current(s:Sample):false and s.o=none<Bool>;",
            false,
        );
        let asks = [
            "current=check(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.seed)",
        ];
        let prepared = prepare_observed(input, &asks, &control).unwrap();
        let stopped =
            evaluate_observed_with_validator(prepared, &control, |env, graph, request, answer| {
                env.validate_answer(graph, request, answer)?;
                if request.id == "current" {
                    flag.store(if signal == Signal::Int { 1 } else { 2 }, Ordering::Relaxed);
                    return Err(ValidationFailure::Stop(signal));
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(stopped.answers[0].status, Decision::Refuted);
        assert!(stopped.answers[0].evidence.iter().any(|r| matches!(
            stopped.nodes[r.0].payload,
            Some(Payload::Counterexample { .. })
        )));
        assert!(stopped.answers[0].reasons.iter().any(|r| {
            r.missing
                .iter()
                .any(|f| f.field.as_deref() == Some("ClosedValue.Sample.o"))
        }));
        assert!(
            stopped.answers[0]
                .reasons
                .iter()
                .any(|r| matches!(r.kind,ReasonKind::Stop(actual) if actual==signal))
        );
        assert_eq!(stopped.answers[1].status, Decision::Undetermined);
        assert!(stopped.answers[1].outputs.is_empty());
        rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
    }
}
