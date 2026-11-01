mod affine_term_fixture {
    include!("../../tests/common/affine_terms.rs");
}
fn affine_term_inputs(revision: &str) -> InputSources {
    let defs = affine_term_fixture::definitions();
    let d = crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        affine_term_fixture::law(digest).into_bytes(),
        affine_term_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn affine_term_result(asks: &[&str]) -> ObservedEvaluation {
    let r =
        evaluate_observed_bytes(affine_term_inputs("r1"), asks, &mut named_call_quiet()).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
#[test]
fn affine_term_application_rechecks_normalization_and_typed_algorithm_obligations() {
    let r = affine_term_result(&[
        "i=evaluate(Terms.cancelEquality,s=@v/s)",
        "o=evaluate(Terms.opaque)",
        "m=evaluate(Terms.opaqueMissing,s=@v/s)",
        "t=evaluate(Terms.tupleOutside,s=@v/s)",
    ]);
    // 対応しない項の算法は値を出さず、型付きの未対応理由を残す。
    for index in [1, 2, 3] {
        let target = r.answers[index].outputs["evaluation"].0;
        assert!(
            r.nodes[target]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::UnsupportedAlgorithm { .. }))
        );
    }
    // 正規化証拠の再検査の代表: stepを落とすと核が拒否する。
    let target = r
        .nodes
        .iter()
        .position(|n| matches!(n.payload, Some(Payload::Normalization { .. })))
        .unwrap();
    rejects_mutated_prefix(&r, target, |ns| {
        let Some(Payload::Normalization { steps, .. }) = &mut ns[target].payload else {
            panic!("normalization")
        };
        assert!(!steps.is_empty());
        steps.pop();
    });
}
fn affine_term_stop_in_batch(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let current = if recheck {
        "current=evaluate(Terms.partial,s=@v/s)"
    } else {
        "current=evaluate(Terms.mixed)"
    };
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        current,
        "later=evaluate(Terms.seed)",
    ];
    let normal = affine_term_result(&asks);
    let expected = StopReason::Cancelled(crate::result::Signal::Term);
    let armed = Rc::new(Cell::new(false));
    let in_recheck = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, phase, s, p, f) = (
        armed.clone(),
        in_recheck.clone(),
        seen.clone(),
        probes.clone(),
        frozen.clone(),
    );
    let mut c = Control::new(move |checkpoint| {
        p.set(p.get() + 1);
        let stop = if recheck {
            if phase.get() && checkpoint == Checkpoint::Expression {
                assert!(!s.replace(true));
                true
            } else {
                false
            }
        } else {
            a.replace(false)
        };
        if stop {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(affine_term_inputs("r1"), &asks, &mut c).unwrap();
    let mut recheck_control = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" && !recheck {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                if ctx.request == 2 && operation == "term_affine_case" && index == 1 {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        if request.id == "current" && recheck {
            let fresh = Environment::new(normal.prepared.inputs(), &mut recheck_control)?;
            in_recheck.set(true);
            let checked = fresh.validate_answer(g, request, answer);
            in_recheck.set(false);
            checked?;
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected.clone()));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for (index, answer) in stopped.answers.iter().enumerate().skip(2) {
        assert!(answer.claim.is_none() && answer.evidence.is_empty());
        if recheck && index == 2 {
            // 元missingを伴う確定値はcomplete_answerで既に独立検査・保存されている。
            assert_eq!(answer.status, Decision::Established);
            assert_eq!(answer.outputs, normal.answers[index].outputs);
            assert!(!normal.answers[index].reasons.is_empty());
            for original in &normal.answers[index].reasons {
                assert!(answer.reasons.iter().any(|r| r.wire() == original.wire()));
            }
        } else {
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(answer.outputs.is_empty())
        }
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.wire())
        else {
            panic!("details")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
#[test]
fn affine_term_actual_case_stop_preserves_prior_value_refutation_and_verified_prefix() {
    affine_term_stop_in_batch(false)
}
#[test]
fn affine_term_integer_point_rechecks_retained_forms_and_original_reapplication() {
    let r = affine_term_result(&["d=check(Terms.unequal,s=@v/s)"]);
    // 反証点の再検査の代表: 点の左右の値を揃えると核が拒否する。
    let target = r
        .nodes
        .iter()
        .position(|n| matches!(&n.payload, Some(Payload::TermComparison { certificate, .. }) if certificate.point.is_some()))
        .unwrap();
    rejects_mutated_prefix(&r, target, |ns| {
        let Some(Payload::TermComparison { certificate, .. }) = &mut ns[target].payload else {
            panic!("certificate")
        };
        let point = certificate.point.as_mut().unwrap();
        point.right = point.left.clone();
    });
}
#[test]
fn affine_tuple_binding_rechecks_unknown_actual_producers_and_cached_source_components() {
    // 同じview本体を、一つの問いのh/qとk/qという異なる成分で再分析する。
    let r = affine_term_result(&["c=evaluate(Terms.tupleCache,s=@v/s)"]);
    assert_eq!(r.status(), "complete");
    assert!(matches!(
        r.nodes[r.answers[0].outputs["value"].0].payload,
        Some(Payload::Scalar(Scalar::Bool(true)))
    ));
}

#[test]
fn affine_term_standard_evidence_rechecks_typed_matrix_point_nodes_and_foreign_producers() {
    let r = affine_term_result(&[
        "a=evaluate(Terms.same,s=@v/s)",
        "b=evaluate(Terms.same,s=@v/s)",
        "q=evaluate(Terms.qCoefficient)",
    ]);
    // 証拠の算術の再検査の代表: 反例の点の値を書き換えると核が拒否する。
    let left = r
        .nodes
        .iter()
        .find_map(|n| match &n.payload {
            Some(Payload::TermCounterexample { left, .. }) => Some(*left),
            _ => None,
        })
        .unwrap();
    rejects_mutated_prefix(&r, left.0, |ns| {
        let Some(Payload::Scalar(value)) = &mut ns[left.0].payload else {
            panic!("point")
        };
        *value = super::super::numeric::literal("17", &value.ty(), &named_call_quiet()).unwrap();
    });
}
