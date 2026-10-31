mod equality_fixture {
    include!("../../tests/common/term_equality.rs");
}
fn equality_inputs(revision: &str) -> InputSources {
    let defs = equality_fixture::definitions();
    let checked =
        crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        equality_fixture::law(digest).into_bytes(),
        equality_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn equality_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(equality_inputs("r1"), asks, &mut named_call_quiet()).unwrap();
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
#[test]
fn finite_term_equality_visits_all_original_argument_products() {
    use std::{cell::RefCell, rc::Rc};
    let counts = Rc::new(RefCell::new(BTreeMap::<usize, Vec<usize>>::new()));
    let seen = counts.clone();
    data::observe_iterations(move |_, ctx, op, index| {
        if op == "term_extensional_case" {
            seen.borrow_mut()
                .entry(ctx.request)
                .or_default()
                .push(index);
        }
    });
    let r = equality_result(&[
        "s=evaluate(Terms.selfEq,s=@v/s)",
        "m=evaluate(Terms.multi)",
        "z=evaluate(Terms.zero)",
        "f=evaluate(Terms.fp)",
        "d=evaluate(Terms.finiteData)",
        "t=evaluate(Terms.tuple)",
    ]);
    data::clear_iteration_observer();
    assert_eq!(r.status(), "complete");
    for (request, n) in [2, 8, 1, 3, 3, 8].into_iter().enumerate() {
        assert_eq!(counts.borrow()[&request], (0..n).collect::<Vec<_>>());
    }
}
#[test]
fn finite_term_equality_does_not_evaluate_skipped_boolean_or_quantifier_comparisons() {
    use std::{cell::RefCell, rc::Rc};
    let counts = Rc::new(RefCell::new(BTreeMap::<usize, usize>::new()));
    let seen = counts.clone();
    data::observe_iterations(move |_, ctx, op, _| {
        if op == "term_extensional_case" {
            *seen.borrow_mut().entry(ctx.request).or_default() += 1;
        }
    });
    let r = equality_result(&[
        "a=evaluate(Terms.andSkip)",
        "o=evaluate(Terms.orSkip)",
        "i=evaluate(Terms.impliesSkip)",
        "l=evaluate(Terms.allSkip)",
        "e=evaluate(Terms.anySkip)",
        "n=evaluate(Terms.andNeeded)",
        "nl=evaluate(Terms.allNeeded)",
        "ne=evaluate(Terms.anyNeeded)",
    ]);
    data::clear_iteration_observer();
    assert_eq!(r.status(), "complete");
    for request in 0..5 {
        assert_eq!(counts.borrow().get(&request).copied().unwrap_or(0), 0);
    }
    for request in 5..8 {
        assert_eq!(counts.borrow()[&request], 1);
    }
}

fn equality_stop_in_batch(recheck: bool) {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        "current=evaluate(Terms.eq,s=@v/s)",
        "later=evaluate(Terms.seed)",
    ];
    let normal = equality_result(&asks);
    let (limits, usage, expected) = reservations_private_stop_usage(if recheck { 2 } else { 0 });
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
    let mut c = Control::new(limits, move |checkpoint| {
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
            usage
        } else {
            Default::default()
        }
    });
    let prepared = prepare_observed(equality_inputs("r1"), &asks, &mut c).unwrap();
    let mut recheck_control = c.clone();
    let stopped = evaluate_observed_with_validator(prepared, &mut c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" && !recheck {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                if ctx.request == 2 && operation == "term_extensional_case" && index == 1 {
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
            // 元入力の独立検査を終えた値と判断を、fresh再検査の停止後も保持する。
            assert_eq!(answer.status, normal.answers[index].status);
            assert_eq!(answer.outputs, normal.answers[index].outputs);
            assert_eq!(answer.claim, normal.answers[index].claim);
            assert_eq!(answer.evidence, normal.answers[index].evidence);
            assert_eq!(answer.scope, normal.answers[index].scope);
        } else {
            assert_eq!(answer.status, Decision::Undetermined);
            assert!(answer.outputs.is_empty());
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
fn finite_term_case_stop_preserves_prior_values_refutation_and_verified_prefix() {
    equality_stop_in_batch(false);
}
