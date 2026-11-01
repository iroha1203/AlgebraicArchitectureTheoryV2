mod equality_fixture {
    include!("../../tests/common/term_equality.rs");
}
fn equality_inputs(revision: &str) -> InputSources {
    let defs = equality_fixture::definitions();
    let checked =
        crate::definition::check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        equality_fixture::law(digest).into_bytes(),
        equality_fixture::archmap(digest, revision).into_bytes(),
    )
}
fn equality_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(equality_inputs("r1"), asks, &quiet()).unwrap();
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

#[test]
fn finite_term_case_stop_preserves_prior_values_refutation_and_verified_prefix() {
    use std::{cell::Cell, rc::Rc};
    let asks = [
        "seed=evaluate(Terms.seed)",
        "prior=check(Terms.prior)",
        "current=evaluate(Terms.eq,s=@v/s)",
        "later=evaluate(Terms.seed)",
    ];
    let normal = equality_result(&asks);
    let expected = crate::result::Signal::Term;
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (a, p, f) = (armed.clone(), probes.clone(), frozen.clone());
    let c = Control::new(move |_| {
        p.set(p.get() + 1);
        if a.replace(false) {
            assert!(f.replace(Some(p.get())).is_none());
            Some(crate::result::Signal::Term)
        } else {
            None
        }
    });
    let prepared = prepare_observed(equality_inputs("r1"), &asks, &c).unwrap();
    let stopped = evaluate_observed_with_validator(prepared, &c, |e, g, request, answer| {
        e.validate_answer(g, request, answer)?;
        if request.id == "prior" {
            let (a, s) = (armed.clone(), seen.clone());
            data::observe_iterations(move |_, ctx, operation, index| {
                if ctx.request == 2 && operation == "term_extensional_case" && index == 1 {
                    assert!(!s.replace(true));
                    a.set(true);
                }
            });
        }
        Ok(())
    });
    data::clear_iteration_observer();
    let stopped = stopped.unwrap();
    assert!(seen.get());
    assert_eq!(stopped.status(), "interrupted");
    assert_eq!(c.stop_reason(), Some(expected));
    assert_eq!(
        format!("{:?}", &stopped.answers[..2]),
        format!("{:?}", &normal.answers[..2])
    );
    assert_eq!(stopped.answers[0].status, Decision::Established);
    assert_eq!(stopped.answers[1].status, Decision::Refuted);
    for answer in stopped.answers.iter().skip(2) {
        assert!(answer.claim.is_none() && answer.evidence.is_empty());
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.outputs.is_empty());
        let reason = answer
            .reasons
            .iter()
            .find(|r| matches!(&r.kind,ReasonKind::Stop(s) if *s==expected))
            .unwrap();
        let (Json::Obj(ref actual), Json::Obj(ref wanted)) = (reason.wire(), expected.issue())
        else {
            panic!("details")
        };
        assert_eq!(actual["details"], wanted["details"]);
    }
    rebuild_for_origin_and_support_recheck(&stopped, &stopped.nodes).unwrap();
}
