#[test]
fn internal_answer_finish_uses_live_outcome_and_rejects_wrong_correspondence() {
    for (law, ask) in [
        (
            "view current(s:Sample):Bool=true;",
            "current=evaluate(Calc.current,s=@v/sample)",
        ),
        (
            "law required current(s:Sample):true;",
            "current=check(Calc.current,s=@v/sample)",
        ),
    ] {
        let control = quiet();
        let prepared = prepare_observed(affine_private_fixture(law), &[ask], &control).unwrap();
        let environment = Environment::with_prepared(&prepared, &control).unwrap();
        let request = &prepared.requests().requests()[0];
        let declaration = &prepared.inputs().law().declarations()["Calc.current"];
        let (params, body, role) = match &declaration.signature {
            Signature::View { params, body, .. } => (params, body, None),
            Signature::Law {
                params, body, role, ..
            } => (params, body, Some(*role)),
            _ => unreachable!(),
        };
        let mut graph = Graph::new(&control);
        graph.requests = prepared.requests().requests().to_vec();
        let mut evaluator = Evaluator {
            environment: &environment,
            graph: &mut graph,
            control: &control,
            request,
            declaration,
            bindings: vec![],
            lexical: BTreeMap::new(),
            formal: BTreeMap::new(),
            base: Scope::default(),
            retained_scope: Scope::default(),
            reasons: vec![],
            completed: BTreeMap::new(),
            answer_evaluation: None,
            verified_observed: None,
            completing: false,
            finite_universal: None,
            sources: BTreeMap::new(),
        };
        evaluator.base.readings.insert(declaration.reading.clone());
        let answer = evaluator.answer(params, None, *body, role).unwrap();
        assert!(evaluator.finish_internal_answer(&answer).unwrap());
        let mut wrong = answer.clone();
        wrong.id = "other".into();
        assert!(evaluator.finish_internal_answer(&wrong).is_err());
        wrong = answer.clone();
        wrong
            .outputs
            .insert("evaluation".into(), evaluator.bindings[0].value);
        assert!(evaluator.finish_internal_answer(&wrong).is_err());
        if answer.claim.is_some() {
            wrong = answer.clone();
            wrong.claim = answer.outputs.get("evaluation").copied();
            assert!(evaluator.finish_internal_answer(&wrong).is_err());
            wrong = answer.clone();
            wrong
                .outputs
                .insert("proposition".into(), evaluator.bindings[0].value);
            assert!(evaluator.finish_internal_answer(&wrong).is_err());
        }
        evaluator.graph.requests[0].id = "forged".into();
        assert!(evaluator.finish_internal_answer(&answer).is_err());
        evaluator.graph.requests[0] = request.clone();
        let Some(Scalar::Subject { subject, .. }) =
            evaluator.graph.nodes[evaluator.bindings[0].value.0].scalar_payload_mut()
        else {
            unreachable!()
        };
        *subject = "other".into();
        assert!(evaluator.finish_internal_answer(&answer).is_err());
    }
}

#[test]
fn internal_answer_delivery_and_cold_reference_keep_public_results() {
    use std::{cell::Cell, rc::Rc};
    for law in [
        "view current():Bool=true and not false;",
        "view current():Bool=forall n in list<Z>[1,2,3].n=n;",
        "law required current():true and not false;",
    ] {
        let request = if law.starts_with("law") {
            "current=check(Calc.current)"
        } else {
            "current=evaluate(Calc.current)"
        };
        let prepared = prepare_observed(affine_private_fixture(law), &[request], &quiet()).unwrap();
        let count = Rc::new(Cell::new((0, 0)));
        let seen = count.clone();
        data::observe_iterations(move |_, _, phase, _| {
            let (finished, raw) = seen.get();
            match phase {
                "internal_answer_finish" => seen.set((finished + 1, raw)),
                "answer_raw_fallback" => seen.set((finished, raw + 1)),
                _ => (),
            }
        });
        let actual = evaluate_observed(prepared, &quiet()).unwrap();
        data::clear_iteration_observer();
        assert_eq!(actual.status(), "complete", "{:?}", actual.issues);
        assert!(count.get().0 > 0, "{law}");
        assert_eq!(
            count.get().1,
            0,
            "normal internal completion must not raw-replay: {law}"
        );
        let prepared = prepare_observed(affine_private_fixture(law), &[request], &quiet()).unwrap();
        let reference = evaluate_observed_with_validator(prepared, &quiet(), |env, g, r, a| {
            env.validate_answer(g, r, a)
        })
        .unwrap();
        assert_eq!(actual.result_wire(), reference.result_wire());
        rebuild_for_origin_and_support_recheck(&actual, &actual.nodes).unwrap();
    }
}
