use super::*;
use archsig_common::control::quiet;
use archsig_input::input::InputSources;

fn example(collection: bool) -> super::super::ObservedEvaluation {
    let quantifier = if collection {
        "x in list<Bool>[false,true]"
    } else {
        "x:Bool"
    };
    let law = include_str!("../../../../../tests/fixtures/counter.law").replace(
        "view amount(s: State): Z = s.count;",
        &format!("view amount(s:State):Bool = s.count>=0 and (forall {quantifier} . x=x);"),
    );
    let result = super::super::evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![include_bytes!("../../../../../tests/fixtures/counter.atoms.json").to_vec()],
            law.into_bytes(),
            include_bytes!("../../../../../tests/fixtures/counter.archmap.json").to_vec(),
        ),
        &["all=evaluate(CountCheck.amount,s=@v/s)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert!(!result.iterations.is_empty());
    result
}

fn graph(result: &super::super::ObservedEvaluation, control: &Control) -> Graph {
    let mut graph = Graph::new(control);
    graph.nodes = result.nodes.clone().into();
    graph.contexts = result.contexts.clone();
    graph.requests = result.prepared.requests().requests().to_vec();
    graph.checked_answers = result.answers.iter().cloned().enumerate().collect();
    graph.frames = result.frames.clone();
    graph.iterations = result.iterations.clone();
    graph.instances = result.instances.clone();
    graph.cases = result.cases.clone();
    graph.universal_witnesses = result.universal_witnesses.clone();
    graph
}

fn input(
    env: &Environment<'_>,
    graph: &Graph,
    cutoff: usize,
) -> Result<IterationInputs, ValidationFailure> {
    let _cutoff = env.state.cutoff.scoped(cutoff);
    let _context = env.state.context.scoped(Some(graph.iterations[0].caller));
    env.iteration_input(graph, 0)
}

fn typed_entries(env: &Environment<'_>) -> usize {
    env.results
        .cache
        .borrow()
        .iterations
        .keys()
        .filter(|key| matches!(key, IterationKey::Typed { .. }))
        .count()
}

fn same(left: &IterationInputs, right: &IterationInputs) {
    assert_eq!(left.0, right.0);
    assert_eq!(left.1, right.1);
    assert_eq!(left.2.scope, right.2.scope);
    assert_eq!(left.2.support, right.2.support);
}

#[test]
fn typed_iteration_reuses_success_across_cutoffs_and_still_rejects_future_producers() {
    let result = example(false);
    let control = quiet();
    let g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.validation_graph_session(&g, || {
        let first = input(&env, &g, g.iterations[0].domain.0 + 1)?;
        assert_eq!(typed_entries(&env), 1);
        let later = input(&env, &g, g.nodes.len())?;
        same(&first, &later);
        assert_eq!(typed_entries(&env), 1);
        assert_eq!(env.results.cache.borrow().iterations.len(), 1);
        for cutoff in [g.iterations[0].source.0, g.iterations[0].domain.0] {
            assert!(
                input(&env, &g, cutoff).is_err(),
                "future producer at cutoff {cutoff}"
            );
        }
        same(&first, &input(&env, &g, g.nodes.len())?);
        Ok(())
    })
    .unwrap();
    env.results.clear_validation();
    assert!(env.results.cache.borrow().iterations.is_empty());
    assert!(env.results.cache.borrow().checked.is_empty());
}

#[test]
fn typed_iteration_does_not_promote_dynamic_or_graphless_success_and_restores_after_collectors() {
    let result = example(false);
    let control = quiet();
    let g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.state
        .validation_session(&env.results, || {
            input(&env, &g, g.nodes.len())?;
            assert_eq!(typed_entries(&env), 0);
            Ok::<_, ValidationFailure>(())
        })
        .unwrap();
    assert!(env.results.cache.borrow().iterations.is_empty());
    env.validation_graph_session(&g, || {
        let reads = env.state.primitive_reads.scoped(Some(BTreeSet::new()));
        let ordinary = input(&env, &g, g.nodes.len())?;
        assert_eq!(typed_entries(&env), 0);
        reads.restore();
        // 同じcutoffの通常entryがあっても、限定成功を自分で確立して保存する。
        same(&ordinary, &input(&env, &g, g.nodes.len())?);
        assert_eq!(typed_entries(&env), 1);
        let missing = env.state.missing_slot_reads.scoped(Some(BTreeSet::new()));
        same(&ordinary, &input(&env, &g, g.iterations[0].domain.0 + 1)?);
        assert_eq!(typed_entries(&env), 1);
        assert!(
            env.results
                .cache
                .borrow()
                .iterations
                .contains_key(&IterationKey::Cutoff(0, g.iterations[0].domain.0 + 1))
        );
        missing.restore();
        same(&ordinary, &input(&env, &g, g.nodes.len())?);
        Ok(())
    })
    .unwrap();
    assert!(env.state.validation_graph.get().is_none());
}

#[test]
fn typed_iteration_nested_other_graph_cannot_read_the_enclosing_graph_success() {
    let result = example(false);
    let control = quiet();
    let g = graph(&result, &control);
    let mut other = graph(&result, &control);
    other.iterations[0].member = super::super::call::Member::SetElement(Scalar::Z(9.into()));
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.validation_graph_session(&g, || {
        let expected = input(&env, &g, g.nodes.len())?;
        assert_eq!(typed_entries(&env), 1);
        assert!(
            env.validation_graph_session(&other, || input(&env, &other, other.nodes.len()))
                .is_err()
        );
        assert_eq!(typed_entries(&env), 1);
        same(&expected, &input(&env, &g, g.nodes.len())?);
        Ok(())
    })
    .unwrap();
    let cold = Environment::with_prepared(&result.prepared, &control).unwrap();
    assert!(
        cold.validation_graph_session(&other, || input(&cold, &other, other.nodes.len()))
            .is_err()
    );
}

#[test]
fn typed_iteration_epoch_rechecks_changed_source_domain_caller_member_and_restoration() {
    let result = example(false);
    let control = quiet();
    let mut g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let original = g.iterations[0].clone();
    let domain_node = g.nodes[original.domain.0].clone();
    for mutation in 0..6 {
        env.validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
            .unwrap();
        assert_eq!(typed_entries(&env), 1);
        match mutation {
            0 => g.iterations[0].source = original.domain,
            1 => g.iterations[0].domain = original.source,
            2 => g.iterations[0].caller.request = usize::MAX,
            3 => g.iterations[0].caller.iteration = Some(0),
            4 => {
                g.iterations[0].member = super::super::call::Member::SetElement(Scalar::Z(9.into()))
            }
            _ => g.nodes[original.domain.0].arguments[0] = original.domain,
        }
        let cold = Environment::with_prepared(&result.prepared, &control).unwrap();
        assert!(
            cold.validation_graph_session(&g, || input(&cold, &g, g.nodes.len()))
                .is_err(),
            "cold mutation {mutation}"
        );
        assert!(
            env.validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
                .is_err(),
            "warm mutation {mutation}"
        );
        assert!(env.results.cache.borrow().iterations.is_empty());
        g.iterations[0] = original.clone();
        g.nodes[original.domain.0] = domain_node.clone();
        env.validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
            .unwrap();
        assert_eq!(typed_entries(&env), 1);
    }
}

#[test]
fn typed_iteration_collection_keeps_cutoff_keys() {
    let result = example(true);
    let control = quiet();
    let g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.validation_graph_session(&g, || {
        let record = &g.iterations[0];
        // In now authenticates the actual normalized producer, member and finite
        // Domain, all of which follow the collection Evaluation.
        let required = [
            record.source,
            record.domain,
            record.finite.unwrap(),
            record.producer.unwrap(),
        ]
        .into_iter()
        .map(|r| r.0)
        .max()
        .unwrap();
        let first = input(&env, &g, g.nodes.len())?;
        same(&first, &input(&env, &g, required + 1)?);
        for cutoff in [record.domain.0 + 1, required] {
            assert!(
                input(&env, &g, cutoff).is_err(),
                "future actual In producer at cutoff {cutoff}"
            );
        }
        same(&first, &input(&env, &g, g.nodes.len())?);
        assert_eq!(typed_entries(&env), 0);
        assert!(
            env.results
                .cache
                .borrow()
                .iterations
                .keys()
                .all(|key| matches!(key, IterationKey::Cutoff(..)))
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn typed_iteration_universal_completion_and_capture_switch_to_cutoff_entries() {
    let result = example(false);
    let control = quiet();
    let g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.validation_graph_session(&g, || {
        let expected = input(&env, &g, g.nodes.len())?;
        let record = &g.iterations[0];
        let span = env.expression_span(&g, record.source)?;
        let expression = env.indexes.inputs.law().program().expressions[&span];
        let context = universal::AnalysisContext {
            plan: universal::UniversalPlan {
                template_span: span,
                body: expression,
                guard: None,
                parameters: vec![],
                family: false,
            },
            template: Some(record.source),
            domains: vec![],
            completions: vec![],
            local_axes: vec![],
            calls: vec![],
            iterations: vec![],
        };
        let universal = env.state.universal_context.scoped(Some(context));
        let cutoff = record.domain.0 + 1;
        same(&expected, &input(&env, &g, cutoff)?);
        assert!(
            env.results
                .cache
                .borrow()
                .iterations
                .contains_key(&IterationKey::Cutoff(0, cutoff))
        );
        universal.restore();
        let completion = env.state.completion_values.scoped(vec![(
            Fact::from(archsig_input::archmap::FactData {
                snapshot: "v".into(),
                subject: "s".into(),
                field: Some("Counter.State.count".into()),
                atom: None,
            }),
            NodeRef(g.nodes.iter().position(|node| matches!(&node.payload, Some(Payload::Scalar(Scalar::Z(value))) if *value == 2.into())).expect("元countの値")),
            Scalar::Z(2.into()),
        )]);
        same(&expected, &input(&env, &g, g.nodes.len())?);
        assert!(
            env.results
                .cache
                .borrow()
                .iterations
                .contains_key(&IterationKey::Cutoff(0, g.nodes.len()))
        );
        completion.restore();
        let capture =
            env.state
                .evaluation_capture
                .scoped(Some(quotient_evaluation::EvaluationCapture {
                    selected: vec![expression],
                    nodes: vec![],
                    roots: vec![],
                    stack: vec![],
                }));
        let cutoff = record.domain.0 + 2;
        assert!(cutoff < g.nodes.len());
        same(&expected, &input(&env, &g, cutoff)?);
        assert!(
            env.results
                .cache
                .borrow()
                .iterations
                .contains_key(&IterationKey::Cutoff(0, cutoff))
        );
        capture.restore();
        same(&expected, &input(&env, &g, g.nodes.len())?);
        assert_eq!(typed_entries(&env), 1);
        Ok(())
    })
    .unwrap();
}

#[test]
fn changing_an_owned_iteration_result_keeps_other_callers_and_memo_unchanged() {
    for collection in [false, true] {
        let result = example(collection);
        let control = quiet();
        let g = graph(&result, &control);
        let env = Environment::with_prepared(&result.prepared, &control).unwrap();
        env.validation_graph_session(&g, || {
            let original = input(&env, &g, g.nodes.len())?;
            let graph_support: Vec<_> = g.nodes.iter().map(|node| node.support.clone()).collect();
            let mut edited = input(&env, &g, g.nodes.len())?;
            let owned = std::rc::Rc::make_mut(&mut edited);
            owned.2.scope.readings.insert("caller-local".into());
            owned.2.support.materialize_mut_for_test().push(Fact::from(
                archsig_input::archmap::FactData {
                    snapshot: "caller-local".into(),
                    subject: "caller-local".into(),
                    field: None,
                    atom: None,
                },
            ));
            assert_ne!(owned.2.support, original.2.support);
            owned.2.support.materialize_mut_for_test().clear();
            owned.1 = Scalar::Bool(true);
            assert!(!original.2.scope.readings.contains("caller-local"));
            assert_eq!(
                g.nodes
                    .iter()
                    .map(|node| node.support.clone())
                    .collect::<Vec<_>>(),
                graph_support
            );
            let warm = input(&env, &g, g.nodes.len())?;
            same(&original, &warm);
            env.results.clear_validation();
            let cold = input(&env, &g, g.nodes.len())?;
            same(&original, &cold);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn ordinary_sibling_append_keeps_success_and_registry_dependency_stays_sticky() {
    let result = example(false);
    let control = quiet();
    let mut g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let first = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    assert!(!env.results.cache.borrow().registry_read);
    let duplicate_iteration = g.iterations[0].clone();
    g.iterations.push(duplicate_iteration);
    let warm = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    same(&first, &warm);
    assert!(std::rc::Rc::ptr_eq(&first, &warm));
    env.results.clear_validation();
    let cold = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    same(&first, &cold);

    // 明示的なregistry依存のあるepochを作り、安全な延長でも事実を戻さない。
    env.results.cache.borrow_mut().registry_read = true;
    let old = g.nodes.len();
    let fresh = g.push(g.nodes[0].clone()).unwrap();
    assert_eq!(fresh.0, old);
    env.validation_graph_session(&g, || Ok(())).unwrap();
    assert!(env.results.cache.borrow().registry_read);
    let saved = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    let duplicate_iteration = g.iterations[0].clone();
    g.iterations.push(duplicate_iteration);
    let after = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    same(&saved, &after);
    assert!(!std::rc::Rc::ptr_eq(&saved, &after));
    assert!(!env.results.cache.borrow().registry_read);
}

#[test]
fn changed_context_rejects_warm_result_and_restored_context_rechecks_like_cold() {
    let result = example(false);
    let control = quiet();
    let mut g = graph(&result, &control);
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    let expected = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    let source = g.iterations[0].source.0;
    let original = g.contexts[source];
    g.contexts[source].request += 1;
    assert!(
        env.validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
            .is_err()
    );
    g.contexts[source] = original;
    let restored = env
        .validation_graph_session(&g, || input(&env, &g, g.nodes.len()))
        .unwrap();
    same(&expected, &restored);
    let cold = Environment::with_prepared(&result.prepared, &control).unwrap();
    let checked = cold
        .validation_graph_session(&g, || input(&cold, &g, g.nodes.len()))
        .unwrap();
    same(&restored, &checked);
}

#[test]
fn published_local_source_keeps_registry_dependency_and_rejects_duplicate_publication() {
    let law = include_str!("../../../../../tests/fixtures/counter.law").replace(
        "view amount(s: State): Z = s.count;",
        "view amount(s:State):Bool = forall x:Bool . x=x;",
    );
    let result = super::super::evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![include_bytes!("../../../../../tests/fixtures/counter.atoms.json").to_vec()],
            law.into_bytes(),
            include_bytes!("../../../../../tests/fixtures/counter.archmap.json").to_vec(),
        ),
        &[
            "a=evaluate(CountCheck.amount,s=@v/s)",
            "b=build(CountCheck,on=@v/s)",
            "l=localize($b.object)",
        ],
        &quiet(),
    )
    .unwrap();
    assert!(!result.iterations.is_empty());
    let control = quiet();
    let mut g = graph(&result, &control);
    let (index, answer) = g.checked_answers.pop().unwrap();
    assert_eq!(index, 2);
    let request = &result.prepared.requests().requests()[index];
    g.active = result.contexts[answer.outputs["system"].0];
    let env = Environment::with_prepared(&result.prepared, &control).unwrap();
    env.validate_answer(&g, request, &answer).unwrap();
    let source = super::super::local_result::published_source(&g, request, &answer).unwrap();
    env.results.cache.borrow_mut().registry_read = true;
    g.checked_answers.push((index, answer.clone()));
    env.keep_published_local_source(&g, index, request, &answer);
    assert!(env.results.source_checked(&source));
    assert!(env.results.cache.borrow().registry_read);
    assert!(
        env.results
            .validation_snapshot
            .borrow()
            .as_ref()
            .unwrap()
            .matches(&g, &control)
            .unwrap()
    );
    let duplicate = g.iterations[0].clone();
    g.iterations.push(duplicate);
    env.validation_graph_session(&g, || Ok(())).unwrap();
    assert!(
        !env.results.source_checked(&source),
        "an old producer registry addition invalidates the source"
    );

    // 登録済みindexの再追加を、新しい検証結果の公開として扱わない。
    g.iterations.pop();
    env.validate_answer(&g, request, &answer).unwrap();
    assert!(env.results.source_checked(&source));
    g.checked_answers.push((index, answer.clone()));
    env.keep_published_local_source(&g, index, request, &answer);
    assert!(!env.results.source_checked(&source));
    assert!(env.results.validation_snapshot.borrow().is_none());
}
