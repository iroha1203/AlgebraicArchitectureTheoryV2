#[test]
fn ordinary_in_uses_static_source_actual_members_and_complete_coverage() {
    use std::{cell::Cell, rc::Rc};
    let sources =
        affine_private_fixture("view current():Bool=forall n in list<Z>[2,2,3,4,5,6].n=n;");
    let prepared =
        prepare_observed(sources, &["current=evaluate(Calc.current)"], &quiet()).unwrap();
    let Signature::View { body, .. } =
        prepared.inputs().law().declarations()["Calc.current"].signature
    else {
        unreachable!()
    };
    let span = prepared.inputs().law().exprs()[body].span;
    let analyses = Rc::new(Cell::new(0));
    let seen = analyses.clone();
    let normalizations = Rc::new(Cell::new(0));
    let normalized = normalizations.clone();
    data::observe_iterations(move |at, _, phase, _| {
        if at == span && phase == "in_set_normalization" {
            normalized.set(normalized.get() + 1);
        }
        if at == span && phase == "source_analysis" {
            seen.set(seen.get() + 1);
        }
    });
    let mut result = evaluate_observed(prepared, &quiet()).unwrap();
    data::clear_iteration_observer();
    assert_eq!(result.status(), "complete", "{:?}", result.issues);
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    assert_eq!(analyses.get(), 0, "外側In元ASTのbodyを予備意味評価しない");
    assert_eq!(normalizations.get(), 1, "通常In collection正規化は一回");
    assert_eq!(result.iterations.len(), 5);
    let domain = result.iterations[0].finite.unwrap();
    let Some(Payload::Domain { elements, .. }) = &result.nodes[domain.0].payload else {
        unreachable!()
    };
    assert_eq!(
        elements
            .iter()
            .map(|reference| data_scalar_at(&result, reference.0))
            .collect::<Vec<_>>(),
        vec![
            &Scalar::Z(2.into()),
            &Scalar::Z(3.into()),
            &Scalar::Z(4.into()),
            &Scalar::Z(5.into()),
            &Scalar::Z(6.into())
        ]
    );
    for (position, record) in result.iterations.iter().enumerate() {
        assert_eq!(record.position, position);
        assert_eq!(record.producer, Some(elements[position]));
        assert_eq!(record.finite, Some(domain));
    }
    let cold_normalizations = Rc::new(Cell::new(0));
    let normalized = cold_normalizations.clone();
    data::observe_iterations(move |at, _, phase, _| {
        if at == span && phase == "in_set_normalization" {
            normalized.set(normalized.get() + 1);
        }
    });
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    data::clear_iteration_observer();
    assert!(
        (1..=2).contains(&cold_normalizations.get()),
        "cold再構築のSet正規化が各member/bodyへ増幅しない: {}",
        cold_normalizations.get()
    );
    let saved = result.iterations[0].clone();
    result.iterations[0].producer = result.iterations[1].producer;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&result, &result.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    result.iterations[0] = saved.clone();
    result.iterations[0].position = 1;
    assert!(matches!(
        rebuild_for_origin_and_support_recheck(&result, &result.nodes),
        Err(ValidationFailure::Internal(_))
    ));
    result.iterations[0] = saved;
    let mut graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    let target = result
        .nodes
        .iter()
        .zip(&result.contexts)
        .enumerate()
        .find_map(|(index, (node, context))| {
            (context.iteration == Some(0)
                && matches!(node.payload, Some(Payload::Scalar(Scalar::Bool(_))))
                && matches!(node.rule, Rule::Input { kind: "law", .. }))
            .then_some(index)
        })
        .expect("未移行Eqの実Scalar");
    let control = quiet();
    let environment = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    environment
        .validate_at(&graph, graph.get(NodeRef(target)).unwrap(), target)
        .unwrap();
    // 現memberの位置/値は正しいまま、別memberをDomainから落とす。
    // coldなlegacy Eq単体の認証も、依存Domainの全coverage proofまで届く。
    let domain_node = &mut graph.nodes[domain.0];
    let Some(Payload::Domain { elements, .. }) = &mut domain_node.payload else {
        unreachable!()
    };
    elements.pop();
    domain_node.arguments.pop();
    let cold = Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &control,
    )
    .unwrap();
    assert!(matches!(
        cold.validate_at(&graph, graph.get(NodeRef(target)).unwrap(), target),
        Err(ValidationFailure::Internal(_))
    ));
}

#[test]
fn ordinary_in_nested_and_empty_domains_keep_scope_and_vacuity() {
    for (body, known, iterations) in [
        ("forall n in list<Z>[].false", true, 0),
        ("exists n in list<Z>[].true", false, 0),
        (
            "forall n in list<Z>[1,2].forall m in list<Z>[n].m=n",
            true,
            4,
        ),
    ] {
        let result = affine_private_example(
            &format!("view current():Bool={body};"),
            &["current=evaluate(Calc.current)"],
        );
        assert_eq!(result.status(), "complete", "{body}: {:?}", result.issues);
        assert_eq!(
            data_scalar_at(&result, result.answers[0].outputs["value"].0),
            &Scalar::Bool(known)
        );
        assert_eq!(result.iterations.len(), iterations);
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}

#[test]
fn ordinary_in_real_owned_collection_keeps_pending_and_failed() {
    for (unknown, owner, failed) in [(true, "A", false), (false, "B", true)] {
        let input = owned_call_fixture::input(unknown, true, "r1");
        let law = String::from_utf8(input.law().bytes().to_vec()).unwrap().replace(
            owned_call_fixture::SCRIPT,
            &format!("{} view gather(a:System,s:State):List<Z> =let checked=narrow(a,s) in list<Z>[1]; view current(a:System,s:State):Bool=forall n in gather(a,s).true;", owned_call_fixture::SCRIPT),
        );
        let sources = InputSources::from_bytes(
            input
                .definitions()
                .iter()
                .map(|item| item.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            input.archmap().bytes().to_vec(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &[&format!(
                "current=evaluate(Reservations.current,a=@v/{owner},s=@v/p)"
            )],
            &quiet(),
        )
        .unwrap_or_else(|failure| panic!("{:?}", failure.wire()));
        assert_ne!(
            result.status(),
            "error",
            "unknown={unknown}: {:?}",
            result.issues
        );
        let nodes: Vec<_> = result
            .nodes
            .iter()
            .zip(&result.contexts)
            .filter(|(_, context)| context.case.is_none())
            .collect();
        let (evaluation, _) = nodes.iter().find(|(node, _)| matches!(&node.payload, Some(Payload::Evaluation { expression, .. }) if matches!(&result.nodes[expression.0].payload, Some(Payload::Expression { location:Location::Law{span}, .. }) if result.prepared.inputs().sources().law().bytes().get(span.0..span.1) == Some(b"forall n in gather(a,s).true")))).expect("初期In Evaluation");
        assert!(matches!(
            evaluation.payload,
            Some(Payload::Evaluation { value: None, .. })
        ));
        assert_eq!(
            evaluation
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::ConditionFailed { .. })),
            failed
        );
        if !failed {
            assert!(
                evaluation
                    .reasons
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Missing))
            );
        }
        assert!(
            result
                .iterations
                .iter()
                .all(|record| record.caller.case.is_some()),
            "初期Pending/Failed collectionから反復を作らない"
        );
        rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    }
}

#[test]
fn ordinary_in_binder_field_and_boolean_body_do_not_materialize_common_support() {
    use std::{cell::Cell, rc::Rc};
    let sources = affine_private_fixture(
        "view current(a:Sample,b:Sample,c:Sample):Bool=forall n in list<Sample>[a,b,c].(n.p = n.p) and (n.p or true);",
    );
    let map = String::from_utf8(sources.archmap().bytes().to_vec()).unwrap().replacen("\"atoms\":[]", r#""atoms":[{"id":"sample-p","subject":"sample","field":"Affine.Sample.p","value":true,"origin":"base"},{"id":"other-p","subject":"other","field":"Affine.Sample.p","value":false,"origin":"base"}]"#, 1);
    let map = map.replacen("\"atoms\":[]", r#""atoms":[{"id":"sample-v2-p","subject":"sample","field":"Affine.Sample.p","value":true,"origin":"base"}]"#, 1);
    let sources = InputSources::from_bytes(
        sources
            .definitions()
            .iter()
            .map(|source| source.bytes().to_vec())
            .collect(),
        sources.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let prepared = prepare_observed(
        sources,
        &["current=evaluate(Calc.current,a=@v/sample,b=@v/other,c=@v2/sample)"],
        &quiet(),
    )
    .unwrap();
    let Signature::View { body, .. } =
        prepared.inputs().law().declarations()["Calc.current"].signature
    else {
        unreachable!()
    };
    let ExprKind::Quant {
        split: archsig_input::law::ast::QuantSplit::Fixed { body, .. },
        ..
    } = prepared.inputs().law().exprs()[body].kind
    else {
        unreachable!()
    };
    let span = prepared.inputs().law().exprs()[body].span;
    let active = Rc::new(Cell::new(false));
    let materializations = Rc::new(Cell::new(0));
    let completed = Rc::new(Cell::new(0));
    let (armed, observed, bodies) = (active.clone(), materializations.clone(), completed.clone());
    data::observe_iterations(move |at, _, phase, _| {
        if at == span && phase == "ordinary_source" {
            armed.set(true);
        }
        if phase == "support_materialize" && armed.get() {
            observed.set(observed.get() + 1);
        }
        if at == span && phase == "ordinary_evaluation" {
            armed.set(false);
            bodies.set(bodies.get() + 1);
        }
    });
    let result = evaluate_observed(prepared, &quiet()).unwrap();
    data::clear_iteration_observer();
    assert_ne!(result.status(), "error", "{:?}", result.issues);
    assert_eq!(result.iterations.len(), 3);
    assert_eq!(completed.get(), 3, "実際の各反復本文を通る");
    assert_eq!(
        materializations.get(),
        0,
        "binder/field/Eq/Boolの支持配送と内部認証では共通支持をFact列へ展開しない"
    );
    assert_eq!(
        data_scalar_at(&result, result.answers[0].outputs["value"].0),
        &Scalar::Bool(true)
    );
    let field_span = result
        .nodes
        .iter()
        .find_map(|node| {
            if node.rule != Rule::Construction("field_evaluation") {
                return None;
            }
            let Some(Payload::Evaluation { parts, .. }) = &node.payload else {
                return None;
            };
            let Location::Law { span } = parts[0].location else {
                return None;
            };
            Some(span)
        })
        .unwrap();
    let verifying = Rc::new(Cell::new(false));
    let cold_materializations = Rc::new(Cell::new(0));
    let verified = Rc::new(Cell::new(0));
    let (inside, allocations, finished) = (
        verifying.clone(),
        cold_materializations.clone(),
        verified.clone(),
    );
    let quant_support_runs = Rc::new(Cell::new(0));
    let quant_support_materializations = Rc::new(Cell::new(0));
    let (quant_runs, quant_materializations) = (
        quant_support_runs.clone(),
        quant_support_materializations.clone(),
    );
    let quant_active = Cell::new(false);
    data::observe_iterations(move |at, context, phase, _| {
        if phase == "quant_parts_support" {
            assert!(!quant_active.replace(true));
            quant_runs.set(quant_runs.get() + 1);
        }
        if phase == "support_materialize" && quant_active.get() {
            quant_materializations.set(quant_materializations.get() + 1);
        }
        if phase == "quant_parts_support_verified" {
            assert!(quant_active.replace(false));
        }
        if at == field_span && context.iteration.is_some() && phase == "field_read" {
            inside.set(true);
        }
        if phase == "support_materialize" && inside.get() {
            allocations.set(allocations.get() + 1);
        }
        if at == field_span && context.iteration.is_some() && phase == "field_read_verified" {
            inside.set(false);
            finished.set(finished.get() + 1);
        }
    });
    rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    data::clear_iteration_observer();
    assert!(verified.get() >= 3, "各実fieldのcold局所検証を通る");
    assert_eq!(
        cold_materializations.get(),
        0,
        "別Arcのterminal Fact葉を含むfield局所照合で全F fallbackを作らない"
    );
    assert!(
        quant_support_runs.get() > 0,
        "量化全coverageのcold支持検査を通る"
    );
    assert_eq!(
        quant_support_materializations.get(),
        quant_support_runs.get(),
        "各全coverage検査で本文数に関わらず最終Fact列を一度だけ作る"
    );
    let root = result.answers[0].outputs["evaluation"].0;
    let Some(Payload::Evaluation { parts, .. }) = &result.nodes[root].payload else {
        unreachable!()
    };
    let mut expected = Vec::new();
    for child in &parts[0].children {
        expected.extend(result.nodes[child.0].support.materialize_for_test());
    }
    expected.sort();
    expected.dedup();
    assert_eq!(
        result.nodes[root].support.materialize_for_test(),
        expected,
        "旧全body flat unionと最終Fact列・順序が一致する"
    );
    rejects_mutated_prefix(&result, root, |nodes| {
        nodes[root].support.materialize_mut_for_test().pop();
    });
    let graph = rebuild_for_origin_and_support_recheck(&result, &result.nodes).unwrap();
    for signal in [Signal::Int, Signal::Term] {
        let armed = Rc::new(Cell::new(false));
        let interrupted = armed.clone();
        let control = Control::new(move |_| interrupted.replace(false).then_some(signal));
        let arm = armed.clone();
        data::observe_iterations(move |_, _, phase, _| {
            if phase == "quant_parts_support" {
                arm.set(true);
            }
        });
        let environment = Environment::with_requests(
            result.prepared.inputs(),
            result.prepared.requests().requests(),
            &control,
        )
        .unwrap();
        assert!(
            matches!(environment.validate_at(&graph, graph.get(NodeRef(root)).unwrap(), root),
            Err(ValidationFailure::Stop(actual)) if actual == signal)
        );
        data::clear_iteration_observer();
        assert_eq!(
            graph.nodes.len(),
            result.nodes.len(),
            "支持射影中のStopでgraphを変更しない"
        );
    }
    let retry_control = quiet();
    Environment::with_requests(
        result.prepared.inputs(),
        result.prepared.requests().requests(),
        &retry_control,
    )
    .unwrap()
    .validate_at(&graph, graph.get(NodeRef(root)).unwrap(), root)
    .unwrap();
    // 実refs/値/Scopeは同じまま、公開可能な旧flat表現でも独立認証する。
    // Arc同一性や唯一の因子分解を新しい意味条件にはしない。
    let mut flat = result.nodes.clone();
    for node in &mut flat {
        node.support = node.support.materialize_for_test().into();
    }
    rebuild_for_origin_and_support_recheck(&result, &flat).unwrap();
}
