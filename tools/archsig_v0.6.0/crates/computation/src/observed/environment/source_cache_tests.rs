use super::*;

fn analysis(value: i32) -> SourceAnalysis {
    SourceAnalysis {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        scope: Scope::default(),
        known_value: Some(Scalar::Z(value.into())),
        affine: None,
        missing: None,
        support: vec![].into(),
        scalar_scope: None,
    }
}

#[test]
fn exact_context_and_remaining_keys_preserve_first_match() {
    let context = super::super::call::Context::default();
    let bindings = vec![
        Binding {
            name: "x".into(),
            value: NodeRef(1),
            ty: Type::Z,
        },
        Binding {
            name: "y".into(),
            value: NodeRef(2),
            ty: Type::Z,
        },
    ];
    let mut cache = ValidationCache::default();
    let entry = (10, (2, 3), bindings.clone(), analysis(1));
    cache.sources.insert(context, entry);
    cache
        .sources
        .insert(context, (10, (2, 3), bindings.clone(), analysis(2)));
    let value = |cache: &ValidationCache, context, limit, span, bindings: &[Binding]| {
        cache
            .sources
            .get(context, limit, span, bindings)
            .map(|a| a.known_value)
    };
    assert_eq!(
        value(&cache, context, 10, (2, 3), &bindings),
        Some(Some(Scalar::Z(1.into())))
    );
    assert!(value(&cache, context, 9, (2, 3), &bindings).is_none());
    assert!(value(&cache, context, 10, (2, 4), &bindings).is_none());
    for changed in [
        super::super::call::Context {
            request: 1,
            ..context
        },
        super::super::call::Context {
            frame: Some(0),
            ..context
        },
        super::super::call::Context {
            iteration: Some(0),
            ..context
        },
        super::super::call::Context {
            instance: Some(0),
            ..context
        },
        super::super::call::Context {
            case: Some(0),
            ..context
        },
    ] {
        assert!(value(&cache, changed, 10, (2, 3), &bindings).is_none());
        cache
            .sources
            .insert(changed, (10, (2, 3), bindings.clone(), analysis(3)));
        assert_eq!(
            value(&cache, changed, 10, (2, 3), &bindings),
            Some(Some(Scalar::Z(3.into())))
        );
    }
    let mut changed = bindings.clone();
    changed.swap(0, 1);
    assert!(value(&cache, context, 10, (2, 3), &changed).is_none());
    for index in 0..3 {
        let mut changed = bindings.clone();
        match index {
            0 => changed[0].name = "other".into(),
            1 => changed[0].value = NodeRef(9),
            _ => changed[0].ty = Type::Bool,
        }
        assert!(value(&cache, context, 10, (2, 3), &changed).is_none());
    }
    cache = ValidationCache::default();
    assert!(value(&cache, context, 10, (2, 3), &bindings).is_none());
}

#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/primitive_valuation_data.rs");
}

#[test]
fn graph_session_keeps_safe_append_and_clears_changed_context_or_failure() {
    let control = archsig_common::control::quiet();
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let mut graph = Graph::new(&control);
    let node = Node {
        ty: NodeType::Value(Type::Z),
        payload: Some(Payload::scalar(Scalar::Z(1.into()))),
        rule: Rule::Construction("evaluation"),
        arguments: vec![],
        support: vec![].into(),
        evidence: vec![],
        judgment: None,
        scope: Scope::default(),
        reasons: vec![],
    };
    graph.push(node.clone()).unwrap();
    let context = super::super::call::Context::default();
    let insert = || {
        env.results
            .cache
            .borrow_mut()
            .sources
            .insert(context, (1, (2, 3), vec![], analysis(1)));
    };
    let hit = || {
        env.results
            .cache
            .borrow()
            .sources
            .get(context, 1, (2, 3), &[])
            .is_some()
    };
    env.validation_graph_session(&graph, || {
        insert();
        Ok(())
    })
    .unwrap();
    graph.push(node).unwrap();
    env.validation_graph_session(&graph, || {
        assert!(hit());
        Ok(())
    })
    .unwrap();
    graph.contexts[0].frame = Some(0);
    env.validation_graph_session(&graph, || {
        assert!(!hit());
        insert();
        Ok(())
    })
    .unwrap();
    let failure: Result<(), ValidationFailure> = env.validation_graph_session(&graph, || {
        assert!(hit());
        Err(internal!("source cache test failure").into())
    });
    assert!(failure.is_err());
    assert!(!hit());
    env.validation_graph_session(&graph, || {
        assert!(!hit());
        Ok(())
    })
    .unwrap();
}

#[test]
fn central_entries_keep_interleaved_context_indices_across_growth() {
    let mut cache = SourceCache::default();
    for index in 0..300 {
        let context = super::super::call::Context {
            request: index % 3,
            ..Default::default()
        };
        cache.insert(context, (index, (2, 3), vec![], analysis(index as i32)));
    }
    assert_eq!(cache.entries.len(), 300);
    let mut positions: Vec<_> = cache.by_context.values().flatten().copied().collect();
    positions.sort_unstable();
    assert_eq!(positions, (0..300).collect::<Vec<_>>());
    for indices in cache.by_context.values() {
        assert!(indices.windows(2).all(|pair| pair[0] < pair[1]));
    }
    for index in 0..300 {
        let context = super::super::call::Context {
            request: index % 3,
            ..Default::default()
        };
        assert_eq!(
            cache.get(context, index, (2, 3), &[]).unwrap().known_value,
            Some(Scalar::Z((index as i32).into()))
        );
    }
}
