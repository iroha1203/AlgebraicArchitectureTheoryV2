use super::*;
use crate::observed::call::Context;
use archsig_common::control::quiet;

#[allow(dead_code)]
mod fixture {
    include!("../../../../../../tests/common/primitive_valuation_data.rs");
}
fn node(value: i32) -> Node {
    Node {
        ty: NodeType::Value(Type::Z),
        payload: Some(Payload::scalar(Scalar::Z(value.into()))),
        rule: Rule::Construction("evaluation"),
        arguments: vec![],
        support: vec![].into(),
        evidence: vec![],
        judgment: None,
        scope: Scope::default(),
        reasons: vec![],
    }
}
fn contexts() -> Vec<Context> {
    let base = Context::default();
    vec![
        base,
        Context { request: 1, ..base },
        Context {
            frame: Some(0),
            ..base
        },
        Context {
            iteration: Some(0),
            ..base
        },
        Context {
            instance: Some(0),
            ..base
        },
        Context {
            case: Some(0),
            ..base
        },
        base,
    ]
}
fn graph(control: &Control) -> Graph {
    let mut g = Graph::new(control);
    for (i, context) in contexts().into_iter().enumerate() {
        g.active = context;
        g.push(node(i as i32)).unwrap();
    }
    g
}
#[test]
fn indexed_candidates_preserve_all_context_fields_order_and_cutoff() {
    let control = quiet();
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let g = graph(&control);
    env.validation_graph_session(&g, || {
        for context in contexts().into_iter().chain([Context {
            case: Some(99),
            ..Default::default()
        }]) {
            let _context = env.state.context.scoped(Some(context));
            for limit in 0..=g.nodes.len() + 1 {
                let expected: Vec<_> = (0..g.nodes.len().min(limit))
                    .filter(|&i| g.context_at(i) == context)
                    .collect();
                assert_eq!(
                    env.context_candidates(&g, limit)?.collect::<Vec<_>>(),
                    expected
                );
            }
        }
        Ok(())
    })
    .unwrap();
}
#[test]
fn candidates_release_cache_borrow_before_nested_validation_and_append_only_new_suffix() {
    let control = quiet();
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let mut g = Graph::new(&control);
    g.push(node(0)).unwrap();
    let original = env
        .validation_graph_session(&g, || {
            let indices = env.context_candidates(&g, usize::MAX)?;
            // 再入先が同じcacheを借用・検査しても外側の候補は保持できる。
            env.validation_graph_session(&g, || {
                assert_eq!(
                    env.context_candidates(&g, usize::MAX)?.collect::<Vec<_>>(),
                    vec![0]
                );
                Ok(())
            })?;
            Ok(indices)
        })
        .unwrap();
    g.push(node(1)).unwrap();
    env.validation_graph_session(&g, || {
        assert_eq!(env.results.cache.borrow().context_candidates.covered_len, 1);
        assert_eq!(
            env.context_candidates(&g, usize::MAX)?.collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert_eq!(env.context_candidates(&g, 1)?.collect::<Vec<_>>(), vec![0]);
        assert_eq!(env.results.cache.borrow().context_candidates.covered_len, 2);
        Ok(())
    })
    .unwrap();
    // Rcを持つ旧候補列にも後の追記を漏らさない。
    assert_eq!(original.collect::<Vec<_>>(), vec![0]);
}
#[test]
fn contexts_missing_or_extra_and_nested_foreign_graph_keep_original_full_scan() {
    let control = quiet();
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let root = graph(&control);
    let mut foreign = graph(&control);
    foreign.active = Context {
        request: 42,
        ..Default::default()
    };
    env.validation_graph_session(&root, || {
        assert_eq!(
            env.context_candidates(&root, 7)?.collect::<Vec<_>>(),
            vec![0, 6]
        );
        for missing in [false, true] {
            if missing {
                foreign.contexts.truncate(1);
            }
            env.validation_graph_session(&foreign, || {
                assert_eq!(
                    env.context_candidates(&foreign, 7)?.collect::<Vec<_>>(),
                    (0..7).collect::<Vec<_>>()
                );
                if missing {
                    assert_eq!(foreign.context_at(1), foreign.active);
                }
                Ok(())
            })?;
        }
        assert_eq!(env.results.cache.borrow().context_candidates.covered_len, 7);
        Ok(())
    })
    .unwrap();
    // root外・不完全contextsではactive fallbackの候補を省かない。
    assert_eq!(
        env.context_candidates(&foreign, 2)
            .unwrap()
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    for extra in [false, true] {
        let mut g = graph(&control);
        if extra {
            g.contexts.push(Default::default());
        } else {
            g.contexts.truncate(1);
        }
        let _graph = env.state.validation_graph.scoped(Some(&g as *const Graph));
        assert_eq!(
            env.context_candidates(&g, 3).unwrap().collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }
}
#[test]
fn changed_cloned_or_shortened_prefix_discards_old_context_positions() {
    let control = quiet();
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let mut g = graph(&control);
    for change in 0..4 {
        env.validation_graph_session(&g, || {
            env.context_candidates(&g, usize::MAX)?;
            Ok(())
        })
        .unwrap();
        match change {
            0 => g.contexts[0] = g.active,
            1 => {
                g.nodes = g.nodes.clone();
                g.contexts = g.contexts.clone();
            }
            2 => {
                g.nodes.truncate(4);
                g.contexts.truncate(4);
            }
            _ => g.nodes[0] = node(99),
        }
        env.validation_graph_session(&g, || {
            assert_eq!(env.results.cache.borrow().context_candidates.covered_len, 0);
            let expected: Vec<_> = (0..g.nodes.len())
                .filter(|&i| g.context_at(i) == env.current_context(&g))
                .collect();
            assert_eq!(
                env.context_candidates(&g, usize::MAX)?.collect::<Vec<_>>(),
                expected
            );
            Ok(())
        })
        .unwrap();
    }
}
#[test]
fn stopped_suffix_build_keeps_a_consistent_prefix_and_first_signal_stays_frozen() {
    use std::cell::Cell;
    let probes = Rc::new(Cell::new(0));
    let stop_at = Rc::new(Cell::new(usize::MAX));
    let count = probes.clone();
    let cutoff = stop_at.clone();
    let control = Control::new(move |_| {
        let n = count.get() + 1;
        count.set(n);
        (n >= cutoff.get()).then_some(Signal::Term)
    });
    let inputs = fixture::inputs();
    let env = Environment::new(&inputs, &control).unwrap();
    let mut g = Graph::new(&control);
    g.push(node(0)).unwrap();
    env.validation_graph_session(&g, || {
        env.context_candidates(&g, 1)?;
        Ok(())
    })
    .unwrap();
    for i in 1..6 {
        g.push(node(i)).unwrap();
    }
    let _graph = env.state.validation_graph.scoped(Some(&g as *const Graph));
    stop_at.set(probes.get() + 4); // suffixの途中で停止する。公開probe回数への期待ではない。
    assert!(matches!(
        env.context_candidates(&g, 6),
        Err(ValidationFailure::Stop(Signal::Term))
    ));
    let covered = env.results.cache.borrow().context_candidates.covered_len;
    assert!((2..6).contains(&covered));
    assert_eq!(
        env.results.cache.borrow().context_candidates.positions[&Context::default()].as_slice(),
        (0..covered).collect::<Vec<_>>()
    );
    let frozen = probes.get();
    assert!(matches!(
        env.context_candidates(&g, 6),
        Err(ValidationFailure::Stop(Signal::Term))
    ));
    assert_eq!(probes.get(), frozen);
    env.results.clear_validation();
    assert_eq!(env.results.cache.borrow().context_candidates.covered_len, 0);
}

#[test]
fn validation_rollback_context_index_drops_scratch_positions_without_changing_held_candidates() {
    let context = Context::default();
    let scratch_context = Context {
        iteration: Some(0),
        ..context
    };
    let mut index = ContextIndex::default();
    index.covered_len = 2;
    index.positions.insert(context, Rc::new(vec![0, 1]));
    let prefix = index.checkpoint();
    let held = index.positions[&context].clone();
    Rc::make_mut(index.positions.get_mut(&context).unwrap()).push(2);
    index.positions.insert(scratch_context, Rc::new(vec![3]));
    index.covered_len = 4;
    index.rollback(prefix);
    assert_eq!(index.covered_len, 2);
    assert_eq!(index.positions[&context].as_slice(), [0, 1]);
    assert!(!index.positions.contains_key(&scratch_context));
    assert_eq!(held.as_slice(), [0, 1]);
    // Reuse the released position for another Context; no stale membership remains.
    let fresh_context = Context {
        iteration: Some(1),
        ..context
    };
    index.positions.insert(fresh_context, Rc::new(vec![2]));
    index.covered_len = 3;
    assert_eq!(index.positions[&fresh_context].as_slice(), [2]);
    assert!(!index.positions.contains_key(&scratch_context));
}
