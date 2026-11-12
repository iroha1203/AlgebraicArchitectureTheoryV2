use super::*;
use archsig_common::control::quiet;
use archsig_input::result::Signal;
fn node(value: i32) -> Node {
    Node {
        ty: NodeType::Value(archsig_common::types::Type::Z),
        payload: Some(Payload::Scalar(Scalar::Z(value.into()))),
        rule: Rule::Construction("evaluation"),
        arguments: vec![],
        support: vec![].into(),
        evidence: vec![],
        judgment: None,
        scope: Scope::default(),
        reasons: vec![],
    }
}
#[test]
fn appended_nodes_keep_prefix_but_mutation_removal_and_replacement_are_checked() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let mut saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    g.push(node(2)).unwrap();
    assert!(saved.matches(&g, &c).unwrap());
    saved.extend_matching(&g, &c).unwrap();
    let original = g.nodes[0].clone();
    g.nodes[0] = node(9);
    assert!(!saved.matches(&g, &c).unwrap());
    g.nodes[0] = original;
    assert!(
        !saved.matches(&g, &c).unwrap(),
        "restoring values does not restore identity"
    );
    saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    assert!(saved.matches(&g, &c).unwrap());
    g.nodes.truncate(1);
    g.contexts.truncate(1);
    assert!(!saved.matches(&g, &c).unwrap());
    g.nodes = vec![node(1), node(8)].into();
    g.contexts.push(Default::default());
    assert!(!saved.matches(&g, &c).unwrap());
}
#[test]
fn cloned_tables_that_append_different_nodes_do_not_share_a_prefix_identity() {
    let c = quiet();
    let mut a = Graph::new(&c);
    a.push(node(1)).unwrap();
    let mut b = Graph::new(&c);
    b.nodes = a.nodes.clone();
    b.contexts = a.contexts.clone();
    a.push(node(2)).unwrap();
    b.push(node(3)).unwrap();
    let saved = ValidationSnapshot::from_graph(&a, &c).unwrap();
    assert!(!saved.matches(&b, &c).unwrap());
    b.nodes[1] = node(2);
    assert!(
        !saved.matches(&b, &c).unwrap(),
        "equal contents of a cloned table are rechecked"
    );
    let refreshed = ValidationSnapshot::from_graph(&b, &c).unwrap();
    assert!(refreshed.matches(&b, &c).unwrap());
}
#[test]
fn unchanged_node_identity_does_not_hide_context_changes() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    let identity = g.nodes.prefix_identity();
    g.contexts[0].frame = Some(0);
    assert!(std::rc::Rc::ptr_eq(&identity, &g.nodes.prefix_identity()));
    assert!(!saved.matches(&g, &c).unwrap());
    g.contexts[0] = Default::default();
    assert!(
        !saved.matches(&g, &c).unwrap(),
        "復元しても旧identityは戻らない"
    );
    let refreshed = ValidationSnapshot::from_graph(&g, &c).unwrap();
    assert!(refreshed.matches(&g, &c).unwrap());
    g.contexts.clear();
    assert!(!saved.matches(&g, &c).unwrap());
}
#[test]
fn prefix_identity_fast_path_keeps_stop_and_freezes_the_probe() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    let calls = std::rc::Rc::new(std::cell::Cell::new(0));
    let observed = calls.clone();
    let stopped = Control::new(move |_| {
        observed.set(observed.get() + 1);
        Some(Signal::Term)
    });
    assert!(matches!(
        saved.matches(&g, &stopped),
        Err(ValidationFailure::Stop(_))
    ));
    assert!(matches!(
        saved.matches(&g, &stopped),
        Err(ValidationFailure::Stop(_))
    ));
    assert_eq!(calls.get(), 1);
}

fn iteration(source: usize, domain: usize) -> crate::observed::call::Iteration {
    crate::observed::call::Iteration {
        caller: Default::default(),
        source: NodeRef(source),
        domain: NodeRef(domain),
        member: crate::observed::call::Member::ListPosition(0),
        finite: Some(NodeRef(domain)),
        position: 0,
        producer: None,
    }
}

#[test]
fn fresh_iteration_producer_keeps_snapshot_and_checks_the_extended_prefix() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    g.iterations.push(iteration(0, 0));
    let mut saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    g.push(node(2)).unwrap();
    g.iterations.push(iteration(0, 1));
    assert!(
        saved.matches(&g, &c).unwrap(),
        "fresh domain must preserve checked prefix"
    );
    saved.extend_matching(&g, &c).unwrap();
    assert_eq!(saved.iterations.as_slice(), g.iterations.as_slice());
    assert!(saved.matches(&g, &c).unwrap());
    saved.extend_matching(&g, &c).unwrap();
    let original = g.iterations[1].clone();
    g.iterations[1].member = crate::observed::call::Member::ListPosition(1);
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[1] = original.clone();
    g.iterations[1].caller.iteration = Some(0);
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[1] = original.clone();
    g.iterations[1].source = NodeRef(1);
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[1] = original.clone();
    g.iterations[1].domain = NodeRef(0);
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[1] = original.clone();
    g.iterations[1].finite = None;
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[1] = original;
    assert!(saved.matches(&g, &c).unwrap());
    g.iterations.remove(0);
    assert!(!saved.matches(&g, &c).unwrap());
}

#[test]
fn iteration_append_without_fresh_producer_and_changed_old_prefix_are_rejected() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    g.iterations.push(iteration(0, 0));
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    g.iterations.push(iteration(0, 0));
    assert!(!saved.matches(&g, &c).unwrap());
    g.push(node(2)).unwrap();
    g.iterations[1].domain = NodeRef(1);
    assert!(saved.matches(&g, &c).unwrap());
    g.iterations[0].member = crate::observed::call::Member::ListPosition(2);
    assert!(!saved.matches(&g, &c).unwrap());
    g.iterations[0] = iteration(0, 0);
    g.nodes[0] = node(9);
    assert!(!saved.matches(&g, &c).unwrap());
}

#[allow(dead_code)]
mod fixture {
    include!("../../../../../tests/common/primitive_valuation_data.rs");
}

#[test]
fn validation_session_reuses_checked_entries_only_across_safe_iteration_append() {
    let c = quiet();
    let inputs = fixture::inputs();
    let environment = Environment::new(&inputs, &c).unwrap();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let key = (crate::observed::call::Context::default(), 0);
    environment
        .validation_graph_session(&g, || {
            environment.results.cache.borrow_mut().checked.insert(key);
            Ok(())
        })
        .unwrap();
    g.push(node(2)).unwrap();
    g.iterations.push(iteration(0, 1));
    environment
        .validation_graph_session(&g, || {
            assert!(environment.results.cache.borrow().checked.contains(&key));
            Ok(())
        })
        .unwrap();
    g.iterations[0].domain = NodeRef(0);
    environment
        .validation_graph_session(&g, || {
            assert!(!environment.results.cache.borrow().checked.contains(&key));
            Ok(())
        })
        .unwrap();
}

#[test]
fn extended_iteration_snapshot_checks_clone_divergence_and_stop() {
    let c = quiet();
    let mut a = Graph::new(&c);
    a.push(node(1)).unwrap();
    let mut saved = ValidationSnapshot::from_graph(&a, &c).unwrap();
    let mut b = Graph::new(&c);
    b.nodes = a.nodes.clone();
    b.contexts = a.contexts.clone();
    a.push(node(2)).unwrap();
    b.push(node(3)).unwrap();
    a.iterations.push(iteration(0, 1));
    b.iterations.push(iteration(0, 1));
    assert!(saved.matches(&a, &c).unwrap());
    saved.extend_matching(&a, &c).unwrap();
    assert!(!saved.matches(&b, &c).unwrap());
    b.nodes[1] = node(2);
    assert!(!saved.matches(&b, &c).unwrap());
    saved = ValidationSnapshot::from_graph(&b, &c).unwrap();
    assert!(saved.matches(&b, &c).unwrap());
    b.iterations[0].member = crate::observed::call::Member::ListPosition(1);
    assert!(!saved.matches(&b, &c).unwrap());
    let stopped = Control::new(|_| Some(Signal::Int));
    assert!(matches!(
        saved.matches(&a, &stopped),
        Err(ValidationFailure::Stop(_))
    ));
}

#[test]
fn finite_only_iteration_producer_does_not_preserve_the_checked_prefix() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    let fresh = g.push(node(2)).unwrap();
    let mut extra = iteration(0, 0);
    extra.finite = Some(fresh);
    g.iterations.push(extra);
    assert!(
        !saved.matches(&g, &c).unwrap(),
        "finite is not part of universal registry cutoff filtering"
    );
}

#[test]
fn node_identity_changes_invalidate_even_an_equal_prefix() {
    let c = quiet();
    for access in ["index", "slice", "iteration", "clone"] {
        let mut g = Graph::new(&c);
        g.push(node(1)).unwrap();
        let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
        match access {
            "index" => {
                let same = g.nodes[0].clone();
                g.nodes[0] = same;
            }
            "slice" => {
                let _same = &mut g.nodes[..];
            }
            "iteration" => for _same in &mut g.nodes {},
            "clone" => g.nodes = g.nodes.clone(),
            _ => unreachable!(),
        }
        assert!(
            !saved.matches(&g, &c).unwrap(),
            "{access} must invalidate identity even when all values are equal"
        );
        let refreshed = ValidationSnapshot::from_graph(&g, &c).unwrap();
        assert!(refreshed.matches(&g, &c).unwrap());
    }
}

#[test]
fn checked_context_append_keeps_the_prefix_but_all_mutable_paths_invalidate_it() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let mut saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    g.active.request = 1;
    g.push(node(2)).unwrap();
    assert!(saved.matches(&g, &c).unwrap());
    saved.extend_matching(&g, &c).unwrap();
    assert!(saved.matches(&g, &c).unwrap());

    for access in [
        "index",
        "slice",
        "deref",
        "iter_mut",
        "into_iter_mut",
        "clear",
        "truncate",
        "replace",
        "clone",
    ] {
        let mut g = Graph::new(&c);
        g.push(node(1)).unwrap();
        g.push(node(2)).unwrap();
        let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
        let original = g.contexts.to_vec();
        match access {
            "index" => {
                g.contexts[0].request = 9;
                g.contexts[0] = original[0];
            }
            "slice" => {
                g.contexts.as_mut_slice()[0] = original[0];
            }
            "deref" => {
                let values: &mut Vec<super::super::call::Context> = &mut g.contexts;
                values[0] = original[0];
            }
            "iter_mut" => {
                g.contexts.iter_mut().for_each(|v| v.request = 0);
            }
            "into_iter_mut" => {
                for v in &mut g.contexts {
                    v.request = 0;
                }
            }
            "clear" => {
                g.contexts.clear();
                g.contexts.extend(original.iter().copied());
            }
            "truncate" => {
                g.contexts.truncate(1);
                g.contexts.push(original[1]);
            }
            "replace" => {
                g.contexts = original.clone().into();
            }
            "clone" => {
                g.contexts = g.contexts.clone();
            }
            _ => unreachable!(),
        }
        assert_eq!(g.contexts.as_slice(), original.as_slice());
        assert!(!saved.matches(&g, &c).unwrap(), "mutable access {access}");
    }
}

#[test]
fn context_prefix_identity_does_not_hide_node_context_length_mismatch() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    g.contexts.push(super::super::call::Context::default());
    assert!(!saved.matches(&g, &c).unwrap());
    let malformed = ValidationSnapshot::from_graph(&g, &c).unwrap();
    assert!(!malformed.matches(&g, &c).unwrap());
}

fn non_reflexive_path_iteration(source: usize, domain: usize) -> crate::observed::call::Iteration {
    let path = crate::observed::path_value::PathValue {
        reading: "r".into(),
        snapshot: "s".into(),
        subject: "u".into(),
        entity: "E".into(),
        step: Some(Box::new(crate::observed::path_value::Step {
            generator: Scalar::Z(0.into()),
            word_tail: vec![],
            target: Scalar::Z(0.into()),
            carrier: vec![],
            images: vec![],
        })),
    };
    crate::observed::call::Iteration {
        member: crate::observed::call::Member::SetElement(Scalar::Path(Box::new(path))),
        ..iteration(source, domain)
    }
}

#[test]
fn newly_copied_non_reflexive_iteration_still_requires_comparison() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    g.iterations.push(non_reflexive_path_iteration(0, 0));
    let saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    assert!(
        !saved.matches(&g, &c).unwrap(),
        "copying an invalid Path must not certify it"
    );
}

#[test]
fn appended_uncompared_iteration_is_not_certified_by_snapshot_extension() {
    let c = quiet();
    let mut g = Graph::new(&c);
    g.push(node(1)).unwrap();
    g.iterations.push(iteration(0, 0));
    let mut saved = ValidationSnapshot::from_graph(&g, &c).unwrap();
    assert!(saved.matches(&g, &c).unwrap());
    saved.extend_matching(&g, &c).unwrap();
    let fresh = g.push(node(2)).unwrap();
    g.iterations
        .push(non_reflexive_path_iteration(fresh.0, fresh.0));
    assert!(
        saved.matches(&g, &c).unwrap(),
        "fresh source/domain preserves old prefix"
    );
    saved.extend_matching(&g, &c).unwrap();
    assert!(
        !saved.matches(&g, &c).unwrap(),
        "new suffix must pass comparison before reuse"
    );
}

#[test]
fn checked_iteration_append_compares_only_the_new_suffix() {
    use std::{cell::Cell, rc::Rc};

    let c = quiet();
    let mut measured = Vec::new();
    for count in [8, 16, 32] {
        let mut graph = Graph::new(&c);
        graph.push(node(1)).unwrap();
        let probes = Rc::new(Cell::new(0));
        let observed = probes.clone();
        let count_checks = Control::new(move |_| {
            observed.set(observed.get() + 1);
            None
        });
        let mut saved = ValidationSnapshot::from_graph(&graph, &c).unwrap();
        for member in 0..count {
            let fresh = graph.push(node(2)).unwrap();
            let mut record = iteration(0, fresh.0);
            record.member = crate::observed::call::Member::ListPosition(member);
            graph.append_iteration(record).unwrap();
            assert!(saved.matches(&graph, &count_checks).unwrap());
            saved.extend_matching(&graph, &count_checks).unwrap();
        }
        measured.push((count, probes.get()));
        assert!(
            saved.iterations.is_empty(),
            "検査付きprefixは内容をコピーしない"
        );
    }
    eprintln!("(iterations, validation checkpoints) {measured:?}");
    assert_eq!(measured[1].1, measured[0].1 * 2);
    assert_eq!(measured[2].1, measured[1].1 * 2);
}

#[test]
fn checked_iteration_append_rejects_invalid_member_and_preserves_registry_invalidation() {
    let c = quiet();
    let mut graph = Graph::new(&c);
    graph.push(node(1)).unwrap();
    let saved = ValidationSnapshot::from_graph(&graph, &c).unwrap();
    let bad = non_reflexive_path_iteration(0, 0);
    assert!(matches!(
        graph.append_iteration(bad),
        Err(ValidationFailure::Internal(_))
    ));
    assert!(graph.iterations.is_empty());
    assert!(saved.matches(&graph, &c).unwrap());

    graph.append_iteration(iteration(0, 0)).unwrap();
    assert!(saved.matches_with_registry(&graph, &c, false).unwrap());
    assert!(
        !saved.matches(&graph, &c).unwrap(),
        "旧producerの追加は一意性を変え得る"
    );
    let saved = ValidationSnapshot::from_graph(&graph, &c).unwrap();
    assert!(saved.matches(&graph, &c).unwrap());
    graph.iterations[0].member = crate::observed::call::Member::ListPosition(1);
    assert!(!saved.matches(&graph, &c).unwrap());
    graph.iterations[0].member = crate::observed::call::Member::ListPosition(0);
    assert!(!saved.matches(&graph, &c).unwrap());
}

#[test]
fn checked_iteration_append_does_not_reuse_a_cloned_table() {
    let c = quiet();
    let mut graph = Graph::new(&c);
    graph.push(node(1)).unwrap();
    graph.append_iteration(iteration(0, 0)).unwrap();
    let saved = ValidationSnapshot::from_graph(&graph, &c).unwrap();
    graph.iterations = graph.iterations.clone();
    assert!(!saved.matches(&graph, &c).unwrap());
}
