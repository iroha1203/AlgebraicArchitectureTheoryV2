use super::*;
use archsig_common::control::quiet;
use archsig_input::result::Signal;
fn node(value: i32) -> Node {
    Node {
        ty: NodeType::Value(archsig_common::types::Type::Z),
        payload: Some(Payload::Scalar(Scalar::Z(value.into()))),
        rule: Rule::Construction("evaluation"),
        arguments: vec![],
        support: vec![],
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
    assert!(saved.matches(&b, &c).unwrap());
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
    assert!(saved.matches(&g, &c).unwrap());
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
    assert_eq!(saved.iterations, g.iterations);
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
