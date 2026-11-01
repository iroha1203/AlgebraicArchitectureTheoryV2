use super::*;
use crate::control::quiet;
use crate::result::Signal;
fn node(value: i32) -> Node {
    Node {
        ty: NodeType::Value(crate::types::Type::Z),
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
