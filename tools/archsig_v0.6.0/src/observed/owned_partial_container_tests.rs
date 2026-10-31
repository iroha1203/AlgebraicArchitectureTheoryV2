use super::*;
mod partial_container_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_containers.rs");
}
fn partial_container_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        partial_container_fixture::input(false, "r1"),
        asks,
        &mut named_call_quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    rebuild_for_origin_and_support_recheck(&r, &r.nodes).unwrap();
    r
}
const PARTIAL_CONTAINER_BAD: &str = "x=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/r)";
#[test]
fn partial_container_calls_reject_original_binder_member_and_condition_mutations() {
    let r = partial_container_result(&[PARTIAL_CONTAINER_BAD]);
    assert_eq!(r.status(), "partial");
    let target = owned_condition(&r, 0);
    let edges = r.nodes[target].arguments.clone();
    let n = edges.len();
    let source = edges[0];
    completion_mutation(&r, source.0, |ns| {
        let Some(Payload::Expression { parameters, .. }) = &mut ns[source.0].payload else {
            panic!("source")
        };
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters[0].1, Type::Z);
        parameters.clear();
    });
    let replacement = r.nodes[edges[n - 2].0].payload.clone();
    completion_mutation(&r, edges[n - 3].0, |ns| {
        ns[edges[n - 3].0].payload = replacement.clone()
    });
    let proof = edges[n - 1];
    completion_mutation(&r, proof.0, |ns| {
        ns[proof.0].ty = NodeType::Value(Type::Bool)
    });
    completion_mutation(&r, target, |ns| ns[target].support.clear());
    completion_mutation(&r, target, |ns| ns[target].scope.snapshots.clear());
    completion_mutation(&r, target, |ns| ns[target].scope.quantifiers.clear());
    let container = edges[2];
    let Some(Payload::Evaluation { value, .. }) = &r.nodes[container.0].payload else {
        panic!("container")
    };
    assert!(value.is_none());
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[container.0].payload else {
            panic!("container")
        };
        assert_eq!(parts[0].children.len(), 3);
        parts[0].children.swap(0, 1);
    });
    completion_mutation(&r, container.0, |ns| {
        let Some(Payload::Evaluation { parts, .. }) = &mut ns[container.0].payload else {
            panic!("container")
        };
        parts[0].children.pop();
    });
    let member = r
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, node)| match &node.payload {
            Some(Payload::Scalar(Scalar::Subject { subject, .. }))
                if subject == "r" && i < container.0 =>
            {
                Some(i)
            }
            _ => None,
        })
        .unwrap();
    completion_mutation(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[member].payload else {
            panic!("member")
        };
        *subject = "q".into();
    });
    assert!(!r.frames.iter().any(|f| f.source == source));
}

