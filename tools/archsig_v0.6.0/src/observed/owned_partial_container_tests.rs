use super::*;
mod partial_container_fixture {
    use crate as archsig;
    include!("../../tests/common/owned_partial_containers.rs");
}
fn partial_container_result(asks: &[&str]) -> ObservedEvaluation {
    let r = evaluate_observed_bytes(
        partial_container_fixture::input(false, "r1"),
        asks,
        &mut quiet(),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", r.issues);
    r
}
const PARTIAL_CONTAINER_BAD: &str = "x=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/r)";
#[test]
fn partial_container_calls_reject_original_binder_member_and_condition_mutations() {
    let r = partial_container_result(&[PARTIAL_CONTAINER_BAD]);
    assert_eq!(r.status(), "partial");
    // 未確定のcontainer引数は値を出さない。
    let container = r.nodes[owned_condition(&r, 0)].arguments[2];
    let Some(Payload::Evaluation { value, .. }) = &r.nodes[container.0].payload else {
        panic!("container")
    };
    assert!(value.is_none());
    // member値の再検査の代表: containerの要素を書き換えると核が拒否する。
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
    rejects_mutated_prefix(&r, member, |ns| {
        let Some(Payload::Scalar(Scalar::Subject { subject, .. })) = &mut ns[member].payload else {
            panic!("member")
        };
        *subject = "q".into();
    });
}
