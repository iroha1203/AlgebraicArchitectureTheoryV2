//! 三入力試験で、整合補完の全件と各補完内のwhole判断を確認する。
use archsig::{canonical::Json, observed::ObservedEvaluation};
use std::collections::{BTreeMap, BTreeSet};

fn object(value: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(fields) = value else {
        panic!("object")
    };
    fields
}
fn field<'a>(value: &'a Json, name: &str) -> &'a Json {
    &object(value)[name]
}
fn array(value: &Json) -> &[Json] {
    let Json::Arr(values) = value else {
        panic!("array")
    };
    values
}
fn node<'a>(wire: &'a Json, reference: &Json) -> &'a Json {
    array(field(wire, "nodes"))
        .iter()
        .find(|node| field(node, "id") == field(reference, "node"))
        .unwrap()
}

pub fn established_cases<'a>(wire: &'a Json, id: &str, expected: u64) -> (&'a Json, Vec<&'a Json>) {
    let answer = array(field(wire, "answers"))
        .iter()
        .find(|answer| field(answer, "id") == &Json::str(id))
        .unwrap();
    assert_eq!(field(answer, "status"), &Json::str("established"));
    assert_eq!(
        field(field(answer, "scope"), "domain"),
        &Json::str("all_completions")
    );
    let proofs: Vec<_> = array(field(answer, "evidence"))
        .iter()
        .map(|reference| field(node(wire, reference), "value"))
        .filter(|value| field(value, "kind") == &Json::str("finite_exhaustion"))
        .collect();
    assert_eq!(proofs.len(), 1);
    let data = field(proofs[0], "data");
    assert_eq!(field(data, "checked"), &Json::Nat(expected));
    let domain = node(wire, field(data, "domain"));
    let members = array(field(field(domain, "value"), "elements"));
    let instances = array(field(data, "instances"));
    assert_eq!(members.len() as u64, expected);
    assert_eq!(instances.len() as u64, expected);
    assert_eq!(
        members
            .iter()
            .map(Json::canonical)
            .collect::<BTreeSet<_>>()
            .len(),
        members.len()
    );
    assert_eq!(
        instances
            .iter()
            .map(Json::canonical)
            .collect::<BTreeSet<_>>()
            .len(),
        instances.len()
    );
    let mut cases = Vec::new();
    for reference in instances {
        let evaluation = node(wire, reference);
        assert_eq!(field(evaluation, "type"), &Json::str("Evaluation"));
        let value = node(wire, field(field(evaluation, "value"), "value"));
        assert_eq!(field(value, "type"), &Json::str("Bool"));
        assert_eq!(field(value, "value"), &Json::Bool(true));
        cases.push(evaluation);
    }
    let claim = node(wire, field(answer, "claim"));
    assert_eq!(
        field(field(claim, "judgment"), "status"),
        field(answer, "status")
    );
    assert_eq!(
        field(field(claim, "judgment"), "evidence"),
        field(answer, "evidence")
    );
    (domain, cases)
}

pub fn original_owner_is_missing(result: &ObservedEvaluation, snapshot: &str) {
    let subject = result
        .prepared()
        .inputs()
        .archmap()
        .snapshots
        .iter()
        .find(|entry| entry.id == snapshot)
        .unwrap()
        .subjects
        .iter()
        .find(|subject| subject.id == "p")
        .unwrap();
    let owner = subject
        .fields
        .iter()
        .find(|field| field.name == "Reservations.State.owner")
        .unwrap();
    assert!(matches!(owner.slot, archsig::archmap::Slot::Missing));
}
