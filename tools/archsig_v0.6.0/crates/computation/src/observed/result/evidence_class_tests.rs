use super::*;

fn evidence(payload: Option<Payload>) -> Node {
    Node {
        ty: NodeType::Evidence,
        rule: Rule::Construction("evidence"),
        arguments: vec![],
        payload,
        support: vec![].into(),
        scope: Scope::default(),
        reasons: vec![],
        evidence: vec![],
        judgment: None,
    }
}

#[test]
fn ordinary_examples_keep_their_wire_kind_and_class() {
    let left = NodeRef(0);
    let right = NodeRef(1);
    let examples = [
        Payload::Counterexample {
            bindings: vec![],
            left,
            right,
            facts: vec![],
        },
        Payload::PathCounterexample {
            bindings: vec![],
            left,
            right,
            facts: vec![],
        },
        Payload::OwnedCallCounterexample {
            bindings: vec![],
            left,
            right,
            facts: vec![],
        },
        Payload::ProjectionCounterexample {
            left,
            right,
            facts: vec![],
        },
        Payload::TermCounterexample {
            bindings: vec![],
            left,
            right,
            facts: vec![],
        },
        Payload::CompletionPair {
            fields: vec![],
            first: vec![left],
            second: vec![right],
            first_result: left,
            second_result: right,
        },
    ];
    for (index, payload) in examples.into_iter().enumerate() {
        let expected = if index == 5 {
            "completion_pair"
        } else {
            "counterexample"
        };
        let Json::Obj(ref wire) = payload.wire() else {
            panic!("evidence payload")
        };
        assert_eq!(wire.get("kind"), Some(&Json::str(expected)));
        assert_eq!(
            evidence(Some(payload)).evidence_class(),
            EvidenceClass::Example
        );
    }
}

#[test]
fn ordinary_proofs_and_absent_payload_remain_proofs() {
    let a = NodeRef(0);
    let proofs = [
        Payload::FiniteExhaustion {
            domain: a,
            checked: 0,
            instances: vec![],
        },
        Payload::EvaluationEvidence {
            instance: a,
            lhs: a,
            rhs: a,
            residual: None,
        },
        Payload::Normalization {
            before: a,
            after: a,
            steps: vec![],
        },
    ];
    for payload in proofs {
        assert_eq!(
            evidence(Some(payload)).evidence_class(),
            EvidenceClass::Proof
        );
    }
    assert_eq!(evidence(None).evidence_class(), EvidenceClass::Proof);
    let mut non_evidence = evidence(Some(Payload::Counterexample {
        bindings: vec![],
        left: a,
        right: a,
        facts: vec![],
    }));
    non_evidence.ty = NodeType::Proposition;
    assert_eq!(non_evidence.evidence_class(), EvidenceClass::Proof);
}

#[test]
fn sealed_native_wire_classification_reads_only_top_level_kind() {
    for (name, expected) in [
        ("counterexample", EvidenceClass::Example),
        ("completion_pair", EvidenceClass::Example),
        ("separating_pair", EvidenceClass::Example),
        ("completion_fibers", EvidenceClass::Completion),
        ("finite_exhaustion", EvidenceClass::Proof),
        ("future_evidence", EvidenceClass::Proof),
    ] {
        let wire = Json::obj([("kind", Json::str(name)), ("data", Json::Arr(vec![]))]);
        assert_eq!(
            EvidenceKind::from_wire(&wire).map_or(EvidenceClass::Proof, EvidenceKind::class),
            expected
        );
    }
    for wire in [
        Json::obj([]),
        Json::obj([("kind", Json::Nat(1))]),
        Json::obj([("data", Json::obj([("kind", Json::str("counterexample"))]))]),
        Json::Arr(vec![]),
    ] {
        assert_eq!(EvidenceKind::from_wire(&wire), None);
    }
}
