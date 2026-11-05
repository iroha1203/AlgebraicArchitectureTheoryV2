use super::*;
use archsig_input::archmap::{FieldAssignment, check_valuation_with_values};

fn legacy_admissible(inputs: &CheckedInputs, values: &[(Fact, Scalar)]) -> bool {
    let pins = values
        .iter()
        .map(|(fact, value)| FieldAssignment {
            snapshot: fact.snapshot.clone(),
            subject: fact.subject.clone(),
            field: fact.field.as_ref().unwrap().to_string(),
            value: data::input_json(value, &quiet()).unwrap(),
        })
        .collect::<Vec<_>>();
    match check_valuation_with_values::<CheckFailure<Box<archsig_common::issue::Issue>>>(
        inputs.archmap().snapshots(),
        inputs.definitions(),
        &pins,
        &quiet(),
    ) {
        Ok(()) => true,
        Err(CheckFailure::Input(issue))
            if issue.code == archsig_common::issue::Code::InconsistentObservation =>
        {
            false
        }
        other => panic!("unexpected legacy check: {other:?}"),
    }
}
fn assert_admission(inputs: &CheckedInputs, values: &[(Fact, Scalar)], expected: bool) {
    assert_eq!(legacy_admissible(inputs, values), expected);
    let actual = Environment::try_primitive_valuation(inputs, values, &quiet()).unwrap();
    assert_eq!(actual.is_some(), expected);
    if let Some(actual) = actual {
        for (fact, value) in values {
            assert_eq!(
                actual
                    .indexes
                    .primitive_valuation
                    .as_ref()
                    .unwrap()
                    .get(fact),
                Some(value)
            );
        }
    }
}

#[test]
fn checked_scalar_and_pure_container_pins_keep_known_and_missing_admission() {
    let inputs = fixture::inputs();
    let values = vec![
        (slot("p", "quantity"), fp("2", 1)),
        (slot("p", "flag"), Scalar::Bool(false)),
        (slot("p", "integer"), Scalar::Z((-123).into())),
        (slot("p", "ratio"), Scalar::Q(2.into(), 3.into())),
        (slot("p", "text"), Scalar::Text("candidate".into())),
        (
            slot("p", "pair"),
            Scalar::Tuple(vec![fp("2", 1), Scalar::Bool(false)]),
        ),
        (
            slot("p", "choice"),
            Scalar::Data {
                family: "Pattern.Token".into(),
                constructor: "Pattern.Token.Right".into(),
                args: vec![fp("2", 1)],
            },
        ),
        (
            slot("p", "sequence"),
            Scalar::List {
                element: Type::Bool,
                items: vec![Scalar::Bool(true), Scalar::Bool(false)],
            },
        ),
        (
            slot("p", "empty"),
            Scalar::List {
                element: Type::Ref("Pattern.Vacant".into()),
                items: vec![],
            },
        ),
        (
            slot("p", "bundle"),
            Scalar::Tuple(vec![
                Scalar::List {
                    element: Type::Bool,
                    items: vec![],
                },
                Scalar::Option {
                    element: Type::Text,
                    value: None,
                },
            ]),
        ),
    ];
    assert_admission(&inputs, &values, true);
    // A Completion stop would reject the legacy structural solver. Pin decoding also
    // uses Completion, so count the already-required per-pin decoder checkpoints.
    let (control, actual_count, _) = stopping(Checkpoint::Completion, usize::MAX, None, false);
    Environment::try_primitive_valuation(&inputs, &values, &control)
        .unwrap()
        .unwrap();
    let mut decoding_count = 0;
    for (fact, value) in &values {
        let field = inputs.archmap().snapshots()[0]
            .subjects
            .iter()
            .find(|s| s.id == fact.subject)
            .unwrap()
            .fields
            .iter()
            .find(|f| Some(&f.name) == fact.field.as_ref())
            .unwrap();
        let (control, count, _) = stopping(Checkpoint::Completion, usize::MAX, None, false);
        archsig_input::archmap::value::check_assignment::<
            CheckFailure<Box<archsig_common::issue::Issue>>,
        >(
            &data::input_json(value, &quiet()).unwrap(),
            &field.ty,
            inputs.definitions(),
            &Environment::new(&inputs, &quiet()).unwrap().indexes.roster,
            "Pattern",
            &control,
        )
        .unwrap();
        decoding_count += count.get();
    }
    assert_eq!(
        actual_count.get(),
        decoding_count,
        "neutral pins still decode, without a second structural check"
    );
}

#[test]
fn references_empty_and_nested_maps_and_owner_changes_keep_structural_checks() {
    let inputs = fixture::inputs();
    assert_admission(
        &inputs,
        &[(slot("p", "link"), subject_value("q", "Part"))],
        true,
    );
    assert_admission(&inputs, &[(slot("p", "table"), table("Part", &[]))], false);
    assert_admission(
        &inputs,
        &[(
            slot("p", "nested"),
            Scalar::Tuple(vec![Scalar::Unit, table("Part", &[])]),
        )],
        false,
    );
    assert_admission(
        &inputs,
        &[(slot("p", "emptytable"), table("Vacant", &[]))],
        true,
    );
    let mut map = fixture::MAP.to_owned();
    let end = map.rfind("]}]}").unwrap();
    map.insert_str(end, r#",{"id":"tp","subject":"p","field":"Pattern.Part.ownedtable","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]]],"origin":"model"}"#);
    let known = fixture::with_map(&map);
    assert_admission(
        &known,
        &[
            (slot("p", "owner"), subject_value("r2", "Root")),
            (slot("p", "flag"), Scalar::Bool(false)),
        ],
        false,
    );
    assert_admission(
        &known,
        &[
            (slot("p", "owner"), subject_value("r2", "Root")),
            (slot("p", "ownedtable"), table("Part", &[("p", "p")])),
        ],
        true,
    );
}

#[test]
fn neutral_value_walk_handles_every_container_and_rejects_ref_map_and_term() {
    let pure = Value::Tuple(vec![
        Value::Unit,
        Value::Bool(true),
        Value::Z(7.into()),
        Value::Q(2.into(), 3.into()),
        Value::Fp(1u32.into()),
        Value::Text("x".into()),
        Value::List(vec![Value::Option(Some(Box::new(Value::Set(vec![
            Value::Bool(false),
        ]))))]),
        Value::Data {
            constructor: "Pattern.Token.Left".into(),
            args: vec![Value::Fp(0u32.into())],
        },
    ]);
    assert!(structural_neutral_value(&pure, &quiet()).unwrap());
    for value in [
        Value::Ref {
            snapshot: "v".into(),
            subject: "p".into(),
        },
        Value::Map(vec![]),
        Value::Option(Some(Box::new(Value::Data {
            constructor: "Pattern.Token.Left".into(),
            args: vec![Value::Map(vec![])],
        }))),
    ] {
        assert!(!structural_neutral_value(&value, &quiet()).unwrap());
    }
    let inputs = fixture::inputs();
    let normal = Environment::new(&inputs, &quiet()).unwrap();
    let term = expression(&normal, "literal", false).known_value.unwrap();
    let field = normal
        .indexes
        .field(&normal.state, "v", "p", "Pattern.Part.program")
        .unwrap();
    let value = archsig_input::archmap::value::check_assignment::<
        CheckFailure<Box<archsig_common::issue::Issue>>,
    >(
        &data::input_json(&term, &quiet()).unwrap(),
        &field.ty,
        inputs.definitions(),
        &normal.indexes.roster,
        "Pattern",
        &quiet(),
    )
    .unwrap();
    assert!(!structural_neutral_value(&value, &quiet()).unwrap());
}

#[test]
fn neutral_walk_and_final_adoption_observe_stop() {
    let mut value = Value::Bool(true);
    for _ in 0..4096 {
        value = Value::Option(Some(Box::new(value)));
    }
    assert!(structural_neutral_value(&value, &quiet()).unwrap());
    let (control, count, _) = stopping(Checkpoint::PrimitiveValuation, usize::MAX, None, false);
    structural_neutral_value(&value, &control).unwrap();
    for at in [1, 2048, count.get()] {
        let (control, _, _) = stopping(
            Checkpoint::PrimitiveValuation,
            at,
            Some(Signal::Term),
            false,
        );
        assert!(matches!(
            structural_neutral_value(&value, &control),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
    }
    let inputs = fixture::inputs();
    let values = [(slot("p", "flag"), Scalar::Bool(false))];
    let (control, count, _) = stopping(Checkpoint::PrimitiveValuation, usize::MAX, None, false);
    Environment::try_primitive_valuation(&inputs, &values, &control)
        .unwrap()
        .unwrap();
    let (control, _, _) = stopping(
        Checkpoint::PrimitiveValuation,
        count.get(),
        Some(Signal::Int),
        false,
    );
    assert!(matches!(
        Environment::try_primitive_valuation(&inputs, &values, &control),
        Err(ValidationFailure::Stop(Signal::Int))
    ));
}

#[test]
fn pure_data_branch_can_remove_a_known_map_cover_without_adding_constraints() {
    use archsig_input::input::{InputSources, check_inputs};
    let base = fixture::inputs();
    let definitions = String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap();
    let right = r#"{"name":"Right","meaning":"右。","arguments":[["Fp","2"]]}"#;
    assert!(definitions.contains(right));
    let definitions = definitions.replace(right, &format!(r#"{right},{{"name":"Table","meaning":"全域表。","arguments":[["Map",["Ref","Pattern.Part"],["Ref","Pattern.Part"]]]}}"#));
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let old_digest = &base.definitions().vocabularies()["Pattern"].digest;
    let new_digest = &checked.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{new_digest}\";view chosen(c:Part):Bool=true;}}"
    );
    let map = String::from_utf8(base.sources().archmap().bytes().to_vec())
        .unwrap()
        .replace(old_digest, new_digest)
        .replace(
            r#""value":{"tag":"Left","args":["0"]}"#,
            r#""value":{"tag":"Table","args":[[[["v","p"],["v","p"]],[["v","q"],["v","q"]]]]}"#,
        );
    assert!(map.contains(r#""tag":"Table""#));
    let inputs = check_inputs(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &quiet(),
    )
    .unwrap();
    assert_admission(
        &inputs,
        &[(
            slot("p", "choice"),
            Scalar::Data {
                family: "Pattern.Token".into(),
                constructor: "Pattern.Token.Right".into(),
                args: vec![fp("2", 1)],
            },
        )],
        true,
    );
    assert_admission(
        &inputs,
        &[(
            slot("q", "choice"),
            Scalar::Data {
                family: "Pattern.Token".into(),
                constructor: "Pattern.Token.Left".into(),
                args: vec![fp("2", 0)],
            },
        )],
        true,
    );
}
