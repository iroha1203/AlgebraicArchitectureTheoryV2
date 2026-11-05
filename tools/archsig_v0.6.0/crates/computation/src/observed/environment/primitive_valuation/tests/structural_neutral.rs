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
    // probeは所属で枝刈りしない。初回に検査した同じ二表を完成判定へ渡す。
    let template = Environment::new(inputs, &quiet()).unwrap();
    let probe = template
        .primitive_dependency_probe_from(values, &quiet())
        .unwrap();
    assert_eq!(
        probe.primitive_constraints_hold(&quiet()).unwrap(),
        expected
    );
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
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Token",
                    "Pattern.Token.Right".into(),
                )
                .expect("valid Data constructor"),
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
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Token",
                    "Pattern.Token.Right".into(),
                )
                .expect("valid Data constructor"),
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
                constructor: crate::observed::result::DataConstructor::new(
                    "Pattern.Token",
                    "Pattern.Token.Left".into(),
                )
                .expect("valid Data constructor"),
                args: vec![fp("2", 0)],
            },
        )],
        true,
    );
}

#[test]
fn checked_probe_constraints_leave_evaluation_read_tracking_unchanged() {
    let inputs = fixture::inputs();
    let template = Environment::new(&inputs, &quiet()).unwrap();
    // 空Mapは型とencodingが正しくても元の登録域を覆わない。
    let values = [(slot("p", "table"), table("Part", &[]))];
    let probe = template
        .primitive_dependency_probe_from(&values, &quiet())
        .unwrap();
    *probe.state.primitive_reads.borrow_mut() = Some(BTreeSet::new());
    *probe.state.missing_slot_reads.borrow_mut() = Some(BTreeSet::new());
    let scalar_values = probe.indexes.primitive_valuation.clone();
    assert!(!probe.primitive_constraints_hold(&quiet()).unwrap());
    assert_eq!(
        probe.state.primitive_reads.borrow().as_ref().unwrap(),
        &BTreeSet::new()
    );
    assert_eq!(
        probe.state.missing_slot_reads.borrow().as_ref().unwrap(),
        &BTreeSet::new()
    );
    assert_eq!(probe.indexes.primitive_valuation, scalar_values);
}

#[test]
fn checked_probe_constraints_propagate_solver_and_final_adoption_stop() {
    let inputs = fixture::inputs();
    let template = Environment::new(&inputs, &quiet()).unwrap();
    let reference = [(slot("p", "link"), subject_value("q", "Part"))];
    let probe = template
        .primitive_dependency_probe_from(&reference, &quiet())
        .unwrap();
    let (control, _, _) = stopping(Checkpoint::Completion, 1, Some(Signal::Term), false);
    assert!(matches!(
        probe.primitive_constraints_hold(&control),
        Err(ValidationFailure::Stop(Signal::Term))
    ));

    let neutral = [(slot("p", "flag"), Scalar::Bool(false))];
    let probe = template
        .primitive_dependency_probe_from(&neutral, &quiet())
        .unwrap();
    let (control, count, _) = stopping(Checkpoint::PrimitiveValuation, usize::MAX, None, false);
    assert!(probe.primitive_constraints_hold(&control).unwrap());
    let (control, _, _) = stopping(
        Checkpoint::PrimitiveValuation,
        count.get(),
        Some(Signal::Int),
        false,
    );
    assert!(matches!(
        probe.primitive_constraints_hold(&control),
        Err(ValidationFailure::Stop(Signal::Int))
    ));
}

#[test]
fn checked_probe_term_reencoding_preserves_wire_after_source_relocation() {
    let inputs = fixture::inputs();
    let template = Environment::new(&inputs, &quiet()).unwrap();
    let term = expression(&template, "literal", false).known_value.unwrap();
    let encoded = data::input_json(&term, &quiet()).unwrap();
    let position = slot("p", "program");
    let probe = template
        .primitive_dependency_probe_from(&[(position.clone(), term)], &quiet())
        .unwrap();
    let checked = &probe.indexes.primitive_valuation.as_ref().unwrap()[&position];
    assert_eq!(data::input_json(checked, &quiet()).unwrap(), encoded);
    assert!(probe.primitive_constraints_hold(&quiet()).unwrap());
    let (control, _, _) = stopping(Checkpoint::Completion, 1, Some(Signal::Term), false);
    assert!(matches!(
        probe.primitive_constraints_hold(&control),
        Err(ValidationFailure::Stop(Signal::Term))
    ));
}

fn assert_probe_solver_path(inputs: &CheckedInputs, values: &[(Fact, Scalar)], skip: bool) {
    let template = Environment::new(inputs, &quiet()).unwrap();
    let probe = template
        .primitive_dependency_probe_from(values, &quiet())
        .unwrap();
    // Inject only after decoding: a Completion stop now identifies structural fallback.
    let (control, count, _) = stopping(Checkpoint::Completion, 1, Some(Signal::Term), false);
    if skip {
        assert!(probe.primitive_constraints_hold(&control).unwrap());
        assert_eq!(count.get(), 0);
    } else {
        assert!(matches!(
            probe.primitive_constraints_hold(&control),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
        assert!(count.get() > 0);
    }
}

#[test]
fn unchanged_known_refs_mix_with_pure_pins_but_missing_and_changed_refs_fall_back() {
    let inputs = fixture::inputs();
    let same = vec![
        (slot("p", "link"), subject_value("p", "Part")),
        (slot("p", "flag"), Scalar::Bool(false)),
    ];
    assert_admission(&inputs, &same, true);
    assert_probe_solver_path(&inputs, &same, true);
    for values in [
        vec![(slot("q", "link"), subject_value("p", "Part"))],
        vec![(slot("p", "link"), subject_value("q", "Part"))],
        vec![
            (slot("p", "link"), subject_value("p", "Part")),
            (slot("p", "owner"), subject_value("r2", "Root")),
        ],
        vec![
            (slot("p", "link"), subject_value("p", "Part")),
            (slot("p", "table"), table("Part", &[])),
        ],
    ] {
        assert_admission(&inputs, &values, legacy_admissible(&inputs, &values));
        assert_probe_solver_path(&inputs, &values, false);
    }
}

#[test]
fn unchanged_known_owned_ref_preserves_member_and_changed_owner_still_falls_back() {
    use archsig_input::input::{InputSources, check_inputs};
    let base = fixture::inputs();
    let definitions = String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap();
    let before = r#"{"name":"link","type":["Ref","Pattern.Part"]"#;
    let after = r#"{"name":"link","type":["Owned","Pattern.Part","owner"]"#;
    assert!(definitions.contains(before));
    let definitions = definitions.replace(before, after);
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let old_digest = &base.definitions().vocabularies()["Pattern"].digest;
    let digest = &checked.vocabularies()["Pattern"].digest;
    let law = String::from_utf8(base.sources().law().bytes().to_vec())
        .unwrap()
        .replace(old_digest, digest);
    let map = String::from_utf8(base.sources().archmap().bytes().to_vec())
        .unwrap()
        .replace(old_digest, digest)
        .replace(
            r#""field":"Pattern.Part.link","value":["v","p"]"#,
            r#""field":"Pattern.Part.link","value":["v","q"]"#,
        );
    let inputs = check_inputs(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &quiet(),
    )
    .unwrap();
    let same = vec![
        (slot("p", "link"), subject_value("q", "Part")),
        (slot("p", "flag"), Scalar::Bool(false)),
    ];
    assert_admission(&inputs, &same, true);
    assert_probe_solver_path(&inputs, &same, true);
    let mut changed_owner = same;
    changed_owner.push((slot("p", "owner"), subject_value("r2", "Root")));
    assert_admission(&inputs, &changed_owner, false);
    assert_probe_solver_path(&inputs, &changed_owner, false);
}

#[test]
fn known_ref_match_requires_both_identity_parts_and_a_top_level_known_slot() {
    let inputs = fixture::inputs();
    let template = Environment::new(&inputs, &quiet()).unwrap();
    let field = template
        .indexes
        .field(&template.state, "v", "p", "Pattern.Part.link")
        .unwrap();
    let reference = |snapshot: &str, subject: &str| Value::Ref {
        snapshot: snapshot.into(),
        subject: subject.into(),
    };
    assert!(unchanged_known_reference(&reference("v", "p"), &field.slot));
    assert!(!unchanged_known_reference(
        &reference("other", "p"),
        &field.slot
    ));
    assert!(!unchanged_known_reference(
        &reference("v", "q"),
        &field.slot
    ));
    assert!(!unchanged_known_reference(
        &reference("v", "p"),
        &Slot::Missing
    ));
    assert!(!unchanged_known_reference(
        &Value::Tuple(vec![reference("v", "p")]),
        &field.slot
    ));
    assert!(!unchanged_known_reference(&Value::Map(vec![]), &field.slot));
}

#[test]
fn unchanged_nested_ref_remains_on_structural_solver_path() {
    use archsig_input::input::{InputSources, check_inputs};
    let base = fixture::inputs();
    let definitions = String::from_utf8(base.sources().definitions()[0].bytes().to_vec()).unwrap();
    let before = r#"{"name":"link","type":["Ref","Pattern.Part"]"#;
    let after = r#"{"name":"link","type":["Tuple",["Ref","Pattern.Part"],"Bool"]"#;
    assert!(definitions.contains(before));
    let definitions = definitions.replace(before, after);
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .unwrap();
    let old_digest = &base.definitions().vocabularies()["Pattern"].digest;
    let digest = &checked.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";view chosen(c:Part):Bool=true;}}"
    );
    let map = String::from_utf8(base.sources().archmap().bytes().to_vec())
        .unwrap()
        .replace(old_digest, digest)
        .replace(
            r#""field":"Pattern.Part.link","value":["v","p"]"#,
            r#""field":"Pattern.Part.link","value":[["v","p"],true]"#,
        );
    let inputs = check_inputs(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &quiet(),
    )
    .unwrap();
    let same = [(
        slot("p", "link"),
        Scalar::Tuple(vec![subject_value("p", "Part"), Scalar::Bool(true)]),
    )];
    assert_admission(&inputs, &same, true);
    assert_probe_solver_path(&inputs, &same, false);
}
