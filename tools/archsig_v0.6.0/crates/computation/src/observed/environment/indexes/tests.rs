use super::*;
use archsig_common::control::quiet;

#[allow(dead_code)]
mod fixture {
    include!("../../../../../../tests/common/primitive_valuation_data.rs");
}

#[test]
fn borrowed_keys_keep_input_storage_order_and_short_lived_queries() {
    let inputs = fixture::inputs();
    let indexes = InputIndexes::new(&inputs, &quiet()).unwrap();
    let mut subjects = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for snapshot in inputs.archmap().snapshots() {
        for subject in &snapshot.subjects {
            subjects.insert((subject.snapshot.clone(), subject.id.clone()), subject);
            for field in &subject.fields {
                fields.insert(
                    (
                        subject.snapshot.clone(),
                        subject.id.clone(),
                        field.name.clone(),
                    ),
                    field,
                );
            }
        }
    }
    let expected_subjects: Vec<_> = subjects
        .iter()
        .map(|((s, id), value)| (s.as_str(), id.as_str(), std::ptr::from_ref(*value)))
        .collect();
    let actual_subjects: Vec<_> = indexes
        .subjects
        .iter()
        .map(|((s, id), value)| (*s, *id, std::ptr::from_ref(*value)))
        .collect();
    assert_eq!(actual_subjects, expected_subjects);
    let expected_fields: Vec<_> = fields
        .iter()
        .map(|((s, id, name), value)| {
            (
                s.as_str(),
                id.as_str(),
                name.as_str(),
                std::ptr::from_ref(*value),
            )
        })
        .collect();
    let actual_fields: Vec<_> = indexes
        .fields
        .iter()
        .map(|((s, id, name), value)| (*s, *id, *name, std::ptr::from_ref(*value)))
        .collect();
    assert_eq!(actual_fields, expected_fields);
    for ((snapshot, id), subject) in &indexes.subjects {
        assert_eq!(snapshot.as_ptr(), subject.snapshot.as_ptr());
        assert_eq!(id.as_ptr(), subject.id.as_ptr());
    }
    for ((snapshot, id, name), field) in &indexes.fields {
        let subject = indexes.subject(snapshot, id).unwrap();
        assert_eq!(snapshot.as_ptr(), subject.snapshot.as_ptr());
        assert_eq!(id.as_ptr(), subject.id.as_ptr());
        assert_eq!(name.as_ptr(), field.name.as_str().as_ptr());
    }
    let state = EvaluationState::default();
    let (subject, field) = {
        let snapshot = String::from("v");
        let id = String::from("p");
        let name = String::from("Pattern.Part.quantity");
        (
            indexes.subject(&snapshot, &id).unwrap(),
            indexes.field(&state, &snapshot, &id, &name).unwrap(),
        )
    };
    assert_eq!(subject.id, "p");
    assert_eq!(field.name, "Pattern.Part.quantity");
    for name in [
        "quantity",
        "Part.quantity",
        "Pattern.Part.Quantity",
        "Pattern.Part.quantity.extra",
    ] {
        assert!(indexes.field(&state, "v", "p", name).is_err());
    }
    assert!(indexes.subject("v", "unknown").is_err());
    assert!(indexes.subject("unknown", "p").is_err());
}

#[test]
fn borrowed_field_lookup_keeps_known_missing_and_read_effects() {
    let inputs = fixture::inputs();
    let indexes = InputIndexes::new(&inputs, &quiet()).unwrap();
    let state = EvaluationState::default();
    state.missing_slot_reads.replace(Some(BTreeSet::new()));
    state.primitive_reads.replace(Some(BTreeSet::new()));
    let slot = |name: &str| {
        Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: "p".into(),
            field: Some(name.into()),
            atom: None,
        })
    };
    let known = indexes
        .field(&state, "v", "p", "Pattern.Part.quantity")
        .unwrap();
    assert!(matches!(known.slot, Slot::Known { .. }));
    assert!(
        state
            .missing_slot_reads
            .borrow()
            .as_ref()
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        state.primitive_reads.borrow().as_ref().unwrap(),
        &BTreeSet::from([slot("Pattern.Part.quantity")])
    );
    for _ in 0..2 {
        let missing = indexes
            .field(&state, "v", "p", "Pattern.Part.third")
            .unwrap();
        assert!(matches!(missing.slot, Slot::Missing));
    }
    assert_eq!(
        state.missing_slot_reads.borrow().as_ref().unwrap(),
        &BTreeSet::from([slot("Pattern.Part.third")])
    );
    let expected = BTreeSet::from([slot("Pattern.Part.quantity"), slot("Pattern.Part.third")]);
    assert_eq!(state.primitive_reads.borrow().as_ref().unwrap(), &expected);
    assert!(
        indexes
            .field(&state, "v", "p", "Pattern.Part.unknown")
            .is_err()
    );
    assert_eq!(state.primitive_reads.borrow().as_ref().unwrap(), &expected);
}
