//! 入力準備・元 byte 列への照合の内部反復で、同じ取消と予算を確認する。
use archsig::{
    archmap::{CheckedArchMap, check_archmap},
    canonical::{Json, sha256_digest},
    definition::{CheckedDefinitions, check_definitions},
    law::{CheckedLaw, check_law},
    observed::{
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{CheckedInputs, InputBytes, InputFailure, InputSources, InputStatus, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/counter.law");
const MAP: &[u8] = include_bytes!("fixtures/counter.archmap.json");

fn sources() -> InputSources {
    let unused = String::from_utf8(DEFINITIONS.to_vec())
        .unwrap()
        .replace("Counter", "Unused");
    InputSources::from_bytes(
        vec![DEFINITIONS.to_vec(), unused.into_bytes()],
        LAW.to_vec(),
        MAP.to_vec(),
    )
}

fn tables(src: &InputSources) -> (CheckedDefinitions, CheckedLaw, CheckedArchMap) {
    let files: Vec<_> = src
        .definitions()
        .iter()
        .map(|input| (input.id(), input.bytes()))
        .collect();
    let definitions = check_definitions(&files).unwrap();
    let law = check_law(src.law().bytes(), &definitions).unwrap();
    let map = check_archmap(src.archmap().bytes(), &definitions).unwrap();
    (definitions, law, map)
}

fn field<'a>(value: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(fields) = value else {
        panic!("object expected")
    };
    &fields[key]
}

fn stop(at: usize, resource: usize) -> (Control, Rc<Cell<usize>>, Rc<Cell<bool>>) {
    let seen = Rc::new(Cell::new(0));
    let probe_seen = seen.clone();
    let semantic = Rc::new(Cell::new(false));
    let probe_semantic = semantic.clone();
    let limits = Limits {
        time_ms: Some(10),
        memory_mib: Some(10),
    };
    let control = Control::new(limits, move |point| {
        if point == Checkpoint::InputBundle {
            probe_seen.set(probe_seen.get() + 1);
        }
        if point == Checkpoint::DefinitionIteration {
            probe_semantic.set(true);
        }
        let exhausted = probe_seen.get() == at;
        Usage {
            signal: (exhausted && resource == 0).then_some(Signal::Term),
            elapsed_ms: if exhausted && resource == 1 { 11 } else { 0 },
            memory_mib: if exhausted && resource == 2 { 12 } else { 0 },
        }
    });
    (control, seen, semantic)
}

fn assert_stop(failure: &InputFailure, control: &Control, resource: usize, retained: bool) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(!failure.declarations().is_empty(), retained);
    assert_eq!(!failure.primitives().is_empty(), retained);
    assert_eq!(!failure.vocabularies().is_empty(), retained);
    for name in ["requests", "answers", "nodes"] {
        assert_eq!(field(&failure.wire(), name), &Json::Arr(vec![]));
    }
    let reason = match resource {
        0 => StopReason::Cancelled(Signal::Term),
        1 => StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 10,
            observed: 11,
        },
        _ => StopReason::BudgetExhausted {
            resource: Resource::MemoryMib,
            limit: 10,
            observed: 12,
        },
    };
    assert_eq!(control.stop_reason(), Some(reason.clone()));
    assert_eq!(failure.issues(), &[reason.wire()]);
}

#[test]
fn bundle_preparation_checks_every_digest_id_and_file_iteration() {
    let src = sources();
    let count = Rc::new(Cell::new(0));
    let measured = count.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::InputBundle {
            measured.set(measured.get() + 1);
        }
        Usage::default()
    });
    let checked = check_inputs(src.clone(), &mut control).unwrap();
    assert_eq!(count.get(), 20); // 四 SHA、四 ID、二つの定義参照、それぞれ前後。
    assert_eq!(checked.sources(), &src);
    assert!(
        checked
            .inputs()
            .iter()
            .all(|i| i.bytes_digest.is_some() && i.model_digest.is_some())
    );
    for at in 1..=count.get() {
        for resource in 0..3 {
            let (mut control, seen, semantic) = stop(at, resource);
            let failure = check_inputs(src.clone(), &mut control).unwrap_err();
            assert_stop(&failure, &control, resource, false);
            assert_eq!(seen.get(), at);
            assert!(!semantic.get(), "入力準備の停止後に定義検査を開始しない");
            assert_eq!(failure.sources(), &src);
            assert_eq!(failure.inputs().len(), 4);
            let digests = (at / 2).min(4);
            for (index, input) in failure.inputs().iter().enumerate() {
                assert!(input.read);
                assert!(input.model_digest.is_none());
                let bytes = match input.id.as_str() {
                    "archmap" => src.archmap().bytes(),
                    "definition0" => src.definitions()[0].bytes(),
                    "definition1" => src.definitions()[1].bytes(),
                    "law" => src.law().bytes(),
                    _ => panic!("unexpected identity"),
                };
                assert_eq!(
                    input.bytes_digest,
                    (index < digests).then(|| sha256_digest(bytes))
                );
            }
        }
    }
}

#[test]
fn invalid_identity_preserves_input_error_over_budget_and_cancellation_over_input() {
    let valid = sources();
    let src = InputSources::new(
        vec![
            valid.definitions()[0].clone(),
            InputBytes::new("unknown", valid.definitions()[1].bytes()),
        ],
        valid.law().clone(),
        valid.archmap().clone(),
    );
    let plain = check_inputs(src.clone(), &mut Control::unlimited()).unwrap_err();
    assert_eq!(plain.status(), InputStatus::Invalid);
    assert!(plain.inputs().iter().all(|i| i.bytes_digest.is_some()));
    for resource in 0..3 {
        // 四 SHA・正しい definition0 の後、definition1 の不一致を得た事後確認。
        let (mut control, seen, semantic) = stop(12, resource);
        let failure = check_inputs(src.clone(), &mut control).unwrap_err();
        assert_eq!(seen.get(), 12);
        assert!(!semantic.get());
        assert_eq!(failure.sources(), &src);
        if resource == 0 {
            assert_stop(&failure, &control, resource, false);
        } else {
            assert_eq!(failure.status(), InputStatus::Invalid);
            assert_eq!(&failure.issues()[1..], plain.issues());
            assert_eq!(failure.issues()[0], control.stop_reason().unwrap().wire());
            assert!(failure.declarations().is_empty());
            assert!(failure.vocabularies().is_empty());
            assert!(matches!(
                control.stop_reason(),
                Some(StopReason::BudgetExhausted { .. })
            ));
        }
    }
}

#[test]
fn checked_table_comparison_has_pre_and_post_stops_with_checked_stage_retained() {
    let src = sources();
    for at in [21, 22] {
        for resource in 0..3 {
            let (mut control, seen, _) = stop(at, resource);
            let (definitions, law, map) = tables(&src);
            let failure =
                CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
                    .unwrap_err();
            assert_eq!(seen.get(), at);
            assert_stop(&failure, &control, resource, true);
            assert_eq!(failure.sources(), &src);
            assert!(
                failure
                    .inputs()
                    .iter()
                    .all(|i| i.bytes_digest.is_some() && i.model_digest.is_some())
            );
        }
    }
}

#[test]
fn mismatched_checked_tables_preserve_error_and_stage_at_post_comparison_budget() {
    let src = sources();
    for resource in 0..3 {
        let (mut control, seen, _) = stop(22, resource);
        let (mut definitions, law, map) = tables(&src);
        definitions
            .declarations
            .values_mut()
            .next()
            .unwrap()
            .meaning
            .push_str(" altered");
        let failure = CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
            .unwrap_err();
        assert_eq!(seen.get(), 22);
        assert_eq!(failure.sources(), &src);
        assert!(failure.declarations().is_empty());
        assert!(failure.primitives().is_empty());
        assert!(failure.vocabularies().is_empty());
        if resource == 0 {
            assert_stop(&failure, &control, resource, false);
        } else {
            assert_eq!(failure.status(), InputStatus::Invalid);
            assert_eq!(failure.issues()[0], control.stop_reason().unwrap().wire());
            assert_eq!(
                field(&failure.issues()[1], "code"),
                &Json::str("vocabulary_mismatch")
            );
        }
    }
}
