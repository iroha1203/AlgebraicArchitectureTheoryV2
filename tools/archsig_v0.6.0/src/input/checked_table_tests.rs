//! 入力準備・元 byte 列への照合の内部反復で、同じ取消を確認する。
use archsig::{
    archmap::{CheckedArchMap, check_archmap},
    canonical::{Json, sha256_digest},
    control::{Checkpoint, Control, StopReason},
    definition::{CheckedDefinitions, check_definitions},
    input::{CheckedInputs, InputBytes, InputFailure, InputSources, InputStatus, check_inputs},
    law::{CheckedLaw, check_law},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &[u8] = include_bytes!("../../tests/fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("../../tests/fixtures/counter.law");
const MAP: &[u8] = include_bytes!("../../tests/fixtures/counter.archmap.json");

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

fn stop(at: usize) -> (Control, Rc<Cell<usize>>, Rc<Cell<bool>>) {
    let seen = Rc::new(Cell::new(0));
    let probe_seen = seen.clone();
    let semantic = Rc::new(Cell::new(false));
    let probe_semantic = semantic.clone();
    let control = Control::new(move |point| {
        if point == Checkpoint::InputBundle {
            probe_seen.set(probe_seen.get() + 1);
        }
        if point == Checkpoint::DefinitionIteration {
            probe_semantic.set(true);
        }
        (probe_seen.get() == at).then_some(Signal::Term)
    });
    (control, seen, semantic)
}

fn assert_stop(failure: &InputFailure, control: &Control, retained: bool) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(!failure.declarations().is_empty(), retained);
    assert_eq!(!failure.primitives().is_empty(), retained);
    assert_eq!(!failure.vocabularies().is_empty(), retained);
    for name in ["requests", "answers", "nodes"] {
        assert_eq!(field(&failure.wire(), name), &Json::Arr(vec![]));
    }
    let reason = StopReason::Cancelled(Signal::Term);
    assert_eq!(control.stop_reason(), Some(reason.clone()));
    assert_eq!(failure.issues(), &[reason.wire()]);
}

#[test]
fn bundle_preparation_checks_every_digest_id_and_file_iteration() {
    let src = sources();
    let count = Rc::new(Cell::new(0));
    let measured = count.clone();
    let mut control = Control::new(move |point| {
        if point == Checkpoint::InputBundle {
            measured.set(measured.get() + 1);
        }
        None
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
        let (mut control, seen, semantic) = stop(at);
        let failure = check_inputs(src.clone(), &mut control).unwrap_err();
        assert_stop(&failure, &control, false);
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

#[test]
fn invalid_identity_reports_cancellation_over_input() {
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
    // 四 SHA・正しい definition0 の後、definition1 の不一致を得た事後確認。
    let (mut control, seen, semantic) = stop(12);
    let failure = check_inputs(src.clone(), &mut control).unwrap_err();
    assert_eq!(seen.get(), 12);
    assert!(!semantic.get());
    assert_eq!(failure.sources(), &src);
    assert_stop(&failure, &control, false);
}

#[test]
fn checked_table_comparison_has_pre_and_post_stops_with_checked_stage_retained() {
    let src = sources();
    for at in [21, 22] {
        let (mut control, seen, _) = stop(at);
        let (definitions, law, map) = tables(&src);
        let failure = CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
            .unwrap_err();
        assert_eq!(seen.get(), at);
        assert_stop(&failure, &control, true);
        assert_eq!(failure.sources(), &src);
        assert!(
            failure
                .inputs()
                .iter()
                .all(|i| i.bytes_digest.is_some() && i.model_digest.is_some())
        );
    }
}

#[test]
fn mismatched_checked_tables_report_cancellation_at_post_comparison() {
    let src = sources();
    let (mut control, seen, _) = stop(22);
    let (mut definitions, law, map) = tables(&src);
    definitions = changed_definitions();
    let failure =
        CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control).unwrap_err();
    assert_eq!(seen.get(), 22);
    assert_eq!(failure.sources(), &src);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    assert_stop(&failure, &control, false);
}

#[test]
fn checked_table_comparison_stops_inside_elements_and_recursive_types() {
    let src = sources();
    let count = Rc::new(Cell::new(0));
    let measured = count.clone();
    let mut control = Control::new(move |point| {
        if point == Checkpoint::TableComparison {
            measured.set(measured.get() + 1);
        }
        None
    });
    let (definitions, law, map) = tables(&src);
    CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control).unwrap();
    let total = count.get();
    assert!(total > 50, "三表の構造内部にも確認点がある");
    for at in [3, total / 3, total * 2 / 3, total - 1] {
        let seen = Rc::new(Cell::new(0));
        let probe = seen.clone();
        let mut control = Control::new(move |point| {
            if point == Checkpoint::TableComparison {
                probe.set(probe.get() + 1);
            }
            (probe.get() == at).then_some(Signal::Term)
        });
        let (definitions, law, map) = tables(&src);
        let failure = CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
            .unwrap_err();
        assert_eq!(seen.get(), at);
        assert_stop(&failure, &control, true);
        assert_eq!(failure.sources(), &src);
    }
}

#[test]
fn internal_comparison_mismatch_stop_preserves_stage() {
    let src = sources();
    for bad_law in [true, false] {
        let changed = || {
            let (mut definitions, law, mut map) = tables(&src);
            if bad_law {
                definitions = changed_definitions();
            } else {
                map.snapshots[0].subjects[0].ty = "Foreign.State".into();
            }
            (definitions, law, map)
        };
        let count = Rc::new(Cell::new(0));
        let measured = count.clone();
        let mut control = Control::new(move |point| {
            if point == Checkpoint::TableComparison {
                measured.set(measured.get() + 1);
            }
            None
        });
        let (definitions, law, map) = changed();
        let plain = CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
            .unwrap_err();
        let at = count.get();
        assert_eq!(plain.status(), InputStatus::Invalid);
        // 最後の比較確認点は、不一致を得た後の外側 compare の事後確認。
        let mut visits = 0;
        let mut control = Control::new(move |point| {
            if point == Checkpoint::TableComparison {
                visits += 1;
            }
            (visits == at).then_some(Signal::Term)
        });
        let (definitions, law, map) = changed();
        let failure = CheckedInputs::from_checked(src.clone(), definitions, law, map, &mut control)
            .unwrap_err();
        assert_eq!(!failure.declarations().is_empty(), !bad_law);
        assert_eq!(!failure.vocabularies().is_empty(), !bad_law);
        assert_stop(&failure, &control, !bad_law);
    }
}

fn changed_definitions() -> archsig::definition::CheckedDefinitions {
    let altered = String::from_utf8(DEFINITIONS.to_vec()).unwrap().replace(
        "実装中の一つのカウンタ状態。",
        "実装中の一つのカウンタ状態。 altered",
    );
    let src = sources();
    let files: Vec<_> = src
        .definitions()
        .iter()
        .enumerate()
        .map(|(i, input)| {
            (
                input.id(),
                if i == 0 {
                    altered.as_bytes()
                } else {
                    input.bytes()
                },
            )
        })
        .collect();
    check_definitions(&files).unwrap()
}

#[test]
fn from_checked_rejects_mutated_map_even_with_original_digests() {
    let definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let law = check_law(LAW, &definitions).unwrap();
    let mut map = check_archmap(MAP, &definitions).unwrap();
    map.snapshots[0].subjects[0].ty = "Foreign.State".into();
    let failure = CheckedInputs::from_checked(
        InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), MAP.to_vec()),
        definitions,
        law,
        map,
        &mut Control::unlimited(),
    )
    .unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(!failure.declarations().is_empty());
    assert!(!failure.vocabularies().is_empty());
}

#[test]
fn from_checked_rejects_internally_mutated_law_tables_and_digests() {
    let src = sources();
    for field_name in [
        "bytes",
        "model",
        "declarations",
        "exprs",
        "types",
        "infos",
        "definitions",
    ] {
        let (definitions, mut law, map) = tables(&src);
        match field_name {
            "bytes" => law.bytes_digest.clear(),
            "model" => law.model_digest.clear(),
            "declarations" => law.declarations.clear(),
            "exprs" => law.exprs.clear(),
            "types" => law.expr_types.clear(),
            "infos" => law.infos.clear(),
            "definitions" => law.definitions = check_definitions(&[]).unwrap(),
            _ => unreachable!(),
        }
        let failure = CheckedInputs::from_checked(
            src.clone(),
            definitions,
            law,
            map,
            &mut Control::unlimited(),
        )
        .unwrap_err();
        assert_eq!(failure.status(), InputStatus::Invalid, "{field_name}");
        assert_eq!(
            field(&failure.issues()[0], "code"),
            &Json::str("vocabulary_mismatch"),
            "{field_name}"
        );
        assert!(failure.declarations().is_empty(), "{field_name}");
    }
}

#[test]
fn from_checked_rejects_internally_mutated_archmap_tables_and_digests() {
    let src = sources();
    for field_name in [
        "bytes",
        "model",
        "vocabularies",
        "sources",
        "origins",
        "snapshots",
    ] {
        let (definitions, law, mut map) = tables(&src);
        match field_name {
            "bytes" => map.bytes_digest.clear(),
            "model" => map.model_digest.clear(),
            "vocabularies" => map.vocabularies.clear(),
            "sources" => map.sources.push(crate::archmap::Source {
                id: "extra".into(),
                uri: "urn:example:extra".into(),
                revision: "r1".into(),
                digest: sha256_digest(b"extra"),
            }),
            "origins" => map.origins.clear(),
            "snapshots" => map.snapshots.clear(),
            _ => unreachable!(),
        }
        let failure = CheckedInputs::from_checked(
            src.clone(),
            definitions,
            law,
            map,
            &mut Control::unlimited(),
        )
        .unwrap_err();
        assert_eq!(failure.status(), InputStatus::Invalid, "{field_name}");
        assert_eq!(
            field(&failure.issues()[0], "code"),
            &Json::str("vocabulary_mismatch"),
            "{field_name}"
        );
        assert!(!failure.declarations().is_empty(), "{field_name}");
    }
}
