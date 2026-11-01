//! 三入力の接続・identity・段階ごとの宣言保持・協調中断の回帰確認。

use archsig::{
    archmap::check_archmap,
    canonical::{Json, sha256_digest},
    control::{Checkpoint, Control, StopReason},
    definition::check_definitions,
    input::{CheckedInputs, InputBytes, InputSources, InputStatus, check_inputs},
    law::check_law,
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/counter.law");
const MAP: &[u8] = include_bytes!("fixtures/counter.archmap.json");

fn sources() -> InputSources {
    InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), MAP.to_vec())
}

fn field<'a>(value: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(fields) = value else {
        panic!("object expected")
    };
    &fields[key]
}

fn array_len(value: &Json) -> usize {
    let Json::Arr(values) = value else {
        panic!("array expected")
    };
    values.len()
}

fn stop_at(target: Checkpoint) -> Control {
    Control::new(move |point| (point == target).then_some(Signal::Int))
}

#[test]
fn checked_bundle_preserves_original_bytes_identities_and_shared_definitions() {
    let inputs = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    assert_eq!(inputs.sources().law().bytes(), LAW);
    assert_eq!(inputs.definitions(), inputs.law().definitions());
    assert_eq!(
        inputs
            .inputs()
            .iter()
            .map(|i| i.id.as_str())
            .collect::<Vec<_>>(),
        ["archmap", "definition0", "law"]
    );
    assert_eq!(
        inputs.inputs()[1].bytes_digest,
        Some(sha256_digest(DEFINITIONS))
    );
    assert!(
        inputs
            .inputs()
            .iter()
            .all(|i| i.model_digest.is_some() && i.path.is_none())
    );
    let metadata = inputs.metadata_wire();
    assert!(array_len(field(&metadata, "declarations")) > inputs.law().infos().len());
    assert_eq!(array_len(field(&metadata, "vocabularies")), 1);
}

#[test]
fn input_id_collisions_and_reserved_ids_are_rejected() {
    let mut src = sources();
    src = InputSources::new(
        vec![InputBytes::new("law", DEFINITIONS)],
        src.law().clone(),
        src.archmap().clone(),
    );
    let failure = check_inputs(src, &mut Control::unlimited()).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(failure.declarations().is_empty());
}

#[test]
fn invalid_or_unsupported_law_keeps_declaration_and_vocabulary_tables_empty() {
    for (law, status) in [
        (b"bad".to_vec(), InputStatus::Invalid),
        (
            String::from_utf8(LAW.to_vec())
                .unwrap()
                .replace("archsig.law/2", "archsig.law/99")
                .into_bytes(),
            InputStatus::Unsupported,
        ),
    ] {
        let src = InputSources::from_bytes(vec![DEFINITIONS.to_vec()], law, MAP.to_vec());
        let failure = check_inputs(src, &mut Control::unlimited()).unwrap_err();
        assert_eq!(failure.status(), status);
        let wire = failure.wire();
        for key in [
            "declarations",
            "vocabularies",
            "requests",
            "answers",
            "nodes",
        ] {
            assert_eq!(array_len(field(&wire, key)), 0);
        }
    }
}

#[test]
fn invalid_archmap_preserves_all_checked_declarations_and_vocabularies() {
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    let src = InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), b"bad".to_vec());
    let failure = check_inputs(src, &mut Control::unlimited()).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(!failure.declarations().is_empty());
    assert!(!failure.primitives().is_empty());
    assert_eq!(failure.vocabularies().len(), 1);
    let metadata = checked.metadata_wire();
    let failed = failure.wire();
    for key in ["declarations", "vocabularies"] {
        assert_eq!(field(&failed, key), field(&metadata, key));
    }
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(array_len(field(&failure.wire(), key)), 0);
    }
}

#[test]
fn cancellation_inside_each_checker_obeys_declaration_stage_rules() {
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    let metadata = checked.metadata_wire();
    for (point, retained) in [
        (Checkpoint::BeforeDefinitions, false),
        (Checkpoint::DefinitionIteration, false),
        (Checkpoint::LawIteration, false),
        (Checkpoint::AfterLaw, true),
        (Checkpoint::BeforeArchMap, true),
        (Checkpoint::ArchMapIteration, true),
        (Checkpoint::AfterArchMap, true),
    ] {
        let failure = check_inputs(sources(), &mut stop_at(point)).unwrap_err();
        assert_eq!(failure.status(), InputStatus::Interrupted, "{point:?}");
        assert_eq!(!failure.declarations().is_empty(), retained, "{point:?}");
        assert_eq!(!failure.vocabularies().is_empty(), retained, "{point:?}");
        if retained {
            let failed = failure.wire();
            for key in ["declarations", "vocabularies"] {
                assert_eq!(field(&failed, key), field(&metadata, key), "{point:?}");
            }
        }
        assert_eq!(field(&failure.issues()[0], "code"), &Json::str("cancelled"));
    }
}

#[test]
fn cancellation_after_multiple_iterations_stops_inside_each_checker() {
    for point in [
        Checkpoint::DefinitionIteration,
        Checkpoint::LawIteration,
        Checkpoint::ArchMapIteration,
    ] {
        let total = Rc::new(Cell::new(0usize));
        let measured = total.clone();
        let mut counting = Control::new(move |current| {
            if current == point {
                measured.set(measured.get() + 1);
            }
            None
        });
        check_inputs(sources(), &mut counting).unwrap();
        assert!(total.get() > 2, "{point:?}");
        let stop_after = total.get() / 2;
        let seen = Rc::new(Cell::new(0usize));
        let probe_seen = seen.clone();
        let mut control = Control::new(move |current| {
            if current == point {
                probe_seen.set(probe_seen.get() + 1);
            }
            (probe_seen.get() == stop_after).then_some(Signal::Term)
        });
        let failure = check_inputs(sources(), &mut control).unwrap_err();
        assert_eq!(seen.get(), stop_after);
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert_eq!(
            control.stop_reason(),
            Some(StopReason::Cancelled(Signal::Term))
        );
        assert_eq!(
            !failure.declarations().is_empty(),
            point == Checkpoint::ArchMapIteration
        );
        assert_eq!(array_len(field(&failure.wire(), "answers")), 0);
    }
}

#[test]
fn from_checked_accepts_matching_tables_and_rejects_mixed_definition_identity() {
    let definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let law = check_law(LAW, &definitions).unwrap();
    let map = check_archmap(MAP, &definitions).unwrap();
    CheckedInputs::from_checked(sources(), definitions, law, map, &mut Control::unlimited())
        .unwrap();

    let mut definitions = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let law = check_law(LAW, &definitions).unwrap();
    let map = check_archmap(MAP, &definitions).unwrap();
    definitions = changed_definitions();
    let failure =
        CheckedInputs::from_checked(sources(), definitions, law, map, &mut Control::unlimited())
            .unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
}

#[test]
fn cloned_controls_share_stop_and_never_resume_after_cancellation() {
    let calls = Rc::new(Cell::new(0));
    let calls_probe = calls.clone();
    let mut control = Control::new(move |_| {
        let n = calls_probe.get() + 1;
        calls_probe.set(n);
        (n >= 2).then_some(Signal::Term)
    });
    let mut helper = control.clone();
    control.checkpoint(Checkpoint::Resolve).unwrap();
    let stopped = helper.checkpoint(Checkpoint::FiniteIteration).unwrap_err();
    assert_eq!(stopped, StopReason::Cancelled(Signal::Term));
    assert_eq!(
        control.checkpoint(Checkpoint::Expression).unwrap_err(),
        stopped
    );
    assert_eq!(calls.get(), 2);
    assert_eq!(control.stop_reason(), Some(stopped));
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
