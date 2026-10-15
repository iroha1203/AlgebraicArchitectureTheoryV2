//! 定義manifestとmodel identityの正規化も、入力検査の同じ中断制御に従う。
mod common;

use archsig::{
    canonical::{Json, sha256_digest},
    definition::{check_definitions, check_definitions_controlled},
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
        prepare_observed,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn definition(fields: usize, nested: bool, meaning: &str) -> String {
    let ty = if nested {
        r#"["Tuple","Bool",["List",["Option","Z"]]]"#
    } else {
        r#""Bool""#
    };
    let fields = (0..fields)
        .map(|i| common::field_json(&format!("f{i}"), ty))
        .collect::<Vec<_>>()
        .join(",");
    let root = common::entity_json("V.Root", "[]", &format!("[{fields}]"));
    let choice = common::data_json(
        "V.Choice",
        &format!(
            "[{},{}]",
            common::constructor_json("Empty", "[]"),
            common::constructor_json("Pair", &format!("[{ty},{ty}]"))
        ),
    );
    common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{root},{choice}]"), "[]")
    ))
    .replace("\"test field\"", &Json::str(meaning).canonical())
}

fn sources(definition: &str) -> InputSources {
    let checked = check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["V"].digest;
    let law = format!("{}reading R {{ view value(): Z = 1; }}", common::HEADER);
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[],"snapshots":[]}}"#
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn probe(at: Option<(usize, u8)>) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(
        Limits {
            time_ms: at.filter(|(_, kind)| *kind == 1).map(|_| 1),
            memory_mib: at.filter(|(_, kind)| *kind == 2).map(|_| 1),
        },
        move |point| {
            if point == Checkpoint::DefinitionCanonical {
                seen.set(seen.get() + 1);
            }
            let kind = at.filter(|(n, _)| seen.get() == *n).map(|(_, kind)| kind);
            Usage {
                signal: (kind == Some(0)).then_some(Signal::Term),
                elapsed_ms: u128::from(kind == Some(1)),
                memory_mib: u128::from(kind == Some(2)),
            }
        },
    );
    (control, count)
}

fn reason(kind: u8) -> StopReason {
    match kind {
        0 => StopReason::Cancelled(Signal::Term),
        1 => StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 1,
            observed: 1,
        },
        _ => StopReason::BudgetExhausted {
            resource: Resource::MemoryMib,
            limit: 1,
            observed: 1,
        },
    }
}

fn stopped(failure: InputFailure, expected: StopReason, count: &Cell<usize>, at: usize) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(failure.issues(), &[expected.wire()]);
    assert!(failure.primitives().is_empty());
    assert!(failure.declarations().is_empty());
    assert!(failure.vocabularies().is_empty());
    assert_eq!(failure.inputs().len(), 3);
    let Json::Obj(ref fields) = failure.wire() else {
        panic!("object")
    };
    for name in ["requests", "answers", "nodes"] {
        assert_eq!(fields[name], Json::Arr(vec![]));
    }
    assert_eq!(count.get(), at);
}

#[test]
fn definition_manifest_and_model_canonicalization_stop_from_bytes_at_internal_boundaries() {
    let source = sources(&definition(3, true, "quote\" slash\\ newline\n雪"));
    let (mut control, total) = probe(None);
    prepare_observed(source.clone(), &["v=evaluate(R.value)"], &mut control).unwrap();
    assert!(total.get() > 20);
    for at in [1, total.get() / 2, total.get()] {
        for kind in 0..3 {
            let (mut control, count) = probe(Some((at, kind)));
            let failure = check_inputs(source.clone(), &mut control).unwrap_err();
            stopped(failure, reason(kind), &count, at);
            let (mut control, count) = probe(Some((at, kind)));
            let PrepareFailure::Inputs(failure) =
                prepare_observed(source.clone(), &["v=evaluate(R.value)"], &mut control)
                    .unwrap_err()
            else {
                panic!("definition stage")
            };
            stopped(*failure, reason(kind), &count, at);
        }
    }
}

#[test]
fn normalization_visits_nested_types_each_field_and_escaped_string_character() {
    let count = |fields, nested, meaning| {
        let text = definition(fields, nested, meaning);
        let (mut control, total) = probe(None);
        let controlled =
            check_definitions_controlled(&[("definition0", text.as_bytes())], &mut control)
                .unwrap();
        let ordinary = check_definitions(&[("definition0", text.as_bytes())]).unwrap();
        assert_eq!(ordinary, controlled);
        assert_eq!(
            controlled.vocabularies["V"].digest,
            sha256_digest(controlled.vocabularies["V"].manifest.canonical().as_bytes())
        );
        total.get()
    };
    let scalar = count(1, false, "x");
    let nested = count(1, true, "x");
    let fields = count(3, true, "x");
    let escaped = count(3, true, "x\"\\\n雪");
    assert!(
        nested > scalar + 20,
        "nested type components: {scalar}/{nested}"
    );
    assert!(fields > nested + 20, "field conversion: {nested}/{fields}");
    assert!(
        escaped > fields + 20,
        "string scalar traversal: {fields}/{escaped}"
    );
}

#[test]
fn definition_errors_keep_their_stage_and_cannot_hide_final_canonical_stop() {
    let valid = definition(1, false, "x");
    let source = sources(&valid);
    for (bad, status) in [
        (
            valid.replacen("\"vocabularies\":", "\"extra\":0,\"vocabularies\":", 1),
            InputStatus::Invalid,
        ),
        (
            valid.replacen("archsig.atom-definition/1", "archsig.atom-definition/99", 1),
            InputStatus::Unsupported,
        ),
    ] {
        let source = InputSources::from_bytes(
            vec![bad.into_bytes()],
            source.law().bytes().to_vec(),
            source.archmap().bytes().to_vec(),
        );
        let (mut control, total) = probe(None);
        let failure = check_inputs(source.clone(), &mut control).unwrap_err();
        assert_eq!(failure.status(), status);
        assert!(failure.primitives().is_empty());
        assert!(failure.declarations().is_empty());
        assert!(failure.vocabularies().is_empty());
        assert_eq!(total.get(), 3, "byte digest before/after and error exit");
        for kind in 0..3 {
            let (mut control, count) = probe(Some((total.get(), kind)));
            stopped(
                check_inputs(source.clone(), &mut control).unwrap_err(),
                reason(kind),
                &count,
                total.get(),
            );
        }
    }
}
