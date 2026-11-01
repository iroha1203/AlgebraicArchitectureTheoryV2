//! 定義manifestとmodel identityの正規化も、入力検査の同じ中断制御に従う。
use crate::common;

use archsig_common::{
    canonical::{Json, sha256_digest},
    control::{Checkpoint, Control},
};
use archsig_computation::observed::{PrepareFailure, prepare_observed};
use archsig_input::{
    definition::{check_definitions, check_definitions_controlled},
    input::{InputFailure, InputSources, InputStatus, check_inputs},
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
    let digest = &checked.vocabularies()["V"].digest;
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

fn probe(at: Option<usize>) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |point| {
        if point == Checkpoint::DefinitionCanonical {
            seen.set(seen.get() + 1);
        }
        (at == Some(seen.get())).then_some(Signal::Term)
    });
    (control, count)
}

fn stopped(failure: InputFailure, expected: Signal, count: &Cell<usize>, at: usize) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(failure.issues(), &[expected.issue()]);
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
    let (control, total) = probe(None);
    prepare_observed(source.clone(), &["v=evaluate(R.value)"], &control).unwrap();
    assert!(total.get() > 20);
    let expected = Signal::Term;
    for at in [1, total.get() / 2, total.get()] {
        let (control, count) = probe(Some(at));
        let failure = check_inputs(source.clone(), &control).unwrap_err();
        stopped(failure, expected, &count, at);
        let (control, count) = probe(Some(at));
        let PrepareFailure::Inputs(failure) =
            prepare_observed(source.clone(), &["v=evaluate(R.value)"], &control).unwrap_err()
        else {
            panic!("definition stage")
        };
        stopped(*failure, expected, &count, at);
    }
}

#[test]
fn normalization_visits_nested_types_each_field_and_escaped_string_chunk() {
    let count = |fields, nested, meaning| {
        let text = definition(fields, nested, meaning);
        let (control, total) = probe(None);
        let controlled =
            check_definitions_controlled(&[("definition0", text.as_bytes())], &control).unwrap();
        let ordinary = check_definitions(&[("definition0", text.as_bytes())]).unwrap();
        assert_eq!(ordinary, controlled);
        assert_eq!(
            controlled.vocabularies()["V"].digest,
            sha256_digest(
                controlled.vocabularies()["V"]
                    .manifest
                    .canonical()
                    .as_bytes()
            )
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
    assert_eq!(escaped, fields, "短い文字列は同じ区切り数で確認する");
    let long = count(3, true, &"x\"\\\n雪".repeat(300));
    assert!(long > escaped + 20, "string chunks: {escaped}/{long}");
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
        let (control, total) = probe(None);
        let failure = check_inputs(source.clone(), &control).unwrap_err();
        assert_eq!(failure.status(), status);
        assert!(failure.primitives().is_empty());
        assert!(failure.declarations().is_empty());
        assert!(failure.vocabularies().is_empty());
        assert_eq!(total.get(), 3, "byte digest before/after and error exit");
        let (control, count) = probe(Some(total.get()));
        let failure = check_inputs(source.clone(), &control).unwrap_err();
        stopped(failure, Signal::Term, &count, total.get());
    }
}
