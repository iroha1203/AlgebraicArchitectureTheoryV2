//! 深部schema/QNameの停止が、元byte列からの入力検査と要求準備へ届く。
use crate::common;

use archsig::{
    canonical::Json,
    control::{Checkpoint, Control},
    definition::{check_definitions, check_definitions_controlled},
    input::{InputFailure, InputSources, InputStatus, check_inputs},
    law::{check_law, check_law_controlled},
    observed::{PrepareFailure, prepare_observed},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn definition(fields: usize) -> String {
    let fields = (0..fields)
        .map(|i| common::field_json(&format!("f{i}"), r#"["Tuple","Z",["Term",["Z","Q"],"Z"]]"#))
        .collect::<Vec<_>>()
        .join(",");
    let root = common::entity_json("V.Root", "[]", &format!("[{fields}]"));
    let data = common::data_json(
        "V.Choice",
        &format!(
            "[{},{}]",
            common::constructor_json("Empty", "[]"),
            common::constructor_json("Many", r#"["Z",["Tuple","Z","Q"]]"#)
        ),
    );
    common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{root},{data}]"), "[]")
    ))
}

fn sources(definition: &str) -> InputSources {
    let checked = check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["V"].digest;
    let law = format!(
        "{}reading Helpers {{ view one(): Z = 1; view two(): Z = 2; }} reading R {{ use Helpers as H; view value(): Z = H.one() + H.two(); }}",
        common::HEADER
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"小さい観測","locations":[],"note":"schemaの中断"}}],"snapshots":[{{"id":"s","origin":"o","subjects":[{{"id":"root","type":"V.Root","origin":"o"}}],"atoms":[]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn probe(point: Checkpoint, at: Option<usize>) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        (at == Some(seen.get())).then_some(Signal::Term)
    });
    (control, count)
}

fn assert_stopped(
    failure: InputFailure,
    expected: &Signal,
    control: &mut Control,
    count: &Cell<usize>,
    at: usize,
) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    assert_eq!(failure.issues(), &[expected.issue()]);
    let Json::Obj(ref fields) = failure.wire() else {
        panic!("object")
    };
    for field in [
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "nodes",
    ] {
        assert_eq!(fields[field], Json::Arr(vec![]), "{field}");
    }
    assert_eq!(count.get(), at);
    assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(*expected));
    assert_eq!(count.get(), at, "停止後はprobeを再開しない");
}

#[test]
fn deep_schema_and_multiple_qnames_stop_from_bytes_before_tables_or_requests_are_published() {
    let source = sources(&definition(8));
    for point in [Checkpoint::DefinitionSchema, Checkpoint::LawName] {
        let (complete, total) = probe(point, None);
        let prepared =
            prepare_observed(source.clone(), &["v=evaluate(R.value)"], &complete).unwrap();
        assert_eq!(prepared.requests().evaluation_order(), &[0]);
        assert!(total.get() > 4, "{point:?}");
        let expected = Signal::Term;
        for at in [1, total.get() / 2, total.get()] {
            let (mut control, count) = probe(point, Some(at));
            let failure = check_inputs(source.clone(), &control).unwrap_err();
            assert_stopped(failure, &expected, &mut control, &count, at);
            let (mut control, count) = probe(point, Some(at));
            let PrepareFailure::Inputs(failure) =
                prepare_observed(source.clone(), &["v=evaluate(R.value)"], &control).unwrap_err()
            else {
                panic!("入力検査内の停止")
            };
            assert_stopped(*failure, &expected, &mut control, &count, at);
        }
    }
}

#[test]
fn unlimited_control_preserves_public_definition_and_law_results() {
    for n in [1, 8] {
        let text = definition(n);
        let ordinary = check_definitions(&[("definition0", text.as_bytes())]).unwrap();
        let controlled = check_definitions_controlled(
            &[("definition0", text.as_bytes())],
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(ordinary, controlled);
        let source = sources(&text);
        let ordinary_law = check_law(source.law().bytes(), &ordinary).unwrap();
        let controlled_law =
            check_law_controlled(source.law().bytes(), &controlled, &Control::unlimited()).unwrap();
        assert_eq!(ordinary_law.model_digest(), controlled_law.model_digest());
        assert_eq!(ordinary_law.infos(), controlled_law.infos());
    }
}
