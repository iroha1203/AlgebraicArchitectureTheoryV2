//! 原始定義の意味検査へ届いた共有中断が、入力不正や false に変わらないことを確かめる。
use archsig::{
    canonical::Json,
    definition::{check_definitions, check_definitions_controlled},
    issue::Code,
    observed::{
        control::{CheckFailure, Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/engine.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/engine.law");
const MAP: &[u8] = include_bytes!("fixtures/engine.archmap.json");

/// 型検査の開始を観測した後、指定した意味検査内の複数回の反復を経て停止する。
fn semantic_control(
    target: Checkpoint,
    after_type: bool,
    stop_after: usize,
) -> (Control, Rc<Cell<usize>>) {
    let calls = Rc::new(Cell::new(0));
    let seen_calls = calls.clone();
    let mut reached_type = false;
    let control = Control::new(Limits::default(), move |point| {
        reached_type |= point == Checkpoint::DefinitionSemantics;
        if point == target && (!after_type || reached_type) {
            seen_calls.set(seen_calls.get() + 1);
        }
        Usage {
            signal: (seen_calls.get() == stop_after).then_some(Signal::Term),
            ..Usage::default()
        }
    });
    (control, calls)
}

fn assert_empty_stage(failure: &archsig::observed::input::InputFailure) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    let Json::Obj(ref fields) = failure.wire() else {
        panic!("object expected")
    };
    for key in [
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "nodes",
    ] {
        assert_eq!(fields[key], Json::Arr(vec![]), "{key}");
    }
    let Json::Obj(issue) = &failure.issues()[0] else {
        panic!("issue expected")
    };
    assert_eq!(issue["code"], Json::str("cancelled"));
    assert_eq!(
        issue["details"],
        Json::obj([("signal", Json::str("SIGTERM"))])
    );
}

#[test]
fn cancellation_inside_primitive_type_data_and_dependency_checks_keeps_empty_stage() {
    for (target, after_type) in [
        (Checkpoint::DefinitionSemantics, false),
        (Checkpoint::DefinitionData, true),
        (Checkpoint::DefinitionDependency, true),
    ] {
        let (mut control, calls) = semantic_control(target, after_type, 3);
        let source =
            InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), MAP.to_vec());
        let failure = check_inputs(source, &mut control).expect_err("意味検査内で取消");
        assert_eq!(calls.get(), 3, "{target:?}");
        assert_empty_stage(&failure);
    }
}

#[test]
fn data_validation_cancellation_is_typed_before_eventual_invalid_self_reference() {
    // Set を通る自己参照は構文を読めても原始 data の正出現検査で拒否する。
    let source = String::from_utf8(DEFINITIONS.to_vec()).unwrap().replacen(
        "[[\"Data\", \"Engine.Expr\"], [\"Data\", \"Engine.Expr\"]]",
        "[[\"Set\", [\"Data\", \"Engine.Expr\"]], [\"Data\", \"Engine.Expr\"]]",
        1,
    );
    let invalid = check_definitions(&[("definition0", source.as_bytes())]).unwrap_err();
    assert_eq!(invalid.issue.code, Code::Syntax);
    let (mut control, calls) = semantic_control(Checkpoint::DefinitionData, true, 3);
    let stopped = check_definitions_controlled(&[("definition0", source.as_bytes())], &mut control)
        .expect_err("停止を Syntax に変換しない");
    assert_eq!(calls.get(), 3);
    assert!(matches!(
        stopped,
        CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
    ));
}

#[test]
fn unlimited_control_preserves_the_complete_primitive_table() {
    let ordinary = check_definitions(&[("definition0", DEFINITIONS)]).unwrap();
    let controlled =
        check_definitions_controlled(&[("definition0", DEFINITIONS)], &mut Control::unlimited())
            .unwrap();
    assert_eq!(ordinary, controlled);
}
