//! 検出済みLaw循環と、DFS途中・診断確定後の停止を区別する。
use crate::common;

use archsig::{
    canonical::Json,
    control::{Checkpoint, Control},
    input::{InputSources, InputStatus, check_inputs},
    issue::{Code, Issue, Location},
    law::check_law,
    result::ResultIssue,
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn view_cycle() -> String {
    common::reading("view first(): Z = second(); view second(): Z = first();")
}

fn reading_cycle() -> String {
    format!(
        "{}reading A {{ use B as Other; view value(): Z = 1; }} reading B {{ use A as Other; view value(): Z = 1; }}",
        common::HEADER
    )
}

fn sources(law: &str) -> InputSources {
    InputSources::from_bytes(
        vec![common::COUNTER_DEFINITION.as_bytes().to_vec()],
        law.as_bytes().to_vec(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}

fn expected_input_issue(law: &str, issue: &Issue) -> Json {
    let mut wire = ResultIssue::Input(issue.clone()).wire();
    let Json::Obj(fields) = &mut wire else {
        panic!("issue")
    };
    let Json::Obj(location) = fields.get_mut("location").unwrap() else {
        panic!("location")
    };
    // 固定入力の参照位置: view の second は3行19列、reading の B は2行17列。
    let (line, column) = if law.contains("view first") {
        (3, 19)
    } else {
        (2, 17)
    };
    location.insert("line".into(), Json::Nat(line));
    location.insert("column".into(), Json::Nat(column));
    wire
}

fn baseline(law: &str) -> (archsig::issue::Issue, usize) {
    let definitions = common::definitions_ok(&[common::COUNTER_DEFINITION]);
    let expected = check_law(law.as_bytes(), &definitions).unwrap_err().issue;
    assert_eq!(expected.code, Code::Cycle);
    let Location::Law { span } = expected.location else {
        panic!("missing Lawの元位置");
    };
    // Span must identify the original reference, rather than a fallback position.
    assert_eq!(
        common::span_text(law, span),
        if law.contains("view first") {
            "second"
        } else {
            "B"
        }
    );
    let total = Rc::new(Cell::new(0));
    let seen = total.clone();
    let mut control = Control::new(move |point| {
        if point == Checkpoint::LawCycle {
            seen.set(seen.get() + 1);
        }
        None
    });
    let failure = check_inputs(sources(law), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(
        failure.issues(),
        [expected_input_issue(law, &expected)]
    );
    assert!(total.get() > 2);
    (expected, total.get())
}

fn injected(stop_after: usize) -> Control {
    let mut seen = 0;
    Control::new(move |point| {
        if point == Checkpoint::LawCycle {
            seen += 1;
        }
        (seen >= stop_after).then_some(Signal::Term)
    })
}

fn assert_cancel_after_cycle(law: &str) {
    let (_, total) = baseline(law);
    let mut control = injected(total);
    let failure = check_inputs(sources(law), &mut control).unwrap_err();
    let reason = Signal::Term;
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(failure.issues(), [reason.issue()]);
    assert_eq!(control.stop_reason(), Some(reason));
}

fn assert_stop_before_cycle(law: &str) {
    let (_, total) = baseline(law);
    // The penultimate LawCycle checkpoint is still inside DFS, before the
    // active-node revisit establishes a cycle. Its stop is not an input failure.
    let mut control = injected(total - 1);
    let failure = check_inputs(sources(law), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(failure.issues(), [Signal::Term.issue()]);
}

#[test]
fn cancellation_after_view_cycle_stays_first() {
    assert_cancel_after_cycle(&view_cycle());
}

#[test]
fn cancellation_after_reading_cycle_stays_first() {
    assert_cancel_after_cycle(&reading_cycle());
}

#[test]
fn stopping_view_dfs_does_not_claim_a_cycle() {
    assert_stop_before_cycle(&view_cycle());
}

#[test]
fn stopping_reading_dfs_does_not_claim_a_cycle() {
    assert_stop_before_cycle(&reading_cycle());
}
