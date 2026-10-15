//! 検出済みLaw循環と、DFS途中・診断確定後の停止を区別する。
mod common;

use archsig::{
    issue::{Code, Location},
    law::{check_law, check_law_controlled},
    observed::{
        control::{CheckFailure, Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
    },
    result::{ResultIssue, Signal},
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

fn baseline(law: &str) -> (archsig::issue::Issue, usize) {
    let definitions = common::definitions_ok(&[common::COUNTER_DEFINITION]);
    let expected = check_law(law.as_bytes(), &definitions).unwrap_err().issue;
    assert_eq!(expected.code, Code::Cycle);
    let Location::Law { span } = expected.location else {
        panic!("Lawの元位置が必要");
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
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::LawCycle {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let failure = check_inputs(sources(law), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(
        failure.issues(),
        [ResultIssue::Input(expected.clone()).wire()]
    );
    assert!(total.get() > 2);
    (expected, total.get())
}

fn injected(stop_after: usize, resource: Option<Resource>, cancel: bool) -> Control {
    let mut seen = 0;
    Control::new(
        Limits {
            time_ms: (resource == Some(Resource::TimeMs)).then_some(1),
            memory_mib: (resource == Some(Resource::MemoryMib)).then_some(1),
        },
        move |point| {
            if point == Checkpoint::LawCycle {
                seen += 1;
            }
            let stop = seen >= stop_after;
            Usage {
                signal: (stop && cancel).then_some(Signal::Term),
                elapsed_ms: u128::from(stop && resource == Some(Resource::TimeMs)),
                memory_mib: u128::from(stop && resource == Some(Resource::MemoryMib)),
            }
        },
    )
}

fn assert_known_cycle_over_budget(law: &str) {
    let (expected, total) = baseline(law);
    let definitions = common::definitions_ok(&[common::COUNTER_DEFINITION]);
    for resource in [Resource::TimeMs, Resource::MemoryMib] {
        let mut control = injected(total, Some(resource), false);
        let failure = check_law_controlled(law.as_bytes(), &definitions, &mut control).unwrap_err();
        let CheckFailure::Input(failure) = failure else {
            panic!("検出済みcycleを予算停止へ上書きしない: {failure:?}");
        };
        assert_eq!(failure.issue, expected);
        let reason = StopReason::BudgetExhausted {
            resource,
            limit: 1,
            observed: 1,
        };
        assert_eq!(control.stop_reason(), Some(reason.clone()));

        let mut control = injected(total, Some(resource), false);
        let failure = check_inputs(sources(law), &mut control).unwrap_err();
        assert_eq!(failure.status(), InputStatus::Invalid);
        assert_eq!(
            failure.issues(),
            [reason.wire(), ResultIssue::Input(expected.clone()).wire()]
        );
        assert!(failure.declarations().is_empty());
        assert!(failure.primitives().is_empty());
        assert!(failure.vocabularies().is_empty());
        assert_eq!(failure.sources().law().bytes(), law.as_bytes());
        assert_eq!(control.stop_reason(), Some(reason));
    }
}

fn assert_cancel_after_cycle(law: &str) {
    let (_, total) = baseline(law);
    // Cancellation also wins when a resource limit is reached in the same sample.
    for resource in [None, Some(Resource::TimeMs), Some(Resource::MemoryMib)] {
        let mut control = injected(total, resource, true);
        let failure = check_inputs(sources(law), &mut control).unwrap_err();
        let reason = StopReason::Cancelled(Signal::Term);
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert_eq!(failure.issues(), [reason.wire()]);
        assert_eq!(control.stop_reason(), Some(reason));
    }
}

fn assert_stop_before_cycle(law: &str) {
    let (_, total) = baseline(law);
    // The penultimate LawCycle checkpoint is still inside DFS, before the
    // active-node revisit establishes a cycle. Its stop is not an input failure.
    for resource in [Resource::TimeMs, Resource::MemoryMib] {
        let mut control = injected(total - 1, Some(resource), false);
        let failure = check_inputs(sources(law), &mut control).unwrap_err();
        let reason = StopReason::BudgetExhausted {
            resource,
            limit: 1,
            observed: 1,
        };
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert_eq!(failure.issues(), [reason.wire()]);
        assert_eq!(control.stop_reason(), Some(reason));
    }
    let mut control = injected(total - 1, None, true);
    let failure = check_inputs(sources(law), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert_eq!(
        failure.issues(),
        [StopReason::Cancelled(Signal::Term).wire()]
    );
}

#[test]
fn view_cycle_preserves_original_issue_and_late_budget() {
    assert_known_cycle_over_budget(&view_cycle());
}

#[test]
fn reading_cycle_preserves_original_issue_and_late_budget() {
    assert_known_cycle_over_budget(&reading_cycle());
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
