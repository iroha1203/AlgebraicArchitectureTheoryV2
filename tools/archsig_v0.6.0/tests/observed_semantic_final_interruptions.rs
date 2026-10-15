//! 小さい意味検査の成功・既知不正・表示の末尾へ共有制御が届くことを確認する。
use archsig::observed::{
    PrepareFailure,
    control::{Checkpoint, Control, Limits, StopReason, Usage},
    input::{InputSources, InputStatus, check_inputs},
    prepare_observed,
};
use archsig::result::Signal;
use std::{cell::Cell, rc::Rc};

fn sources(body: &str) -> InputSources {
    let law = include_str!("fixtures/counter.law")
        .replace("  view amount", &format!("  {body}\n  view amount"));
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law.into_bytes(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}
fn probe(at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let control = Control::new(
        Limits {
            time_ms: (mode == 1).then_some(1),
            memory_mib: (mode == 2).then_some(1),
        },
        move |point| {
            if point == Checkpoint::LawSemantics {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() == at;
            Usage {
                signal: (stop && mode == 0).then_some(Signal::Term),
                elapsed_ms: u128::from(stop && mode == 1),
                memory_mib: u128::from(stop && mode == 2),
            }
        },
    );
    (control, visits)
}
#[test]
fn prepared_byte_inputs_keep_known_semantic_invalid_above_late_budget() {
    for body in [
        "view wrong(): Z = true;",
        "view wrong(t: Option<Bool>): Z = t();",
    ] {
        let (mut baseline, total) = probe(usize::MAX, 0);
        let invalid = check_inputs(sources(body), &mut baseline).unwrap_err();
        assert_eq!(invalid.status(), InputStatus::Invalid);
        assert!(total.get() > 5);
        for mode in 0..3 {
            let (mut control, seen) = probe(total.get(), mode);
            let failure = prepare_observed(
                sources(body),
                &["a=evaluate(CountCheck.amount,s=@v/s)"],
                &mut control,
            )
            .unwrap_err();
            let PrepareFailure::Inputs(failure) = failure else {
                panic!("Law input failure expected")
            };
            assert_eq!(seen.get(), total.get());
            assert!(failure.declarations().is_empty());
            assert!(failure.primitives().is_empty());
            assert!(failure.vocabularies().is_empty());
            if mode == 0 {
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::Cancelled(Signal::Term))
                ));
            } else {
                assert_eq!(failure.status(), InputStatus::Invalid);
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted { .. })
                ));
                let mut expected_issues =
                    vec![control.stop_reason().expect("observed budget").wire()];
                expected_issues.extend_from_slice(invalid.issues());
                assert_eq!(failure.issues(), expected_issues);
            }
        }
    }
}
#[test]
fn nested_type_erasure_and_invalid_call_diagnostics_remain_interruptible_from_bytes() {
    for body in [
        "view nested(t: Option<Option<Bool>>): Option<Option<Bool>> = t;",
        "view wrong(t: Option<Option<Bool>>): Z = t();",
    ] {
        let (mut baseline, total) = probe(usize::MAX, 0);
        let _ = check_inputs(sources(body), &mut baseline);
        assert!(total.get() > 20);
        // Small representative interior and terminal points; private units cover
        // every nested component of erasure and diagnostic rendering directly.
        for at in [total.get() / 2, total.get() - 1, total.get()] {
            let (mut control, seen) = probe(at, 0);
            let failure = check_inputs(sources(body), &mut control).unwrap_err();
            assert_eq!(seen.get(), at);
            assert_eq!(failure.status(), InputStatus::Interrupted);
            assert!(matches!(
                control.stop_reason(),
                Some(StopReason::Cancelled(Signal::Term))
            ));
        }
    }
}
