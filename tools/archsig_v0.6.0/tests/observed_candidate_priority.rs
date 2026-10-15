//! 最後の構文候補が確定した不正を、共有予算が入力中断へ変えないことを確認する。
use archsig::{
    observed::{
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn sources(declaration: &str) -> InputSources {
    let law = include_str!("fixtures/counter.law")
        .replace("  view amount", &format!("  {declaration}\n  view amount"));
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
            if point == Checkpoint::LawIteration {
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
fn exhausted_syntax_candidates_keep_invalid_span_and_budget_reason_from_bytes() {
    for declaration in [
        "change bad() when true = ;",
        "view bad(): Bool = forall x: Z .;",
    ] {
        let (mut baseline, total) = probe(usize::MAX, 0);
        let invalid = check_inputs(sources(declaration), &mut baseline).unwrap_err();
        assert_eq!(invalid.status(), InputStatus::Invalid);
        assert!(total.get() > 12);
        // These are Result exits after the empty body's Syntax has been
        // constructed: expression/candidate/declaration/reading/Law exits.
        // The private units independently arm at the diagnostic's construction.
        for at in total.get() - 6..=total.get() {
            for mode in 0..3 {
                let (mut control, _) = probe(at, mode);
                let failure = check_inputs(sources(declaration), &mut control).unwrap_err();
                assert!(failure.declarations().is_empty());
                assert!(failure.primitives().is_empty());
                assert!(failure.vocabularies().is_empty());
                if mode == 0 {
                    assert_eq!(failure.status(), InputStatus::Interrupted);
                    assert_eq!(
                        control.stop_reason(),
                        Some(StopReason::Cancelled(Signal::Term))
                    );
                } else {
                    assert_eq!(
                        failure.status(),
                        InputStatus::Invalid,
                        "{declaration} {at}/{}",
                        total.get()
                    );
                    let reason = control.stop_reason().expect("budget sampled");
                    assert!(matches!(reason, StopReason::BudgetExhausted { .. }));
                    let mut expected = vec![reason.wire()];
                    expected.extend_from_slice(invalid.issues());
                    assert_eq!(
                        failure.issues(),
                        expected,
                        "original diagnostic and byte span"
                    );
                }
            }
        }
    }
}
