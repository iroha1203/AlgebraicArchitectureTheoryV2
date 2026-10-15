//! 字句不正を持つ小さい byte bundle でも、終了時の取消と状態順位を保持する。
use archsig::observed::{
    control::{Checkpoint, Control, Limits, StopReason, Usage},
    input::{InputSources, InputStatus, check_inputs},
};
use archsig::result::Signal;
use std::{cell::Cell, rc::Rc};

fn sources(suffix: &[u8]) -> InputSources {
    let mut law = include_bytes!("fixtures/counter.law").to_vec();
    law.extend_from_slice(b"\n");
    law.extend_from_slice(suffix);
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law,
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}

#[test]
fn byte_bundle_lexer_error_preserves_syntax_over_budget_and_samples_cancel() {
    for suffix in [b"01".as_slice(), b"?", &[0xff]] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut baseline = Control::new(Limits::default(), move |point| {
            if point == Checkpoint::LawIteration {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        });
        let expected = check_inputs(sources(suffix), &mut baseline).unwrap_err();
        assert_eq!(expected.status(), InputStatus::Invalid);
        assert!(
            expected.issues()[0]
                .canonical()
                .contains(r#""code":"syntax""#)
        );
        let final_at = count.get();
        for resource in 0..3 {
            let mut n = 0;
            let mut control = Control::new(
                Limits {
                    time_ms: (resource == 1).then_some(1),
                    memory_mib: (resource == 2).then_some(1),
                },
                move |point| {
                    if point == Checkpoint::LawIteration {
                        n += 1;
                    }
                    let stop = n >= final_at;
                    Usage {
                        signal: (stop && resource == 0).then_some(Signal::Term),
                        elapsed_ms: u128::from(stop && resource == 1),
                        memory_mib: u128::from(stop && resource == 2),
                    }
                },
            );
            let failure = check_inputs(sources(suffix), &mut control).unwrap_err();
            assert!(failure.declarations().is_empty());
            assert!(
                failure.primitives().is_empty(),
                "Law検査不成立では両表を公開しない"
            );
            assert!(failure.vocabularies().is_empty());
            assert_eq!(
                failure.sources().law().bytes(),
                sources(suffix).law().bytes()
            );
            if resource == 0 {
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::Cancelled(Signal::Term))
                ));
            } else {
                assert_eq!(failure.status(), InputStatus::Invalid);
                let mut expected_issues =
                    vec![control.stop_reason().expect("observed budget").wire()];
                expected_issues.extend_from_slice(expected.issues());
                assert_eq!(
                    failure.issues(),
                    expected_issues,
                    "検出済みsyntaxと予算の両方を保持する"
                );
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted { .. })
                ));
            }
        }
    }
}
