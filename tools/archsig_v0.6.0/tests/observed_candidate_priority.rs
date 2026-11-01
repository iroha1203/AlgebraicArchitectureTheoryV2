//! 最後の構文候補が確定した不正より、取消の停止が優先されることを確認する。
use archsig::{
    control::{Checkpoint, Control},
    input::{InputSources, InputStatus, check_inputs},
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
fn probe(at: usize) -> (Control, Rc<Cell<usize>>) {
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let control = Control::new(move |point| {
        if point == Checkpoint::LawIteration {
            seen.set(seen.get() + 1);
        }
        (seen.get() == at).then_some(Signal::Term)
    });
    (control, visits)
}
#[test]
fn exhausted_syntax_candidates_yield_to_cancellation_from_bytes() {
    for declaration in [
        "change bad() when true = ;",
        "view bad(): Bool = forall x: Z .;",
    ] {
        let (baseline, total) = probe(usize::MAX);
        let invalid = check_inputs(sources(declaration), &baseline).unwrap_err();
        assert_eq!(invalid.status(), InputStatus::Invalid);
        assert!(total.get() > 12);
        // These are Result exits after the empty body's Syntax has been
        // constructed: expression/candidate/declaration/reading/Law exits.
        // The private units independently arm at the diagnostic's construction.
        for at in total.get() - 6..=total.get() {
            let (control, _) = probe(at);
            let failure = check_inputs(sources(declaration), &control).unwrap_err();
            assert!(failure.declarations().is_empty());
            assert!(failure.primitives().is_empty());
            assert!(failure.vocabularies().is_empty());
            assert_eq!(failure.status(), InputStatus::Interrupted);
            assert_eq!(control.stop_reason(), Some(Signal::Term));
        }
    }
}
