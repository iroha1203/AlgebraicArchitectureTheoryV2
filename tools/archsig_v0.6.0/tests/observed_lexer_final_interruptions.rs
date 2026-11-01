//! 字句不正を持つ小さい byte bundle でも、終了時の取消と状態順位を保持する。
use archsig::result::Signal;
use archsig::{
    control::{Checkpoint, Control},
    input::{InputSources, InputStatus, check_inputs},
};
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
fn byte_bundle_lexer_error_samples_cancel_at_the_final_checkpoint() {
    for suffix in [b"01".as_slice(), b"?", &[0xff]] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut baseline = Control::new(move |point| {
            if point == Checkpoint::LawIteration {
                seen.set(seen.get() + 1);
            }
            None
        });
        let expected = check_inputs(sources(suffix), &mut baseline).unwrap_err();
        assert_eq!(expected.status(), InputStatus::Invalid);
        assert!(
            expected.issues()[0]
                .canonical()
                .contains(r#""code":"syntax""#)
        );
        let final_at = count.get();
        let mut n = 0;
        let mut control = Control::new(move |point| {
            if point == Checkpoint::LawIteration {
                n += 1;
            }
            (n >= final_at).then_some(Signal::Term)
        });
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
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert!(matches!(control.stop_reason(), Some(Signal::Term)));
    }
}
