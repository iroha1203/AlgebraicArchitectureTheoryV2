use archsig::{
    canonical::Json,
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};
pub fn at_checkpoint(inputs: &InputSources, asks: &[&str], position: usize) -> Json {
    let seen = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(false));
    let (c, f) = (seen.clone(), frozen.clone());
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
            if c.get() == position {
                assert!(!f.replace(true));
                return Usage {
                    signal: Some(Signal::Term),
                    ..Default::default()
                };
            }
        }
        Usage::default()
    });
    let result = evaluate_observed_bytes(inputs.clone(), asks, &mut control).unwrap();
    assert_eq!(result.status(), "interrupted");
    assert_eq!(seen.get(), position);
    assert!(frozen.get());
    let wire = result.wire();
    assert_eq!(seen.get(), position);
    wire
}
pub fn first_position(
    inputs: &InputSources,
    asks: &[&str],
    total: usize,
    predicate: impl Fn(&Json) -> bool,
) -> usize {
    assert!(total > 0);
    assert!(predicate(&at_checkpoint(inputs, asks, total)));
    let (mut low, mut high) = (1, total);
    while low < high {
        let mid = low + (high - low) / 2;
        if predicate(&at_checkpoint(inputs, asks, mid)) {
            high = mid
        } else {
            low = mid + 1
        }
    }
    assert!(predicate(&at_checkpoint(inputs, asks, low)));
    low
}
