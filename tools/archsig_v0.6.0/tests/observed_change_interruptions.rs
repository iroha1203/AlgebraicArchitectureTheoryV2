use archsig::{
    canonical::Json,
    control::{Checkpoint, Control},
    input::{InputFailure, InputSources, InputStatus, check_inputs},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn sources(body: &str) -> InputSources {
    let law = include_str!("fixtures/counter.law").replace(
        "view amount",
        &format!("change shift(s: State) = {body};\n  view amount"),
    );
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law.into_bytes(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}

fn count(body: &str) -> usize {
    let seen = Rc::new(Cell::new(0));
    let probe = seen.clone();
    let mut control = Control::new(move |point| {
        if point == Checkpoint::LawChange {
            probe.set(probe.get() + 1);
        }
        None
    });
    let _ = check_inputs(sources(body), &mut control);
    seen.get()
}

fn stop(at: usize) -> Control {
    let mut seen = 0;
    Control::new(move |point| {
        if point == Checkpoint::LawChange {
            seen += 1;
        }
        (seen == at).then_some(Signal::Term)
    })
}

fn assert_stopped(failure: &InputFailure, control: &Control) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    assert_eq!(failure.inputs().len(), 3);
    let wire = failure.wire();
    let Json::Obj(fields) = &wire else {
        panic!("object")
    };
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(fields[key], Json::Arr(vec![]));
    }
    assert_eq!(control.stop_reason(), Some(Signal::Term));
}

#[test]
fn nested_change_groups_add_internal_stop_boundaries() {
    let flat = "s with { count = s.count + 1 }";
    let nested = format!("{}{}{}", "(".repeat(6), flat, ")".repeat(6));
    check_inputs(sources(&nested), &mut Control::unlimited()).unwrap();
    let at = count(flat) + 1;
    assert!(count(&nested) > at + 4);
    let mut control = stop(at);
    let failure = check_inputs(sources(&nested), &mut control).unwrap_err();
    assert_stopped(&failure, &control);
}

#[test]
fn invalid_grouped_change_cannot_hide_a_stop_at_its_final_boundary() {
    let body = "((((s))))";
    let invalid = check_inputs(sources(body), &mut Control::unlimited()).unwrap_err();
    assert_eq!(invalid.status(), InputStatus::Invalid);
    let steps = count(body);
    assert!(steps > 8);
    for at in 1..=steps {
        let mut control = stop(at);
        let failure = check_inputs(sources(body), &mut control).unwrap_err();
        assert_stopped(&failure, &control);
    }
}

#[test]
fn let_if_and_update_checks_share_cancellation() {
    let body = "let n = 1 in if true then ((s with { count = s.count + n })) else ((s with { count = 0 }))";
    check_inputs(sources(body), &mut Control::unlimited()).unwrap();
    let steps = count(body);
    assert!(steps > 10);
    for at in [1, steps / 2, steps] {
        let mut control = stop(at);
        let failure = check_inputs(sources(body), &mut control).unwrap_err();
        assert_stopped(&failure, &control);
    }
}
