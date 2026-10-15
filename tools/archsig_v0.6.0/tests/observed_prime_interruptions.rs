//! Fp の素数性内部へ三入力検査の共有制御が届き、既知不正と元位置を保つ。
use archsig::{
    canonical::Json,
    definition::{check_definitions, check_definitions_controlled},
    issue::{Code, Issue, Location},
    law::{check_law, check_law_controlled},
    observed::{
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
    },
    result::{ResultIssue, Signal},
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &str = include_str!("fixtures/counter.atoms.json");
const HEADER: &str = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";";

fn sources(in_law: bool, modulus: &str) -> InputSources {
    let (definitions, law) = if in_law {
        (
            DEFINITIONS.to_owned(),
            format!("{HEADER} reading R {{ view echo(x: Fp({modulus})): Bool = true; }}"),
        )
    } else {
        (
            DEFINITIONS.replace(
                "\"type\": \"Z\"",
                &format!("\"type\": [\"Fp\", \"{modulus}\"]"),
            ),
            format!("{HEADER} reading R {{ view ready(): Bool = true; }}"),
        )
    };
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        b"bad".to_vec(),
    )
}

fn probe(in_law: bool, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let target = if in_law {
        Checkpoint::LawSemantics
    } else {
        Checkpoint::DefinitionSemantics
    };
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let control = Control::new(
        Limits {
            time_ms: (mode == 1).then_some(1),
            memory_mib: (mode == 2).then_some(1),
        },
        move |point| {
            if point == target {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() == at;
            Usage {
                elapsed_ms: u128::from(stop && mode == 1),
                memory_mib: u128::from(stop && mode == 2),
                signal: (stop && mode == 0).then_some(Signal::Term),
            }
        },
    );
    (control, visits)
}

fn empty_stage(failure: &InputFailure) {
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    let Json::Obj(ref wire) = failure.wire() else {
        panic!("object expected")
    };
    for key in [
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "nodes",
    ] {
        assert_eq!(wire[key], Json::Arr(vec![]), "{key}");
    }
}

fn negative_baseline(in_law: bool) -> (Issue, usize) {
    let source = sources(in_law, "49");
    let issue = if in_law {
        let definitions =
            check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
        let issue = check_law(source.law().bytes(), &definitions)
            .unwrap_err()
            .issue;
        let Location::Law { span } = issue.location else {
            panic!("Law span expected")
        };
        assert_eq!(&source.law().bytes()[span.0..span.1], b"Fp(49)");
        issue
    } else {
        let issue = check_definitions(&[("definition0", source.definitions()[0].bytes())])
            .unwrap_err()
            .issue;
        assert!(
            matches!(&issue.location, Location::Definition { input, pointer, .. }
            if input == "definition0" && pointer == "/vocabularies/0/declarations/0/fields/0/type")
        );
        issue
    };
    assert_eq!(issue.code, Code::Syntax);
    let (mut baseline, total) = probe(in_law, usize::MAX, 0);
    let failure = check_inputs(source, &mut baseline).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(failure.issues(), [ResultIssue::Input(issue.clone()).wire()]);
    empty_stage(&failure);
    assert!(total.get() > 10);
    (issue, total.get())
}

#[test]
fn fp_internal_iteration_stops_from_bytes_keep_empty_definition_and_law_stages() {
    for in_law in [false, true] {
        let (_, negative_total) = negative_baseline(in_law);
        // 49 terminates on divisor 7; 101 has the same prefix and continues
        // the small-prime loop. These later visits are inside that loop,
        // before the outer type-checking exits of the successful Fp type.
        for at in [negative_total, negative_total + 4, negative_total + 8] {
            for mode in 0..3 {
                let (mut control, seen) = probe(in_law, at, mode);
                let failure = check_inputs(sources(in_law, "101"), &mut control).unwrap_err();
                assert_eq!(seen.get(), at, "in_law {in_law} at {at}");
                assert_eq!(failure.status(), InputStatus::Interrupted);
                empty_stage(&failure);
                let reason = control.stop_reason().expect("shared stop");
                assert_eq!(failure.issues(), [reason.wire()]);
                assert!(matches!(reason, StopReason::Cancelled(Signal::Term)) == (mode == 0));
            }
        }
    }
}

#[test]
fn completed_composite_checks_keep_the_original_pointer_or_span_above_budget() {
    for in_law in [false, true] {
        let (issue, total) = negative_baseline(in_law);
        // One primitive type exit, and additionally the Law checker exit,
        // follow the primality function's final (divisor-detected) sample.
        let primality_post = total - if in_law { 2 } else { 1 };
        for at in primality_post..=total {
            for mode in 0..3 {
                let (mut control, _) = probe(in_law, at, mode);
                let failure = check_inputs(sources(in_law, "49"), &mut control).unwrap_err();
                empty_stage(&failure);
                let reason = control.stop_reason().expect("terminal stop");
                if mode == 0 {
                    assert_eq!(failure.status(), InputStatus::Interrupted);
                    assert_eq!(failure.issues(), [reason.wire()]);
                } else {
                    assert_eq!(
                        failure.status(),
                        InputStatus::Invalid,
                        "in_law {in_law} at {at}/{total}"
                    );
                    assert_eq!(
                        failure.issues(),
                        [reason.wire(), ResultIssue::Input(issue.clone()).wire()]
                    );
                }
            }
        }
        // The previous pre-iteration sample precedes finding divisor 7.
        let (mut control, _) = probe(in_law, primality_post - 1, 1);
        let failure = check_inputs(sources(in_law, "49"), &mut control).unwrap_err();
        assert_eq!(failure.status(), InputStatus::Interrupted);
        empty_stage(&failure);
    }
}

#[test]
fn unlimited_fp_controls_preserve_the_checked_definition_and_law_tables() {
    let source = sources(false, "101");
    let files = [("definition0", source.definitions()[0].bytes())];
    let ordinary = check_definitions(&files).unwrap();
    let controlled = check_definitions_controlled(&files, &mut Control::unlimited()).unwrap();
    assert_eq!(ordinary, controlled);
    let law_source = sources(true, "101");
    let ordinary = check_law(law_source.law().bytes(), &ordinary).unwrap();
    let controlled = check_law_controlled(
        law_source.law().bytes(),
        &controlled,
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(ordinary.bytes_digest, controlled.bytes_digest);
    assert_eq!(ordinary.model_digest, controlled.model_digest);
    assert_eq!(ordinary.infos, controlled.infos);
    assert_eq!(ordinary.expr_types, controlled.expr_types);
    assert_eq!(ordinary.definitions, controlled.definitions);
}
