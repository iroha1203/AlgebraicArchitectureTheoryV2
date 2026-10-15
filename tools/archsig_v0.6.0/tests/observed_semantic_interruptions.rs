//! 入力の字句・構文検査の後にも、型検査と循環探索へ共有中断制御が届く。
mod common;

use archsig::{
    archmap::check_archmap_controlled,
    definition::check_definitions,
    issue::Code,
    law::{check_law, check_law_controlled},
    observed::control::{CheckFailure, Checkpoint, Control, Limits, Resource, StopReason, Usage},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn counting(point: Checkpoint) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(Limits::default(), move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    (control, count)
}

fn cancelled(point: Checkpoint, stop_after: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(Limits::default(), move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        Usage {
            signal: (seen.get() == stop_after).then_some(Signal::Term),
            ..Usage::default()
        }
    });
    (control, count)
}

fn repeated_sum() -> String {
    (0..16).fold("x".to_owned(), |body, _| format!("({body} + x)"))
}

#[test]
fn cancellation_reaches_inside_a_single_law_expression_after_syntax_checking() {
    let definitions = common::definitions_ok(&[common::EMPTY_DEFINITION]);
    let short = common::reading("view value(x: Z): Z = x;");
    let long = common::reading(&format!("view value(x: Z): Z = {};", repeated_sum()));
    let (mut baseline, small_steps) = counting(Checkpoint::LawSemantics);
    check_law_controlled(short.as_bytes(), &definitions, &mut baseline).unwrap();
    let (mut complete, full_steps) = counting(Checkpoint::LawSemantics);
    check_law_controlled(long.as_bytes(), &definitions, &mut complete).unwrap();
    // 両入力は同じ一宣言。短い本体の検査全体より遅い境界でも、長い本体内へ到達する。
    let stop_after = small_steps.get() + 3;
    assert!(full_steps.get() > stop_after + 10);
    let (mut control, seen) = cancelled(Checkpoint::LawSemantics, stop_after);
    let failure = check_law_controlled(long.as_bytes(), &definitions, &mut control).unwrap_err();
    assert!(matches!(
        failure,
        CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
    ));
    assert_eq!(seen.get(), stop_after);
}

#[test]
fn speculative_quantifier_type_checking_never_swallows_a_stop() {
    let definitions = common::definitions_ok(&[common::EMPTY_DEFINITION]);
    let law = common::reading("law optional quantified(): forall x: Z . exists y: Z . x = y;");
    let (mut baseline, count) = counting(Checkpoint::LawSemantics);
    check_law_controlled(law.as_bytes(), &definitions, &mut baseline).unwrap();
    assert!(count.get() > 10);
    // 候補を試し直す経路も含め、小さい入力の全境界へそれぞれ取消を注入する。
    for stop_after in 1..=count.get() {
        let (mut control, seen) = cancelled(Checkpoint::LawSemantics, stop_after);
        let failure = check_law_controlled(law.as_bytes(), &definitions, &mut control).unwrap_err();
        assert!(
            matches!(
                failure,
                CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
            ),
            "{stop_after}: {failure:?}"
        );
        assert_eq!(seen.get(), stop_after);
    }
}

#[test]
fn cancellation_inside_cycle_dfs_stays_distinct_from_a_cycle_input_error() {
    let definitions = common::definitions_ok(&[common::EMPTY_DEFINITION]);
    let law = format!(
        "{}reading A {{ use B as Other; view value(): Z = 1; }} reading B {{ use A as Other; view value(): Z = 1; }}",
        common::HEADER
    );
    assert_eq!(
        check_law(law.as_bytes(), &definitions)
            .unwrap_err()
            .issue
            .code,
        Code::Cycle
    );
    // 空のview graphの終端、reading DFSの根、nodeに続くedgeを停止点にする。
    let (mut control, seen) = cancelled(Checkpoint::LawCycle, 4);
    let failure = check_law_controlled(law.as_bytes(), &definitions, &mut control).unwrap_err();
    assert!(matches!(
        failure,
        CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
    ));
    assert_eq!(seen.get(), 4);
}

fn term_input(body: &str) -> (archsig::definition::CheckedDefinitions, String) {
    let declaration = common::entity_json(
        "V.State",
        "[]",
        &format!(
            "[{}]",
            common::field_json("function", r#"["Term",["Z"],"Z"]"#)
        ),
    );
    let source = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{declaration}]"), "[]")
    ));
    let definitions = check_definitions(&[("definition0", source.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies["V"].digest;
    let body_json = archsig::canonical::Json::str(body).canonical();
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"test","locations":[],"note":"Term input"}}],"snapshots":[{{"id":"s","origin":"model","subjects":[{{"id":"root","type":"V.State","origin":"model"}}],"atoms":[{{"id":"f","subject":"root","field":"V.State.function","origin":"model","value":{{"params":["x"],"body":{body_json}}}}}]}}]}}"#
    );
    (definitions, map)
}

#[test]
fn archmap_term_lexer_parser_and_late_type_check_share_the_control() {
    let (definitions, map) = term_input(&repeated_sum());
    let (mut baseline, total) = counting(Checkpoint::ArchMapTerm);
    check_archmap_controlled(map.as_bytes(), &definitions, &mut baseline).unwrap();
    assert!(total.get() > 50);
    // 前半の字句/構文検査と、返却直前の2境界より前の式検査の両方へ注入する。
    for stop_after in [total.get() / 2, total.get() - 4] {
        let (mut control, seen) = cancelled(Checkpoint::ArchMapTerm, stop_after);
        let failure =
            check_archmap_controlled(map.as_bytes(), &definitions, &mut control).unwrap_err();
        assert!(
            matches!(
                failure,
                CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
            ),
            "{stop_after}: {failure:?}"
        );
        assert_eq!(seen.get(), stop_after);
    }
}

#[test]
fn a_budget_exhausted_inside_term_type_check_is_not_an_invalid_term() {
    let (definitions, map) = term_input(&repeated_sum());
    let (mut baseline, total) = counting(Checkpoint::ArchMapTerm);
    check_archmap_controlled(map.as_bytes(), &definitions, &mut baseline).unwrap();
    let stop_after = total.get() - 4;
    let mut seen = 0usize;
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        move |point| {
            if point == Checkpoint::ArchMapTerm {
                seen += 1;
            }
            Usage {
                elapsed_ms: u128::from(seen >= stop_after),
                ..Usage::default()
            }
        },
    );
    let failure = check_archmap_controlled(map.as_bytes(), &definitions, &mut control).unwrap_err();
    assert!(matches!(
        failure,
        CheckFailure::Stopped(StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 1,
            observed: 1
        })
    ));
}
