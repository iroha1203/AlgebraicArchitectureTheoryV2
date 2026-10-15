//! 拒否が決まった型の元診断を、共有 budget と取消の優先規則に沿って保持する。
use archsig::{
    canonical::Json,
    definition::check_definitions,
    issue::{Code, Issue, Location},
    law::check_law,
    observed::{
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
    },
    result::{ResultIssue, Signal},
};
use std::{cell::Cell, rc::Rc};

const DEFINITIONS: &str = include_str!("fixtures/counter.atoms.json");
const HEADER: &str = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";";

fn source(definitions: String, body: &str, import: bool) -> InputSources {
    let binding = if import {
        let definitions = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
        format!(
            "use vocabulary Counter version \"1\" digest \"{}\";",
            definitions.vocabularies["Counter"].digest
        )
    } else {
        String::new()
    };
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        format!("{HEADER} reading R {{ {binding} {body} }}").into_bytes(),
        // Reaching this deliberately invalid next stage would expose a lost earlier diagnostic.
        b"bad".to_vec(),
    )
}

fn definition_source(ty: &str) -> InputSources {
    source(
        DEFINITIONS.replace("\"type\": \"Z\"", &format!("\"type\": {ty}")),
        "view ready(): Bool = true;",
        false,
    )
}

fn data_source(arguments: &str) -> InputSources {
    source(
        format!(
            r#"{{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
                "vocabularies":[{{"semantics":"archsig/0.6.0","namespace":"Counter",
                "version":"1","dependencies":[],"declarations":[{{"kind":"data",
                "name":"Counter.Tree","meaning":"木。","constructors":[
                {{"name":"Leaf","arguments":[],"meaning":"葉。"}},
                {{"name":"Node","arguments":{arguments},"meaning":"子。"}}]}}]}}]}}"#
        ),
        "view ready(): Bool = true;",
        false,
    )
}

fn probe(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(
        Limits {
            time_ms: (mode == 1).then_some(1),
            memory_mib: (mode == 2).then_some(1),
        },
        move |current| {
            if current == point {
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
    (control, count)
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

fn baseline(input: &InputSources, in_law: bool, point: Checkpoint) -> (Issue, usize) {
    let issue = if in_law {
        let definitions =
            check_definitions(&[("definition0", input.definitions()[0].bytes())]).unwrap();
        check_law(input.law().bytes(), &definitions)
            .unwrap_err()
            .issue
    } else {
        check_definitions(&[("definition0", input.definitions()[0].bytes())])
            .unwrap_err()
            .issue
    };
    assert!(matches!(issue.code, Code::Syntax | Code::Type));
    let (mut control, total) = probe(point, usize::MAX, 0);
    let failure = check_inputs(input.clone(), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(failure.issues(), [ResultIssue::Input(issue.clone()).wire()]);
    empty_stage(&failure);
    (issue, total.get())
}

fn terminal_priority(input: InputSources, in_law: bool, point: Checkpoint, unwind: usize) -> Issue {
    let (issue, total) = baseline(&input, in_law, point);
    let post = total.checked_sub(unwind).unwrap();
    assert!(post > 1);
    for at in post..=total {
        for mode in 0..3 {
            let (mut control, seen) = probe(point, at, mode);
            let failure = check_inputs(input.clone(), &mut control).unwrap_err();
            assert_eq!(seen.get(), at, "{point:?} at {at}/{total}");
            empty_stage(&failure);
            let reason = control.stop_reason().expect("shared terminal stop");
            if mode == 0 {
                assert_eq!(reason, StopReason::Cancelled(Signal::Term));
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert_eq!(failure.issues(), [reason.wire()]);
            } else {
                assert!(matches!(reason, StopReason::BudgetExhausted { .. }));
                assert_eq!(
                    failure.status(),
                    InputStatus::Invalid,
                    "post {post}, at {at}"
                );
                assert_eq!(
                    failure.issues(),
                    [reason.wire(), ResultIssue::Input(issue.clone()).wire()]
                );
            }
        }
    }
    issue
}

#[test]
fn definition_set_and_term_rejections_keep_original_pointer_and_budget() {
    for (ty, ordinal) in [
        (r#"["Set",["Term",[],"Z"]]"#, 9),
        (r#"["Term",[],["Ref","Counter.State"]]"#, 7),
        (r#"["Term",[["Ref","Counter.State"]],"Z"]"#, 7),
    ] {
        let input = definition_source(ty);
        let (issue, total) = baseline(&input, false, Checkpoint::DefinitionData);
        assert_eq!(total, ordinal, "first refusal is the last data sample");
        assert!(
            matches!(&issue.location, Location::Definition { input, pointer, .. }
            if input == "definition0" && pointer == "/vocabularies/0/declarations/0/fields/0/type")
        );
        assert_eq!(
            terminal_priority(input.clone(), false, Checkpoint::DefinitionData, 0),
            issue
        );
        // The immediately preceding sample is before the forbidden component is read.
        for mode in 0..3 {
            let (mut control, _) = probe(Checkpoint::DefinitionData, ordinal - 1, mode);
            let failure = check_inputs(input.clone(), &mut control).unwrap_err();
            assert_eq!(failure.status(), InputStatus::Interrupted);
            empty_stage(&failure);
            assert_eq!(failure.issues(), [control.stop_reason().unwrap().wire()]);
        }
    }
}

#[test]
fn negative_data_self_occurrence_keeps_constructor_argument_location_above_budget() {
    let input = data_source(r#"[["Set",["Data","Counter.Tree"]]]"#);
    // The leaf rejects, then the enclosing Set check propagates that same Issue.
    let issue = terminal_priority(input.clone(), false, Checkpoint::DefinitionData, 1);
    assert!(
        matches!(&issue.location, Location::Definition { input, pointer, .. }
        if input == "definition0" && pointer == "/vocabularies/0/declarations/0/constructors/1/arguments/0")
    );
    assert_eq!(
        issue.message,
        "data の自己参照は直接または Tuple・List・Option を通る"
    );
    let (_, total) = baseline(&input, false, Checkpoint::DefinitionData);
    let (mut control, _) = probe(Checkpoint::DefinitionData, total - 2, 1);
    let failure = check_inputs(input, &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Interrupted);
    empty_stage(&failure);
}

#[test]
fn law_set_term_path_and_reference_free_parameters_keep_original_spans_above_budget() {
    for (body, fragment, message) in [
        (
            "view bad(x: Set<Term<()->Z>>): Bool = true;",
            "Set<Term<()->Z>>",
            "Set の要素型は Term・Path を含まない",
        ),
        (
            "view bad(x: Set<Path<State,State>>): Bool = true;",
            "Set<Path<State,State>>",
            "Set の要素型は Term・Path を含まない",
        ),
        (
            "view bad(x: Term<()->State>): Bool = true;",
            "Term<()->State>",
            "Term の引数・戻り型は参照・Map・Path を含まない値型",
        ),
        (
            "view bad(x: Term<(State)->Z>): Bool = true;",
            "Term<(State)->Z>",
            "Term の引数・戻り型は参照・Map・Path を含まない値型",
        ),
        (
            "change bad(s: State, x: State) = s with {count = 0};",
            "State",
            "ここには参照・Map・Path を含まない値型が必要",
        ),
    ] {
        let input = source(DEFINITIONS.into(), body, true);
        // Predicate post, resolve_type exit, then the Law checking exit.
        let issue = terminal_priority(input.clone(), true, Checkpoint::LawSemantics, 2);
        assert_eq!(issue.message, message);
        let Location::Law { span } = issue.location else {
            panic!("Law span expected")
        };
        assert_eq!(&input.law().bytes()[span.0..span.1], fragment.as_bytes());
    }
}

#[test]
fn law_expression_set_term_and_numeric_rejections_keep_original_diagnostics_above_budget() {
    for (body, message) in [
        (
            "view bad(): Bool = set<Term<()->Z>>{} = set<Term<()->Z>>{};",
            "Set の要素型は Term・Path を含まない",
        ),
        (
            "view bad(): Bool = set { fn() => true | x in list<Bool>[true] } = set<Bool>{};",
            "Set の要素型は Term・Path を含まない",
        ),
        (
            "view bad(): Bool = -true = false;",
            "単項 - は Z・Q・Fp とその組",
        ),
        (
            "view bad(): Bool = true + false = false;",
            "算術は Z・Q・Fp とその組",
        ),
        (
            "view bad(): Bool = sum(list<Bool>[true]) = false;",
            "sum の要素は数値",
        ),
    ] {
        let input = source(DEFINITIONS.into(), body, true);
        // One expression checker exit and the Law checking exit follow the
        // predicate post. Nested operator parents add another expression exit.
        let issue = terminal_priority(input, true, Checkpoint::LawSemantics, 3);
        assert_eq!(issue.message, message);
    }
}

#[test]
fn reference_field_change_rejection_keeps_original_field_span_above_budget() {
    let definitions = DEFINITIONS.replace("\"type\": \"Z\"", r#""type": ["Ref","Counter.State"]"#);
    let input = source(
        definitions,
        "change bad(s: State) = s with {count = s};",
        true,
    );
    // The change-body exit uses LawChange; only the outer Law exit uses this point.
    let issue = terminal_priority(input.clone(), true, Checkpoint::LawSemantics, 1);
    assert_eq!(
        issue.message,
        "change は owner・参照・Map を含む field を更新しない"
    );
    let Location::Law { span } = issue.location else {
        panic!("Law span expected")
    };
    assert_eq!(&input.law().bytes()[span.0..span.1], b"count");
}

#[test]
fn data_property_true_remains_an_intermediate_fact_when_budget_stops_it() {
    // A Term inside data is valid. Its containment flag is an intermediate
    // property, so stopping its computation cannot produce a Syntax Issue.
    let input = data_source(r#"[["Term",[],"Bool"]]"#);
    let ordinary = check_definitions(&[("definition0", input.definitions()[0].bytes())]).unwrap();
    assert!(ordinary.data_properties()["Counter.Tree"].term_or_path);
    // Initial map (2), iteration/name (2), Leaf pre/post (2), Node/argument
    // entries (2), Term entry/post (2): the true predicate's post is step 10.
    for mode in 0..3 {
        let (mut control, seen) = probe(Checkpoint::DefinitionData, 10, mode);
        let failure = check_inputs(input.clone(), &mut control).unwrap_err();
        assert_eq!(seen.get(), 10);
        assert_eq!(failure.status(), InputStatus::Interrupted);
        empty_stage(&failure);
        assert_eq!(failure.issues(), [control.stop_reason().unwrap().wire()]);
    }
}
