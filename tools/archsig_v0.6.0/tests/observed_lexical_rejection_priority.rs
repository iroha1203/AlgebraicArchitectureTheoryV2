//! 必須の字句拒否を確定した直後にも、元診断と共有停止理由を保持する。
mod common;
use archsig::{
    archmap::check_archmap,
    definition::check_definitions,
    issue::{Code, Issue, Location},
    observed::{
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
    },
    result::{ResultIssue, Signal},
};
use std::{cell::Cell, rc::Rc};

fn probe(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    (
        Control::new(
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
                    signal: (stop && mode == 0).then_some(Signal::Term),
                    elapsed_ms: u128::from(stop && mode == 1),
                    memory_mib: u128::from(stop && mode == 2),
                }
            },
        ),
        count,
    )
}

fn assert_priority(
    make: impl Fn() -> InputSources,
    issue: Issue,
    point: Checkpoint,
    after_rejection: usize,
    definition_failure: bool,
) {
    let (mut baseline, count) = probe(point, usize::MAX, 0);
    let original = check_inputs(make(), &mut baseline).unwrap_err();
    assert_eq!(original.status(), InputStatus::Invalid);
    assert_eq!(original.issues(), [ResultIssue::Input(issue).wire()]);
    let total = count.get();
    let first_post = total.checked_sub(after_rejection).unwrap();
    assert!(first_post > 1);
    // The private helper tests independently pin the exact per-character posts.
    // Here the offsets are only the source's Result-unwind wrappers, so the
    // first injection is the post of the rejecting operation itself.
    for at in [first_post - 1, first_post, total] {
        for mode in 0..3 {
            let (mut control, _) = probe(point, at, mode);
            let failure = check_inputs(make(), &mut control).unwrap_err();
            assert_eq!(failure.declarations().is_empty(), definition_failure);
            assert_eq!(failure.primitives().is_empty(), definition_failure);
            assert_eq!(failure.vocabularies().is_empty(), definition_failure);
            let reason = control
                .stop_reason()
                .expect("the requested post was sampled");
            if mode == 0 || at < first_post {
                assert_eq!(failure.status(), InputStatus::Interrupted, "{at}/{total}");
                assert_eq!(failure.issues(), [reason.wire()]);
            } else {
                assert_eq!(failure.status(), InputStatus::Invalid, "{at}/{total}");
                assert!(matches!(reason, StopReason::BudgetExhausted { .. }));
                let mut expected = vec![reason.wire()];
                expected.extend_from_slice(original.issues());
                assert_eq!(
                    failure.issues(),
                    expected,
                    "original code/message/pointer/span/details"
                );
            }
            if mode == 0 {
                assert_eq!(reason, StopReason::Cancelled(Signal::Term));
            }
        }
    }
}

fn definition_source(namespace: &str, ty: &str) -> String {
    common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json(
            namespace,
            &format!(
                "[{}]",
                common::entity_json(
                    "V.Root",
                    "[]",
                    &format!("[{}]", common::field_json("value", ty))
                )
            ),
            "[]",
        )
    ))
}

#[test]
fn definition_name_and_fp_digit_refusals_keep_empty_stage_and_exact_diagnostic() {
    for (namespace, ty, trailing, pointer) in [
        ("bad!", "\"Z\"", 3, "/vocabularies/0/namespace"),
        ("!bad", "\"Z\"", 2, "/vocabularies/0/namespace"),
        ("law", "\"Z\"", 2, "/vocabularies/0/namespace"),
        (
            "V",
            "[\"Fp\",\"1x\"]",
            6,
            "/vocabularies/0/declarations/0/fields/0/type/1",
        ),
        (
            "V",
            "[\"Fp\",\"0\"]",
            5,
            "/vocabularies/0/declarations/0/fields/0/type/1",
        ),
        (
            "V",
            "[\"Fp\",\"\"]",
            5,
            "/vocabularies/0/declarations/0/fields/0/type/1",
        ),
    ] {
        let definition = definition_source(namespace, ty);
        let issue = check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap_err()
            .issue;
        assert_eq!(issue.code, Code::Syntax);
        assert_eq!(
            issue.location,
            Location::Definition {
                input: "definition0".into(),
                pointer: pointer.into(),
                span: None,
            }
        );
        assert_priority(
            || {
                InputSources::from_bytes(
                    vec![definition.as_bytes().to_vec()],
                    b"unread law".to_vec(),
                    b"unread map".to_vec(),
                )
            },
            issue,
            Checkpoint::DefinitionSchema,
            trailing,
            true,
        );
    }
}

#[test]
fn required_field_exhaustion_keeps_invalid_without_promoting_an_earlier_mismatch() {
    let definition = r#"{"semantics":"archsig/0.6.0","vocabularies":[]}"#;
    let issue = check_definitions(&[("definition0", definition.as_bytes())])
        .unwrap_err()
        .issue;
    assert_eq!(issue.code, Code::Syntax);
    assert_eq!(issue.message, "欄 `format` が必要");
    // Last find post, then read's enclosing schema post.
    assert_priority(
        || {
            InputSources::from_bytes(
                vec![definition.as_bytes().to_vec()],
                b"unread law".to_vec(),
                b"unread map".to_vec(),
            )
        },
        issue,
        Checkpoint::DefinitionSchema,
        1,
        true,
    );
}

fn value_sources(ty: &str, value: &str) -> InputSources {
    let definition = definition_source("V", ty);
    value_sources_from_definition(definition, value)
}

fn value_sources_from_definition(definition: String, value: &str) -> InputSources {
    let defs = common::definitions_ok(&[&definition]);
    let digest = &defs.vocabularies["V"].digest;
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"test","locations":[],"note":"value"}}],"snapshots":[{{"id":"s","origin":"model","subjects":[{{"id":"root","type":"V.Root","origin":"model"}}],"atoms":[{{"id":"v","subject":"root","field":"V.Root.value","origin":"model","value":{value}}}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        common::reading("view ready(): Bool = true;").into_bytes(),
        map.into_bytes(),
    )
}

fn choice_definition() -> String {
    let root = common::entity_json(
        "V.Root",
        "[]",
        &format!(
            "[{}]",
            common::field_json("value", r#"["Data","V.Choice"]"#)
        ),
    );
    let data = common::data_json(
        "V.Choice",
        &format!(
            "[{},{}]",
            common::constructor_json("A", "[]"),
            common::constructor_json("B", "[]")
        ),
    );
    common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{root},{data}]"), "[]")
    ))
}

#[test]
fn constructor_and_field_exhaustion_keep_only_established_lookup_rejections() {
    let definition = choice_definition();
    let absent = r#"{"tag":"Absent","args":[]}"#;
    let source = value_sources_from_definition(definition.clone(), absent);
    let defs = check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
    let issue = check_archmap(source.archmap().bytes(), &defs)
        .unwrap_err()
        .issue;
    assert_eq!(
        issue.location,
        Location::ArchMap {
            pointer: "/snapshots/0/atoms/0/value/tag".into(),
            span: None
        }
    );
    assert_priority(
        || value_sources_from_definition(definition.clone(), absent),
        issue,
        Checkpoint::ArchMapSchema,
        3,
        false,
    );

    let (mut baseline, total) = probe(Checkpoint::ArchMapSchema, usize::MAX, 0);
    check_inputs(
        value_sources_from_definition(definition.clone(), absent),
        &mut baseline,
    )
    .unwrap_err();
    // A's post is two points before the rejecting final B post. A matching
    // second constructor remains untried, so the first false cannot be invalid.
    let at = total.get() - 5;
    for mode in 0..3 {
        let (mut control, _) = probe(Checkpoint::ArchMapSchema, at, mode);
        let failure = check_inputs(
            value_sources_from_definition(definition.clone(), r#"{"tag":"B","args":[]}"#),
            &mut control,
        )
        .unwrap_err();
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert_eq!(failure.issues(), [control.stop_reason().unwrap().wire()]);
    }

    let make_field = || {
        let source = value_sources("\"Z\"", "\"1\"");
        InputSources::from_bytes(
            vec![source.definitions()[0].bytes().to_vec()],
            source.law().bytes().to_vec(),
            String::from_utf8(source.archmap().bytes().to_vec())
                .unwrap()
                .replace("V.Root.value", "V.Root.absent")
                .into_bytes(),
        )
    };
    let source = make_field();
    let defs = check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
    let issue = check_archmap(source.archmap().bytes(), &defs)
        .unwrap_err()
        .issue;
    assert_eq!(issue.code, Code::Reference);
    assert_eq!(
        issue.location,
        Location::ArchMap {
            pointer: "/snapshots/0/atoms/0/field".into(),
            span: None
        }
    );
    assert_priority(make_field, issue, Checkpoint::ArchMapSchema, 2, false);
}

#[test]
fn required_data_and_term_fields_keep_the_exact_outer_value_diagnostic() {
    for (data, value, message) in [
        (
            true,
            r#"{"bad":"A","args":[]}"#,
            "data の値は {\"tag\":...,\"args\":[...]}",
        ),
        (
            true,
            r#"{"tag":"A","bad":[]}"#,
            "data の値は {\"tag\":...,\"args\":[...]}",
        ),
        (
            false,
            r#"{"bad":["x"],"body":"0"}"#,
            "Term は {\"params\":[...],\"body\":\"...\"}",
        ),
        (
            false,
            r#"{"params":["x"],"bad":"0"}"#,
            "Term は {\"params\":[...],\"body\":\"...\"}",
        ),
    ] {
        let definition = if data {
            choice_definition()
        } else {
            definition_source("V", r#"["Term",["Z"],"Z"]"#)
        };
        let source = value_sources_from_definition(definition.clone(), value);
        let defs = check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
        let issue = check_archmap(source.archmap().bytes(), &defs)
            .unwrap_err()
            .issue;
        assert_eq!(issue.code, Code::Syntax);
        assert_eq!(issue.message, message);
        assert_eq!(
            issue.location,
            Location::ArchMap {
                pointer: "/snapshots/0/atoms/0/value".into(),
                span: None
            }
        );
        assert_priority(
            || value_sources_from_definition(definition.clone(), value),
            issue,
            Checkpoint::ArchMapSchema,
            3,
            false,
        );
    }
}

#[test]
fn integer_encoding_refusals_keep_checked_tables_and_original_numeric_message() {
    for (ty, value, trailing) in [
        ("\"Z\"", "\"1x\"", 3),
        ("\"Z\"", "\"\"", 3),
        ("\"Z\"", "\"x1\"", 3),
        ("\"Z\"", "\"00\"", 3),
        ("\"Z\"", "\"-0\"", 3),
        ("\"Q\"", "[\"1x\",\"1\"]", 3),
        ("\"Q\"", "[\"1\",\"1x\"]", 3),
        ("[\"Fp\",\"13\"]", "\"1x\"", 3),
        ("[\"Fp\",\"13\"]", "\"-1\"", 2),
    ] {
        let source = value_sources(ty, value);
        let defs = check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
        let issue = check_archmap(source.archmap().bytes(), &defs)
            .unwrap_err()
            .issue;
        assert_eq!(issue.code, Code::Syntax);
        assert_eq!(
            issue.location,
            Location::ArchMap {
                pointer: "/snapshots/0/atoms/0/value".into(),
                span: None
            }
        );
        assert_priority(
            || value_sources(ty, value),
            issue,
            Checkpoint::ArchMapSchema,
            trailing,
            false,
        );
    }
}

#[test]
fn term_parameter_refusals_keep_the_parameter_pointer_and_checked_tables() {
    for (name, trailing) in [("x!", 3), ("!x", 2), ("law", 2)] {
        let value = format!(r#"{{"params":["{name}"],"body":"0"}}"#);
        let ty = r#"["Term",["Z"],"Z"]"#;
        let source = value_sources(ty, &value);
        let defs = check_definitions(&[("definition0", source.definitions()[0].bytes())]).unwrap();
        let issue = check_archmap(source.archmap().bytes(), &defs)
            .unwrap_err()
            .issue;
        assert_eq!(issue.code, Code::Syntax);
        assert_eq!(
            issue.location,
            Location::ArchMap {
                pointer: "/snapshots/0/atoms/0/value/params/0".into(),
                span: None
            }
        );
        assert_priority(
            || value_sources(ty, &value),
            issue,
            Checkpoint::ArchMapSchema,
            trailing,
            false,
        );
    }
}
