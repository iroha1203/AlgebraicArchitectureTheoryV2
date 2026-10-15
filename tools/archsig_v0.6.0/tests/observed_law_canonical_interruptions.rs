use archsig::{
    canonical::{Json, sha256_digest},
    law::{self, lexer},
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
        prepare_observed,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const LAW: &str = include_str!("fixtures/counter.law");

fn sources(law: &str) -> InputSources {
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law.as_bytes().to_vec(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}

fn steps(law: &str) -> usize {
    let seen = Rc::new(Cell::new(0));
    let probe = seen.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::LawCanonical {
            probe.set(probe.get() + 1);
        }
        Usage::default()
    });
    check_inputs(sources(law), &mut control).unwrap();
    seen.get()
}

fn stop(at: usize, resource: usize) -> Control {
    let mut seen = 0;
    Control::new(
        Limits {
            time_ms: (resource == 1).then_some(7),
            memory_mib: (resource == 2).then_some(11),
        },
        move |point| {
            if point == Checkpoint::LawCanonical {
                seen += 1;
            }
            let stopping = seen == at;
            Usage {
                signal: (stopping && resource == 0).then_some(Signal::Term),
                elapsed_ms: if stopping && resource == 1 { 9 } else { 0 },
                memory_mib: if stopping && resource == 2 { 13 } else { 0 },
            }
        },
    )
}

fn assert_stopped(failure: &InputFailure, control: &Control, resource: usize) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    assert_eq!(failure.inputs().len(), 3);
    for input in failure.inputs() {
        assert!(input.bytes_digest.is_some());
        assert_eq!(input.model_digest.is_some(), input.id == "definition0");
    }
    let expected = match resource {
        0 => StopReason::Cancelled(Signal::Term),
        1 => StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 7,
            observed: 9,
        },
        2 => StopReason::BudgetExhausted {
            resource: Resource::MemoryMib,
            limit: 11,
            observed: 13,
        },
        _ => unreachable!(),
    };
    assert_eq!(control.stop_reason(), Some(expected.clone()));
    assert_eq!(failure.issues(), &[expected.wire()]);
    let wire = failure.wire();
    let Json::Obj(fields) = &wire else {
        panic!("object")
    };
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(fields[key], Json::Arr(vec![]));
    }
}

fn exercise(resource: usize) {
    let total = steps(LAW);
    let tokens = lexer::lex(LAW.as_bytes()).unwrap().len();
    // The first range walks tokens; the later range walks their JSON strings,
    // and the final checkpoint follows the model hash.
    assert!(total > 4 * tokens);
    for at in [1, 2 * tokens, total / 2, total] {
        let mut control = stop(at, resource);
        let failure = check_inputs(sources(LAW), &mut control).unwrap_err();
        assert_stopped(&failure, &control, resource);

        let mut control = stop(at, resource);
        let failure = prepare_observed(
            sources(LAW),
            &["a=evaluate(CountCheck.amount,s=@v/s)"],
            &mut control,
        )
        .unwrap_err();
        let PrepareFailure::Inputs(failure) = failure else {
            panic!("canonical interruption must precede request resolution")
        };
        assert_stopped(&failure, &control, resource);
    }
}

#[test]
fn law_canonical_tokens_strings_and_hash_share_cancellation() {
    exercise(0);
}

#[test]
fn law_canonical_tokens_strings_and_hash_share_time_budget() {
    exercise(1);
}

#[test]
fn law_canonical_tokens_strings_and_hash_share_memory_budget() {
    exercise(2);
}

#[test]
fn law_canonical_preserves_token_order_unicode_escaping_and_digest() {
    prepare_observed(
        sources(LAW),
        &["a=evaluate(CountCheck.amount,s=@v/s)"],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(
        law::model_canonical(&[]),
        r#"{"semantics":"archsig/0.6.0","tokens":[]}"#
    );
    let tokens = vec![lexer::Token {
        kind: lexer::TokenKind::Str,
        text: "雪\n\"\\\u{1}".into(),
        span: (0, 1),
    }];
    let expected =
        r#"{"semantics":"archsig/0.6.0","tokens":[{"kind":"string","text":"雪\u000a\"\\\u0001"}]}"#;
    assert_eq!(law::model_canonical(&tokens), expected);
    assert_eq!(
        law::model_digest(&tokens),
        sha256_digest(expected.as_bytes())
    );

    let expanded = LAW.replace(
        "view amount",
        "view second(s: State): Z = s.count;\n  view amount",
    );
    assert!(steps(&expanded) > steps(LAW));
    for text in [
        LAW.to_owned(),
        LAW.replace("version \"1\"", r#"version "\u0031""#),
        expanded,
    ] {
        let checked = check_inputs(sources(&text), &mut Control::unlimited()).unwrap();
        let tokens = lexer::lex(text.as_bytes()).unwrap();
        let expected = Json::obj([
            ("semantics", Json::str(law::SEMANTICS)),
            (
                "tokens",
                Json::Arr(
                    tokens
                        .iter()
                        .map(|token| {
                            Json::obj([
                                ("kind", Json::str(token.kind.wire())),
                                ("text", Json::str(token.text.clone())),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
        .canonical();
        assert_eq!(law::model_canonical(&tokens), expected);
        assert_eq!(
            checked.law().model_digest,
            sha256_digest(expected.as_bytes())
        );
        assert_eq!(checked.law().model_digest, law::model_digest(&tokens));
    }
}
