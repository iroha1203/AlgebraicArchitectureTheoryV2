//! 必須の構文・参照・schema拒否が確定した直後の予算優先と元診断を検査する。
use archsig::{
    canonical::Json,
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
        prepare_observed,
        request::ResolveFailure,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

const LAW: &str = include_str!("fixtures/counter.law");
const MAP: &str = include_str!("fixtures/counter.archmap.json");
fn sources(law: &str, map: &str) -> InputSources {
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law.as_bytes().to_vec(),
        map.as_bytes().to_vec(),
    )
}
fn probe(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let visits = Rc::new(Cell::new(0));
    let seen = visits.clone();
    let control = Control::new(
        Limits {
            time_ms: (mode == 1).then_some(1),
            memory_mib: (mode == 2).then_some(1),
        },
        move |current| {
            if current == point {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() >= at;
            Usage {
                signal: (stop && mode == 0).then_some(Signal::Term),
                elapsed_ms: u128::from(stop && mode == 1),
                memory_mib: u128::from(stop && mode == 2),
            }
        },
    );
    (control, visits)
}
fn request_issues(failure: &PrepareFailure) -> Vec<Json> {
    let PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { issues, .. },
        ..
    } = failure
    else {
        panic!("request invalid: {failure:?}")
    };
    issues.iter().map(|issue| issue.wire()).collect()
}
fn assert_request_priority(law: &str, ask: &str, point: Checkpoint, at: usize) {
    let normal =
        prepare_observed(sources(law, MAP), &[ask], &mut Control::unlimited()).unwrap_err();
    let expected = request_issues(&normal);
    for mode in 0..3 {
        let (mut control, visits) = probe(point, at, mode);
        let failure = prepare_observed(sources(law, MAP), &[ask], &mut control).unwrap_err();
        assert_eq!(visits.get(), at, "{ask}");
        if mode == 0 {
            assert!(matches!(
                failure,
                PrepareFailure::Requests {
                    failure: ResolveFailure::Interrupted {
                        reason: StopReason::Cancelled(Signal::Term)
                    },
                    ..
                }
            ));
        } else {
            assert_eq!(
                request_issues(&failure),
                expected,
                "original request/argument/message: {ask}"
            );
            let PrepareFailure::Requests {
                inputs,
                failure:
                    ResolveFailure::Invalid {
                        requests,
                        stop_reason,
                        ..
                    },
            } = &failure
            else {
                panic!("invalid request")
            };
            assert!(requests.is_empty());
            assert!(inputs.law().declarations.contains_key("CountCheck.amount"));
            assert_eq!(inputs.archmap().snapshots[0].subjects[0].id, "s");
            assert_eq!(stop_reason.as_ref(), control.stop_reason().as_ref());
            assert!(matches!(
                stop_reason,
                Some(StopReason::BudgetExhausted { .. })
            ));
            let Json::Obj(ref wire) = failure.wire().unwrap() else {
                panic!("wire")
            };
            assert_eq!(wire["status"], Json::str("invalid"));
            let mut expected_wire = vec![stop_reason.as_ref().unwrap().wire()];
            expected_wire.extend(expected.clone());
            assert_eq!(wire["issues"], Json::Arr(expected_wire));
            for key in ["requests", "answers", "nodes"] {
                assert_eq!(wire[key], Json::Arr(vec![]));
            }
        }
    }
}
#[test]
fn required_delimiter_mismatch_keeps_usage_at_the_first_false_post_from_bytes() {
    // user_name: 1..7; expect pre: 8; whitespace: 9,10; '=' mismatch post: 11.
    assert_request_priority(LAW, "a!", Checkpoint::RequestSyntax, 11);
    for mode in 0..3 {
        let (mut control, _) = probe(Checkpoint::RequestSyntax, 10, mode);
        assert!(matches!(
            prepare_observed(sources(LAW, MAP), &["a!"], &mut control),
            Err(PrepareFailure::Requests {
                failure: ResolveFailure::Interrupted { .. },
                ..
            })
        ));
    }
}
#[test]
fn required_declaration_and_binding_searches_keep_their_final_rejection_from_bytes() {
    // Repeat the complete first reading under a different name, without a second header.
    let extra = LAW
        .split_once("reading CountCheck")
        .unwrap()
        .1
        .split_once("reading CountAudit")
        .unwrap()
        .0;
    let ambiguous = format!("{LAW}\nreading Other{extra}");
    for (law, ask) in [
        (LAW, "a=evaluate(No.such)"),
        (LAW, "a=evaluate(absent)"),
        (ambiguous.as_str(), "a=evaluate(amount)"),
        (LAW, "a=evaluate(CountCheck.amount,unknown=@v/s)"),
        (LAW, "a=evaluate(CountCheck.amount,s=@absent/s)"),
        (LAW, "a=evaluate(CountCheck.amount,s=@v/absent)"),
        (LAW, "a=evaluate(CountCheck.amount)"),
    ] {
        let (mut baseline, total) = probe(Checkpoint::RequestBinding, usize::MAX, 0);
        prepare_observed(sources(law, MAP), &[ask], &mut baseline).unwrap_err();
        assert_request_priority(law, ask, Checkpoint::RequestBinding, total.get());
    }
}
#[test]
fn optional_selector_mismatches_and_untried_search_candidates_still_interrupt() {
    for (ask, point, at) in [
        // A valid request remains interrupted while the selector syntax is still being read.
        (
            "a=evaluate(CountCheck.amount,s=@v/s)",
            Checkpoint::RequestSyntax,
            47,
        ),
        // The first short-name candidate is CountAudit.bounded, before CountCheck.amount.
        ("a=evaluate(amount,s=@v/s)", Checkpoint::RequestBinding, 6),
    ] {
        for mode in 0..3 {
            let (mut control, visits) = probe(point, at, mode);
            assert!(matches!(
                prepare_observed(sources(LAW, MAP), &[ask], &mut control),
                Err(PrepareFailure::Requests {
                    failure: ResolveFailure::Interrupted { .. },
                    ..
                })
            ));
            assert_eq!(visits.get(), at);
        }
    }
}
#[test]
fn required_archmap_schema_rejections_keep_original_locations_after_the_first_false_post() {
    let cases = [
        (MAP.replace("\"id\": \"v\"", "\"id\": \"!\""), 3),
        (MAP.replace("\"id\": \"v\"", "\"id\": \"v!\""), 3),
        (
            MAP.replace("\"namespace\": \"Counter\"", "\"namespace\": \"Counter!\""),
            2,
        ),
        (
            MAP.replace("\"type\": \"Counter.State\"", "\"type\": \"Counter.!\""),
            4,
        ),
        (
            MAP.replace(
                "\"field\": \"Counter.State.count\"",
                "\"field\": \"Counter.State.!\"",
            ),
            4,
        ),
        (
            MAP.replace(
                "\"locations\": []",
                "\"locations\": [{\"source\":\"absent\",\"path\":\"a/../b\"}]",
            ),
            2,
        ),
        (MAP.replace("\"sources\": [],", "\"unknown\": [],"), 3),
        (MAP.replace("\"sources\": [],", ""), 3),
        (MAP.replace("\"format\": \"archsig.archmap/2\",", ""), 1),
        (MAP.replace("\"semantics\": \"archsig/0.6.0\",", ""), 1),
    ];
    for (map, trailing_posts) in cases {
        assert_ne!(map, MAP, "fixture mutation");
        let (mut baseline, total) = probe(Checkpoint::ArchMapSchema, usize::MAX, 0);
        let normal = check_inputs(sources(LAW, &map), &mut baseline).unwrap_err();
        assert!(matches!(
            normal.status(),
            InputStatus::Invalid | InputStatus::Unsupported
        ));
        // Start at the actual invalid-character/final-candidate post, before outer wrappers.
        for at in total.get() - trailing_posts..=total.get() {
            for mode in 0..3 {
                let (mut control, visits) = probe(Checkpoint::ArchMapSchema, at, mode);
                let failure = check_inputs(sources(LAW, &map), &mut control).unwrap_err();
                assert_eq!(visits.get(), at);
                assert!(!failure.declarations().is_empty());
                assert!(!failure.vocabularies().is_empty());
                if mode == 0 {
                    assert_eq!(failure.status(), InputStatus::Interrupted);
                } else {
                    assert_eq!(
                        failure.status(),
                        normal.status(),
                        "{map} at {at}/{}",
                        total.get()
                    );
                    let reason = control.stop_reason().expect("budget sampled");
                    assert!(matches!(reason, StopReason::BudgetExhausted { .. }));
                    let mut expected = vec![reason.wire()];
                    expected.extend_from_slice(normal.issues());
                    assert_eq!(
                        failure.issues(),
                        expected,
                        "original pointer/message at {at}"
                    );
                }
            }
        }
    }
}
