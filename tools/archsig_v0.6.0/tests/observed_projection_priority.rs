//! 射影不正の確定後の予算、取消、動的候補の局所棄却を区別する。
mod common;

use archsig::{
    canonical::Json,
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputSources, check_inputs},
        prepare_observed,
        projection::{
            ProjectionFailure, ProjectionStep, ProjectionType, resolve_projection_controlled,
        },
        request::{RequestIssueCode, ResolveFailure},
    },
    result::Signal,
    types::Type,
};
use std::{cell::Cell, rc::Rc};

fn sources() -> InputSources {
    let root = common::entity_json("W.Root", "[]", "[]");
    let choice = common::data_json(
        "W.Choice",
        &format!(
            "[{},{}]",
            common::constructor_json("Maybe", r#"[["Option","Z"]]"#),
            common::constructor_json("Items", r#"[["List","Z"]]"#)
        ),
    );
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{root},{choice}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["W"].digest;
    let law = common::reading_with(
        "W",
        digest,
        r#"
        view echo(s: Root): Root = s;
        view choice(): Choice = Maybe(some(1));
        view pair(): (Z,Z) = (1,2);
    "#,
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
        "vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],
        "sources":[],"origins":[{{"id":"o","mode":"specification","method":"射影検査",
        "locations":[],"note":"小さい要求"}}],"snapshots":[{{"id":"v","origin":"o",
        "subjects":[{{"id":"s","type":"W.Root","origin":"o"}}],"atoms":[]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

#[derive(Clone, Copy)]
enum Stop {
    Cancel,
    Time,
    Memory,
}

fn probe(at: Option<usize>, stop: Stop) -> (Control, Rc<Cell<usize>>, StopReason) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let reason = match stop {
        Stop::Cancel => StopReason::Cancelled(Signal::Term),
        Stop::Time => StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 3,
            observed: 5,
        },
        Stop::Memory => StopReason::BudgetExhausted {
            resource: Resource::MemoryMib,
            limit: 7,
            observed: 11,
        },
    };
    let control = Control::new(
        Limits {
            time_ms: matches!(stop, Stop::Time).then_some(3),
            memory_mib: matches!(stop, Stop::Memory).then_some(7),
        },
        move |point| {
            if point == Checkpoint::Projection {
                seen.set(seen.get() + 1);
            }
            let hit = at.is_some_and(|at| seen.get() >= at);
            Usage {
                elapsed_ms: if hit && matches!(stop, Stop::Time) {
                    5
                } else {
                    0
                },
                memory_mib: if hit && matches!(stop, Stop::Memory) {
                    11
                } else {
                    0
                },
                signal: (hit && matches!(stop, Stop::Cancel)).then_some(Signal::Term),
            }
        },
    );
    (control, count, reason)
}

#[test]
fn known_projection_errors_preserve_usage_and_budget_while_cancellation_wins() {
    for (bad, producer, message) in [
        (
            "bad=evaluate(R.echo,s=$choice.value.some)",
            "choice=evaluate(R.choice)",
            "この型で公開されていない射影",
        ),
        (
            "bad=evaluate(R.echo,s=$pair.value[2])",
            "pair=evaluate(R.pair)",
            "Tuple の index が範囲外",
        ),
        (
            "bad=evaluate(R.echo,s=$choice.value[1])",
            "choice=evaluate(R.choice)",
            "全 constructor で index が範囲外",
        ),
        (
            "bad=evaluate(R.echo,s=$choice.value[0].missing)",
            "choice=evaluate(R.choice)",
            "公開された射影が型候補にない",
        ),
    ] {
        let asks = [bad, producer];
        let (mut baseline, total, _) = probe(None, Stop::Time);
        let normal = prepare_observed(sources(), &asks, &mut baseline).unwrap_err();
        let PrepareFailure::Requests {
            failure:
                ResolveFailure::Invalid {
                    issues,
                    stop_reason: None,
                    ..
                },
            ..
        } = &normal
        else {
            panic!("projection error");
        };
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, RequestIssueCode::Projection);
        assert_eq!(issues[0].request, "bad");
        assert_eq!(issues[0].argument, "bind.s");
        assert_eq!(issues[0].message, message);
        let expected_issue = issues[0].wire();
        if bad.ends_with("value.some)") {
            assert_eq!(total.get(), 4, "review counterexample point");
        }
        for kind in [Stop::Cancel, Stop::Time, Stop::Memory] {
            let (mut control, count, reason) = probe(Some(total.get()), kind);
            let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
            let wire_value = failure.wire().unwrap();
            let Json::Obj(wire) = &wire_value else {
                panic!("object");
            };
            assert_eq!(wire["nodes"], Json::Arr(vec![]));
            assert_eq!(wire["answers"], Json::Arr(vec![]));
            if matches!(kind, Stop::Cancel) {
                assert_eq!(wire["status"], Json::str("interrupted"));
                assert_eq!(wire["issues"], Json::Arr(vec![reason.wire()]));
                assert!(
                    matches!(&failure, PrepareFailure::Requests { failure: ResolveFailure::Interrupted { reason: actual }, .. } if actual == &reason)
                );
            } else {
                assert_eq!(wire["status"], Json::str("invalid"));
                assert_eq!(
                    wire["issues"],
                    Json::Arr(vec![reason.wire(), expected_issue.clone()])
                );
                assert!(
                    matches!(&failure, PrepareFailure::Requests { failure: ResolveFailure::Invalid { stop_reason: Some(actual), .. }, .. } if actual == &reason)
                );
            }
            let PrepareFailure::Requests { inputs, .. } = &failure else {
                panic!("requests");
            };
            assert!(inputs.law().declarations.contains_key("R.choice"));
            assert_eq!(inputs.archmap().snapshots[0].subjects[0].id, "s");
            assert_eq!(count.get(), total.get());
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            assert_eq!(
                count.get(),
                total.get(),
                "latched stop does not resume the probe"
            );
        }
        // Before the first projection step no invalid result has been established.
        for kind in [Stop::Cancel, Stop::Time, Stop::Memory] {
            let (mut control, count, reason) = probe(Some(1), kind);
            let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
            assert!(
                matches!(failure, PrepareFailure::Requests { failure: ResolveFailure::Interrupted { reason: actual }, .. } if actual == reason)
            );
            assert_eq!(count.get(), 1);
        }
    }
}

#[test]
fn early_projection_errors_use_the_same_priority_policy() {
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    for (ty, path, message) in [
        (
            ProjectionType::Law(Type::Data("W.Absent".into())),
            vec![ProjectionStep::Index(0)],
            "data 宣言がない",
        ),
        (
            ProjectionType::Law(Type::Data("W.Root".into())),
            vec![ProjectionStep::Index(0)],
            "data 型でない",
        ),
        (
            ProjectionType::Law(Type::Path("W.Root".into(), "W.Root".into())),
            vec![ProjectionStep::Field("generators".into())],
            "generators は index まで指定する",
        ),
        (
            ProjectionType::Dynamic(vec![]),
            vec![ProjectionStep::Field("some".into())],
            "公開された射影が型候補にない",
        ),
    ] {
        let (mut baseline, total, _) = probe(None, Stop::Time);
        assert_eq!(
            resolve_projection_controlled(checked.law(), ty.clone(), &path, &mut baseline),
            Err(ProjectionFailure::Invalid(message.into()))
        );
        for kind in [Stop::Cancel, Stop::Time, Stop::Memory] {
            let (mut control, count, reason) = probe(Some(total.get()), kind);
            let expected = if matches!(kind, Stop::Cancel) {
                ProjectionFailure::Interrupted(reason.clone())
            } else {
                ProjectionFailure::Invalid(message.into())
            };
            assert_eq!(
                resolve_projection_controlled(checked.law(), ty.clone(), &path, &mut control),
                Err(expected)
            );
            assert_eq!(count.get(), total.get());
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        }
    }
}

#[test]
fn dynamic_candidate_rejection_never_establishes_global_invalidity() {
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    let initial = || {
        ProjectionType::Dynamic(vec![
            ProjectionType::Law(Type::Bool),
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
        ])
    };
    let path = [ProjectionStep::Field("some".into())];
    let (mut baseline, total, _) = probe(None, Stop::Time);
    let normal =
        resolve_projection_controlled(checked.law(), initial(), &path, &mut baseline).unwrap();
    assert_eq!(normal.ty, ProjectionType::Law(Type::Z));
    for at in 1..=total.get() {
        for kind in [Stop::Cancel, Stop::Time, Stop::Memory] {
            let (mut control, count, reason) = probe(Some(at), kind);
            assert_eq!(
                resolve_projection_controlled(checked.law(), initial(), &path, &mut control),
                Err(ProjectionFailure::Interrupted(reason.clone()))
            );
            assert_eq!(count.get(), at);
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            assert_eq!(count.get(), at);
        }
    }
}
