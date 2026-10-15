//! 小さい byte 入力から要求解決まで、構文・束縛・依存・射影の途中停止を検査する。
mod common;

use archsig::{
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
    let root = common::entity_json(
        "W.Root",
        "[]",
        &format!("[{}]", common::field_json("count", r#""Z""#)),
    );
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
    let law = format!(
        r#"{}reading R {{ use vocabulary W version "1" digest "{digest}";
      view pair(s: Root, t: Root): (Z,Z) = (s.count,t.count);
      view echo(s: Root): Root = s;
      view accept(x: Z, y: Z): Z = x + y;
      view choice(): Choice = Maybe(some(1));
      law required positive(s: Root): s.count >= 0;
    }}"#,
        common::HEADER
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],"sources":[],
      "origins":[{{"id":"o","mode":"specification","method":"小さい観測","locations":[],"note":"要求の中断"}}],
      "snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"s","type":"W.Root","origin":"o"}}],
        "atoms":[{{"id":"count","subject":"s","field":"W.Root.count","value":"2","origin":"o"}}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

const REQUESTS: [&str; 5] = [
    "  last = evaluate ( R.accept , x = $pair.value[1] , bind.y = $choice.value[0].some )  ",
    "pair=evaluate(R.pair,s=@v/s,t=$subject.value)",
    "subject=evaluate(R.echo,s=@v/s)",
    "choice=evaluate(R.choice)",
    "claim=check(R.positive,s=$subject.value)",
];

fn counting(point: Checkpoint) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    (
        Control::new(Limits::default(), move |current| {
            if current == point {
                seen.set(seen.get() + 1);
            }
            Usage::default()
        }),
        count,
    )
}

#[derive(Clone, Copy, Debug)]
enum Stop {
    Cancel,
    Time,
    Memory,
}

fn interrupt(point: Checkpoint, at: usize, kind: Stop) -> (Control, Rc<Cell<usize>>, StopReason) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let limits = Limits {
        time_ms: matches!(kind, Stop::Time).then_some(1),
        memory_mib: matches!(kind, Stop::Memory).then_some(1),
    };
    let reason = match kind {
        Stop::Cancel => StopReason::Cancelled(Signal::Term),
        Stop::Time => StopReason::BudgetExhausted {
            resource: Resource::TimeMs,
            limit: 1,
            observed: 1,
        },
        Stop::Memory => StopReason::BudgetExhausted {
            resource: Resource::MemoryMib,
            limit: 1,
            observed: 1,
        },
    };
    let control = Control::new(limits, move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        let stop = seen.get() >= at;
        Usage {
            signal: (stop && matches!(kind, Stop::Cancel)).then_some(Signal::Term),
            elapsed_ms: u128::from(stop && matches!(kind, Stop::Time)),
            memory_mib: u128::from(stop && matches!(kind, Stop::Memory)),
        }
    });
    (control, count, reason)
}

fn assert_request_stop(
    failure: PrepareFailure,
    control: &mut Control,
    count: &Cell<usize>,
    at: usize,
    reason: &StopReason,
) {
    let wire_value = failure.wire().expect("中断は内部結果を返す");
    let archsig::canonical::Json::Obj(fields) = &wire_value else {
        panic!("object")
    };
    assert_eq!(
        fields["issues"],
        archsig::canonical::Json::Arr(vec![reason.wire()])
    );
    let wire = wire_value.canonical();
    for empty in [r#""requests":[]"#, r#""nodes":[]"#, r#""answers":[]"#] {
        assert!(wire.contains(empty), "{empty}: {wire}");
    }
    assert!(wire.contains(r#""status":"interrupted""#));
    assert!(!wire.contains(r#""code":"usage""#));
    assert!(!wire.contains(r#""code":"cycle""#));
    let PrepareFailure::Requests {
        inputs,
        failure: ResolveFailure::Interrupted { reason: actual },
    } = failure
    else {
        panic!("要求段階のtypedな中断を期待");
    };
    assert_eq!(&actual, reason);
    assert!(inputs.law().declarations.contains_key("R.accept"));
    assert_eq!(inputs.archmap().snapshots[0].subjects[0].id, "s");
    assert_eq!(count.get(), at);
    assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason.clone()));
    assert_eq!(count.get(), at, "停止後にprobeや新たな導出を始めない");
}

fn assert_known_budget_wire(failure: &PrepareFailure, reason: &StopReason, original_code: &str) {
    use archsig::canonical::Json;
    let Json::Obj(ref wire) = failure.wire().unwrap() else {
        panic!("object")
    };
    assert_eq!(wire["status"], Json::str("invalid"));
    assert_eq!(wire["nodes"], Json::Arr(vec![]));
    assert_eq!(wire["answers"], Json::Arr(vec![]));
    let Json::Arr(issues) = &wire["issues"] else {
        panic!("issues")
    };
    assert_eq!(
        issues[0],
        reason.wire(),
        "resource/limit/observedを理由に保持する"
    );
    assert!(issues.len() > 1, "元の確定した不正も保持する");
    for issue in &issues[1..] {
        let Json::Obj(issue) = issue else {
            panic!("issue object")
        };
        assert_eq!(issue["code"], Json::str(original_code));
    }
    let PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { stop_reason, .. },
        ..
    } = failure
    else {
        panic!("known Invalid")
    };
    assert_eq!(stop_reason.as_ref(), Some(reason));
}

#[test]
fn syntax_binding_dependency_and_projection_stop_at_start_middle_and_end() {
    for point in [
        Checkpoint::RequestSyntax,
        Checkpoint::RequestBinding,
        Checkpoint::RequestDependency,
        Checkpoint::Projection,
    ] {
        let (mut baseline, total) = counting(point);
        let complete = prepare_observed(sources(), &REQUESTS, &mut baseline).unwrap();
        assert_eq!(complete.requests().evaluation_order(), &[2, 1, 3, 0, 4]);
        assert!(total.get() > 4, "各phaseに反復の途中がある: {point:?}");
        for at in [1, total.get() / 2, total.get()] {
            for kind in [Stop::Cancel, Stop::Time, Stop::Memory] {
                let (mut control, count, reason) = interrupt(point, at, kind);
                let failure = prepare_observed(sources(), &REQUESTS, &mut control).unwrap_err();
                assert_request_stop(failure, &mut control, &count, at, &reason);
            }
        }
    }
}

#[test]
fn stopping_inside_cycle_walk_preserves_only_cycles_already_established() {
    let asks = [
        "a=evaluate(R.echo,s=$b.value)",
        "b=evaluate(R.echo,s=$a.value)",
        "later=check(R.positive,s=$a.value)",
    ];
    let (mut baseline, total) = counting(Checkpoint::RequestDependency);
    let cycle = prepare_observed(sources(), &asks, &mut baseline).unwrap_err();
    assert!(
        matches!(cycle,PrepareFailure::Requests { failure: ResolveFailure::Invalid { ref issues,.. },.. }
        if issues.iter().map(|i| i.request.as_str()).collect::<Vec<_>>() == ["a", "b"])
    );
    for at in [1, total.get() / 2, total.get() - 4, total.get()] {
        for kind in [Stop::Cancel, Stop::Time] {
            let (mut control, count, reason) = interrupt(Checkpoint::RequestDependency, at, kind);
            let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
            if matches!(kind, Stop::Time)
                && let PrepareFailure::Requests {
                    failure:
                        ResolveFailure::Invalid {
                            requests,
                            issues,
                            stop_reason,
                        },
                    ..
                } = &failure
            {
                assert_eq!(stop_reason.as_ref(), Some(&reason));
                assert_known_budget_wire(&failure, &reason, "cycle");
                assert_eq!(requests.len(), 3, "解決済みgraphを保持する");
                assert!(!issues.is_empty());
                assert!(issues.iter().all(|i| i.code == RequestIssueCode::Cycle
                    && ["a", "b"].contains(&i.request.as_str())));
                assert_eq!(count.get(), at, "budget後に未確認cycleを探索しない");
                assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
                assert_eq!(count.get(), at);
            } else {
                assert_request_stop(failure, &mut control, &count, at, &reason);
            }
        }
    }
}

#[test]
fn a_stop_at_the_last_syntax_error_boundary_is_not_usage() {
    let asks = ["bad=evaluate(R.accept,x=$pair.value[01])"];
    let (mut baseline, total) = counting(Checkpoint::RequestSyntax);
    assert!(matches!(
        prepare_observed(sources(), &asks, &mut baseline),
        Err(PrepareFailure::Requests {
            failure: ResolveFailure::Invalid { .. },
            ..
        })
    ));
    let (mut control, count, reason) =
        interrupt(Checkpoint::RequestSyntax, total.get(), Stop::Cancel);
    let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
    assert_request_stop(failure, &mut control, &count, total.get(), &reason);
    for kind in [Stop::Time, Stop::Memory] {
        let (mut control, count, reason) = interrupt(Checkpoint::RequestSyntax, total.get(), kind);
        let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
        assert_known_budget_wire(&failure, &reason, "usage");
        assert!(matches!(failure, PrepareFailure::Requests {
            failure: ResolveFailure::Invalid { issues, .. }, ..
        } if issues.len() == 1 && issues[0].code == RequestIssueCode::Syntax));
        assert_eq!(count.get(), total.get());
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        assert_eq!(count.get(), total.get());
    }
}

#[test]
fn failed_projection_candidates_cannot_swallow_cancellation_or_budget() {
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    let candidates = || {
        ProjectionType::Dynamic(vec![
            ProjectionType::Law(Type::Bool),
            ProjectionType::Law(Type::Option(Box::new(Type::Z))),
        ])
    };
    let path = [ProjectionStep::Field("some".into())];
    let (mut baseline, total) = counting(Checkpoint::Projection);
    let plan =
        resolve_projection_controlled(checked.law(), candidates(), &path, &mut baseline).unwrap();
    assert_eq!(plan.ty, ProjectionType::Law(Type::Z));
    // 不適合なBool候補を捨てる分岐と、次候補の成功後を含む小さい全境界へ注入する。
    for at in 1..=total.get() {
        for kind in [Stop::Cancel, Stop::Time] {
            let (mut control, count, reason) = interrupt(Checkpoint::Projection, at, kind);
            assert_eq!(
                resolve_projection_controlled(checked.law(), candidates(), &path, &mut control),
                Err(ProjectionFailure::Interrupted(reason.clone()))
            );
            assert_eq!(count.get(), at);
            assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        }
    }
}

#[test]
fn final_request_budget_preserves_known_type_error_but_cancellation_wins() {
    let type_asks = [
        "bad=evaluate(R.echo,s=$number.value)",
        "number=evaluate(R.accept,x=$pair.value[0],y=$pair.value[1])",
        "pair=evaluate(R.pair,s=@v/s,t=@v/s)",
    ];
    let raw_duplicate = ["bad=evaluate(R.echo,s=@v/s,s=@v/s)"];
    let normalized_duplicate = ["bad=evaluate(R.echo,s=@v/s,bind.s=@v/s)"];
    let reserved = ["let=evaluate(R.echo,s=@v/s)"];
    for (asks, point, expected) in [
        (
            type_asks.as_slice(),
            Checkpoint::Resolve,
            RequestIssueCode::Type,
        ),
        (
            raw_duplicate.as_slice(),
            Checkpoint::RequestSyntax,
            RequestIssueCode::DuplicateArgument,
        ),
        (
            normalized_duplicate.as_slice(),
            Checkpoint::RequestBinding,
            RequestIssueCode::DuplicateArgument,
        ),
        (
            reserved.as_slice(),
            Checkpoint::RequestSyntax,
            RequestIssueCode::Syntax,
        ),
    ] {
        let (mut baseline, total) = counting(point);
        let normal = prepare_observed(sources(), asks, &mut baseline).unwrap_err();
        assert!(matches!(normal,
            PrepareFailure::Requests { failure: ResolveFailure::Invalid { issues, stop_reason: None, .. }, .. }
            if issues[0].code == expected));
        for kind in [Stop::Time, Stop::Memory, Stop::Cancel] {
            let (mut control, count, reason) = interrupt(point, total.get(), kind);
            let failure = prepare_observed(sources(), asks, &mut control).unwrap_err();
            if matches!(kind, Stop::Cancel) {
                assert_request_stop(failure, &mut control, &count, total.get(), &reason);
            } else {
                assert_known_budget_wire(&failure, &reason, "usage");
                assert!(
                    matches!(failure, PrepareFailure::Requests { failure: ResolveFailure::Invalid { issues, .. }, .. }
                    if issues[0].code == expected)
                );
                assert_eq!(count.get(), total.get());
                assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
            }
        }
    }
}

#[test]
fn budget_after_first_of_two_independent_cycles_keeps_only_confirmed_cycle() {
    use archsig::observed::request::resolve_observed_requests_controlled;
    let checked = check_inputs(sources(), &mut Control::unlimited()).unwrap();
    let asks = [
        "a=evaluate(R.echo,s=$b.value)",
        "b=evaluate(R.echo,s=$a.value)",
        "c=evaluate(R.echo,s=$d.value)",
        "d=evaluate(R.echo,s=$c.value)",
    ];
    let (mut baseline, total) = counting(Checkpoint::RequestDependency);
    let normal = resolve_observed_requests_controlled(
        checked.law(),
        checked.archmap(),
        &asks,
        &mut baseline,
    )
    .unwrap_err();
    assert!(
        matches!(normal, ResolveFailure::Invalid { issues, stop_reason: None, .. }
        if issues.iter().map(|i| i.request.as_str()).collect::<Vec<_>>() == ["a", "b", "c", "d"])
    );
    let mut first_known = None;
    // Each candidate is the same fixed four-node graph, stopped at one of its finite checkpoints.
    for at in 1..=total.get() {
        let (mut control, count, reason) = interrupt(Checkpoint::RequestDependency, at, Stop::Time);
        let failure = resolve_observed_requests_controlled(
            checked.law(),
            checked.archmap(),
            &asks,
            &mut control,
        )
        .unwrap_err();
        assert_eq!(count.get(), at);
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
        if let ResolveFailure::Invalid {
            requests,
            issues,
            stop_reason,
        } = failure
        {
            assert_eq!(requests.len(), 4);
            assert!(matches!(
                stop_reason,
                Some(StopReason::BudgetExhausted { .. })
            ));
            first_known = Some(issues.into_iter().map(|i| i.request).collect::<Vec<_>>());
            break;
        }
    }
    assert_eq!(first_known.unwrap(), ["a"]);
}
