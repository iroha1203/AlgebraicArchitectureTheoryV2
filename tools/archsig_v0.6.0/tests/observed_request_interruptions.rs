//! 小さい byte 入力から要求解決まで、構文・束縛・依存・射影の途中停止を検査する。
use crate::common;

use archsig::{
    control::{Checkpoint, Control},
    input::{InputSources, check_inputs},
    observed::{
        PrepareFailure, prepare_observed,
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
    let digest = &definitions.vocabularies()["W"].digest;
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
        Control::new(move |current| {
            if current == point {
                seen.set(seen.get() + 1);
            }
            None
        }),
        count,
    )
}

fn interrupt(point: Checkpoint, at: usize) -> (Control, Rc<Cell<usize>>, Signal) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(move |current| {
        if current == point {
            seen.set(seen.get() + 1);
        }
        (seen.get() >= at).then_some(Signal::Term)
    });
    (control, count, Signal::Term)
}

fn assert_request_stop(
    failure: PrepareFailure,
    control: &mut Control,
    count: &Cell<usize>,
    at: usize,
    reason: &Signal,
) {
    let wire_value = failure.wire().expect("中断は内部結果を返す");
    let archsig::canonical::Json::Obj(fields) = &wire_value else {
        panic!("object")
    };
    assert_eq!(
        fields["issues"],
        archsig::canonical::Json::Arr(vec![reason.issue()])
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
    assert!(inputs.law().declarations().contains_key("R.accept"));
    assert_eq!(inputs.archmap().snapshots()[0].subjects[0].id, "s");
    assert_eq!(count.get(), at);
    assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(*reason));
    assert_eq!(count.get(), at, "停止後にprobeや新たな導出を始めない");
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
            let (mut control, count, reason) = interrupt(point, at);
            let failure = prepare_observed(sources(), &REQUESTS, &mut control).unwrap_err();
            assert_request_stop(failure, &mut control, &count, at, &reason);
        }
    }
}

#[test]
fn stopping_inside_cycle_walk_reports_interruption() {
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
        let (mut control, count, reason) = interrupt(Checkpoint::RequestDependency, at);
        let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
        assert_request_stop(failure, &mut control, &count, at, &reason);
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
    let (mut control, count, reason) = interrupt(Checkpoint::RequestSyntax, total.get());
    let failure = prepare_observed(sources(), &asks, &mut control).unwrap_err();
    assert_request_stop(failure, &mut control, &count, total.get(), &reason);
}

#[test]
fn failed_projection_candidates_cannot_swallow_cancellation() {
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
        let (mut control, count, reason) = interrupt(Checkpoint::Projection, at);
        assert_eq!(
            resolve_projection_controlled(checked.law(), candidates(), &path, &mut control),
            Err(ProjectionFailure::Interrupted(reason))
        );
        assert_eq!(count.get(), at);
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
    }
}

#[test]
fn final_request_cancellation_wins_over_known_type_error() {
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
            PrepareFailure::Requests { failure: ResolveFailure::Invalid { issues, .. }, .. }
            if issues[0].code == expected));
        let (mut control, count, reason) = interrupt(point, total.get());
        let failure = prepare_observed(sources(), asks, &mut control).unwrap_err();
        assert_request_stop(failure, &mut control, &count, total.get(), &reason);
    }
}

#[test]
fn a_stop_between_two_independent_cycles_is_reported_as_interrupted() {
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
    assert!(matches!(normal, ResolveFailure::Invalid { issues, .. }
        if issues.iter().map(|i| i.request.as_str()).collect::<Vec<_>>() == ["a", "b", "c", "d"]));
    // Each candidate is the same fixed four-node graph, stopped at one of its finite checkpoints.
    for at in 1..=total.get() {
        let (mut control, count, reason) = interrupt(Checkpoint::RequestDependency, at);
        let failure = resolve_observed_requests_controlled(
            checked.law(),
            checked.archmap(),
            &asks,
            &mut control,
        )
        .unwrap_err();
        assert_eq!(count.get(), at);
        assert!(
            matches!(&failure, ResolveFailure::Interrupted { reason: actual } if actual == &reason)
        );
        assert_eq!(control.checkpoint(Checkpoint::Resolve), Err(reason));
    }
}
