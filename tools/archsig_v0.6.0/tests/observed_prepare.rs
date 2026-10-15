use archsig::observed::{
    PrepareFailure,
    control::{Checkpoint, Control, Limits, Usage},
    input::InputSources,
    prepare_checked_observed, prepare_observed,
    request::{RequestIssueCode, ResolveFailure},
};

fn inputs() -> InputSources {
    InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        include_bytes!("fixtures/counter.law").to_vec(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    )
}

#[test]
fn byte_inputs_and_checked_inputs_resolve_the_same_requests() {
    let texts = [
        "a=evaluate(CountCheck.amount,s=@v/s)",
        "c=check(CountCheck.nonnegative)",
    ];
    let mut control = Control::unlimited();
    let prepared = prepare_observed(inputs(), &texts, &mut control).unwrap();
    assert_eq!(prepared.requests().evaluation_order(), &[0, 1]);
    assert_eq!(
        prepared.requests().requests()[0].declaration(),
        "CountCheck.amount"
    );
    assert_eq!(prepared.inputs().sources(), &inputs());
    // 検査済み bundle を所有したまま、別の問いを再解決する入口も同じ元入力を使う。
    let checked = archsig::observed::input::check_inputs(inputs(), &mut control).unwrap();
    let reused = prepare_checked_observed(checked, &texts, &mut control).unwrap();
    assert_eq!(prepared.requests(), reused.requests());
    assert_eq!(prepared.inputs().inputs(), reused.inputs().inputs());
}

#[test]
fn request_failure_preserves_checked_input_tables() {
    let failure = prepare_observed(
        inputs(),
        &["a=evaluate(CountCheck.amount)"],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let PrepareFailure::Requests {
        inputs: checked,
        failure,
    } = failure
    else {
        panic!("入力検査は成功する")
    };
    assert_eq!(checked.sources(), &inputs());
    assert!(checked.law().declarations.contains_key("CountCheck.amount"));
    let ResolveFailure::Invalid {
        requests,
        issues,
        stop_reason,
    } = failure
    else {
        panic!("束縛不足")
    };
    assert!(stop_reason.is_none());
    assert!(requests.is_empty());
    assert_eq!(issues[0].code, RequestIssueCode::MissingBinding);
}

#[test]
fn the_same_control_reaches_request_resolution() {
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        |point| Usage {
            elapsed_ms: u128::from(point == Checkpoint::Resolve),
            ..Usage::default()
        },
    );
    let failure =
        prepare_observed(inputs(), &["c=check(CountCheck.nonnegative)"], &mut control).unwrap_err();
    let PrepareFailure::Requests {
        inputs: checked,
        failure,
    } = failure
    else {
        panic!("検査段階は中断しない")
    };
    assert!(
        checked
            .law()
            .declarations
            .contains_key("CountCheck.nonnegative")
    );
    assert!(matches!(failure, ResolveFailure::Interrupted { .. }));
    assert_eq!(control.stop_reason().unwrap().code(), "budget_exhausted");
}

#[test]
fn cycles_keep_the_graph_and_leave_computation_outputs_empty() {
    let law = String::from_utf8(include_bytes!("fixtures/counter.law").to_vec())
        .unwrap()
        .replace(
            "view amount",
            "view same(s: State): State = s;\n  view amount",
        );
    let sources = InputSources::from_bytes(
        vec![include_bytes!("fixtures/counter.atoms.json").to_vec()],
        law.into_bytes(),
        include_bytes!("fixtures/counter.archmap.json").to_vec(),
    );
    let failure = prepare_observed(
        sources,
        &[
            "a=evaluate(CountCheck.same,s=$b.value)",
            "b=evaluate(CountCheck.same,s=$a.value)",
            "c=evaluate(CountCheck.amount,s=$a.value)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let wire = failure.wire().unwrap();
    let archsig::canonical::Json::Obj(fields) = &wire else {
        panic!("object")
    };
    assert_eq!(fields["status"], archsig::canonical::Json::str("invalid"));
    for key in ["answers", "nodes"] {
        assert_eq!(fields[key], archsig::canonical::Json::Arr(vec![]));
    }
    let ResolveFailure::Invalid {
        requests,
        issues,
        stop_reason,
    } = (match &failure {
        PrepareFailure::Requests { failure, .. } => failure,
        _ => panic!("要求の循環"),
    })
    else {
        panic!("invalid")
    };
    assert!(stop_reason.is_none());
    assert_eq!(requests.len(), 3);
    assert_eq!(requests[0].dependencies, ["b"]);
    assert_eq!(requests[2].dependencies, ["a"]);
    assert_eq!(
        issues
            .iter()
            .map(|i| i.request.as_str())
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    let archsig::canonical::Json::Arr(issues) = &fields["issues"] else {
        panic!("array")
    };
    for issue in issues {
        let archsig::canonical::Json::Obj(issue) = issue else {
            panic!("object")
        };
        assert!(!issue.contains_key("location"));
    }
}

#[test]
fn outside_operations_have_no_evaluation_result() {
    let failure = prepare_observed(
        inputs(),
        &["b=build(CountCheck,on=@v/s)"],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    assert!(failure.wire().is_none());
    assert!(matches!(
        failure,
        PrepareFailure::Requests {
            failure: ResolveFailure::NotApplicable { .. },
            ..
        }
    ));
}
