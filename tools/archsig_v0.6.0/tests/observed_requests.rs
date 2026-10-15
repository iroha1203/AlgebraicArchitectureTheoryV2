//! byte 入力の既存検査から、観測要求の束縛・依存・公開射影を接続する。
mod common;
use archsig::{
    archmap::CheckedArchMap,
    law::CheckedLaw,
    observed::{
        control::{Control, Limits, StopReason, Usage},
        projection::{ProjectionStep, ProjectionType},
        request::{
            ArgumentOrigin, RequestDefault, RequestIssueCode, ResolveFailure,
            resolve_observed_requests, resolve_observed_requests_controlled,
        },
    },
    types::Type,
};

fn inputs() -> (CheckedLaw, CheckedArchMap) {
    let definitions = common::definitions_ok(&[common::COUNTER_DEFINITION]);
    let digest = &definitions.vocabularies["Counter"].digest;
    let law = format!(
        r#"{}reading R {{
      use vocabulary Counter version "1" digest "{digest}";
      view echo(s: State): State = s;
      view number(s: State): Z = s.count;
      view plus(x: Z): Z = x + 1;
      view pair(): (Z,Bool) = (1, true);
      view numbers(): List<Z> = list<Z>[1,2];
      view maybe(): Option<Z> = some(1);
      view named(on: State): Z = on.count;
      view route(s: State): Path<State,State> = identity(s);
      law required positive(s: State): s.count >= 0;
    }}"#,
        common::HEADER
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Counter","version":"1","digest":"{digest}"}}],"sources":[],
      "origins":[{{"id":"o","mode":"specification","method":"小さい観測","locations":[],"note":"要求解決"}}],
      "snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"s","type":"Counter.State","origin":"o"}}],"atoms":[]}}]}}"#
    );
    (
        archsig::law::check_law(law.as_bytes(), &definitions).unwrap(),
        archsig::archmap::check_archmap(map.as_bytes(), &definitions).unwrap(),
    )
}

fn rejects(asks: &[&str], expected: RequestIssueCode) {
    let (law, map) = inputs();
    match resolve_observed_requests(&law, &map, asks).unwrap_err() {
        ResolveFailure::Invalid {
            requests,
            issues,
            stop_reason,
        } => {
            assert!(stop_reason.is_none());
            assert!(requests.is_empty());
            assert_eq!(issues[0].code, expected, "{issues:?}");
            assert!(!issues[0].wire().canonical().contains("location"));
        }
        other => panic!("要求不正を期待: {other:?}"),
    }
}

#[test]
fn forward_backward_references_and_stable_order_keep_original_requests() {
    let (law, map) = inputs();
    let texts = [
        "second=evaluate(plus,x=$first.value)",
        "first=evaluate(R.number,s=@v/s)",
        "independent=check(R.positive)",
        "last=check(R.positive,bind.s=$identity.value)",
        "identity=evaluate(R.echo,s=@v/s)",
    ];
    let resolved = resolve_observed_requests(&law, &map, &texts).unwrap();
    assert_eq!(resolved.evaluation_order(), &[1, 0, 2, 4, 3]);
    let r = &resolved.requests()[0];
    assert_eq!(r.text, texts[0]);
    assert_eq!(r.declaration(), "R.plus");
    assert_eq!(r.dependencies, ["first"]);
    assert_eq!(r.arguments[0].name, "bind.x");
    assert_eq!(r.arguments[0].origin, ArgumentOrigin::Explicit);
    assert_eq!(r.constraints[0].projection.ty, ProjectionType::Law(Type::Z));
    assert_eq!(
        resolved.requests()[2].defaults,
        vec![
            RequestDefault::ObservedEnvironment,
            RequestDefault::UniversalParameters {
                declaration: "R.positive".into(),
                parameters: vec!["s".into()]
            }
        ]
    );
    assert_eq!(
        resolved
            .requests()
            .iter()
            .map(|r| r.id.as_str())
            .collect::<Vec<_>>(),
        vec!["second", "first", "independent", "last", "identity"]
    );
    let wire = r.wire().canonical();
    assert!(wire.contains("\"origin\":\"explicit\""));
    assert!(!wire.contains("constraints"));
}

#[test]
fn missing_unknown_duplicate_and_static_type_errors_are_rejected() {
    rejects(&["a=evaluate(R.number)"], RequestIssueCode::MissingBinding);
    rejects(&["a=check(Unknown)"], RequestIssueCode::Reference);
    rejects(
        &["a=check(R.positive)", "a=check(R.positive)"],
        RequestIssueCode::DuplicateId,
    );
    rejects(
        &["a=check(R.positive,s=@v/s,s=@v/s)"],
        RequestIssueCode::DuplicateArgument,
    );
    rejects(
        &["a=check(R.positive,s=@v/s,bind.s=@v/s)"],
        RequestIssueCode::DuplicateArgument,
    );
    rejects(
        &["a=check(R.positive,missing=@v/s)"],
        RequestIssueCode::Reference,
    );
    rejects(
        &["a=check(R.positive,s=@v/missing)"],
        RequestIssueCode::Reference,
    );
    rejects(
        &["a=check(R.positive,s=$missing.value)"],
        RequestIssueCode::Reference,
    );
    rejects(&["a=evaluate(R.plus,x=@v/s)"], RequestIssueCode::Type);
    rejects(
        &["a=check(R.positive,s=$b)", "b=check(R.positive)"],
        RequestIssueCode::Projection,
    );
    rejects(&["a=evaluate(R.plus,x=1)"], RequestIssueCode::Syntax);
    rejects(&["a=evaluate(R.plus,x=list[1])"], RequestIssueCode::Syntax);
    rejects(&["law=check(R.positive)"], RequestIssueCode::Syntax);
}

#[test]
fn projection_table_rejects_metadata_and_static_bounds_but_keeps_dynamic_conditions() {
    rejects(
        &["a=evaluate(R.pair)", "b=evaluate(R.plus,x=$a.value[2])"],
        RequestIssueCode::Projection,
    );
    rejects(
        &[
            "a=evaluate(R.number,s=@v/s)",
            "b=evaluate(R.plus,x=$a.evaluation.parts[0])",
        ],
        RequestIssueCode::Projection,
    );
    rejects(
        &[
            "a=evaluate(R.echo,s=@v/s)",
            "b=evaluate(R.plus,x=$a.value.snapshot)",
        ],
        RequestIssueCode::Projection,
    );
    rejects(
        &["a=evaluate(R.pair)", "b=evaluate(R.plus,x=$a.value[1])"],
        RequestIssueCode::Type,
    );
    rejects(
        &["a=evaluate(R.pair)", "b=evaluate(R.plus,x=$a.value[01])"],
        RequestIssueCode::Syntax,
    );
    let (law, map) = inputs();
    let texts = [
        "a=evaluate(R.numbers)",
        "b=evaluate(R.plus,x=$a.value[99])",
        "o=evaluate(R.maybe)",
        "s=evaluate(R.plus,x=$o.value.some)",
        "n=evaluate(R.number,s=@v/s)",
        "e=evaluate(R.plus,x=$n.evaluation.value)",
        "r=evaluate(R.echo,s=@v/s)",
        "env=check(R.positive,s=$r.evaluation.environment.root)",
    ];
    let resolved = resolve_observed_requests(&law, &map, &texts).unwrap();
    for i in [1, 3, 5, 7] {
        assert!(resolved.requests()[i].constraints[0].dynamic);
    }
    let archsig::observed::request::Selector::Answer { path, .. } =
        &resolved.requests()[1].arguments[0].value
    else {
        panic!("answer");
    };
    assert_eq!(
        path,
        &vec![
            ProjectionStep::Field("value".into()),
            ProjectionStep::Index(99)
        ]
    );
}

#[test]
fn architecture_and_other_kinds_have_a_dedicated_applicability_result() {
    let (law, map) = inputs();
    for (text, environment) in [
        ("a=build(R,on=@v/s)", false),
        ("a=diagnose($d.system,degree=1)", false),
        ("a=evaluate(R.number,on=$b.object,s=@v/s)", true),
        ("a=evaluate(R.named,on=@v/s)", true),
    ] {
        assert!(
            matches!(resolve_observed_requests(&law,&map,&[text]),Err(ResolveFailure::NotApplicable { architecture_environment,.. }) if architecture_environment == environment)
        );
    }
    assert!(resolve_observed_requests(&law, &map, &["a=evaluate(R.named,bind.on=@v/s)"]).is_ok());
}

#[test]
fn cycles_report_each_member_and_keep_the_graph_without_marking_downstream() {
    let (law, map) = inputs();
    let error = resolve_observed_requests(
        &law,
        &map,
        &[
            "a=evaluate(R.plus,x=$b.value)",
            "b=evaluate(R.plus,x=$a.value)",
            "c=evaluate(R.plus,x=$a.value)",
        ],
    )
    .unwrap_err();
    let ResolveFailure::Invalid {
        requests,
        issues,
        stop_reason,
    } = error
    else {
        panic!("cycle");
    };
    assert!(stop_reason.is_none());
    assert_eq!(requests.len(), 3);
    assert_eq!(requests[2].dependencies, ["a"]);
    assert_eq!(
        issues
            .iter()
            .map(|i| (i.code, i.request.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (RequestIssueCode::Cycle, "a"),
            (RequestIssueCode::Cycle, "b")
        ]
    );
    assert!(
        issues
            .iter()
            .all(|i| !i.wire().canonical().contains("location"))
    );
}

#[test]
fn request_resolution_uses_the_same_latched_interrupt_control() {
    let (law, map) = inputs();
    let mut calls = 0;
    let mut control = Control::new(
        Limits {
            time_ms: Some(2),
            memory_mib: None,
        },
        move |_| {
            calls += 1;
            Usage {
                elapsed_ms: calls,
                ..Usage::default()
            }
        },
    );
    let error =
        resolve_observed_requests_controlled(&law, &map, &["a=check(R.positive)"], &mut control)
            .unwrap_err();
    assert!(matches!(
        error,
        ResolveFailure::Interrupted {
            reason: StopReason::BudgetExhausted { observed: 2, .. }
        }
    ));
}

fn dependent_inputs(known_owner: bool) -> (CheckedLaw, CheckedArchMap) {
    let root = common::entity_json("W.Root", "[]", "[]");
    let owner = common::field_json("owner", r#"["Ref","W.Root"]"#);
    let item = common::entity_json("W.Item", &format!("[{owner}]"), "[]");
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{root},{item}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["W"].digest;
    let law = format!(
        r#"{}reading R {{ use vocabulary W version "1" digest "{digest}";
      view belongs(a: Root, b: Item[a]): Bool = true;
      view echo(a: Root): Root = a;
      law required present(a: Root, b: Item[a]): true;
    }}"#,
        common::HEADER
    );
    let atoms = if known_owner {
        r#"{"id":"owner","subject":"i","field":"W.Item.owner","value":["v","A"],"origin":"o"}"#
    } else {
        ""
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],"sources":[],
      "origins":[{{"id":"o","mode":"specification","method":"小さい観測","locations":[],"note":"所属"}}],
      "snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"A","type":"W.Root","origin":"o"}},{{"id":"B","type":"W.Root","origin":"o"}},{{"id":"i","type":"W.Item","origin":"o"}}],"atoms":[{atoms}]}},{{"id":"w","origin":"o","subjects":[{{"id":"B","type":"W.Root","origin":"o"}}],"atoms":[]}}]}}"#
    );
    (
        archsig::law::check_law(law.as_bytes(), &definitions).unwrap(),
        archsig::archmap::check_archmap(map.as_bytes(), &definitions).unwrap(),
    )
}

#[test]
fn owner_mismatches_are_static_and_missing_owners_remain_constraints() {
    let (law, map) = dependent_inputs(true);
    let valid =
        resolve_observed_requests(&law, &map, &["a=evaluate(R.belongs,b=@v/i,a=@v/A)"]).unwrap();
    assert!(!valid.requests()[0].constraints[1].dynamic);
    let error = resolve_observed_requests(&law, &map, &["a=evaluate(R.belongs,a=@v/B,b=@v/i)"])
        .unwrap_err();
    assert!(
        matches!(error, ResolveFailure::Invalid { issues,.. } if issues[0].code == RequestIssueCode::Type)
    );
    let (law, map) = dependent_inputs(false);
    let conditional = resolve_observed_requests(
        &law,
        &map,
        &[
            "a=evaluate(R.belongs,a=@v/B,b=@v/i)",
            "c=check(R.present,b=@v/i)",
        ],
    )
    .unwrap();
    assert!(conditional.requests()[0].constraints[1].dynamic);
    assert!(conditional.requests()[0].constraints[1].owner.is_some());
    assert!(conditional.requests()[1].constraints[0].dynamic);
    assert_eq!(
        conditional.requests()[1].defaults[1],
        RequestDefault::UniversalParameters {
            declaration: "R.present".into(),
            parameters: vec!["a".into()]
        }
    );
}

#[test]
fn cross_snapshot_owned_bindings_are_static_errors_even_with_missing_owner() {
    for known_owner in [false, true] {
        let (law, map) = dependent_inputs(known_owner);
        for ask in [
            "a=evaluate(R.belongs,a=@w/B,b=@v/i)",
            "a=check(R.present,a=@w/B,b=@v/i)",
        ] {
            let failure = resolve_observed_requests(&law, &map, &[ask]).unwrap_err();
            assert!(
                matches!(failure, ResolveFailure::Invalid { issues, .. }
                if issues.len() == 1 && issues[0].code == RequestIssueCode::Type
                && issues[0].argument == "bind.b"),
                "known owner={known_owner}, {ask}"
            );
        }
    }
}

#[test]
fn unevaluated_owner_answer_projection_remains_a_dynamic_constraint() {
    for known_owner in [false, true] {
        let (law, map) = dependent_inputs(known_owner);
        for ask in [
            "a=evaluate(R.belongs,a=$root.value,b=@v/i)",
            "a=check(R.present,a=$root.value,b=@v/i)",
        ] {
            let resolved =
                resolve_observed_requests(&law, &map, &[ask, "root=evaluate(R.echo,a=@w/B)"])
                    .unwrap();
            let constraint = &resolved.requests()[0].constraints[1];
            assert!(constraint.dynamic);
            assert!(matches!(
                constraint.owner,
                Some(archsig::observed::request::Selector::Answer { .. })
            ));
            assert_eq!(resolved.evaluation_order(), &[1, 0]);
        }
    }
}

#[test]
fn data_constructor_projection_preserves_alternative_types_and_conditions() {
    let zero = common::constructor_json("Empty", "[]");
    let one = common::constructor_json("Number", r#"["Z"]"#);
    let boolean = common::constructor_json("Flag", r#"["Bool"]"#);
    let data = common::data_json("W.Choice", &format!("[{zero},{one},{boolean}]"));
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{data}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["W"].digest;
    let law = format!(
        r#"{}reading R {{ use vocabulary W version "1" digest "{digest}";
      view choice(): Choice = Number(1);
      view plus(x: Z): Z = x + 1;
    }}"#,
        common::HEADER
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],"sources":[],"origins":[],"snapshots":[]}}"#
    );
    let law = archsig::law::check_law(law.as_bytes(), &definitions).unwrap();
    let map = archsig::archmap::check_archmap(map.as_bytes(), &definitions).unwrap();
    let requests = resolve_observed_requests(
        &law,
        &map,
        &["a=evaluate(R.choice)", "b=evaluate(R.plus,x=$a.value[0])"],
    )
    .unwrap();
    let constraint = &requests.requests()[1].constraints[0];
    assert!(constraint.dynamic);
    assert_eq!(
        constraint.projection.ty,
        ProjectionType::Dynamic(vec![
            ProjectionType::Law(Type::Z),
            ProjectionType::Law(Type::Bool)
        ])
    );
    assert!(
        matches!(resolve_observed_requests(&law,&map,&["a=evaluate(R.choice)","b=evaluate(R.plus,x=$a.value[1])"]),Err(ResolveFailure::Invalid { issues,.. }) if issues[0].code == RequestIssueCode::Projection)
    );
}

#[test]
fn path_endpoints_keep_reference_types_and_generator_lists_are_not_exposed() {
    let (law, map) = inputs();
    let requests = resolve_observed_requests(
        &law,
        &map,
        &[
            "r=evaluate(R.route,s=@v/s)",
            "a=check(R.positive,s=$r.value.source)",
            "b=check(R.positive,s=$r.value.target)",
        ],
    )
    .unwrap();
    for i in [1, 2] {
        assert_eq!(
            requests.requests()[i].constraints[0].projection.ty,
            ProjectionType::Law(Type::Ref("Counter.State".into()))
        );
    }
    rejects(
        &[
            "r=evaluate(R.route,s=@v/s)",
            "a=check(R.positive,s=$r.value.generators)",
        ],
        RequestIssueCode::Projection,
    );
    rejects(
        &[
            "r=evaluate(R.route,s=@v/s)",
            "a=check(R.positive,s=$r.value.action)",
        ],
        RequestIssueCode::Projection,
    );
}
