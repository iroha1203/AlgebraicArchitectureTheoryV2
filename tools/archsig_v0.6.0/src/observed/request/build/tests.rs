use super::*;
use crate::{
    control::{Limits, Usage},
    input::check_inputs,
};
mod fixture {
    use crate as archsig;
    include!("../../../../tests/common/request_acceptance_data.rs");
}

fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn resolved(asks: &[&str]) -> ResolvedRequests {
    let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
    resolve_inner(inputs.law(), inputs.archmap(), asks, &mut quiet(), None).unwrap()
}
fn invalid_case(asks: &[&str], code: RequestIssueCode, id: &str, argument: &str) {
    let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
    let Err(ResolveFailure::Invalid { issues, .. }) =
        resolve_observed_requests_controlled(inputs.law(), inputs.archmap(), asks, &mut quiet())
    else {
        panic!("不正なbuildは未実装通知より先に拒否する: {asks:?}");
    };
    assert!(
        issues
            .iter()
            .any(|issue| issue.code == code && issue.request == id && issue.argument == argument),
        "{issues:?}"
    );
}
#[test]
fn backward_root_handle_and_build_outputs_keep_types_and_dependencies() {
    let asks = [
        "b=build(R,on=$a.object.root)",
        "read=evaluate(R.first,on=$b.object)",
        "checked=check(R.prior,on=$b.algebra.base.object)",
        "a=build(R,on=@v/A)",
        "root=evaluate(R.root,a=$b.algebra.base.subject)",
    ];
    let result = resolved(&asks);
    assert_eq!(result.evaluation_order(), &[3, 0, 1, 2, 4]);
    assert_eq!(
        result
            .requests()
            .iter()
            .map(|r| r.id.as_str())
            .collect::<Vec<_>>(),
        ["b", "read", "checked", "a", "root"]
    );
    assert_eq!(result.requests()[0].kind, QuestionKind::Build);
    assert_eq!(result.requests()[0].declaration(), None);
    assert_eq!(result.requests()[0].dependencies, ["a"]);
    assert_eq!(
        result.requests()[0].arguments[0].origin,
        ArgumentOrigin::Explicit
    );
    assert!(result.requests()[0].defaults.is_empty());
    let constraint = &result.requests()[4].constraints[0];
    assert_eq!(
        constraint.projection.ty,
        ProjectionType::Law(Type::Ref("Requests.Root".into()))
    );
    assert_eq!(
        result.requests()[0]
            .wire()
            .canonical()
            .contains("\"kind\":\"build\""),
        true
    );
}
#[test]
fn root_returned_by_a_view_is_accepted_without_evaluating_its_body() {
    let result = resolved(&["b=build(R,on=$a.value)", "a=evaluate(R.root,a=@v/A)"]);
    assert_eq!(result.evaluation_order(), &[1, 0]);
    assert_eq!(result.requests()[0].dependencies, ["a"]);
}
#[test]
fn valid_build_reaches_execution_after_static_resolution() {
    let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
    let resolved = resolve_observed_requests_controlled(
        inputs.law(),
        inputs.archmap(),
        &["b=build(R,on=@v/A)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(resolved.requests()[0].kind, QuestionKind::Build);
}
#[test]
fn build_rejects_missing_unknown_and_duplicate_arguments_and_names() {
    for (ask, code, argument) in [
        ("b=build(R)", RequestIssueCode::Type, "on"),
        (
            "b=build(R,on=@v/A,reading=R)",
            RequestIssueCode::Type,
            "reading",
        ),
        ("b=build(R,on=@v/A,x=@v/A)", RequestIssueCode::Type, "x"),
        (
            "b=build(R,on=@v/A,on=@v/B)",
            RequestIssueCode::DuplicateArgument,
            "on",
        ),
        ("b=build(Missing,on=@v/A)", RequestIssueCode::Type, "head"),
        ("b=build(R.first,on=@v/A)", RequestIssueCode::Type, "head"),
        ("b=build(@v/A,on=@v/A)", RequestIssueCode::Type, "head"),
        ("b=build(R,on=@v/absent)", RequestIssueCode::Reference, "on"),
        (
            "b=build(R,on=$absent.value)",
            RequestIssueCode::Reference,
            "absent",
        ),
    ] {
        invalid_case(&[ask], code, "b", argument);
    }
    invalid_case(
        &["b=build(R,on=@v/A)", "b=build(R,on=@v/B)"],
        RequestIssueCode::DuplicateId,
        "b",
        "b",
    );
}
#[test]
fn build_rejects_owned_entity_values_and_architecture_instead_of_root() {
    for asks in [
        vec!["b=build(R,on=@v/i)"],
        vec!["b=build(R,on=$a.value)", "a=evaluate(R.first)"],
        vec!["b=build(R,on=$a.object)", "a=build(R,on=@v/A)"],
        vec!["b=build(R,on=$a)", "a=evaluate(R.root,a=@v/A)"],
    ] {
        invalid_case(&asks, RequestIssueCode::Type, "b", "on");
    }
}
#[test]
fn build_public_projection_table_rejects_private_values_and_indices() {
    for projection in [
        "configuration",
        "overrides",
        "object.configuration",
        "algebra.objects[0]",
        "algebra.base.private",
        "algebra.base.subject[0]",
        "object.root[0]",
    ] {
        let ask = format!("take=evaluate(R.root,a=$b.{projection})");
        let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
        let result = resolve_observed_requests_controlled(
            inputs.law(),
            inputs.archmap(),
            &[&ask, "b=build(R,on=@v/A)"],
            &mut quiet(),
        );
        assert!(
            matches!(result, Err(ResolveFailure::Invalid { .. })),
            "{projection}: {result:?}"
        );
    }
}
#[test]
fn build_cycles_keep_request_ids_edges_and_never_recurse_into_output_types() {
    let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
    for asks in [
        vec!["a=build(R,on=$a.object.root)"],
        vec![
            "a=build(R,on=$b.algebra.base.subject)",
            "b=build(R,on=$a.object.root)",
        ],
    ] {
        let Err(ResolveFailure::Invalid {
            requests, issues, ..
        }) = resolve_observed_requests_controlled(
            inputs.law(),
            inputs.archmap(),
            &asks,
            &mut quiet(),
        )
        else {
            panic!("循環を拒否する");
        };
        assert_eq!(requests.len(), asks.len());
        assert!(issues.iter().all(|i| i.code == RequestIssueCode::Cycle));
        for request in requests {
            assert_eq!(request.dependencies.len(), 1);
            assert!(issues.iter().any(|issue| issue.request == request.id));
        }
    }
}
#[test]
fn build_binding_and_projection_checkpoints_obey_cancellation() {
    use crate::result::Signal;
    let inputs = check_inputs(fixture::input(), &mut quiet()).unwrap();
    for target in [
        Checkpoint::RequestBinding,
        Checkpoint::RequestDependency,
        Checkpoint::Projection,
    ] {
        let mut c = Control::new(Limits::default(), move |point| Usage {
            signal: (point == target).then_some(Signal::Term),
            ..Usage::default()
        });
        assert!(matches!(
            resolve_observed_requests_controlled(
                inputs.law(),
                inputs.archmap(),
                &["b=build(R,on=$a.value)", "a=evaluate(R.root,a=@v/A)"],
                &mut c
            ),
            Err(ResolveFailure::Interrupted { .. })
        ));
    }
}

#[test]
fn build_rejects_arrow_instances_as_roots() {
    mod paths {
        use crate as archsig;
        include!("../../../../tests/common/public_path_compose.rs");
    }
    let inputs = check_inputs(paths::input(false, "build-arrow"), &mut quiet()).unwrap();
    assert!(
        matches!(resolve_observed_requests_controlled(inputs.law(), inputs.archmap(), &["b=build(Walk,on=@v/e)"], &mut quiet()), Err(ResolveFailure::Invalid { issues, .. }) if issues.iter().any(|i| i.request == "b" && i.argument == "on" && i.code == RequestIssueCode::Type))
    );
}

#[test]
fn reading_visibility_uses_transitive_imports_without_adding_other_registered_roots() {
    use crate::input::InputSources;
    let other = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Other","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Other.Root","meaning":"別の根。","parameters":[],"fields":[],"alignments":[]}]}]}"#;
    let o = crate::definition::check_definitions(&[("other", other.as_bytes())]).unwrap();
    let od = &o.vocabularies["Other"].digest;
    let definition = fixture::D.replacen(
        "\"dependencies\":[]",
        &format!(r#""dependencies":[{{"namespace":"Other","version":"1","digest":"{od}"}}]"#),
        1,
    );
    let d = crate::definition::check_definitions(&[
        ("requests", definition.as_bytes()),
        ("other", other.as_bytes()),
    ])
    .unwrap();
    let rd = &d.vocabularies["Requests"].digest;
    let original = fixture::input();
    let old = crate::definition::check_definitions(&[("requests", fixture::D.as_bytes())]).unwrap();
    let map = String::from_utf8(original.archmap().bytes().to_vec())
        .unwrap()
        .replace(&old.vocabularies["Requests"].digest, rd)
        .replace(
            "\"vocabularies\":[",
            &format!(r#""vocabularies":[{{"namespace":"Other","version":"1","digest":"{od}"}},"#),
        )
        .replace(
            "\"subjects\":[",
            "\"subjects\":[{\"id\":\"C\",\"type\":\"Other.Root\",\"origin\":\"spec\"},",
        );
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading R{{use vocabulary Requests version "1" digest "{rd}";{}}}reading S{{use vocabulary Other version "1" digest "{od}";}}"#,
        fixture::BODY
    );
    let input = InputSources::from_bytes(
        vec![definition.into_bytes(), other.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    );
    let checked = check_inputs(input, &mut quiet()).unwrap();
    let valid = resolve_inner(
        checked.law(),
        checked.archmap(),
        &["b=build(R,on=@v/C)"],
        &mut quiet(),
        None,
    )
    .unwrap();
    assert_eq!(
        valid.requests()[0].head,
        Selector::Declaration { name: "R".into() }
    );
    assert!(
        matches!(resolve_observed_requests_controlled(checked.law(), checked.archmap(), &["b=build(S,on=@v/A)"], &mut quiet()), Err(ResolveFailure::Invalid { issues, .. }) if issues.iter().any(|i| i.argument == "on" && i.code == RequestIssueCode::Type))
    );
}
