//! 依存戻り型の添字を生産側の束縛へ対応付け、値を評価せず所属を照合する。
mod common;

use archsig::{
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::InputSources,
        prepare_observed,
        request::{RequestIssueCode, ResolveFailure, Selector},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn sources(known_owner: bool) -> InputSources {
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
          view owned(a: Root, b: Item[a]): Item[a] = b;
          view renamed(x: Root, y: Item[x]): Item[x] = y;
          view generic(b: Item): Item = b;
          view echo(a: Root): Root = a;
          view nested(a: Root, b: Item[a]): (List<Option<Item[a]>>,Bool) = (list<Option<Item[a]>>[some(b)],true);
          view accepts(a: Root, b: (List<Option<Item[a]>>,Bool)): Bool = true;
          view belongs(a: Root, b: Item[a]): Bool = true;
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
          "origins":[{{"id":"o","mode":"specification","method":"小さい観測","locations":[],"note":"依存戻り型"}}],
          "snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"A","type":"W.Root","origin":"o"}},{{"id":"B","type":"W.Root","origin":"o"}},{{"id":"i","type":"W.Item","origin":"o"}}],"atoms":[{atoms}]}},
          {{"id":"w","origin":"o","subjects":[{{"id":"A","type":"W.Root","origin":"o"}}],"atoms":[]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn assert_owner_error(failure: PrepareFailure, consumer: &str) {
    let wire = failure.wire().unwrap().canonical();
    assert!(wire.contains(r#""status":"invalid""#));
    assert!(wire.contains(r#""nodes":[]"#));
    assert!(wire.contains(r#""answers":[]"#));
    let PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { issues, .. },
        ..
    } = failure
    else {
        panic!("要求の不正: {failure:?}")
    };
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0].code, RequestIssueCode::Type);
    assert_eq!(issues[0].request, consumer);
    assert_eq!(issues[0].argument, "bind.b");
    assert!(!issues[0].wire().canonical().contains("location"));
}

#[test]
fn dependent_answer_owner_rejects_static_mismatch_for_both_output_paths_and_question_kinds() {
    for output in ["value", "evaluation.value"] {
        for question in ["evaluate(R.belongs", "check(R.present"] {
            for target in ["@v/B", "@w/A"] {
                let consumer = format!("c={question},a={target},b=$o.{output})");
                let asks = [consumer.as_str(), "o=evaluate(R.owned,a=@v/A,b=@v/i)"];
                assert_owner_error(
                    prepare_observed(sources(true), &asks, &mut Control::unlimited()).unwrap_err(),
                    "c",
                );
            }
        }
    }
}

#[test]
fn nested_return_owner_survives_projection_and_compares_inside_container_types() {
    for projection in ["value[0][0].some", "evaluation.value[0][0].some"] {
        let consumer = format!("c=evaluate(R.belongs,a=@v/B,b=$o.{projection})");
        assert_owner_error(
            prepare_observed(
                sources(true),
                &[&consumer, "o=evaluate(R.nested,a=@v/A,b=@v/i)"],
                &mut Control::unlimited(),
            )
            .unwrap_err(),
            "c",
        );
    }
    assert_owner_error(
        prepare_observed(
            sources(true),
            &[
                "c=evaluate(R.accepts,a=@v/B,b=$o.value)",
                "o=evaluate(R.nested,a=@v/A,b=@v/i)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap_err(),
        "c",
    );
    let prepared = prepare_observed(
        sources(true),
        &[
            "c=evaluate(R.belongs,a=@v/A,b=$o.value[0][0].some)",
            "o=evaluate(R.nested,a=@v/A,b=@v/i)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    let constraint = &prepared.requests().requests()[0].constraints[1];
    assert!(constraint.dynamic, "List/Option射影の実値適合は残る");
    assert!(
        matches!(&constraint.projection_owners["a"], Selector::Subject { snapshot, subject } if snapshot == "v" && subject == "A")
    );
    assert_eq!(
        constraint.projection_owners["a"],
        constraint.expected_owners["a"]
    );
    assert!(
        !prepared.requests().requests()[0]
            .wire()
            .canonical()
            .contains("owners")
    );
}

#[test]
fn renamed_owner_indices_and_answer_chains_use_each_producers_binding_scope() {
    let asks = [
        "c=evaluate(R.belongs,a=@v/B,b=$middle.value)",
        "middle=evaluate(R.renamed,x=@v/A,y=$first.value)",
        "first=evaluate(R.owned,a=@v/A,b=@v/i)",
    ];
    assert_owner_error(
        prepare_observed(sources(true), &asks, &mut Control::unlimited()).unwrap_err(),
        "c",
    );
    let prepared = prepare_observed(
        sources(true),
        &[
            "c=evaluate(R.belongs,a=@v/A,b=$middle.value)",
            asks[1],
            asks[2],
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert_eq!(prepared.requests().evaluation_order(), &[2, 1, 0]);
    let constraint = &prepared.requests().requests()[0].constraints[1];
    assert_eq!(
        constraint.projection_owners["x"],
        constraint.expected_owners["a"]
    );
    assert!(
        !constraint.dynamic,
        "所属は束縛から静的に一致し、値生成の成否はAnswer依存として扱う"
    );
}

#[test]
fn unknown_owners_keep_constraints_without_inferring_view_value_identity() {
    for (producer, target) in [
        ("o=evaluate(R.generic,b=@v/i)", "@v/B"),
        ("o=evaluate(R.owned,a=$root.value,b=@v/i)", "@v/B"),
        ("o=evaluate(R.owned,a=@v/A,b=@v/i)", "$root.value"),
    ] {
        let consumer = format!("c=evaluate(R.belongs,a={target},b=$o.value)");
        let prepared = prepare_observed(
            sources(false),
            &[&consumer, producer, "root=evaluate(R.echo,a=@w/A)"],
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(prepared.requests().requests()[0].constraints[1].dynamic);
    }
    let prepared = prepare_observed(
        sources(false),
        &[
            "c=check(R.present,b=$o.value)",
            "o=evaluate(R.owned,a=@v/A,b=@v/i)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap();
    assert!(prepared.requests().requests()[0].constraints[0].dynamic);
}

#[test]
fn equal_answer_owner_selectors_match_but_distinct_answers_remain_unknown() {
    for (target, dynamic) in [("$root.value", false), ("$other.value", true)] {
        let consumer = format!("c=evaluate(R.belongs,a={target},b=$o.value)");
        let prepared = prepare_observed(
            sources(false),
            &[
                &consumer,
                "o=evaluate(R.owned,a=$root.value,b=@v/i)",
                "root=evaluate(R.echo,a=@v/A)",
                "other=evaluate(R.echo,a=@v/A)",
            ],
            &mut Control::unlimited(),
        )
        .unwrap();
        let constraint = &prepared.requests().requests()[0].constraints[1];
        assert_eq!(constraint.dynamic, dynamic);
        assert!(
            matches!(&constraint.projection_owners["a"], Selector::Answer { id, .. } if id == "root")
        );
    }
}

#[test]
fn dependent_answer_cycles_keep_original_cycle_members_and_request_graph() {
    let failure = prepare_observed(
        sources(false),
        &[
            "a=evaluate(R.owned,a=@v/A,b=$b.value)",
            "b=evaluate(R.renamed,x=@v/A,y=$a.value)",
            "later=evaluate(R.belongs,a=@v/A,b=$a.value)",
        ],
        &mut Control::unlimited(),
    )
    .unwrap_err();
    let PrepareFailure::Requests {
        failure: ResolveFailure::Invalid {
            requests, issues, ..
        },
        ..
    } = failure
    else {
        panic!("cycle")
    };
    assert_eq!(requests.len(), 3);
    assert_eq!(
        issues
            .iter()
            .map(|issue| (issue.code, issue.request.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (RequestIssueCode::Cycle, "a"),
            (RequestIssueCode::Cycle, "b")
        ]
    );
}

#[test]
fn owner_type_walk_stops_early_and_preserves_known_mismatch_with_late_budget() {
    let asks = [
        "c=evaluate(R.belongs,a=@v/B,b=$o.value)",
        "o=evaluate(R.owned,a=@v/A,b=@v/i)",
    ];
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::RequestBinding {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    assert_owner_error(
        prepare_observed(sources(true), &asks, &mut baseline).unwrap_err(),
        "c",
    );
    for at in [1, count.get()] {
        for cancelled in [false, true] {
            let seen = Rc::new(Cell::new(0usize));
            let observed = seen.clone();
            let mut control = Control::new(
                Limits {
                    time_ms: Some(1),
                    memory_mib: None,
                },
                move |point| {
                    if point == Checkpoint::RequestBinding {
                        observed.set(observed.get() + 1);
                    }
                    let stop = observed.get() >= at;
                    Usage {
                        elapsed_ms: u128::from(stop && !cancelled),
                        signal: (stop && cancelled).then_some(Signal::Term),
                        ..Usage::default()
                    }
                },
            );
            let failure = prepare_observed(sources(true), &asks, &mut control).unwrap_err();
            if at > 1 && !cancelled {
                assert_owner_error(failure, "c");
            } else {
                assert!(matches!(
                    failure,
                    PrepareFailure::Requests {
                        failure: ResolveFailure::Interrupted { .. },
                        ..
                    }
                ));
            }
            assert_eq!(seen.get(), at);
            assert!(matches!(
                control.checkpoint(Checkpoint::Resolve),
                Err(StopReason::Cancelled(_)) | Err(StopReason::BudgetExhausted { .. })
            ));
            assert_eq!(seen.get(), at);
        }
    }
}
