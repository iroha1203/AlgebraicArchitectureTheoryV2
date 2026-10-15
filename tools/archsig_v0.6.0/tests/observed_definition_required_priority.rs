//! 必須の依存・所属・field・添字探索の終端拒否を、三入力 byte 経路で検査する。
use archsig::{
    canonical::Json,
    definition::check_definitions,
    issue::{Code, Details, Issue, Location},
    observed::{
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
    },
    result::{ResultIssue, Signal},
};
use std::{cell::Cell, rc::Rc};

fn field(name: &str, ty: Json) -> Json {
    Json::obj([
        ("name", Json::str(name)),
        ("type", ty),
        ("meaning", Json::str("この位置の参照。")),
    ])
}
fn reference(name: &str) -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str(name)])
}
fn owned(name: &str, index: &str) -> Json {
    Json::Arr(vec![Json::str("Owned"), Json::str(name), Json::str(index)])
}
fn record(kind: &str, name: &str, parameters: Vec<Json>, fields: Vec<Json>) -> Json {
    record_aligned(kind, name, parameters, fields, vec![])
}
fn record_aligned(
    kind: &str,
    name: &str,
    parameters: Vec<Json>,
    fields: Vec<Json>,
    alignments: Vec<Json>,
) -> Json {
    Json::obj([
        ("kind", Json::str(kind)),
        ("name", Json::str(name)),
        ("meaning", Json::str("定義された構造。")),
        ("parameters", Json::Arr(parameters)),
        ("fields", Json::Arr(fields)),
        ("alignments", Json::Arr(alignments)),
    ])
}
fn root() -> Json {
    record("entity", "R.Root", vec![], vec![])
}
fn child() -> Json {
    record(
        "entity",
        "R.Child",
        vec![field("owner", reference("R.Root"))],
        vec![],
    )
}
fn vocabulary(namespace: &str, declarations: Vec<Json>, dependencies: Vec<Json>) -> Json {
    Json::obj([
        ("semantics", Json::str("archsig/0.6.0")),
        ("namespace", Json::str(namespace)),
        ("version", Json::str("1")),
        ("declarations", Json::Arr(declarations)),
        ("dependencies", Json::Arr(dependencies)),
    ])
}
fn definition(vocabularies: Vec<Json>) -> Vec<u8> {
    Json::obj([
        ("format", Json::str("archsig.atom-definition/1")),
        ("semantics", Json::str("archsig/0.6.0")),
        ("vocabularies", Json::Arr(vocabularies)),
    ])
    .canonical()
    .into_bytes()
}
fn sources(declarations: Vec<Json>) -> InputSources {
    from_files(vec![definition(vec![vocabulary(
        "R",
        declarations,
        vec![],
    )])])
}
fn from_files(definitions: Vec<Vec<u8>>) -> InputSources {
    InputSources::from_bytes(
        definitions,
        b"law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading R { view ready(): Bool = true; }".to_vec(),
        // A lost definition error must not silently advance into this next input.
        b"bad".to_vec(),
    )
}
fn probe(point: Checkpoint, at: usize, mode: usize) -> (Control, Rc<Cell<usize>>) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let control = Control::new(
        Limits {
            time_ms: (mode != 2).then_some(7),
            memory_mib: (mode != 1).then_some(11),
        },
        move |current| {
            if current == point {
                seen.set(seen.get() + 1);
            }
            let stop = seen.get() == at;
            Usage {
                elapsed_ms: if stop && mode != 2 { 9 } else { 0 },
                memory_mib: if stop && mode != 1 { 13 } else { 0 },
                signal: (stop && mode == 0).then_some(Signal::Term),
            }
        },
    );
    (control, count)
}
fn reason(mode: usize) -> StopReason {
    match mode {
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
    }
}
fn empty_stage(failure: &InputFailure) {
    assert!(failure.declarations().is_empty());
    assert!(failure.primitives().is_empty());
    assert!(failure.vocabularies().is_empty());
    let Json::Obj(ref wire) = failure.wire() else {
        panic!("object expected")
    };
    for key in [
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "nodes",
    ] {
        assert_eq!(wire[key], Json::Arr(vec![]), "{key}");
    }
}
fn ordinary_issue(input: &InputSources) -> Issue {
    let names: Vec<_> = (0..input.definitions().len())
        .map(|n| format!("definition{n}"))
        .collect();
    let files: Vec<_> = names
        .iter()
        .zip(input.definitions())
        .map(|(id, source)| (id.as_str(), source.bytes()))
        .collect();
    check_definitions(&files).unwrap_err().issue
}
fn assert_issue(issue: &Issue, code: Code, message: &str, pointer: &str) {
    assert_eq!(issue.code, code);
    assert_eq!(issue.message, message);
    assert_eq!(issue.details, Details::Empty);
    assert_eq!(
        issue.location,
        Location::Definition {
            input: "definition0".into(),
            pointer: pointer.into(),
            span: None
        }
    );
}
/// `unwind` is the number of same-kind samples after the first completed
/// required failure. Each fixture fixes it from the actual helper/caller path.
fn required_priority(
    input: InputSources,
    point: Checkpoint,
    unwind: usize,
    code: Code,
    message: &str,
    pointer: &str,
) {
    let issue = ordinary_issue(&input);
    assert_issue(&issue, code, message, pointer);
    let (mut control, total) = probe(point, usize::MAX, 0);
    let failure = check_inputs(input.clone(), &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(failure.issues(), [ResultIssue::Input(issue.clone()).wire()]);
    empty_stage(&failure);
    let post = total.get().checked_sub(unwind).unwrap();
    assert!(
        post > 1,
        "a required failure must be reached inside its helper"
    );
    for at in post..=total.get() {
        for mode in 0..3 {
            let (mut control, seen) = probe(point, at, mode);
            let failure = check_inputs(input.clone(), &mut control).unwrap_err();
            assert_eq!(seen.get(), at, "{message}, {point:?} {at}/{}", total.get());
            assert_eq!(control.stop_reason(), Some(reason(mode)));
            empty_stage(&failure);
            if mode == 0 {
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert_eq!(failure.issues(), [reason(mode).wire()]);
            } else {
                assert_eq!(
                    failure.status(),
                    InputStatus::Invalid,
                    "{message}, first post {post}, got {at}"
                );
                assert_eq!(
                    failure.issues(),
                    [
                        reason(mode).wire(),
                        ResultIssue::Input(issue.clone()).wire()
                    ]
                );
            }
        }
    }
    // Before the final predicate/candidate is examined, no required rejection
    // is known. A speculative local mismatch cannot become an input Issue.
    for mode in 0..3 {
        let (mut control, seen) = probe(point, post - 1, mode);
        let failure = check_inputs(input.clone(), &mut control).unwrap_err();
        assert_eq!(seen.get(), post - 1);
        assert_eq!(
            failure.status(),
            InputStatus::Interrupted,
            "{message}: before final decision"
        );
        assert_eq!(failure.issues(), [reason(mode).wire()]);
        empty_stage(&failure);
    }
}

#[test]
fn exhausted_dependency_candidates_keep_original_reference_above_budget() {
    let b = definition(vec![vocabulary(
        "B",
        vec![record("entity", "B.Item", vec![], vec![])],
        vec![],
    )]);
    let c = definition(vec![vocabulary(
        "C",
        vec![record("entity", "C.Item", vec![], vec![])],
        vec![],
    )]);
    let checked = check_definitions(&[("b", &b), ("c", &c)]).unwrap();
    let binding = |name: &str| {
        Json::obj([
            ("namespace", Json::str(name)),
            ("version", Json::str("1")),
            ("digest", Json::str(&checked.vocabularies[name].digest)),
        ])
    };
    let a = definition(vec![vocabulary(
        "A",
        vec![record(
            "entity",
            "A.Item",
            vec![],
            vec![field("item", reference("B.Item"))],
        )],
        vec![binding("C")],
    )]);
    required_priority(
        from_files(vec![a, b, c]),
        Checkpoint::DefinitionDependency,
        0,
        Code::Reference,
        "namespace `B` の dependency がない",
        "/vocabularies/0/declarations/0/fields/0/type/1",
    );
}

#[test]
fn owned_index_final_mismatch_keeps_original_reference_above_budget() {
    let record = record(
        "entity",
        "R.Record",
        vec![field("r", reference("R.Root"))],
        vec![field("item", owned("R.Child", "missing"))],
    );
    required_priority(
        sources(vec![root(), child(), record]),
        Checkpoint::DefinitionSemantics,
        1,
        Code::Reference,
        "添字 `missing` は左にある parameter を指す",
        "/vocabularies/0/declarations/2/fields/0/type/2",
    );
}

#[test]
fn required_root_and_owned_target_keep_the_original_syntax_above_budget() {
    let other = record(
        "entity",
        "R.Other",
        vec![field("owner", reference("R.Child"))],
        vec![],
    );
    required_priority(
        sources(vec![root(), child(), other]),
        Checkpoint::DefinitionSemantics,
        3,
        Code::Syntax,
        "owner の型は所属先を持たない entity",
        "/vocabularies/0/declarations/2/parameters/0/name",
    );
    let record = record(
        "entity",
        "R.Record",
        vec![field("r", reference("R.Root"))],
        vec![field("item", owned("R.Root", "r"))],
    );
    required_priority(
        sources(vec![root(), record]),
        Checkpoint::DefinitionSemantics,
        3,
        Code::Syntax,
        "`R.Root` は所属先を持たない entity・arrow",
        "/vocabularies/0/declarations/1/fields/0/type",
    );
}

#[test]
fn missing_arrow_and_correspondence_fields_keep_the_original_syntax_above_budget() {
    let arrow = record(
        "arrow",
        "R.Edge",
        vec![field("owner", reference("R.Root"))],
        vec![],
    );
    required_priority(
        sources(vec![root(), arrow]),
        Checkpoint::DefinitionSemantics,
        2,
        Code::Syntax,
        "arrow は owner・from・to の field を持つ",
        "/vocabularies/0/declarations/1/name",
    );
    let correspondence = record(
        "correspondence",
        "R.Link",
        vec![field("from", reference("R.Root"))],
        vec![],
    );
    required_priority(
        sources(vec![root(), correspondence]),
        Checkpoint::DefinitionSemantics,
        1,
        Code::Syntax,
        "correspondence は parameters に from・to を持つ",
        "/vocabularies/0/declarations/1/name",
    );
}

#[test]
fn correspondence_root_failure_keeps_original_parameter_location_above_budget() {
    let correspondence = record(
        "correspondence",
        "R.Link",
        vec![
            field("from", reference("R.Child")),
            field("to", reference("R.Root")),
        ],
        vec![],
    );
    required_priority(
        sources(vec![root(), child(), correspondence]),
        Checkpoint::DefinitionSemantics,
        3,
        Code::Syntax,
        "correspondence の from・to は根 entity",
        "/vocabularies/0/declarations/2/parameters/0/name",
    );
}

#[test]
fn alignment_final_field_mismatch_keeps_original_reference_above_budget() {
    let correspondence = record_aligned(
        "correspondence",
        "R.Link",
        vec![
            field("from", reference("R.Root")),
            field("to", reference("R.Root")),
        ],
        vec![field(
            "items",
            Json::Arr(vec![
                Json::str("Map"),
                owned("R.Child", "from"),
                owned("R.Child", "to"),
            ]),
        )],
        vec![Json::obj([
            ("source", Json::str("R.Child.missing")),
            ("target", Json::str("R.Child.owner")),
            ("meaning", Json::str("位置の対応。")),
        ])],
    );
    required_priority(
        sources(vec![root(), child(), correspondence]),
        Checkpoint::DefinitionSemantics,
        3,
        Code::Reference,
        "field `R.Child.missing` を解決できない",
        "/vocabularies/0/declarations/2/alignments/0/source",
    );
}

#[test]
fn optional_absence_and_untried_field_candidates_remain_interrupted() {
    for declarations in [vec![root()], vec![root(), child()]] {
        let input = sources(declarations);
        let ordinary_files = [("definition0", input.definitions()[0].bytes())];
        assert!(check_definitions(&ordinary_files).is_ok());
        let (mut baseline, count) = probe(Checkpoint::DefinitionSemantics, usize::MAX, 0);
        // The deliberately bad ArchMap is later; only DefinitionSemantics is sampled.
        let _ = check_inputs(input.clone(), &mut baseline);
        assert!(count.get() > 1);
        for at in [1, count.get() - 1, count.get()] {
            for mode in 0..3 {
                let (mut control, seen) = probe(Checkpoint::DefinitionSemantics, at, mode);
                let failure = check_inputs(input.clone(), &mut control).unwrap_err();
                assert_eq!(seen.get(), at);
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert_eq!(failure.issues(), [reason(mode).wire()]);
                empty_stage(&failure);
            }
        }
    }
}

#[test]
fn an_untried_owner_field_candidate_cannot_be_promoted_to_invalid() {
    let child = record(
        "entity",
        "R.Child",
        vec![
            field("r", reference("R.Root")),
            field("owner", reference("R.Root")),
        ],
        vec![],
    );
    let input = sources(vec![root(), child]);
    assert!(check_definitions(&[("definition0", input.definitions()[0].bytes())]).is_ok());
    // Each Ref type contributes four samples. Then field/find entries, the
    // first candidate pre and post: r != owner, with owner still untried.
    let first_mismatch_post = 12;
    for mode in 0..3 {
        let (mut control, seen) = probe(Checkpoint::DefinitionSemantics, first_mismatch_post, mode);
        let failure = check_inputs(input.clone(), &mut control).unwrap_err();
        assert_eq!(seen.get(), first_mismatch_post);
        assert_eq!(failure.status(), InputStatus::Interrupted);
        assert_eq!(failure.issues(), [reason(mode).wire()]);
        assert_eq!(control.stop_reason(), Some(reason(mode)));
        empty_stage(&failure);
    }
}
