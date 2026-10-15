//! Schema helper の内部と入力不正を確定した後の停止優先順位。
mod common;
use archsig::{
    observed::{
        PrepareFailure,
        control::{Checkpoint, Control, Limits, Resource, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
        prepare_observed,
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn sources(id: &str, path: &str, kind: &str) -> InputSources {
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json(
            "V",
            &format!("[{}]", common::entity_json("V.Root", "[]", "[]")),
            "[]"
        )
    ));
    let defs = common::definitions_ok(&[&definition]);
    let digest = &defs.vocabularies["V"].digest;
    let mut map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[{{"id":"source","uri":"urn:test","revision":"1","digest":"sha256:0000000000000000000000000000000000000000000000000000000000000000"}}],"origins":[{{"id":"origin","mode":"observed","method":"test","locations":[{{"source":"source","path":"{path}","span":[0,1]}}]}}],"snapshots":[{{"id":"snap","origin":"origin","subjects":[{{"id":"{id}","type":"V.Root","origin":"origin"}}],"atoms":[]}}]}}"#
    );
    if kind == "version" {
        map = map.replace("archsig.archmap/2", "archsig.archmap/9");
    }
    if kind == "field" {
        map = map.replacen("\"sources\":[", "\"unknown\":true,\"sources\":[", 1);
    }
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        common::reading("view one(): Z = 1;").into_bytes(),
        map.into_bytes(),
    )
}
fn probe(at: Option<(usize, usize)>) -> (Control, Rc<Cell<usize>>) {
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    (
        Control::new(
            Limits {
                time_ms: at.filter(|(_, r)| *r == 1).map(|_| 1),
                memory_mib: at.filter(|(_, r)| *r == 2).map(|_| 1),
            },
            move |point| {
                if point == Checkpoint::ArchMapSchema {
                    count.set(count.get() + 1);
                }
                let r = at.filter(|(n, _)| *n == count.get()).map(|(_, r)| r);
                Usage {
                    signal: (r == Some(0)).then_some(Signal::Term),
                    elapsed_ms: u128::from(r == Some(1)),
                    memory_mib: u128::from(r == Some(2)),
                }
            },
        ),
        seen,
    )
}
fn total(input: InputSources) -> usize {
    let (mut control, seen) = probe(None);
    let _ = check_inputs(input, &mut control);
    seen.get()
}
#[test]
fn byte_preparation_reaches_each_id_character_and_relative_path_segment() {
    let short = || sources("a", "a", "valid");
    let long_id = || sources("abcdef", "a", "valid");
    let long_path = || sources("a", "a/b/c/d", "valid");
    assert_eq!(total(long_id()), total(short()) + 10);
    assert_eq!(total(long_path()), total(short()) + 6);
    for make in [
        long_id as fn() -> InputSources,
        long_path as fn() -> InputSources,
    ] {
        let end = total(make());
        for at in [1, end / 2, end] {
            for resource in 0..3 {
                let (mut control, _) = probe(Some((at, resource)));
                let failure =
                    prepare_observed(make(), &["a=evaluate(R.one)"], &mut control).unwrap_err();
                let PrepareFailure::Inputs(failure) = failure else {
                    panic!("input failure")
                };
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert!(!failure.primitives().is_empty());
                assert!(!failure.declarations().is_empty());
            }
        }
    }
}
#[test]
fn schema_version_and_relative_path_errors_outrank_later_budgets_but_not_signals() {
    for (kind, path, status) in [
        ("version", "a", InputStatus::Unsupported),
        ("field", "a", InputStatus::Invalid),
        ("valid", "a/../c", InputStatus::Invalid),
    ] {
        let make = || sources("a", path, kind);
        let baseline = check_inputs(make(), &mut Control::unlimited()).unwrap_err();
        assert_eq!(baseline.status(), status);
        let last = total(make());
        for resource in 0..3 {
            let (mut control, seen) = probe(Some((last, resource)));
            let failure = check_inputs(make(), &mut control).unwrap_err();
            assert_eq!(seen.get(), last);
            if resource == 0 {
                assert_eq!(failure.status(), InputStatus::Interrupted);
                assert_eq!(
                    control.stop_reason(),
                    Some(StopReason::Cancelled(Signal::Term))
                );
            } else {
                assert_eq!(failure.status(), status);
                let mut expected_issues =
                    vec![control.stop_reason().expect("observed budget").wire()];
                expected_issues.extend_from_slice(baseline.issues());
                assert_eq!(failure.issues(), expected_issues);
                assert_eq!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted {
                        resource: if resource == 1 {
                            Resource::TimeMs
                        } else {
                            Resource::MemoryMib
                        },
                        limit: 1,
                        observed: 1
                    })
                );
            }
        }
    }
}
