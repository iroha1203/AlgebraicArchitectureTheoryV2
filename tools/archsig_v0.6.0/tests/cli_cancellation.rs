//! CLI check の固定 checkpoint 取消と、配送を始めない停止。

mod common;
use archsig::observed::control::{Checkpoint, Control, Limits, Usage};
use archsig::result::{Signal, Status};
use archsig::run::{CheckArgs, Io, Signals, run_check};
use common::cli::*;
use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

struct NoOutput;
impl Io for NoOutput {
    fn create_dir(&mut self, _: &Path) -> std::io::Result<()> {
        panic!("中断後に配送しない")
    }
    fn write(&mut self, _: &Path, _: &[u8]) -> std::io::Result<()> {
        panic!("中断後に配送しない")
    }
    fn flush(&mut self, _: &Path) -> std::io::Result<()> {
        panic!("中断後に配送しない")
    }
    fn rename_noreplace(&mut self, _: &Path, _: &Path) -> std::io::Result<()> {
        panic!("中断後に配送しない")
    }
    fn remove_dir_all(&mut self, _: &Path) -> std::io::Result<()> {
        panic!("作成していないpathを削除しない")
    }
}

#[derive(Default)]
struct Finalize {
    calls: usize,
}
impl Signals for Finalize {
    fn freeze(&mut self) -> Option<Signal> {
        self.calls += 1;
        None
    }
}

fn inputs(name: &str, with_map: bool) -> (std::path::PathBuf, CheckArgs) {
    let dir = workdir(name);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/counter.atoms.json").as_slice(),
        ),
        ("l.law", include_bytes!("fixtures/counter.law").as_slice()),
        (
            "a.json",
            include_bytes!("fixtures/counter.archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let args = CheckArgs {
        atom_definitions: vec![dir.join("d.json")],
        law: dir.join("l.law"),
        archmap: with_map.then(|| dir.join("a.json")),
        out: dir.join("out"),
    };
    (dir, args)
}

#[test]
fn cancellation_at_each_input_stage_stops_before_delivery() {
    for (signal, code) in [(Signal::Int, 130), (Signal::Term, 143)] {
        for (index, point) in [
            Checkpoint::DefinitionSchema,
            Checkpoint::DefinitionSemantics,
            Checkpoint::LawIteration,
            Checkpoint::LawSemantics,
            Checkpoint::ArchMapSchema,
            Checkpoint::ArchMapCanonical,
        ]
        .into_iter()
        .enumerate()
        {
            let (dir, args) = inputs(&format!("cancel-{code}-{index}"), true);
            let trace = Rc::new(RefCell::new(Vec::new()));
            let observed = Rc::clone(&trace);
            let mut control = Control::new(Limits::default(), move |current| {
                observed.borrow_mut().push(current);
                Usage {
                    signal: (current == point).then_some(signal),
                    ..Usage::default()
                }
            });
            let mut signals = Finalize::default();
            let outcome = run_check(
                &mut NoOutput,
                &mut signals,
                &args,
                Instant::now(),
                &mut control,
            );
            assert_eq!(
                (outcome.status, outcome.exit_code),
                (Status::Interrupted, code)
            );
            assert_eq!(signals.calls, 1, "checkpointではfreezeしない");
            let trace = trace.borrow();
            assert_eq!(trace.last(), Some(&point));
            assert_eq!(trace.iter().filter(|p| **p == point).count(), 1);
            assert!(outcome.result.is_none());
            let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
            let issues = arr(get(&receipt, "issues"));
            assert_eq!(issues.len(), 1);
            assert_eq!(s(get(&issues[0], "code")), "cancelled");
            assert_eq!(s(get(get(&issues[0], "details"), "signal")), signal.wire());
            assert!(arr(get(&issues[0], "dependencies")).is_empty());
            assert!(arr(get(&issues[0], "missing")).is_empty());
            assert!(!has(&receipt, "result"));
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        }
    }
}

#[test]
fn cancellation_without_archmap_also_has_no_artifact() {
    let (dir, args) = inputs("cancel-no-map", false);
    let mut control = Control::new(Limits::default(), |point| Usage {
        signal: (point == Checkpoint::LawSemantics).then_some(Signal::Term),
        ..Usage::default()
    });
    let mut signals = Finalize::default();
    let outcome = run_check(
        &mut NoOutput,
        &mut signals,
        &args,
        Instant::now(),
        &mut control,
    );
    assert_eq!(
        (outcome.status, outcome.exit_code),
        (Status::Interrupted, 143)
    );
    assert_eq!(signals.calls, 1);
    assert!(!dir.join("out").exists());
}

#[test]
fn controlled_budget_stop_is_preserved_without_a_signal() {
    let (dir, args) = inputs("controlled-budget-stop", true);
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        |point| Usage {
            elapsed_ms: u128::from(point == Checkpoint::DefinitionSchema),
            ..Usage::default()
        },
    );
    let mut signals = Finalize::default();
    let outcome = run_check(
        &mut NoOutput,
        &mut signals,
        &args,
        Instant::now(),
        &mut control,
    );
    assert_eq!(
        (outcome.status, outcome.exit_code),
        (Status::Interrupted, 75)
    );
    let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
    let issue = &arr(get(&receipt, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "budget_exhausted");
    assert_eq!(s(get(get(issue, "details"), "resource")), "time_ms");
    assert_eq!(s(get(get(issue, "details"), "limit")), "1");
    assert_eq!(s(get(get(issue, "details"), "observed")), "1");
    assert!(!dir.join("out").exists());
}
