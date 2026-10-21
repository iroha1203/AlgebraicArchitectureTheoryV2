//! Path composeの取消・資源停止と、同じ配送経路の既存データ保護。
mod common;
#[path = "common/public_path_compose.rs"]
mod fixture;
use archsig::{
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
    },
    result::{Signal, Status},
    run::{run_requests, CheckArgs, Io, RunArgs, Signals},
};
use common::cli::*;
use std::{
    cell::Cell,
    path::{Path, PathBuf},
    rc::Rc,
    time::Instant,
};
const ASKS: [&str; 3] = [fixture::E, fixture::F, fixture::C];
fn setup(name: &str) -> (PathBuf, RunArgs) {
    let dir = workdir(name);
    let input = fixture::input(false, "path-delivery");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let args = RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![dir.join("d.json")],
            law: dir.join("l.law"),
            archmap: Some(dir.join("a.json")),
            out: dir.join("out"),
        },
        asks: ASKS.iter().map(|s| (*s).into()).collect(),
        reuse: None,
        time_ms: None,
        memory_mib: None,
    };
    (dir, args)
}
#[derive(Default)]
struct Finalize(usize);
impl Signals for Finalize {
    fn freeze(&mut self) -> Option<Signal> {
        self.0 += 1;
        None
    }
}
#[derive(Default)]
struct Files {
    created: Vec<PathBuf>,
    removed: Vec<PathBuf>,
    writes: usize,
    fail_write: bool,
    race: bool,
}
impl Io for Files {
    fn create_dir(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::create_dir(p)?;
        self.created.push(p.into());
        Ok(())
    }
    fn write(&mut self, p: &Path, bytes: &[u8]) -> std::io::Result<()> {
        self.writes += 1;
        if self.fail_write && self.writes == 2 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "fixture write denied",
            ));
        }
        std::fs::write(p, bytes)
    }
    fn flush(&mut self, p: &Path) -> std::io::Result<()> {
        std::fs::File::open(p)?.sync_all()
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        if self.race {
            std::fs::create_dir(to)?;
            std::fs::write(to.join("result.json"), b"existing result bytes")?;
        }
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            from,
            rustix::fs::CWD,
            to,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(Into::into)
    }
    fn remove_dir_all(&mut self, p: &Path) -> std::io::Result<()> {
        assert_eq!(Some(p), self.created.first().map(PathBuf::as_path));
        self.removed.push(p.into());
        std::fs::remove_dir_all(p)
    }
}
#[test]
fn path_compose_request_resolution_stops_notify_without_starting_output() {
    for mode in 0..4 {
        let (dir, mut args) = setup(&format!("path-compose-resolver-stop-{mode}"));
        args.time_ms = (mode == 0).then(|| "1".into());
        args.memory_mib = (mode == 1).then(|| "1".into());
        let mut control = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |point| {
                let stop = point == Checkpoint::RequestBinding;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: if stop {
                        match mode {
                            2 => Some(Signal::Int),
                            3 => Some(Signal::Term),
                            _ => None,
                        }
                    } else {
                        None
                    },
                }
            },
        );
        let mut io = Files::default();
        let mut signals = Finalize::default();
        let outcome = run_requests(&mut io, &mut signals, &args, Instant::now(), &mut control);
        assert_eq!(outcome.status, Status::Interrupted);
        assert_eq!(
            outcome.exit_code,
            match mode {
                2 => 130,
                3 => 143,
                _ => 75,
            }
        );
        assert!(outcome.result.is_none());
        assert!(io.created.is_empty());
        assert!(io.removed.is_empty());
        assert_eq!(signals.0, 1);
        let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
        assert!(!has(&receipt, "result"));
        assert!(!arr(get(&receipt, "issues")).is_empty());
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn path_compose_late_stops_publish_only_checked_values_with_consistent_status_and_exit() {
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut probe = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::NativeResultNode {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let original =
        evaluate_observed_bytes(fixture::input(false, "path-delivery"), &ASKS, &mut probe).unwrap();
    assert_eq!(original.status(), "complete");
    let total = count.get();
    assert!(total >= 3);
    for mode in 0..4 {
        let (dir, mut args) = setup(&format!("path-compose-late-stop-{mode}"));
        args.time_ms = (mode == 0).then(|| "1".into());
        args.memory_mib = (mode == 1).then(|| "1".into());
        let count = Rc::new(Cell::new(0usize));
        let seen = count.clone();
        let mut control = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |p| {
                if p == Checkpoint::NativeResultNode {
                    seen.set(seen.get() + 1);
                }
                let stop = seen.get() >= total;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: if stop {
                        match mode {
                            2 => Some(Signal::Int),
                            3 => Some(Signal::Term),
                            _ => None,
                        }
                    } else {
                        None
                    },
                }
            },
        );
        let mut io = Files::default();
        let mut signals = Finalize::default();
        let outcome = run_requests(&mut io, &mut signals, &args, Instant::now(), &mut control);
        let code = match mode {
            2 => 130,
            3 => 143,
            _ => 75,
        };
        assert_eq!(outcome.status, Status::Interrupted);
        assert_eq!(outcome.exit_code, code);
        assert_eq!(signals.0, 1);
        assert_eq!(count.get(), total);
        assert!(outcome.result.is_some());
        assert!(io.removed.is_empty());
        let result =
            archsig::json::parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
        assert_eq!(s(get(&result, "status")), "interrupted");
        assert_eq!(num(get(&result, "exit_code")), code as u64);
        let answer = &arr(get(&result, "answers"))[2];
        assert_eq!(s(get(answer, "status")), "established");
        assert!(!has(get(answer, "outputs"), "map"));
        assert!(has(get(answer, "outputs"), "operation"));
        assert!(arr(get(&result, "nodes"))
            .iter()
            .all(|n| s(get(n, "state")) == "value"));
        assert!(!dir.read_dir().unwrap().any(|e| {
            e.unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".archsig-")
        }));
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn path_compose_write_failures_remove_only_this_runs_temporary_directory() {
    for race in [false, true] {
        let (dir, args) = setup(&format!("path-compose-write-failure-{race}"));
        let older = dir.join(".out.archsig-older");
        std::fs::create_dir(&older).unwrap();
        std::fs::write(older.join("keep"), b"older bytes").unwrap();
        let existing = dir.join("existing");
        std::fs::create_dir(&existing).unwrap();
        std::fs::write(existing.join("result.json"), b"previous bytes").unwrap();
        let mut io = Files {
            fail_write: !race,
            race,
            ..Files::default()
        };
        let mut signals = Finalize::default();
        let outcome = run_requests(
            &mut io,
            &mut signals,
            &args,
            Instant::now(),
            &mut Control::unlimited(),
        );
        assert_eq!(outcome.status, Status::Error);
        assert_eq!(outcome.exit_code, 74);
        assert!(outcome.result.is_none());
        assert_eq!(signals.0, 1);
        assert_eq!(io.removed.len(), 1);
        assert!(!io.removed[0].exists());
        assert_eq!(std::fs::read(older.join("keep")).unwrap(), b"older bytes");
        assert_eq!(
            std::fs::read(existing.join("result.json")).unwrap(),
            b"previous bytes"
        );
        if race {
            assert_eq!(
                std::fs::read(args.inputs.out.join("result.json")).unwrap(),
                b"existing result bytes"
            );
        } else {
            assert!(!args.inputs.out.exists());
        }
        let receipt = archsig::json::parse(outcome.receipt().as_bytes()).unwrap();
        assert!(!has(&receipt, "result"));
        assert_eq!(s(get(&arr(get(&receipt, "issues"))[0], "code")), "io");
        std::fs::remove_dir_all(dir).unwrap();
    }
}
