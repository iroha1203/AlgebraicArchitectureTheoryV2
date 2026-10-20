//! AC7: 入力の読込み、出力の確定、確定時の中断状態。

mod common;
use archsig::result::{Signal, Status};
use archsig::run::{CheckArgs, Io, Signals, internal_outcome, run_check};
use common::cli::*;
use std::path::{Path, PathBuf};
use std::time::Instant;

const DEFINITION: &str = include_str!("fixtures/reservations.atoms.json");
const LAW: &str = include_str!("fixtures/reservations.law");
const MAP: &str = include_str!("fixtures/reservations.archmap.json");

fn input_dir(name: &str) -> PathBuf {
    let dir = common::cli::workdir(name);
    std::fs::write(dir.join("d.json"), DEFINITION).unwrap();
    dir
}

#[test]
fn symlinked_inputs_are_resolved_and_copied() {
    let dir = input_dir("symlink");
    std::fs::write(dir.join("real.law"), LAW).unwrap();
    std::os::unix::fs::symlink("d.json", dir.join("definition-link.json")).unwrap();
    std::os::unix::fs::symlink("real.law", dir.join("link.law")).unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "definition-link.json",
            "--law",
            "link.law",
            "--out",
            "o",
        ],
    );
    consistent(&dir, &r, "complete", 0);
    assert_eq!(
        std::fs::read(dir.join("o/inputs/law.law")).unwrap(),
        LAW.as_bytes()
    );
    assert_eq!(
        std::fs::read(dir.join("o/inputs/definitions/0.json")).unwrap(),
        DEFINITION.as_bytes()
    );
    assert!(
        !std::fs::symlink_metadata(dir.join("o/inputs/definitions/0.json"))
            .unwrap()
            .file_type()
            .is_symlink()
    );
    assert!(
        !std::fs::symlink_metadata(dir.join("o/inputs/law.law"))
            .unwrap()
            .file_type()
            .is_symlink()
    );
}

#[test]
fn source_uris_and_law_references_are_not_read() {
    let dir = input_dir("noreads");
    // 同名のファイルがあっても、同梱されていない reading を探さない。
    std::fs::write(dir.join("Other.law"), LAW).unwrap();
    std::fs::write(
        dir.join("l.law"),
        LAW.replacen(
            "reading Reservations {",
            "reading Reservations {\n  use Other as O;",
            1,
        ),
    )
    .unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "o1",
        ],
    );
    let res = notified(&dir, &r, "invalid", 65);
    assert_eq!(s(get(&arr(get(&res, "issues"))[0], "code")), "reference");
    // 存在しない uri の source を指す observed の由来でも、ArchMap を検査できる。
    let observed = MAP
        .replace("\"sources\": []", &format!("\"sources\": [{{\"id\": \"src\", \"uri\": \"file:///nonexistent/archsig\", \"revision\": \"r\", \"digest\": \"sha256:{}\"}}]", "a".repeat(64)))
        .replace("\"mode\": \"specification\"", "\"mode\": \"observed\"")
        .replace("\"locations\": [],", "\"locations\": [{\"source\": \"src\", \"path\": \"src/missing.rs\"}],");
    std::fs::write(dir.join("l2.law"), LAW).unwrap();
    std::fs::write(dir.join("a.json"), observed).unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l2.law",
            "--archmap",
            "a.json",
            "--out",
            "o2",
        ],
    );
    consistent(&dir, &r, "complete", 0);
}

#[test]
fn existing_outputs_are_never_overwritten() {
    let dir = input_dir("existing");
    std::fs::write(dir.join("l.law"), LAW).unwrap();
    std::fs::create_dir(dir.join("o")).unwrap();
    std::fs::write(dir.join("o/keep.txt"), "keep").unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "o",
        ],
    );
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    assert_eq!(
        std::fs::read_to_string(dir.join("o/keep.txt")).unwrap(),
        "keep"
    );
    assert!(!dir.join("o/result.json").exists());
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "missing-parent/o",
        ],
    );
    assert_eq!(r.code, 64);
    assert!(!dir.join("missing-parent").exists());
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "",
        ],
    );
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    for out in ["d2/.", "d3/..", "."] {
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--out",
                out,
            ],
        );
        assert_eq!(r.code, 64, "{out}");
        assert!(!has(&r.receipt, "result"), "{out}");
    }
    assert!(!dir.join("d2").exists());
}

#[test]
fn unreadable_inputs_are_io_errors() {
    let dir = input_dir("unreadable");
    std::fs::create_dir(dir.join("adir")).unwrap();
    std::fs::write(dir.join("a.json"), MAP).unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "adir",
            "--archmap",
            "a.json",
            "--out",
            "o",
        ],
    );
    let res = notified(&dir, &r, "error", 74);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "io");
    assert_eq!(s(get(get(issue, "details"), "operation")), "read");
    assert_eq!(s(get(get(issue, "details"), "path")), "adir");
    assert!(!dir.join("o").exists());
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "nothing.law",
            "--out",
            "o2",
        ],
    );
    notified(&dir, &r, "error", 74);
    // ArchMap だけが読めなくても、検査を始めない。
    std::fs::write(dir.join("l.law"), LAW).unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "adir",
            "--out",
            "o4",
        ],
    );
    let res = notified(&dir, &r, "error", 74);
    assert_eq!(s(get(&arr(get(&res, "issues"))[0], "code")), "io");
    assert!(!dir.join("o4").exists());
    // UTF-8 でない path も path として扱い、読めなければ io とする。
    use std::os::unix::ffi::OsStrExt;
    let bad = std::ffi::OsStr::from_bytes(b"\xff.law");
    let out = bin()
        .current_dir(&dir)
        .arg("check")
        .args(["--atom-definition", "d.json"])
        .arg("--law")
        .arg(bad)
        .args(["--out", "o3"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(74));
    let receipt = archsig::json::parse(&out.stdout).unwrap();
    assert_eq!(s(get(&receipt, "status")), "error");
    assert!(!has(&receipt, "result"));
    assert!(!dir.join("o3").exists());
}

/// 指定した操作で失敗するファイル操作。それ以外は実ファイルへ書く。
struct FaultyIo {
    fail: &'static str,
    error: std::io::ErrorKind,
}

impl Io for FaultyIo {
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        assert_ne!(self.fail, "collision", "未所有 directory の削除は禁止");
        if self.fail == "cleanup" {
            return Err(std::io::ErrorKind::PermissionDenied.into());
        }
        std::fs::remove_dir_all(path)
    }

    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        if self.fail == "collision" {
            std::fs::create_dir(path)?;
            std::fs::write(path.join("theirs.txt"), "theirs")?;
            return Err(std::io::ErrorKind::AlreadyExists.into());
        }
        if self.fail == "create" || (self.fail == "create-inputs" && path.ends_with("inputs")) {
            return Err(self.error.into());
        }
        std::fs::create_dir(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        if (matches!(self.fail, "write" | "cleanup") && path.ends_with("result.json"))
            || (self.fail == "write-input" && path.ends_with("law.law"))
        {
            return Err(self.error.into());
        }
        std::fs::write(path, bytes)
    }
    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        if (self.fail == "flush" && path.ends_with("result.json"))
            || (self.fail == "flush-input" && path.ends_with("law.law"))
            || (self.fail == "flush-directory" && path.ends_with("inputs"))
        {
            return Err(self.error.into());
        }
        std::fs::File::open(path)?.sync_all()
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        if self.fail == "race" {
            // 確定の直前に別の処理が出力先を作った。
            std::fs::create_dir(to).unwrap();
            std::fs::write(to.join("theirs.txt"), "theirs").unwrap();
            return Err(std::io::ErrorKind::AlreadyExists.into());
        }
        if self.fail == "rename" {
            return Err(self.error.into());
        }
        std::fs::rename(from, to)
    }
}

/// finalize の開始までに捕捉した signal を差し込み、確定の回数を数える。
struct FakeSignals {
    before: Option<Signal>,
    freezes: usize,
}

impl Signals for FakeSignals {
    fn freeze(&mut self) -> Option<Signal> {
        self.freezes += 1;
        self.before
    }
}

fn args(dir: &Path) -> CheckArgs {
    std::fs::write(dir.join("l.law"), LAW).unwrap();
    CheckArgs {
        atom_definitions: vec![dir.join("d.json")],
        law: dir.join("l.law"),
        archmap: None,
        out: dir.join("o"),
    }
}

#[test]
fn failures_before_publication_leave_the_output_untouched() {
    for fail in [
        "create",
        "create-inputs",
        "write",
        "write-input",
        "flush",
        "flush-input",
        "flush-directory",
        "rename",
    ] {
        let dir = input_dir(&format!("fault-{fail}"));
        let mut io = FaultyIo {
            fail,
            error: std::io::ErrorKind::PermissionDenied,
        };
        let mut signals = FakeSignals {
            before: None,
            freezes: 0,
        };
        let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
        assert_eq!((out.status, out.exit_code), (Status::Error, 74), "{fail}");
        assert!(out.result.is_none());
        assert!(
            out.receipt().contains("\"exit_code\":74") && !out.receipt().contains("\"result\"")
        );
        assert!(!dir.join("o").exists(), "{fail}: 出力先を作らない");
        assert!(std::fs::read_dir(&dir).unwrap().all(|e| {
            !e.unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".o.archsig-")
        }));
        let receipt = archsig::json::parse(out.receipt().as_bytes()).unwrap();
        let issue = &arr(get(&receipt, "issues"))[0];
        assert_eq!(s(get(issue, "code")), "io");
        assert_eq!(s(get(get(issue, "details"), "operation")), fail_word(fail));
        assert!(!s(get(issue, "message")).is_empty());
        assert!(
            out.stderr.iter().any(|m| m.contains(fail_word(fail))),
            "{fail}: {:?}",
            out.stderr
        );
    }
    // signal を受けていても、公開前の書込みの失敗は error/74 へ退避する。
    let dir = input_dir("fault-signal");
    let mut io = FaultyIo {
        fail: "write",
        error: std::io::ErrorKind::PermissionDenied,
    };
    let mut signals = FakeSignals {
        before: Some(Signal::Int),
        freezes: 0,
    };
    let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
    assert_eq!((out.status, out.exit_code), (Status::Error, 74));
    assert!(out.result.is_none());
    // 確定時の競合では、相手が作った出力先を上書きしない。
    let dir = input_dir("fault-race");
    let mut io = FaultyIo {
        fail: "race",
        error: std::io::ErrorKind::AlreadyExists,
    };
    let mut signals = FakeSignals {
        before: None,
        freezes: 0,
    };
    let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
    assert_eq!((out.status, out.exit_code), (Status::Error, 74));
    assert_eq!(
        std::fs::read_to_string(dir.join("o/theirs.txt")).unwrap(),
        "theirs"
    );
    assert!(!dir.join("o/result.json").exists());
    assert!(std::fs::read_dir(&dir).unwrap().all(|e| {
        !e.unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".o.archsig-")
    }));
}

fn fail_word(fail: &str) -> &'static str {
    if fail.starts_with("create") {
        "create"
    } else if fail.starts_with("write") {
        "write"
    } else if fail.starts_with("flush") {
        "flush"
    } else {
        "rename"
    }
}

#[test]
fn cleanup_preserves_unowned_paths_and_reports_remnants() {
    for fail in ["collision", "cleanup"] {
        let dir = input_dir(fail);
        let mut io = FaultyIo {
            fail,
            error: std::io::ErrorKind::PermissionDenied,
        };
        let mut signals = FakeSignals {
            before: None,
            freezes: 0,
        };
        let outcome = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
        assert_eq!((outcome.status, outcome.exit_code), (Status::Error, 74));
        assert!(!dir.join("o").exists());
        let temporary: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| {
                p.file_name()
                    .unwrap()
                    .to_string_lossy()
                    .starts_with(".o.archsig-")
            })
            .collect();
        assert_eq!(temporary.len(), 1);
        if fail == "collision" {
            assert_eq!(
                std::fs::read_to_string(temporary[0].join("theirs.txt")).unwrap(),
                "theirs"
            );
        } else {
            assert!(
                outcome.stderr.iter().any(|m| m.contains("片付けられない")
                    && m.contains(&temporary[0].display().to_string()))
            );
        }
        std::fs::remove_dir_all(&temporary[0]).unwrap();
    }
}

#[test]
fn signals_decide_the_status_once_at_finalize() {
    for (before, code) in [
        (Some(Signal::Int), 130),
        (Some(Signal::Term), 143),
        (None, 0),
    ] {
        let dir = input_dir(&format!("sig-{code}"));
        let mut io = FaultyIo {
            fail: "",
            error: std::io::ErrorKind::Other,
        };
        let mut signals = FakeSignals { before, freezes: 0 };
        let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
        assert_eq!(out.exit_code, code);
        assert_eq!(signals.freezes, 1);
        let res = archsig::json::parse(&std::fs::read(dir.join("o/result.json")).unwrap()).unwrap();
        assert_eq!(num(get(&res, "exit_code")), u64::from(code));
        if code != 0 {
            assert_eq!(s(get(&res, "status")), "interrupted");
            let cancelled = arr(get(&res, "issues"))
                .iter()
                .find(|i| s(get(i, "code")) == "cancelled")
                .unwrap();
            let signal = if code == 130 { "SIGINT" } else { "SIGTERM" };
            assert_eq!(s(get(get(cancelled, "details"), "signal")), signal);
        }
    }
}

#[test]
fn unread_second_definition_reports_io_without_files() {
    let dir = input_dir("unread-second-definition");
    std::fs::write(dir.join("l.law"), b"invalid law").unwrap();
    std::fs::write(dir.join("a.json"), b"invalid JSON").unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--atom-definition",
            "missing.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "o",
        ],
    );
    let res = notified(&dir, &r, "error", 74);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "io");
    assert_eq!(s(get(get(issue, "details"), "operation")), "read");
    assert_eq!(s(get(get(issue, "details"), "path")), "missing.json");
    assert!(!dir.join("o").exists());
}

#[test]
fn definition_dependencies_are_not_loaded_from_neighbor_files() {
    let dir = input_dir("no-definition-search");
    std::fs::write(
        dir.join("Counter.atoms.json"),
        include_str!("fixtures/counter.atoms.json"),
    )
    .unwrap();
    std::fs::write(
        dir.join("extras.json"),
        include_str!("fixtures/extras.atoms.json"),
    )
    .unwrap();
    std::fs::write(
        dir.join("l.law"),
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Empty {}\n",
    )
    .unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "extras.json",
            "--law",
            "l.law",
            "--out",
            "o",
        ],
    );
    let res = notified(&dir, &r, "invalid", 65);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "reference");
    let location = get(issue, "location");
    assert_eq!(s(get(location, "input")), "definition0");
    assert_eq!(
        s(get(location, "pointer")),
        "/vocabularies/0/dependencies/0"
    );
}

#[test]
fn internal_failure_does_not_keep_any_inputs_or_copies() {
    let dir = input_dir("internal");
    let mut io = FaultyIo {
        fail: "",
        error: std::io::ErrorKind::Other,
    };
    let mut signals = FakeSignals {
        before: None,
        freezes: 0,
    };
    let arguments = args(&dir);
    let out = internal_outcome(&mut io, &mut signals, &arguments, Instant::now());
    assert_eq!((out.status, out.exit_code), (Status::Error, 70));
    assert_eq!(signals.freezes, 1);
    let receipt = archsig::json::parse(out.receipt().as_bytes()).unwrap();
    assert_eq!(s(get(&receipt, "status")), "error");
    assert_eq!(num(get(&receipt, "exit_code")), 70);
    assert_eq!(s(get(&arr(get(&receipt, "issues"))[0], "code")), "internal");
    assert!(!dir.join("o").exists());
}
