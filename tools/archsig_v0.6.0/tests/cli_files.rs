//! AC7: 入力の読込み、出力の確定、中断、receipt の配送。

mod common;
use archsig::result::{Signal, Status};
use archsig::run::{CheckArgs, Io, Signals, run_check};
use common::cli::*;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::{Duration, Instant};

const LAW: &str = include_str!("fixtures/reservations.law");
const MAP: &str = include_str!("fixtures/reservations.archmap.json");

#[test]
fn symlinked_inputs_are_resolved_and_copied() {
    let dir = workdir("symlink");
    std::fs::write(dir.join("real.law"), LAW).unwrap();
    std::os::unix::fs::symlink("real.law", dir.join("link.law")).unwrap();
    let r = run(&dir, &["check", "--law", "link.law", "--out", "o"]);
    consistent(&dir, &r, "complete", 0);
    assert_eq!(
        std::fs::read(dir.join("o/inputs/law.law")).unwrap(),
        LAW.as_bytes()
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
    let dir = workdir("noreads");
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
    let r = run(&dir, &["check", "--law", "l.law", "--out", "o1"]);
    let res = consistent(&dir, &r, "invalid", 65);
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
    let dir = workdir("existing");
    std::fs::write(dir.join("l.law"), LAW).unwrap();
    std::fs::create_dir(dir.join("o")).unwrap();
    std::fs::write(dir.join("o/keep.txt"), "keep").unwrap();
    let r = run(&dir, &["check", "--law", "l.law", "--out", "o"]);
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    assert_eq!(
        std::fs::read_to_string(dir.join("o/keep.txt")).unwrap(),
        "keep"
    );
    assert!(!dir.join("o/result.json").exists());
    let r = run(
        &dir,
        &["check", "--law", "l.law", "--out", "missing-parent/o"],
    );
    assert_eq!(r.code, 64);
    assert!(!dir.join("missing-parent").exists());
}

#[test]
fn unreadable_inputs_are_io_errors() {
    let dir = workdir("unreadable");
    std::fs::create_dir(dir.join("adir")).unwrap();
    std::fs::write(dir.join("a.json"), MAP).unwrap();
    let r = run(
        &dir,
        &[
            "check",
            "--law",
            "adir",
            "--archmap",
            "a.json",
            "--out",
            "o",
        ],
    );
    let res = consistent(&dir, &r, "error", 74);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "io");
    assert_eq!(s(get(get(issue, "details"), "operation")), "read");
    assert_eq!(s(get(get(issue, "details"), "path")), "adir");
    let inputs = arr(get(&res, "inputs"));
    let law = inputs.iter().find(|i| s(get(i, "kind")) == "law").unwrap();
    assert_eq!(s(get(law, "state")), "unread");
    assert!(!has(law, "bytes_digest") && !has(law, "path"));
    let map = inputs
        .iter()
        .find(|i| s(get(i, "kind")) == "archmap")
        .unwrap();
    assert_eq!(s(get(map, "state")), "read");
    assert!(!dir.join("o/inputs/law.law").exists());
    assert_eq!(
        std::fs::read(dir.join("o/inputs/archmap.json")).unwrap(),
        MAP.as_bytes()
    );
    let r = run(&dir, &["check", "--law", "nothing.law", "--out", "o2"]);
    consistent(&dir, &r, "error", 74);
}

/// 指定した操作の n 回目で失敗するファイル操作。それ以外は実ファイルへ書く。
struct FaultyIo {
    fail: &'static str,
    error: std::io::ErrorKind,
}

impl Io for FaultyIo {
    fn read_input(&mut self, path: &Path) -> std::io::Result<Vec<u8>> {
        std::fs::read(path)
    }
    fn exists(&mut self, path: &Path) -> bool {
        std::fs::symlink_metadata(path).is_ok()
    }
    fn is_dir(&mut self, path: &Path) -> bool {
        path.is_dir()
    }
    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        if self.fail == "create" {
            return Err(self.error.into());
        }
        std::fs::create_dir(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        if self.fail == "write" && path.ends_with("result.json") {
            return Err(self.error.into());
        }
        std::fs::write(path, bytes)
    }
    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        if self.fail == "flush" && path.ends_with("result.json") {
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

/// 捕捉した signal を差し込む。freeze の後に届いた signal は状態へ反映しない。
struct FakeSignals {
    before: Option<Signal>,
    after_freeze: Option<Signal>,
    frozen: bool,
}

impl Signals for FakeSignals {
    fn received(&mut self) -> Option<Signal> {
        self.before
    }
    fn freeze(&mut self) -> Option<Signal> {
        self.frozen = true;
        let _late = self.after_freeze;
        self.before
    }
}

fn args(dir: &Path) -> CheckArgs {
    std::fs::write(dir.join("l.law"), LAW).unwrap();
    CheckArgs {
        law: dir.join("l.law"),
        archmap: None,
        out: dir.join("o"),
    }
}

#[test]
fn failures_before_publication_leave_the_output_untouched() {
    for fail in ["create", "write", "flush", "rename"] {
        let dir = workdir(&format!("fault-{fail}"));
        let mut io = FaultyIo {
            fail,
            error: std::io::ErrorKind::PermissionDenied,
        };
        let mut signals = FakeSignals {
            before: None,
            after_freeze: None,
            frozen: false,
        };
        let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
        assert_eq!((out.status, out.exit_code), (Status::Error, 74), "{fail}");
        assert!(out.result.is_none());
        assert!(
            out.receipt().contains("\"exit_code\":74") && !out.receipt().contains("\"result\"")
        );
        assert!(!dir.join("o").exists(), "{fail}: 出力先を作らない");
        assert!(
            out.stderr.iter().any(|m| m.contains(fail_word(fail))),
            "{fail}: {:?}",
            out.stderr
        );
    }
    // 確定時の競合では、相手が作った出力先を上書きしない。
    let dir = workdir("fault-race");
    let mut io = FaultyIo {
        fail: "race",
        error: std::io::ErrorKind::AlreadyExists,
    };
    let mut signals = FakeSignals {
        before: None,
        after_freeze: None,
        frozen: false,
    };
    let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
    assert_eq!((out.status, out.exit_code), (Status::Error, 74));
    assert_eq!(
        std::fs::read_to_string(dir.join("o/theirs.txt")).unwrap(),
        "theirs"
    );
    assert!(!dir.join("o/result.json").exists());
    // 一時 directory の path を stderr に示す。
    let tmp: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            p.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".o.archsig-")
        })
        .collect();
    assert_eq!(tmp.len(), 1);
    assert!(
        out.stderr
            .iter()
            .any(|m| m.contains(&tmp[0].display().to_string()))
    );
}

fn fail_word(fail: &str) -> &'static str {
    match fail {
        "create" => "create",
        "write" => "write",
        "flush" => "flush",
        _ => "rename",
    }
}

#[test]
fn signals_decide_the_status_once_at_finalize() {
    for (before, code) in [
        (Some(Signal::Int), 130),
        (Some(Signal::Term), 143),
        (None, 0),
    ] {
        let dir = workdir(&format!("sig-{code}"));
        let mut io = FaultyIo {
            fail: "",
            error: std::io::ErrorKind::Other,
        };
        // 確定後に届く signal は状態を変えない。
        let mut signals = FakeSignals {
            before,
            after_freeze: Some(Signal::Term),
            frozen: false,
        };
        let out = run_check(&mut io, &mut signals, &args(&dir), Instant::now());
        assert_eq!(out.exit_code, code);
        assert!(signals.frozen);
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

/// 検査に時間のかかる Law。
fn slow_law(dir: &Path) {
    let n = 400_000;
    let law = format!(
        "{}reading R {{ view f(): Z = {}0{}; }}\n",
        common::HEADER,
        "(".repeat(n),
        ")".repeat(n)
    );
    std::fs::write(dir.join("slow.law"), law).unwrap();
}

#[test]
fn real_signals_interrupt_the_check() {
    for (sig, code, name) in [("-INT", 130, "SIGINT"), ("-TERM", 143, "SIGTERM")] {
        let dir = workdir(&format!("real{sig}"));
        slow_law(&dir);
        let child = bin()
            .current_dir(&dir)
            .args(["check", "--law", "slow.law", "--out", "o"])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        std::thread::sleep(Duration::from_millis(300));
        let status = std::process::Command::new("kill")
            .arg(sig)
            .arg(child.id().to_string())
            .status()
            .unwrap();
        assert!(status.success());
        let out = child.wait_with_output().unwrap();
        assert_eq!(
            out.status.code(),
            Some(code),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let receipt =
            archsig::json::parse(String::from_utf8(out.stdout).unwrap().trim_end().as_bytes())
                .unwrap();
        assert_eq!(s(get(&receipt, "status")), "interrupted");
        let res = archsig::json::parse(&std::fs::read(dir.join("o/result.json")).unwrap()).unwrap();
        assert_eq!(num(get(&res, "exit_code")), code as u64);
        let cancelled = arr(get(&res, "issues"))
            .iter()
            .find(|i| s(get(i, "code")) == "cancelled")
            .unwrap();
        assert_eq!(s(get(get(cancelled, "details"), "signal")), name);
    }
}

#[test]
fn receipt_delivery_failure_keeps_the_published_result() {
    let dir = workdir("receipt");
    slow_law(&dir);
    let mut child = bin()
        .current_dir(&dir)
        .args(["check", "--law", "slow.law", "--out", "o"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // receipt を書く前に stdout の読み手を閉じる。
    drop(child.stdout.take());
    let out = child.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&out.stderr).contains("stdout"));
    let res = archsig::json::parse(&std::fs::read(dir.join("o/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&res, "status")), "complete");
    assert_eq!(num(get(&res, "exit_code")), 0);
}
