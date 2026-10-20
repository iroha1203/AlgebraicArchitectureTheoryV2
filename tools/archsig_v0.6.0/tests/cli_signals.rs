//! 実製品バイナリのsignalと配送を、満杯のstdoutで同期する。
#![cfg(unix)]
mod common;
use archsig::json::parse;
use common::cli::*;
use nix::sys::signal::{Signal, kill};
use nix::unistd::Pid;
use std::io::{Read, Write};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &[u8] = include_bytes!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");

struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
fn setup(name: &str) -> PathBuf {
    let dir = workdir(name);
    std::fs::write(dir.join("d.json"), D).unwrap();
    std::fs::write(dir.join("l.law"), L).unwrap();
    std::fs::write(dir.join("a.json"), A).unwrap();
    dir
}
fn command(dir: &Path, kind: &str, definition: &str) -> Command {
    let mut command = bin();
    command.current_dir(dir).args([
        kind,
        "--atom-definition",
        definition,
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ]);
    if kind == "run" {
        command.args(["--ask", "n=evaluate(CountCheck.amount,s=@v/s)"]);
    }
    command.stderr(Stdio::piped());
    command
}
fn send(child: &Child, signal: Signal) {
    kill(Pid::from_raw(child.id().try_into().unwrap()), signal).unwrap();
}
fn wait_for(child: &mut Child, ready: impl Fn() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(30);
    while !ready() {
        assert!(
            child.try_wait().unwrap().is_none(),
            "同期境界の前に終了した"
        );
        assert!(Instant::now() < deadline, "同期境界へ到達しなかった");
        std::thread::sleep(Duration::from_millis(1));
    }
}

/// stdoutを書けない境界を先に作る。時刻や入力の大きさでfinalizeとの競走を作らない。
fn full_stdout() -> (UnixStream, OwnedFd, usize) {
    let (reader, mut writer) = UnixStream::pair().unwrap();
    reader
        .set_read_timeout(Some(Duration::from_secs(30)))
        .unwrap();
    writer.set_nonblocking(true).unwrap();
    let bytes = [b'x'; 4096];
    let mut count = 0;
    loop {
        match writer.write(&bytes) {
            Ok(n) => {
                assert!(n > 0);
                count += n;
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
            Err(e) => panic!("stdout同期: {e}"),
        }
    }
    writer.set_nonblocking(false).unwrap();
    (reader, writer.into(), count)
}

#[test]
fn signals_after_publication_keep_result_receipt_and_exit_frozen() {
    let dir = setup("after-publication");
    std::fs::write(
        dir.join("a.json"),
        A.replace("\"value\": \"2\"", "\"value\": \"12\""),
    )
    .unwrap();
    let (mut reader, writer, count) = full_stdout();
    let mut command = command(&dir, "run", "d.json");
    command.args(["--ask", "audit=check(CountAudit.bounded,s=@v/s)"]);
    let mut child = Running(command.stdout(Stdio::from(writer)).spawn().unwrap());
    drop(command);
    wait_for(&mut child.0, || dir.join("out/result.json").exists());
    assert!(
        child.0.try_wait().unwrap().is_none(),
        "receiptは満杯stdoutで待機中"
    );
    send(&child.0, Signal::SIGTERM);
    send(&child.0, Signal::SIGINT);
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes).unwrap();
    assert!(bytes[..count].iter().all(|b| *b == b'x'));
    let line = std::str::from_utf8(&bytes[count..]).unwrap();
    assert_eq!(line.matches('\n').count(), 1);
    let receipt = parse(line.trim_end().as_bytes()).unwrap();
    let result = parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
    assert_eq!(child.0.wait().unwrap().code(), Some(1));
    for doc in [&receipt, &result] {
        assert_eq!(s(get(doc, "status")), "complete");
        assert_eq!(num(get(doc, "exit_code")), 1);
    }
    assert!(!has(&receipt, "issues"));
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "refuted"
    );
}

#[test]
fn broken_stdout_after_publication_keeps_partial_result_and_exit_code() {
    let dir = setup("broken-stdout");
    let missing = A.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", "");
    std::fs::write(dir.join("a.json"), missing).unwrap();
    let mut child = Running(
        command(&dir, "run", "d.json")
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    // 読取側を閉じ、receiptのwriteによるEPIPE/SIGPIPEを実際に発生させる。
    drop(child.0.stdout.take());
    let mut stderr = String::new();
    child
        .0
        .stderr
        .take()
        .unwrap()
        .read_to_string(&mut stderr)
        .unwrap();
    assert_eq!(child.0.wait().unwrap().code(), Some(2));
    assert!(stderr.contains("stdout"));
    let result = parse(&std::fs::read(dir.join("out/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&result, "status")), "partial");
    assert_eq!(num(get(&result, "exit_code")), 2);
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[0], "status")),
        "undetermined"
    );
    assert!(!std::fs::read_dir(&dir).unwrap().any(|e| {
        e.unwrap()
            .file_name()
            .to_string_lossy()
            .contains(".archsig-")
    }));
}
