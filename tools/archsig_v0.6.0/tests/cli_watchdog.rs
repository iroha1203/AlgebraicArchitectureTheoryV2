//! 製品CLIに依存せず、実際の子プロセスでテスト用監視を検査する。
#[path = "common/watchdog.rs"]
mod watchdog;

use crate::common::cli;

use std::io::Write;
use std::process::Command;
use std::time::{Duration, Instant};

fn child(mode: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args([
            "--ignored",
            "--exact",
            "cli_watchdog::watchdog_child",
            "--nocapture",
        ])
        .env("ARCHSIG_WATCHDOG_TEST_CHILD", mode);
    command
}

#[test]
#[ignore = "親テストが専用の子プロセスとして実行する"]
fn watchdog_child() {
    let mode = std::env::var("ARCHSIG_WATCHDOG_TEST_CHILD").expect("専用の子プロセス");
    println!("child-pid={}", std::process::id());
    let bytes = vec![b'x'; 1024 * 1024];
    std::io::stdout().write_all(&bytes).unwrap();
    std::io::stdout().flush().unwrap();
    std::io::stderr().write_all(&bytes).unwrap();
    std::io::stderr().flush().unwrap();
    if mode == "hang" {
        loop {
            std::thread::park();
        }
    }
    // stdinはCommand::outputと同じくEOF。
    assert_eq!(
        std::io::Read::read(&mut std::io::stdin(), &mut [0]).unwrap(),
        0
    );
    std::process::exit(if mode == "normal" { 7 } else { 0 });
}

#[test]
fn normal_child_preserves_streams_and_nonzero_exit() {
    let captured = watchdog::output(&mut child("normal"), Duration::from_secs(30)).unwrap();
    assert!(!captured.timed_out);
    assert_eq!(captured.output.status.code(), Some(7));
    assert!(captured.output.stdout.ends_with(&vec![b'x'; 1024 * 1024]));
    assert_eq!(captured.output.stderr, vec![b'x'; 1024 * 1024]);
}

#[test]
fn successful_child_preserves_exit_status() {
    let captured = watchdog::output(&mut child("success"), Duration::from_secs(30)).unwrap();
    assert!(!captured.timed_out);
    assert!(captured.output.status.success());
    assert!(captured.output.stdout.ends_with(&vec![b'x'; 1024 * 1024]));
    assert_eq!(captured.output.stderr, vec![b'x'; 1024 * 1024]);
}

#[test]
fn hanging_child_is_killed_reaped_and_next_child_runs() {
    let started = Instant::now();
    let captured = watchdog::output(&mut child("hang"), Duration::from_secs(5)).unwrap();
    assert!(captured.timed_out);
    assert!(!captured.output.status.success());
    assert!(started.elapsed() < Duration::from_secs(30));
    assert!(captured.output.stdout.ends_with(&vec![b'x'; 1024 * 1024]));
    assert_eq!(captured.output.stderr, vec![b'x'; 1024 * 1024]);
    #[cfg(unix)]
    {
        let stdout = String::from_utf8(captured.output.stdout).unwrap();
        let pid = stdout
            .split("child-pid=")
            .nth(1)
            .unwrap()
            .lines()
            .next()
            .unwrap()
            .parse()
            .unwrap();
        assert_eq!(
            nix::sys::wait::waitpid(nix::unistd::Pid::from_raw(pid), None),
            Err(nix::errno::Errno::ECHILD)
        );
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(captured.output.status.signal(), Some(9));
    }
    normal_child_preserves_streams_and_nonzero_exit();
}

#[test]
fn spawn_failure_is_reported() {
    let mut command = Command::new(std::env::current_exe().unwrap().join("missing-child"));
    assert!(watchdog::output(&mut command, Duration::from_secs(30)).is_err());
}

#[test]
fn explicit_deadline_preserves_the_cli_receipt() {
    let dir = cli::workdir("watchdog-explicit-deadline");
    let default = cli::run_binary(&dir, &["run"]);
    let explicit = cli::run_binary_with_deadline(&dir, &["run"], Duration::from_secs(30));
    assert_ne!(default.code, 0);
    assert_eq!(explicit.code, default.code);
    assert_eq!(explicit.receipt.value, default.receipt.value);
    assert_eq!(explicit.stdout, default.stdout);
    assert_eq!(explicit.stderr, default.stderr);
}
