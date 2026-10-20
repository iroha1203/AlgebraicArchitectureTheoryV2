//! `archsig check`・`run`・`version`。

use archsig::result::Signal;
use archsig::run::{
    Command, Io, Outcome, Signals, VERSION_LINE, parse_args, run_check, usage_outcome,
};
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::time::Instant;

/// 実ファイルの操作。
struct FileIo;

impl Io for FileIo {
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(path)
    }

    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::create_dir(path)
    }

    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        std::fs::File::create_new(path)?.write_all(bytes)
    }

    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::File::open(path)?.sync_all()
    }

    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        use rustix::fs::{CWD, RenameFlags, renameat_with};
        renameat_with(CWD, from, CWD, to, RenameFlags::NOREPLACE).map_err(std::io::Error::from)
    }
}

/// handlerで最初のSIGINT/SIGTERMを記録する。finalizeでは呼出しthreadをblockし、
/// 捕捉済みとpendingを一度だけ含める。CLIはthreadを追加せず、終了までblockを保つ。
struct ProcessSignals {
    first: Arc<AtomicI32>,
    int: Arc<AtomicBool>,
    term: Arc<AtomicBool>,
    frozen: Option<Option<Signal>>,
}

impl ProcessSignals {
    fn new() -> ProcessSignals {
        use signal_hook::consts::{SIGINT, SIGTERM};
        let int = Arc::new(AtomicBool::new(false));
        let term = Arc::new(AtomicBool::new(false));
        let first = Arc::new(AtomicI32::new(0));
        for (signal, flag) in [(SIGINT, Arc::clone(&int)), (SIGTERM, Arc::clone(&term))] {
            let seen = Arc::clone(&first);
            // SAFETY: handlerは固定サイズのlock-free atomic操作だけを行う。
            // allocation、lock、I/Oを行わず、参照先は登録closureのArcが保持する。
            unsafe {
                signal_hook::low_level::register(signal, move || {
                    let _ = seen.compare_exchange(0, signal, Ordering::SeqCst, Ordering::SeqCst);
                    flag.store(true, Ordering::SeqCst);
                })
            }
            .expect("SIGINT/SIGTERMのhandlerを登録できる");
        }
        ProcessSignals {
            first,
            int,
            term,
            frozen: None,
        }
    }

    fn observed_signal(first: &AtomicI32, int: &AtomicBool, term: &AtomicBool) -> Option<Signal> {
        use signal_hook::consts::{SIGINT, SIGTERM};
        if first.load(Ordering::SeqCst) == 0 {
            let observed = if int.load(Ordering::SeqCst) {
                SIGINT
            } else if term.load(Ordering::SeqCst) {
                SIGTERM
            } else {
                return None;
            };
            // checkpointでも最初の捕捉順を共有し、後着signalで置き換えない。
            let _ = first.compare_exchange(0, observed, Ordering::SeqCst, Ordering::SeqCst);
        }
        match first.load(Ordering::SeqCst) {
            SIGINT => Some(Signal::Int),
            SIGTERM => Some(Signal::Term),
            _ => None,
        }
    }

    fn control(
        &self,
        started: Instant,
        limits: archsig::observed::control::Limits,
    ) -> archsig::observed::control::Control {
        use archsig::observed::control::{Control, Usage};
        let first = Arc::clone(&self.first);
        let int = Arc::clone(&self.int);
        let term = Arc::clone(&self.term);
        Control::new(limits, move |_| Usage {
            elapsed_ms: started.elapsed().as_millis(),
            memory_mib: u128::from(archsig::run::peak_rss_bytes()) / (1024 * 1024),
            signal: Self::observed_signal(&first, &int, &term),
        })
    }
}

impl Signals for ProcessSignals {
    fn freeze(&mut self) -> Option<Signal> {
        if let Some(decided) = self.frozen {
            return decided;
        }
        use nix::sys::signal::{SigSet, SigmaskHow, Signal as OsSignal, pthread_sigmask};
        let mut blocked = SigSet::empty();
        blocked.add(OsSignal::SIGINT);
        blocked.add(OsSignal::SIGTERM);
        pthread_sigmask(SigmaskHow::SIG_BLOCK, Some(&blocked), None)
            .expect("SIGINT/SIGTERMをblockできる");
        // SAFETY: sigpendingは有効なsigset_tへの書込みだけを行い、成功後にだけ読む。
        let pending = unsafe {
            let mut pending = std::mem::MaybeUninit::<nix::libc::sigset_t>::uninit();
            assert_eq!(nix::libc::sigpending(pending.as_mut_ptr()), 0);
            pending.assume_init()
        };
        // SAFETY: pendingはsigpendingで初期化済み、signal番号はOS定数。
        unsafe {
            if nix::libc::sigismember(&pending, signal_hook::consts::SIGINT) == 1 {
                self.int.store(true, Ordering::SeqCst);
            }
            if nix::libc::sigismember(&pending, signal_hook::consts::SIGTERM) == 1 {
                self.term.store(true, Ordering::SeqCst);
            }
        }
        let decided = Self::observed_signal(&self.first, &self.int, &self.term);
        self.frozen = Some(decided);
        decided
    }
}

/// stderr へ可能な範囲で書く。書けなくても確定した終了コードを変えない。
fn note(message: &str) {
    let _ = writeln!(std::io::stderr(), "{message}");
}

fn main() {
    let started = Instant::now();
    let args: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    let mut signals = ProcessSignals::new();
    let (outcome, version) = execute(&args, &mut signals, started);
    finish(outcome, version);
}

fn finish(outcome: Option<Outcome>, version: &str) -> ! {
    let mut stdout = std::io::stdout().lock();
    let line = match &outcome {
        Some(o) => o.receipt(),
        None => version.to_owned(),
    };
    if let Err(e) = writeln!(stdout, "{line}").and_then(|_| stdout.flush()) {
        note(&format!("archsig: stdout へ書けなかった: {e}"));
    }
    let code = match outcome {
        Some(o) => {
            for m in &o.stderr {
                note(m);
            }
            o.exit_code
        }
        None => 0,
    };
    std::process::exit(i32::from(code));
}

fn execute(
    args: &[std::ffi::OsString],
    signals: &mut ProcessSignals,
    started: Instant,
) -> (Option<Outcome>, &'static str) {
    let mut io = FileIo;
    match parse_args(args) {
        Ok(Command::Version) => (None, VERSION_LINE),
        Ok(Command::Check(check)) => {
            let mut control =
                signals.control(started, archsig::observed::control::Limits::default());
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_check(&mut io, &mut *signals, &check, started, &mut control)
            }));
            match outcome {
                Ok(o) => (Some(o), ""),
                Err(_) => (
                    Some(archsig::run::internal_outcome(
                        &mut io,
                        &mut *signals,
                        &check,
                        started,
                    )),
                    "",
                ),
            }
        }
        Ok(Command::Run(run)) => {
            let mut control = signals.control(started, run.limits());
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                archsig::run::run_requests(&mut io, &mut *signals, &run, started, &mut control)
            }));
            (
                Some(outcome.unwrap_or_else(|_| archsig::run::run_internal_outcome(&mut *signals))),
                "",
            )
        }
        Err(e) => (Some(usage_outcome(&mut io, signals, e, started)), ""),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig::observed::control::{Checkpoint, StopReason};

    /// handler登録はprocess共有でmaskはthreadに残るため、各試験を別processで行う。
    fn isolated_signal_test(name: &str) -> bool {
        if std::env::var("ARCHSIG_TEST_SIGNAL_CASE").as_deref() == Ok(name) {
            return true;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &format!("tests::{name}"), "--test-threads=1"])
            .env("ARCHSIG_TEST_SIGNAL_CASE", name)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        false
    }

    fn signal_reaches_control(signal: i32, expected: Signal) {
        let mut signals = ProcessSignals::new();
        let mut control = signals.control(
            Instant::now(),
            archsig::observed::control::Limits::default(),
        );
        signal_hook::low_level::raise(signal).unwrap();
        assert_eq!(
            control.checkpoint(Checkpoint::DefinitionSchema),
            Err(StopReason::Cancelled(expected))
        );
        assert_eq!(signals.frozen, None, "checkpointでfinalizeを開始しない");
        assert_eq!(signals.freeze(), Some(expected));
    }

    #[test]
    fn observed_first_signal_survives_a_later_signal_before_finalize() {
        for (first_signal, later_signal, expected) in [
            (
                signal_hook::consts::SIGTERM,
                signal_hook::consts::SIGINT,
                Signal::Term,
            ),
            (
                signal_hook::consts::SIGINT,
                signal_hook::consts::SIGTERM,
                Signal::Int,
            ),
        ] {
            let mut signals = ProcessSignals {
                first: Arc::new(AtomicI32::new(0)),
                int: Arc::new(AtomicBool::new(first_signal == signal_hook::consts::SIGINT)),
                term: Arc::new(AtomicBool::new(
                    first_signal == signal_hook::consts::SIGTERM,
                )),
                frozen: None,
            };
            let mut control = signals.control(
                Instant::now(),
                archsig::observed::control::Limits::default(),
            );
            assert_eq!(
                control.checkpoint(Checkpoint::LawSemantics),
                Err(StopReason::Cancelled(expected))
            );
            if later_signal == signal_hook::consts::SIGINT {
                signals.int.store(true, Ordering::SeqCst);
            } else {
                signals.term.store(true, Ordering::SeqCst);
            }
            // 後着handlerも、既に捕捉したsignalを置き換えない。
            let _ =
                signals
                    .first
                    .compare_exchange(0, later_signal, Ordering::SeqCst, Ordering::SeqCst);
            assert_eq!(signals.freeze(), Some(expected));
            assert_eq!(signals.frozen, Some(Some(expected)));
        }
    }

    #[test]
    fn sigint_reaches_control_without_freezing() {
        if !isolated_signal_test("sigint_reaches_control_without_freezing") {
            return;
        }
        signal_reaches_control(signal_hook::consts::SIGINT, Signal::Int);
    }

    #[test]
    fn sigterm_reaches_control_without_freezing() {
        if !isolated_signal_test("sigterm_reaches_control_without_freezing") {
            return;
        }
        signal_reaches_control(signal_hook::consts::SIGTERM, Signal::Term);
    }

    #[test]
    fn signal_handler_records_received_order_without_a_monitor_thread() {
        if !isolated_signal_test("signal_handler_records_received_order_without_a_monitor_thread") {
            return;
        }
        let mut signals = ProcessSignals::new();
        signal_hook::low_level::raise(signal_hook::consts::SIGTERM).unwrap();
        signal_hook::low_level::raise(signal_hook::consts::SIGINT).unwrap();
        assert_eq!(
            signals.first.load(Ordering::SeqCst),
            signal_hook::consts::SIGTERM
        );
        assert_eq!(signals.freeze(), Some(Signal::Term));
    }

    #[test]
    fn finalize_includes_both_pending_signals_with_sigint_priority() {
        if !isolated_signal_test("finalize_includes_both_pending_signals_with_sigint_priority") {
            return;
        }
        use nix::sys::signal::{SigSet, SigmaskHow, Signal as OsSignal, pthread_sigmask};
        let mut signals = ProcessSignals::new();
        let mut blocked = SigSet::empty();
        blocked.add(OsSignal::SIGINT);
        blocked.add(OsSignal::SIGTERM);
        pthread_sigmask(SigmaskHow::SIG_BLOCK, Some(&blocked), None).unwrap();
        signal_hook::low_level::raise(signal_hook::consts::SIGTERM).unwrap();
        signal_hook::low_level::raise(signal_hook::consts::SIGINT).unwrap();
        assert_eq!(signals.first.load(Ordering::SeqCst), 0);
        assert_eq!(signals.freeze(), Some(Signal::Int));
    }

    #[test]
    fn finalize_keeps_signals_blocked_and_ignores_later_pending_signals() {
        if !isolated_signal_test("finalize_keeps_signals_blocked_and_ignores_later_pending_signals")
        {
            return;
        }
        use nix::sys::signal::{SigSet, SigmaskHow, Signal as OsSignal, pthread_sigmask};
        let mut signals = ProcessSignals::new();
        assert_eq!(signals.freeze(), None);
        let mut mask = SigSet::empty();
        pthread_sigmask(SigmaskHow::SIG_BLOCK, None, Some(&mut mask)).unwrap();
        assert!(mask.contains(OsSignal::SIGINT));
        assert!(mask.contains(OsSignal::SIGTERM));
        signal_hook::low_level::raise(signal_hook::consts::SIGTERM).unwrap();
        signal_hook::low_level::raise(signal_hook::consts::SIGINT).unwrap();
        assert_eq!(signals.first.load(Ordering::SeqCst), 0);
        assert_eq!(signals.freeze(), None);
    }

    // 製品へ同期flag/環境変数を追加せず、同じparse/execute/finishをsubprocessで使う。
    #[test]
    #[ignore = "real_signals_cancel_cli_execution_before_artifactsがsubprocessとして起動する"]
    fn signal_cli_child() {
        use std::io::Read;
        let kind = std::env::var("ARCHSIG_TEST_CHILD_KIND").unwrap();
        let mut signals = ProcessSignals::new();
        println!("\nARCHSIG_READY");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_exact(&mut [0]).unwrap();
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        while signals.first.load(Ordering::SeqCst) == 0 {
            assert!(Instant::now() < deadline, "実signalを捕捉しなかった");
            std::thread::yield_now();
        }
        let mut args = vec![
            kind.as_str(),
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "out",
        ];
        if kind == "run" {
            args.extend(["--ask", "n=evaluate(CountCheck.amount,s=@v/s)"]);
        }
        let args: Vec<_> = args.into_iter().map(std::ffi::OsString::from).collect();
        let (outcome, version) = execute(&args, &mut signals, Instant::now());
        finish(outcome, version);
    }

    #[test]
    fn real_signals_cancel_cli_execution_before_artifacts() {
        use archsig::json::{JNode, JValue, parse};
        use nix::sys::signal::{Signal as OsSignal, kill};
        use nix::unistd::Pid;
        use std::io::{BufRead, BufReader, Read};
        use std::process::{Child, Command, Stdio};
        struct Running(Child);
        impl Drop for Running {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        fn field<'a>(node: &'a JNode, key: &str) -> &'a JNode {
            let JValue::Obj(fields) = &node.value else {
                panic!("object")
            };
            &fields.iter().find(|(name, _)| name == key).unwrap().1
        }
        fn text(node: &JNode) -> &str {
            let JValue::Str(value) = &node.value else {
                panic!("string")
            };
            value
        }
        for kind in ["check", "run"] {
            for (signal, code, name) in [
                (OsSignal::SIGINT, 130, "SIGINT"),
                (OsSignal::SIGTERM, 143, "SIGTERM"),
            ] {
                let dir = std::env::temp_dir().join(format!(
                    "archsig-signal-{}-{kind}-{name}",
                    std::process::id()
                ));
                let _ = std::fs::remove_dir_all(&dir);
                std::fs::create_dir(&dir).unwrap();
                std::fs::write(
                    dir.join("d.json"),
                    include_bytes!("../tests/fixtures/counter.atoms.json"),
                )
                .unwrap();
                std::fs::write(
                    dir.join("l.law"),
                    include_bytes!("../tests/fixtures/counter.law"),
                )
                .unwrap();
                std::fs::write(
                    dir.join("a.json"),
                    include_bytes!("../tests/fixtures/counter.archmap.json"),
                )
                .unwrap();
                let mut child = Running(
                    Command::new(std::env::current_exe().unwrap())
                        .current_dir(&dir)
                        .args([
                            "--ignored",
                            "--exact",
                            "tests::signal_cli_child",
                            "--nocapture",
                            "--test-threads=1",
                        ])
                        .env("ARCHSIG_TEST_CHILD_KIND", kind)
                        .stdin(Stdio::piped())
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .spawn()
                        .unwrap(),
                );
                let mut stdout = BufReader::new(child.0.stdout.take().unwrap());
                loop {
                    let mut line = String::new();
                    assert!(stdout.read_line(&mut line).unwrap() > 0, "同期合図前に終了");
                    if line.trim() == "ARCHSIG_READY" {
                        break;
                    }
                }
                kill(Pid::from_raw(child.0.id().try_into().unwrap()), signal).unwrap();
                child.0.stdin.take().unwrap().write_all(b"x").unwrap();
                let mut receipt = String::new();
                stdout.read_to_string(&mut receipt).unwrap();
                assert_eq!(child.0.wait().unwrap().code(), Some(code));
                assert_eq!(receipt.matches('\n').count(), 1);
                let receipt = parse(receipt.trim_end().as_bytes()).unwrap();
                assert_eq!(text(field(&receipt, "status")), "interrupted");
                assert_eq!(
                    field(&receipt, "exit_code").value,
                    JValue::Num(code.to_string())
                );
                let JValue::Arr(issues) = &field(&receipt, "issues").value else {
                    panic!("issues")
                };
                assert!(issues.iter().any(|i| text(field(i, "code")) == "cancelled"
                    && text(field(field(i, "details"), "signal")) == name));
                let JValue::Obj(fields) = &receipt.value else {
                    panic!("receipt")
                };
                assert!(!fields.iter().any(|(name, _)| name == "result"));
                assert!(!dir.join("out").exists());
                assert!(!std::fs::read_dir(&dir).unwrap().any(|e| {
                    e.unwrap()
                        .file_name()
                        .to_string_lossy()
                        .contains(".archsig-")
                }));
            }
        }
    }
}
