//! `archsig check` と `archsig version`。

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

/// SIGINT・SIGTERM の捕捉。監視の thread が受けた順に最初の signal を残し、handler は受信の
/// 有無を flag に立てる。finalize の開始時に一度だけ読んで確定し、以後の signal は handler が
/// 受けるだけで状態へ反映しない。受信順の分からない pending の signal は SIGINT を先とする。
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
        signal_hook::flag::register(SIGINT, Arc::clone(&int))
            .expect("SIGINT の handler を登録できる");
        signal_hook::flag::register(SIGTERM, Arc::clone(&term))
            .expect("SIGTERM の handler を登録できる");
        let first = Arc::new(AtomicI32::new(0));
        let mut signals = signal_hook::iterator::Signals::new([SIGINT, SIGTERM])
            .expect("SIGINT・SIGTERM の handler を登録できる");
        let seen = Arc::clone(&first);
        std::thread::spawn(move || {
            for s in signals.forever() {
                let _ = seen.compare_exchange(0, s, Ordering::SeqCst, Ordering::SeqCst);
            }
        });
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

    fn control(&self, started: Instant) -> archsig::observed::control::Control {
        use archsig::observed::control::{Control, Limits, Usage};
        let first = Arc::clone(&self.first);
        let int = Arc::clone(&self.int);
        let term = Arc::clone(&self.term);
        Control::new(Limits::default(), move |_| Usage {
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
            let mut control = signals.control(started);
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
        Err(e) => (Some(usage_outcome(&mut io, signals, e, started)), ""),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig::observed::control::{Checkpoint, StopReason};

    fn signal_reaches_control(signal: i32, expected: Signal) {
        let mut signals = ProcessSignals::new();
        let mut control = signals.control(Instant::now());
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
            let mut control = signals.control(Instant::now());
            assert_eq!(
                control.checkpoint(Checkpoint::LawSemantics),
                Err(StopReason::Cancelled(expected))
            );
            if later_signal == signal_hook::consts::SIGINT {
                signals.int.store(true, Ordering::SeqCst);
            } else {
                signals.term.store(true, Ordering::SeqCst);
            }
            // 監視threadの後処理も、既に捕捉したsignalを置き換えない。
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
        signal_reaches_control(signal_hook::consts::SIGINT, Signal::Int);
    }

    #[test]
    fn sigterm_reaches_control_without_freezing() {
        signal_reaches_control(signal_hook::consts::SIGTERM, Signal::Term);
    }
}
