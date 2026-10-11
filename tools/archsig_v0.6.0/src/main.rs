//! `archsig check` と `archsig version`。

use archsig::result::Signal;
use archsig::run::{
    Command, Io, Outcome, Signals, VERSION_LINE, parse_args, run_check, usage_outcome,
};
use std::io::Write;
use std::path::Path;
use std::time::Instant;

/// 実ファイルの操作。
struct FileIo;

impl Io for FileIo {
    fn read_input(&mut self, path: &Path) -> std::io::Result<Vec<u8>> {
        // metadata は symlink を辿る。開始時に解決した先の通常ファイルだけを読む。
        if !std::fs::metadata(path)?.is_file() {
            return Err(std::io::Error::other("通常ファイルではない"));
        }
        std::fs::read(path)
    }

    fn exists(&mut self, path: &Path) -> bool {
        std::fs::symlink_metadata(path).is_ok()
    }

    fn is_dir(&mut self, path: &Path) -> bool {
        std::fs::metadata(path).is_ok_and(|m| m.is_dir())
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

/// SIGINT・SIGTERM の捕捉。handler が受けた signal は finalize の開始時に一度だけ読む。
/// 受信順は分からないので、両方を受けていれば SIGINT を先とする。以後の signal は handler が
/// 受けるだけで、状態へ反映しない。
struct ProcessSignals {
    signals: signal_hook::iterator::Signals,
    frozen: Option<Option<Signal>>,
}

impl ProcessSignals {
    fn new() -> ProcessSignals {
        let signals = signal_hook::iterator::Signals::new([
            signal_hook::consts::SIGINT,
            signal_hook::consts::SIGTERM,
        ])
        .expect("SIGINT・SIGTERM の handler を登録できる");
        ProcessSignals {
            signals,
            frozen: None,
        }
    }
}

impl Signals for ProcessSignals {
    fn freeze(&mut self) -> Option<Signal> {
        if let Some(decided) = self.frozen {
            return decided;
        }
        let pending: Vec<i32> = self.signals.pending().collect();
        let decided = if pending.contains(&signal_hook::consts::SIGINT) {
            Some(Signal::Int)
        } else if pending.contains(&signal_hook::consts::SIGTERM) {
            Some(Signal::Term)
        } else {
            None
        };
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
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_check(&mut io, &mut *signals, &check, started)
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
