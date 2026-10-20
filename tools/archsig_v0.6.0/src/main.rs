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
}

impl Signals for ProcessSignals {
    fn freeze(&mut self) -> Option<Signal> {
        use signal_hook::consts::{SIGINT, SIGTERM};
        if let Some(decided) = self.frozen {
            return decided;
        }
        let decided = match self.first.load(Ordering::SeqCst) {
            SIGINT => Some(Signal::Int),
            SIGTERM => Some(Signal::Term),
            _ if self.int.load(Ordering::SeqCst) => Some(Signal::Int),
            _ if self.term.load(Ordering::SeqCst) => Some(Signal::Term),
            _ => None,
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
