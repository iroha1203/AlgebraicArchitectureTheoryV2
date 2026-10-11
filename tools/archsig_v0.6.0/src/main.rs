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

/// SIGINT・SIGTERM の捕捉。確定点ごとに受信済みの signal を読み、最初のものを残す。
/// 同じ確定点で両方を読んだ場合は受信順が分からないので SIGINT を先とする。
struct ProcessSignals {
    signals: signal_hook::iterator::Signals,
    first: Option<Signal>,
    frozen: bool,
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
            first: None,
            frozen: false,
        }
    }

    fn poll(&mut self) {
        if self.frozen {
            return;
        }
        let mut pending: Vec<i32> = self.signals.pending().collect();
        pending.sort_by_key(|s| {
            if *s == signal_hook::consts::SIGINT {
                0
            } else {
                1
            }
        });
        for s in pending {
            let signal = if s == signal_hook::consts::SIGINT {
                Signal::Int
            } else {
                Signal::Term
            };
            self.first.get_or_insert(signal);
        }
    }
}

impl Signals for ProcessSignals {
    fn received(&mut self) -> Option<Signal> {
        self.poll();
        self.first
    }

    fn freeze(&mut self) -> Option<Signal> {
        self.poll();
        self.frozen = true;
        self.first
    }
}

fn main() {
    let started = Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut signals = ProcessSignals::new();
    // 深い入れ子の入力に備え、大きなスタックの thread で実行する。
    let outcome = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || execute(&args, &mut signals, started))
        .expect("実行 thread を起動できる")
        .join();
    let (outcome, version) = match outcome {
        Ok(o) => o,
        Err(_) => {
            eprintln!("archsig: 内部障害で終了した");
            std::process::exit(70);
        }
    };
    let mut stdout = std::io::stdout().lock();
    let line = match &outcome {
        Some(o) => o.receipt(),
        None => version.to_owned(),
    };
    if let Err(e) = writeln!(stdout, "{line}").and_then(|_| stdout.flush()) {
        eprintln!("archsig: stdout へ書けなかった: {e}");
    }
    let code = match outcome {
        Some(o) => {
            for m in &o.stderr {
                eprintln!("{m}");
            }
            o.exit_code
        }
        None => 0,
    };
    std::process::exit(i32::from(code));
}

fn execute(
    args: &[String],
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
