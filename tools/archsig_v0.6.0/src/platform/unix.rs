use super::PlatformError;
use archsig_common::control::Control;
use archsig_input::result::Signal;
use std::ffi::{OsStr, OsString};
use std::os::fd::AsFd;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};

// -1: computation/publication, 0: delivery, positive: already captured interruption.
static DELIVERY: AtomicI32 = AtomicI32::new(-1);

pub(super) struct ProcessSignals {
    first: Arc<AtomicI32>,
    int: Arc<AtomicBool>,
    term: Arc<AtomicBool>,
    frozen: Option<Option<Signal>>,
}

impl ProcessSignals {
    pub(super) fn install() -> Result<Self, PlatformError> {
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
                    let delivery = DELIVERY.load(Ordering::SeqCst);
                    if delivery >= 0 {
                        // SAFETY: _exit is async-signal-safe. Publication has finished;
                        // no temporary artifact or buffered file needs cleanup here.
                        nix::libc::_exit(if delivery > 0 { delivery } else { 128 + signal });
                    }
                })
            }
            .map_err(|err| PlatformError {
                operation: "signal_init",
                message: format!("cannot register signal handler ({signal}): {err}"),
            })?;
        }
        Ok(ProcessSignals {
            first,
            int,
            term,
            frozen: None,
        })
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

    pub(super) fn control(&self) -> Control {
        // Flags may already be set before control construction (including test injection).
        Self::observed_signal(&self.first, &self.int, &self.term);
        Control::from_signal_flag(
            Arc::clone(&self.first),
            signal_hook::consts::SIGINT,
            signal_hook::consts::SIGTERM,
        )
    }

    pub(super) fn prior_signal_exit_code(&self) -> Option<i32> {
        let prior = self.first.load(Ordering::SeqCst);
        (prior != 0).then_some(128 + prior)
    }

    pub(super) fn freeze(&mut self) -> Option<Signal> {
        if let Some(decided) = self.frozen {
            return decided;
        }
        use nix::sys::signal::{SigSet, SigmaskHow, Signal as OsSignal, pthread_sigmask};
        let mut blocked = SigSet::empty();
        blocked.add(OsSignal::SIGINT);
        blocked.add(OsSignal::SIGTERM);
        if pthread_sigmask(SigmaskHow::SIG_BLOCK, Some(&blocked), None).is_ok() {
            // SAFETY: sigpendingは有効なsigset_tへの書込みだけを行い、成功後にだけ読む。
            let mut pending = std::mem::MaybeUninit::<nix::libc::sigset_t>::uninit();
            let rc = unsafe { nix::libc::sigpending(pending.as_mut_ptr()) };
            if rc == 0 {
                // SAFETY: rc == 0 のため sigpending によって初期化済み。
                let pending = unsafe { pending.assume_init() };
                // SAFETY: pendingはsigpendingで初期化済み、signal番号はOS定数。
                unsafe {
                    if nix::libc::sigismember(&pending, signal_hook::consts::SIGINT) == 1 {
                        self.int.store(true, Ordering::SeqCst);
                    }
                    if nix::libc::sigismember(&pending, signal_hook::consts::SIGTERM) == 1 {
                        self.term.store(true, Ordering::SeqCst);
                    }
                }
            }
        }
        let decided = Self::observed_signal(&self.first, &self.int, &self.term);
        self.frozen = Some(decided);
        decided
    }
}

pub(super) fn enter_immediate_delivery() {
    DELIVERY.store(0, Ordering::SeqCst);
}

pub(super) fn begin_delivery(code: u8) -> Result<(), PlatformError> {
    DELIVERY.store(
        if matches!(code, 130 | 143) {
            i32::from(code)
        } else {
            0
        },
        Ordering::SeqCst,
    );
    use nix::sys::signal::{SigSet, SigmaskHow, Signal as OsSignal, pthread_sigmask};
    let mut mask = SigSet::empty();
    mask.add(OsSignal::SIGINT);
    mask.add(OsSignal::SIGTERM);
    pthread_sigmask(SigmaskHow::SIG_UNBLOCK, Some(&mask), None).map_err(|err| PlatformError {
        operation: "signal_unblock",
        message: format!("cannot unblock SIGINT/SIGTERM before delivery: {err}"),
    })
}

pub(super) fn write_stdout_line(line: &str) -> std::io::Result<()> {
    write_line(&mut std::io::stdout().lock(), line)
}

pub(super) fn write_stderr_line(line: &str) -> std::io::Result<()> {
    write_line(&mut std::io::stderr().lock(), line)
}

fn write_line(writer: &mut impl AsFd, line: &str) -> std::io::Result<()> {
    // std::io::Stdout suppresses EBADF for a closed descriptor. Use unbuffered
    // descriptor writes so a missing or read-only destination is a real failure.
    for mut bytes in [line.as_bytes(), b"\n".as_slice()] {
        while !bytes.is_empty() {
            match rustix::io::write(&*writer, bytes) {
                Ok(0) => return Err(std::io::ErrorKind::WriteZero.into()),
                Ok(written) => bytes = &bytes[written..],
                Err(rustix::io::Errno::INTR) => continue,
                Err(error) => return Err(error.into()),
            }
        }
    }
    Ok(())
}

pub(super) fn rename_noreplace(from: &Path, to: &Path) -> std::io::Result<()> {
    use rustix::fs::{CWD, RenameFlags, renameat_with};
    renameat_with(CWD, from, CWD, to, RenameFlags::NOREPLACE).map_err(std::io::Error::from)
}

pub(super) fn read_reuse_result_nofollow(dir: &Path, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    use rustix::fs::{Mode, OFlags, openat};
    let directory = openat(
        rustix::fs::CWD,
        dir,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW,
        Mode::empty(),
    )?;
    let file = openat(
        &directory,
        "result.json",
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK,
        Mode::empty(),
    )?;
    let file = std::fs::File::from(file);
    archsig_common::limits::read_file_handle_bounded(file, max_bytes)
}

pub(super) fn split_source_binding(value: &OsStr) -> Result<(String, PathBuf), &'static str> {
    let bytes = value.as_bytes();
    let at = bytes
        .iter()
        .position(|b| *b == b'=')
        .ok_or("expected source-id=local-file")?;
    let id = std::str::from_utf8(&bytes[..at]).map_err(|_| "source ID must be UTF-8")?;
    if id.is_empty() || at + 1 == bytes.len() {
        return Err("source bindings need distinct IDs and nonempty paths");
    }
    Ok((
        id.to_owned(),
        PathBuf::from(OsString::from_vec(bytes[at + 1..].to_vec())),
    ))
}

pub(super) fn split_flag_value(arg: &OsStr) -> Option<(&str, OsString)> {
    let bytes = arg.as_bytes();
    let eq = bytes.iter().position(|b| *b == b'=')?;
    if eq <= 2 || !bytes.starts_with(b"--") {
        return None;
    }
    let flag = std::str::from_utf8(&bytes[..eq]).ok()?;
    Some((flag, OsString::from_vec(bytes[eq + 1..].to_vec())))
}

pub(super) fn send_signal(pid: u32, signal: Signal) -> Result<(), PlatformError> {
    use nix::sys::signal::{Signal as OsSignal, kill};
    use nix::unistd::Pid;
    let raw = i32::try_from(pid).map_err(|_| PlatformError {
        operation: "signal_send",
        message: format!("pid {pid} out of range"),
    })?;
    let os_sig = match signal {
        Signal::Int => OsSignal::SIGINT,
        Signal::Term => OsSignal::SIGTERM,
    };
    kill(Pid::from_raw(raw), os_sig).map_err(|err| PlatformError {
        operation: "signal_send",
        message: err.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::control::Checkpoint;

    /// handler登録はprocess共有でmaskはthreadに残るため、各試験を別processで行う。
    fn isolated_signal_test(name: &str) -> bool {
        if std::env::var("ARCHSIG_TEST_SIGNAL_CASE").as_deref() == Ok(name) {
            return true;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                &format!("platform::unix::tests::{name}"),
                "--test-threads=1",
            ])
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
        let mut signals = ProcessSignals::install().unwrap();
        let control = signals.control();
        signal_hook::low_level::raise(signal).unwrap();
        assert_eq!(
            control.checkpoint(Checkpoint::DefinitionSchema),
            Err(expected)
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
            let control = signals.control();
            assert_eq!(control.checkpoint(Checkpoint::LawSemantics), Err(expected));
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
        let mut signals = ProcessSignals::install().unwrap();
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
        let mut signals = ProcessSignals::install().unwrap();
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
        let mut signals = ProcessSignals::install().unwrap();
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

    #[test]
    fn split_source_binding_supports_non_utf8_paths_on_unix() {
        let raw = OsString::from_vec(b"src1=/tmp/\xfffile.rs".to_vec());
        let (id, path) = split_source_binding(&raw).unwrap();
        assert_eq!(id, "src1");
        assert_eq!(path.as_os_str().as_bytes(), b"/tmp/\xfffile.rs");
        assert!(split_source_binding(OsStr::new("missing_eq")).is_err());
        assert!(split_source_binding(OsStr::new("=empty_id")).is_err());
        assert!(split_source_binding(OsStr::new("empty_path=")).is_err());
    }

    #[test]
    fn split_flag_value_preserves_embedded_equals_and_non_utf8_paths() {
        let raw = OsString::from_vec(b"--archmap=/tmp/\xffmap.json".to_vec());
        let (flag, val) = split_flag_value(&raw).unwrap();
        assert_eq!(flag, "--archmap");
        assert_eq!(val.as_os_str().as_bytes(), b"/tmp/\xffmap.json");

        let (ask_flag, ask_val) =
            split_flag_value(OsStr::new("--ask=q=evaluate(A.x,s=@v/s)")).unwrap();
        assert_eq!(ask_flag, "--ask");
        assert_eq!(ask_val, "q=evaluate(A.x,s=@v/s)");

        let (empty_flag, empty_val) = split_flag_value(OsStr::new("--archmap=")).unwrap();
        assert_eq!(empty_flag, "--archmap");
        assert!(empty_val.is_empty());

        assert!(split_flag_value(OsStr::new("--law")).is_none());
        assert!(split_flag_value(OsStr::new("--=val")).is_none());
        assert!(split_flag_value(OsStr::new("-h=val")).is_none());
    }
}
