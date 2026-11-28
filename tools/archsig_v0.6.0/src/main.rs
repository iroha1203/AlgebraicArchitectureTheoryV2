//! `archsig` CLI エントリポイント（`ExitCode` でクリーン終了）。

use archsig::cli::format::{render_json_value, render_outcome, render_raw_json_str};
use archsig::cli::{
    CliCommand, OutputFormat, parse_cli, with_detail_level, with_out_options, with_progress,
};
use archsig::commands::execute_cli_command;
use archsig::platform::{self, PlatformError, ProcessSignals};
#[cfg(test)]
use archsig::run::parse_args;
use archsig::run::{Command, FileIo, Outcome, VERSION_LINE, execute_command, with_max_file_bytes};
#[cfg(test)]
use archsig_input::result::Signal;
use archsig_input::result::{ResultIssue, Status};
#[cfg(test)]
use std::io::Write;
use std::process::ExitCode;

fn signal_init_failure_outcome(err: &PlatformError) -> Outcome {
    Outcome {
        status: Status::Error,
        exit_code: 70,
        result: None,
        summary: None,
        issues: vec![
            ResultIssue::Internal {
                operation: err.operation.to_owned(),
                message: err.message.clone(),
            }
            .wire(),
        ],
    }
}

fn main() -> ExitCode {
    // 捕捉した内部障害は receipt で通知する。panic の既定表示を重複させない。
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    let mut signals = match ProcessSignals::install() {
        Ok(signals) => signals,
        Err(err) => {
            let outcome = signal_init_failure_outcome(&err);
            let _ = platform::write_stderr_line(&outcome.receipt());
            return ExitCode::from(70);
        }
    };

    let parsed = match parse_cli(&args) {
        Ok(parsed) => parsed,
        Err(err) => {
            let outcome = err.into_outcome(&mut signals);
            return finish_formatted(Some(outcome), "", 0, OutputFormat::Json).1;
        }
    };

    let options = parsed.options;
    let progress = options.verbose || options.progress;
    let format = options.format;

    match parsed.command {
        CliCommand::Help(text) => finish_formatted(None, text, 0, OutputFormat::Json).1,
        CliCommand::Version => {
            ProcessSignals::enter_immediate_delivery();
            if let Some(code) = signals.prior_signal_exit_code() {
                return ExitCode::from(u8::try_from(code).unwrap_or(70));
            }
            let rendered = render_raw_json_str(VERSION_LINE, format);
            finish_formatted(None, &rendered, 0, format).1
        }
        CliCommand::Evidence(ref ev_args) => {
            ProcessSignals::enter_immediate_delivery();
            if let Some(code) = signals.prior_signal_exit_code() {
                return ExitCode::from(u8::try_from(code).unwrap_or(70));
            }
            let res = with_progress(progress, || {
                archsig::observe::execute_evidence(ev_args, options.max_file_bytes)
            });
            match res {
                Ok(resp) => {
                    let rendered = render_raw_json_str(&resp.text, format);
                    finish_formatted(None, &rendered, resp.code, format).1
                }
                Err(outcome) => finish_formatted(Some(outcome), "", 0, format).1,
            }
        }
        CliCommand::LawFibers(ref fib_args) => {
            ProcessSignals::enter_immediate_delivery();
            if let Some(code) = signals.prior_signal_exit_code() {
                return ExitCode::from(u8::try_from(code).unwrap_or(70));
            }
            let res = with_progress(progress, || {
                archsig::observe::execute_fibers(fib_args, options.max_file_bytes)
            });
            match res {
                Ok(resp) => {
                    let rendered = render_raw_json_str(&resp.text, format);
                    finish_formatted(None, &rendered, resp.code, format).1
                }
                Err(outcome) => finish_formatted(Some(outcome), "", 0, format).1,
            }
        }
        CliCommand::Digest(_) | CliCommand::InspectInputs(_) | CliCommand::InspectResult(_) => {
            let control = signals.control();
            let res = with_progress(progress, || {
                execute_cli_command(
                    &parsed.command,
                    options.max_file_bytes,
                    &mut signals,
                    &control,
                )
            });
            match res {
                Ok(output) => {
                    let rendered = render_json_value(&output.json, format);
                    finish_formatted(None, &rendered, output.exit_code, format).1
                }
                Err(outcome) => finish_formatted(Some(outcome), "", 0, format).1,
            }
        }
        CliCommand::Check(c) => {
            let cmd = Command::Check(c);
            let mut io = FileIo;
            let control = signals.control();
            let outcome = with_progress(progress, || {
                with_out_options(options.out_options, || {
                    with_detail_level(options.detail, || {
                        execute_command(&cmd, &mut io, &mut signals, &control)
                    })
                })
            });
            finish_formatted(outcome, "", 0, format).1
        }
        CliCommand::Run(r) => {
            let cmd = Command::Run(r);
            let mut io = FileIo;
            let control = signals.control();
            let outcome = with_progress(progress, || {
                with_out_options(options.out_options, || {
                    with_detail_level(options.detail, || {
                        execute_command(&cmd, &mut io, &mut signals, &control)
                    })
                })
            });
            finish_formatted(outcome, "", 0, format).1
        }
        CliCommand::Reobserve(r) => {
            let cmd = Command::Reobserve(r);
            let mut io = FileIo;
            let control = signals.control();
            let outcome = with_progress(progress, || {
                with_out_options(options.out_options, || {
                    with_detail_level(options.detail, || {
                        with_max_file_bytes(options.max_file_bytes, || {
                            execute_command(&cmd, &mut io, &mut signals, &control)
                        })
                    })
                })
            });
            finish_formatted(outcome, "", 0, format).1
        }
    }
}

fn finish_formatted(
    outcome: Option<Outcome>,
    information: &str,
    success_code: u8,
    format: OutputFormat,
) -> (u8, ExitCode) {
    let code = outcome.as_ref().map_or(success_code, |o| o.exit_code);
    if let Err(err) = ProcessSignals::begin_delivery(code) {
        let failure = signal_init_failure_outcome(&err);
        let _ = platform::write_stderr_line(&render_outcome(&failure, format));
        return (70, ExitCode::from(70));
    }
    let rendered = outcome
        .as_ref()
        .map_or_else(|| information.to_owned(), |o| render_outcome(o, format));
    let failed = outcome.as_ref().is_some_and(|o| {
        matches!(
            o.status,
            Status::Invalid | Status::Unsupported | Status::Error | Status::Interrupted
        )
    });
    // Verified partial answers remain useful even when execution was interrupted.
    let has_answers = outcome.as_ref().is_some_and(|o| o.summary.is_some());
    if failed && has_answers {
        let o = outcome.as_ref().expect("failure has an outcome");
        let diagnostic = Outcome {
            status: o.status,
            exit_code: o.exit_code,
            result: o.result.clone(),
            summary: None,
            issues: o.issues.clone(),
        };
        if let Err(error) = platform::write_stderr_line(&render_outcome(&diagnostic, format)) {
            let c = if error.kind() == std::io::ErrorKind::BrokenPipe {
                141
            } else {
                74
            };
            return (c, ExitCode::from(c));
        }
    }
    let result = if failed && !has_answers {
        platform::write_stderr_line(&rendered)
    } else {
        platform::write_stdout_line(&rendered)
    };
    let exit = match result {
        Ok(()) => code,
        Err(error) if error.kind() == std::io::ErrorKind::BrokenPipe => 141,
        Err(error) => {
            if !failed || has_answers {
                let diagnostic = Outcome {
                    status: Status::Error,
                    exit_code: 74,
                    result: outcome.as_ref().and_then(|o| o.result.clone()),
                    summary: None,
                    issues: vec![
                        ResultIssue::Io {
                            operation: "write",
                            path: "stdout".into(),
                            message: format!("cannot deliver stdout: {error}"),
                        }
                        .wire(),
                    ],
                };
                if let Err(error) =
                    platform::write_stderr_line(&render_outcome(&diagnostic, format))
                    && error.kind() == std::io::ErrorKind::BrokenPipe
                {
                    return (141, ExitCode::from(141));
                }
            }
            74
        }
    };
    (exit, ExitCode::from(exit))
}

#[cfg(test)]
fn finish_and_exit_for_test(outcome: Option<Outcome>, information: &str) -> ! {
    let (code, _) = finish_formatted(outcome, information, 0, OutputFormat::Json);
    std::process::exit(i32::from(code));
}

#[cfg(test)]
fn execute(
    args: &[std::ffi::OsString],
    signals: &mut ProcessSignals,
) -> (Option<Outcome>, &'static str) {
    let mut io = FileIo;
    match parse_args(args) {
        Ok(archsig::run::Command::Help(text)) => (None, text),
        Ok(command) => {
            let control = signals.control();
            (
                execute_command(&command, &mut io, signals, &control),
                VERSION_LINE,
            )
        }
        Err(e) => (Some(archsig::run::usage_outcome(&mut io, signals, e)), ""),
    }
}

#[cfg(test)]
#[allow(dead_code)]
#[path = "../tests/common/watchdog.rs"]
mod test_watchdog;

#[cfg(test)]
mod delivery_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn signal_init_failure_produces_structured_exit_70_receipt() {
        let err = PlatformError {
            operation: "signal_init",
            message: "injected signal failure".into(),
        };
        let outcome = signal_init_failure_outcome(&err);
        assert_eq!(outcome.status, Status::Error);
        assert_eq!(outcome.exit_code, 70);
        let receipt = outcome.receipt();
        let node = archsig_common::json::parse(receipt.as_bytes()).unwrap();
        let archsig_common::json::JValue::Obj(fields) = &node.value else {
            panic!("receipt must be object");
        };
        assert_eq!(
            fields.iter().find(|(k, _)| k == "status").unwrap().1.value,
            archsig_common::json::JValue::Str("error".into())
        );
        assert_eq!(
            fields
                .iter()
                .find(|(k, _)| k == "exit_code")
                .unwrap()
                .1
                .value,
            archsig_common::json::JValue::Num("70".into())
        );
        let archsig_common::json::JValue::Arr(issues) =
            &fields.iter().find(|(k, _)| k == "issues").unwrap().1.value
        else {
            panic!("issues must be array");
        };
        assert_eq!(issues.len(), 1);
    }

    // 製品へ同期flag/環境変数を追加せず、同じparse/execute/finishをsubprocessで使う。
    #[cfg(unix)]
    #[test]
    #[ignore = "real_signals_cancel_cli_execution_before_artifactsがsubprocessとして起動する"]
    fn signal_cli_child() {
        use std::io::Read;
        let kind = std::env::var("ARCHSIG_TEST_CHILD_KIND").unwrap();
        let mut signals = ProcessSignals::install().unwrap();
        println!("\nARCHSIG_READY");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_exact(&mut [0]).unwrap();
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        while signals.prior_signal_exit_code().is_none() {
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
        if matches!(kind.as_str(), "run" | "reobserve") {
            args.extend(["--ask", "n=evaluate(CountCheck.amount,s=@v/s)"]);
        }
        if kind == "reobserve" {
            args.extend([
                "--before-atom-definition",
                "d.json",
                "--before-law",
                "l.law",
                "--before-archmap",
                "a.json",
                "--before-ask",
                "n=evaluate(CountCheck.amount,s=@v/s)",
            ]);
        }
        let args: Vec<_> = args.into_iter().map(std::ffi::OsString::from).collect();
        let (outcome, version) = execute(&args, &mut signals);
        finish_and_exit_for_test(outcome, version);
    }

    #[cfg(unix)]
    #[test]
    fn real_signals_cancel_cli_execution_before_artifacts() {
        use archsig_common::json::{JNode, JValue, parse};
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
        for kind in ["check", "run", "reobserve"] {
            for (signal, code, name) in
                [(Signal::Int, 130, "SIGINT"), (Signal::Term, 143, "SIGTERM")]
            {
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
                let child = Running(
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
                let (status, timed_out, receipt) = std::thread::scope(|scope| {
                    // Drop the child before scope joins readers on a synchronization failure.
                    let mut child = child;
                    let mut stdout = BufReader::new(child.0.stdout.take().unwrap());
                    let mut stderr = child.0.stderr.take().unwrap();
                    let (ready, received) = std::sync::mpsc::sync_channel(1);
                    let reader = scope.spawn(move || {
                        loop {
                            let mut line = String::new();
                            assert!(stdout.read_line(&mut line).unwrap() > 0, "同期合図前に終了");
                            if line.trim() == "ARCHSIG_READY" {
                                break;
                            }
                        }
                        ready.send(()).unwrap();
                        let mut receipt = String::new();
                        stderr.read_to_string(&mut receipt).unwrap();
                        receipt
                    });
                    received
                        .recv_timeout(std::time::Duration::from_secs(30))
                        .expect("signal child readiness deadline");
                    platform::send_signal(child.0.id(), signal).unwrap();
                    child.0.stdin.take().unwrap().write_all(b"x").unwrap();
                    let (status, timed_out) =
                        test_watchdog::wait(&mut child.0, std::time::Duration::from_secs(30))
                            .unwrap();
                    (status, timed_out, reader.join().unwrap())
                });
                assert!(!timed_out, "signal child did not exit");
                assert_eq!(status.code(), Some(code));
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
                std::fs::remove_dir_all(&dir).unwrap();
            }
        }
    }
}
