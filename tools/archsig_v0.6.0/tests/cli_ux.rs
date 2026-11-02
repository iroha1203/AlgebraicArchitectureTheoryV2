//! CLI discovery, repeatable validation, stable answers and stream failures.
use crate::common::{cli::*, watchdog};
use archsig_common::json::parse;
use std::process::Stdio;
use std::time::Duration;

fn setup() -> std::path::PathBuf {
    let dir = workdir("ux");
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/counter.atoms.json").as_slice(),
        ),
        ("l.law", include_bytes!("fixtures/counter.law").as_slice()),
        (
            "a.json",
            include_bytes!("fixtures/counter.archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
const RUN: &[&str] = &[
    "run",
    "--atom-definition",
    "d.json",
    "--law",
    "l.law",
    "--archmap",
    "a.json",
    "--ask",
    "n=evaluate(CountCheck.amount,s=@v/s)",
];

#[test]
fn help_and_version_are_discoverable_without_inputs() {
    for args in [
        vec!["--help"],
        vec!["-h"],
        vec!["help"],
        vec!["run", "--help"],
        vec!["help", "run"],
        vec!["check", "--help"],
        vec!["help", "check"],
        vec!["version", "--help"],
        vec!["help", "version"],
    ] {
        let out = watchdog::output(bin().args(&args), Duration::from_secs(10)).unwrap();
        assert!(!out.timed_out);
        assert_eq!(out.output.status.code(), Some(0), "{args:?}");
        assert!(out.output.stderr.is_empty());
        let help = String::from_utf8(out.output.stdout).unwrap();
        assert!(help.contains("Usage: archsig"));
    }
    let out = run_binary(&setup(), &["--version"]);
    assert_eq!(out.code, 0);
    assert_eq!(s(get(&out.receipt, "version")), "0.6.0");
}

#[test]
fn check_without_output_is_repeatable_and_errors_go_to_stderr() {
    let dir = setup();
    let args = &[
        "check",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
    ];
    for _ in 0..2 {
        let r = without_file_changes(&dir, || run_binary(&dir, args));
        assert_eq!(r.code, 0);
        assert_eq!(s(get(&r.receipt, "status")), "complete");
        assert!(!has(&r.receipt, "result"));
        assert!(r.stderr.is_empty());
    }
    std::fs::write(dir.join("l.law"), "invalid").unwrap();
    let r = without_file_changes(&dir, || run_binary(&dir, args));
    notified(&dir, &r, "invalid", 65);
}

#[test]
fn saving_adds_path_without_hiding_answers_or_reuse_warnings() {
    let dir = setup();
    let mut args = RUN.to_vec();
    args.extend(["--reuse", "missing"]);
    let brief = run_binary(&dir, &args);
    args.extend(["--out", "saved"]);
    let saved = run_binary(&dir, &args);
    assert_eq!(brief.code, 0);
    assert_eq!(saved.code, 0);
    assert!(brief.stderr.is_empty() && saved.stderr.is_empty());
    assert_eq!(s(get(&saved.receipt, "format")), "archsig.summary/1");
    assert_eq!(
        get(&brief.receipt, "answers").value,
        get(&saved.receipt, "answers").value
    );
    assert_eq!(
        get(&brief.receipt, "warnings").value,
        get(&saved.receipt, "warnings").value
    );
    assert_eq!(arr(get(&saved.receipt, "warnings")).len(), 1);
    assert_eq!(s(get(&saved.receipt, "result")), "saved/result.json");
    let repeated = without_file_changes(&dir, || run_binary(&dir, &args));
    notified(&dir, &repeated, "invalid", 64);
}

#[test]
fn readonly_stdout_reports_io_failure_without_changing_saved_result() {
    for save in [false, true] {
        let dir = setup();
        let mut command = bin();
        command.current_dir(&dir).args(RUN);
        if save {
            command.args(["--out", "saved"]);
        }
        command.stdout(Stdio::from(
            std::fs::File::open(dir.join("d.json")).unwrap(),
        ));
        let mut child = command.stderr(Stdio::piped()).spawn().unwrap();
        let (status, timed_out) = watchdog::wait(&mut child, Duration::from_secs(10)).unwrap();
        assert!(!timed_out);
        assert_eq!(status.code(), Some(74));
        let mut stderr = Vec::new();
        std::io::Read::read_to_end(&mut child.stderr.take().unwrap(), &mut stderr).unwrap();
        let diagnostic = parse(&stderr).unwrap();
        assert_eq!(s(get(&diagnostic, "status")), "error");
        assert_eq!(s(get(&arr(get(&diagnostic, "issues"))[0], "code")), "io");
        if save {
            let result = parse(&std::fs::read(dir.join("saved/result.json")).unwrap()).unwrap();
            assert_eq!(num(get(&result, "exit_code")), 0);
        }
    }
}

#[test]
fn input_failures_are_machine_readable_on_stderr() {
    let law = include_str!("fixtures/counter.law");
    for (text, code, issue) in [
        ("invalid".to_owned(), 65, "syntax"),
        (
            law.replace("archsig/0.6.0", "archsig/99"),
            69,
            "unsupported_version",
        ),
        (law.replace("Z = s.count", "Bool = s.count"), 65, "type"),
    ] {
        let dir = setup();
        std::fs::write(dir.join("l.law"), text).unwrap();
        let r = without_file_changes(&dir, || run_binary(&dir, RUN));
        let status = if code == 69 { "unsupported" } else { "invalid" };
        let notification = notified(&dir, &r, status, code);
        assert_eq!(s(get(&arr(get(&notification, "issues"))[0], "code")), issue);
    }
}

#[test]
fn broken_stderr_after_stdout_failure_reports_broken_pipe_and_keeps_saved_result() {
    use std::os::fd::OwnedFd;
    use std::os::unix::net::UnixStream;
    for save in [false, true] {
        let dir = setup();
        let (reader, writer) = UnixStream::pair().unwrap();
        drop(reader);
        let mut command = bin();
        command.current_dir(&dir).args(RUN);
        if save {
            command.args(["--out", "saved"]);
        }
        command.stdout(Stdio::from(
            std::fs::File::open(dir.join("d.json")).unwrap(),
        ));
        command.stderr(Stdio::from(OwnedFd::from(writer)));
        let mut child = command.spawn().unwrap();
        let (status, timed_out) = watchdog::wait(&mut child, Duration::from_secs(10)).unwrap();
        assert!(!timed_out);
        assert_eq!(status.code(), Some(141));
        if save {
            let result = parse(&std::fs::read(dir.join("saved/result.json")).unwrap()).unwrap();
            assert_eq!(s(get(&result, "status")), "complete");
            assert_eq!(num(get(&result, "exit_code")), 0);
        }
    }
}
