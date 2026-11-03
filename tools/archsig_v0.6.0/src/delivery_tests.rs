//! 実ファイルの保存失敗と標準出力・標準エラーへの配送を子プロセスで検査する。
use super::*;
use archsig::run::Io;
use archsig_common::json::{JNode, JValue, parse};
use std::path::Path;
use std::time::Duration;

struct FailingSave(String);
impl Io for FailingSave {
    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        FileIo.create_dir(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        if self.0 == "write" && path.ends_with("result.json") {
            return Err(std::io::ErrorKind::PermissionDenied.into());
        }
        FileIo.write(path, bytes)
    }
    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        FileIo.flush(path)
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        if self.0 == "rename" {
            std::fs::create_dir(to)?;
            std::fs::write(to.join("keep"), "existing output")?;
        }
        FileIo.rename_noreplace(from, to)
    }
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        FileIo.remove_dir_all(path)
    }
}

#[test]
#[ignore = "save_failures_keep_answers_on_stdout が独立プロセスで起動する"]
fn save_child() {
    let mut signals = ProcessSignals::new();
    let args: Vec<_> = [
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--ask",
        "q=check(CountAudit.bounded,s=@v/s)",
        "--out",
        "out",
        "--reuse",
        "absent",
    ]
    .map(std::ffi::OsString::from)
    .into();
    let command = parse_args(&args).unwrap();
    let control = signals.control();
    let outcome = execute_command(
        &command,
        &mut FailingSave(std::env::var("ARCHSIG_TEST_SAVE").unwrap()),
        &mut signals,
        &control,
    );
    finish(outcome, "");
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

#[test]
fn save_failures_keep_answers_on_stdout() {
    for (name, count, code, decision) in [
        ("established", Some("2"), 0, "established"),
        ("refuted", Some("12"), 1, "refuted"),
        ("missing", None, 2, "undetermined"),
    ] {
        let dir = std::env::temp_dir().join(format!("archsig-save-{}-{name}", std::process::id()));
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
        let original = include_str!("../tests/fixtures/counter.archmap.json");
        let map = match count {
            Some(n) => original.replace("\"value\": \"2\"", &format!("\"value\": \"{n}\"")),
            None => original.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", ""),
        };
        std::fs::write(dir.join("a.json"), map).unwrap();
        let mut baseline = None;
        for mode in ["ok", "write", "rename"] {
            let mut child = std::process::Command::new(std::env::current_exe().unwrap());
            child
                .current_dir(&dir)
                .args([
                    "--exact",
                    "delivery_tests::save_child",
                    "--ignored",
                    "--nocapture",
                    "--quiet",
                ])
                .env("ARCHSIG_TEST_SAVE", mode);
            let captured = test_watchdog::output(&mut child, Duration::from_secs(30)).unwrap();
            assert!(!captured.timed_out);
            let output = captured.output;
            assert_eq!(
                output.status.code(),
                Some(if mode == "ok" { code } else { 74 })
            );
            // Rust test harness の行を除き、finish が stdout へ出した JSON を読む。
            let stdout = String::from_utf8(output.stdout).unwrap();
            let lines: Vec<_> = stdout
                .lines()
                .filter(|line| line.starts_with('{'))
                .collect();
            assert_eq!(lines.len(), 1, "{stdout}");
            let summary = parse(lines[0].as_bytes()).unwrap();
            assert_eq!(text(field(&summary, "format")), "archsig.summary/1");
            assert_eq!(
                field(&summary, "exit_code").value,
                JValue::Num(code.to_string())
            );
            let JValue::Arr(answers) = &field(&summary, "answers").value else {
                panic!("answers")
            };
            assert_eq!(text(field(&answers[0], "status")), decision);
            if mode == "ok" {
                assert!(output.stderr.is_empty());
                assert!(dir.join("out/result.json").is_file());
                baseline = Some(summary);
            } else {
                for key in ["answers", "warnings", "status", "exit_code"] {
                    assert_eq!(
                        field(&summary, key).value,
                        field(baseline.as_ref().unwrap(), key).value
                    );
                }
                assert!(!lines[0].contains("\"result\":"));
                let receipt = parse(&output.stderr).unwrap();
                assert_eq!(text(field(&receipt, "status")), "error");
                assert_eq!(field(&receipt, "exit_code").value, JValue::Num("74".into()));
                let JValue::Arr(issues) = &field(&receipt, "issues").value else {
                    panic!("issues")
                };
                assert_eq!(text(field(&issues[0], "code")), "io");
                assert_eq!(text(field(field(&issues[0], "details"), "operation")), mode);
                assert!(!dir.join("out/result.json").exists());
                if mode == "rename" {
                    assert_eq!(
                        std::fs::read_to_string(dir.join("out/keep")).unwrap(),
                        "existing output"
                    );
                }
            }
            assert!(std::fs::read_dir(&dir).unwrap().all(|entry| {
                !entry
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .starts_with(".out.archsig-")
            }));
            if dir.join("out").exists() {
                std::fs::remove_dir_all(dir.join("out")).unwrap();
            }
        }
        std::fs::remove_dir_all(dir).unwrap();
    }
}
