//! `check` と `version` の実行(実行仕様 §§1・5–7)。

use crate::archmap::check_archmap;
use crate::canonical::{Json, sha256_digest};
use crate::law::check_law;
use crate::result::*;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::time::Instant;

pub const VERSION_LINE: &str =
    r#"{"product":"archsig","version":"0.6.0","semantics":["archsig/0.6.0"]}"#;

/// 出力のファイル操作。テストで失敗を差し込めるように分ける。
pub trait Io {
    fn create_dir(&mut self, path: &Path) -> std::io::Result<()>;
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()>;
    /// 書いたファイルまたは directory を永続化する。
    fn flush(&mut self, path: &Path) -> std::io::Result<()>;
    /// 既存の path を置き換えずに rename する。
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()>;
}

/// 実行の中で捕捉した signal。finalize の開始時に一度だけ確定する。
pub trait Signals {
    /// 以後の signal を状態へ反映しないようにし、受信済み・pending の signal を確定する。
    fn freeze(&mut self) -> Option<Signal>;
}

#[derive(Debug, PartialEq, Eq)]
pub struct CheckArgs {
    pub law: PathBuf,
    pub archmap: Option<PathBuf>,
    pub out: PathBuf,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    Check(CheckArgs),
    Version,
}

/// CLI の不正。check の `--out` がちょうど一つ読めた場合は出力先として使う。
#[derive(Debug, PartialEq, Eq)]
pub struct UsageError {
    pub argument: String,
    pub message: String,
    pub out: Option<PathBuf>,
}

/// 全コマンドと全 flag(実行仕様 §1)のうち、この版が提供する check と version を読む。
/// 引数は OS の文字列で受け取る。flag は文字列として照合し、path の値は UTF-8 に限らない。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    let usage = |argument: &str, message: &str, out: Option<PathBuf>| UsageError {
        argument: argument.to_owned(),
        message: message.to_owned(),
        out,
    };
    let text = |a: &OsString| a.to_string_lossy().into_owned();
    match args.first().map(|a| a.to_str().unwrap_or("\u{FFFD}")) {
        Some("version") if args.len() == 1 => return Ok(Command::Version),
        Some("version") => {
            return Err(usage(&text(&args[1]), "version は引数を取らない", None));
        }
        Some("check") => {}
        Some(other) => return Err(usage(other, "コマンドは check か version", None)),
        None => return Err(usage("", "コマンドが必要", None)),
    }
    let mut law = None;
    let mut archmap = None;
    let mut out: Option<PathBuf> = None;
    let mut outs = 0;
    let mut first_error: Option<(String, String)> = None;
    let mut i = 1;
    while i < args.len() {
        let flag = text(&args[i]);
        if flag == "--out" {
            outs += 1;
        }
        let slot = match flag.as_str() {
            "--law" => Some(&mut law),
            "--archmap" => Some(&mut archmap),
            "--out" => Some(&mut out),
            _ => None,
        };
        let Some(slot) = slot else {
            first_error.get_or_insert((
                flag.clone(),
                "check の flag は --law・--archmap・--out".to_owned(),
            ));
            i += 1;
            continue;
        };
        let Some(value) = args.get(i + 1) else {
            first_error.get_or_insert((flag.clone(), "flag に値が必要".to_owned()));
            break;
        };
        if slot.is_some() {
            first_error.get_or_insert((flag.clone(), "flag が重複している".to_owned()));
        } else {
            *slot = Some(PathBuf::from(value));
        }
        i += 2;
    }
    let confirmed = if outs == 1 { out.clone() } else { None };
    if let Some((argument, message)) = first_error {
        return Err(usage(&argument, &message, confirmed));
    }
    let Some(law) = law else {
        return Err(usage("--law", "--law が必要", confirmed));
    };
    let Some(out) = out else {
        return Err(usage("--out", "--out が必要", None));
    };
    Ok(Command::Check(CheckArgs { law, archmap, out }))
}

/// 実行の結果。stdout の receipt と終了コード、stderr の自然文。
#[derive(Debug)]
pub struct Outcome {
    pub status: Status,
    pub exit_code: u8,
    pub result: Option<PathBuf>,
    pub stderr: Vec<String>,
}

impl Outcome {
    pub fn receipt(&self) -> String {
        let mut entries = vec![
            ("format", Json::str("archsig.receipt/1")),
            ("status", Json::str(self.status.wire())),
            ("exit_code", Json::Nat(u64::from(self.exit_code))),
        ];
        if let Some(r) = &self.result {
            entries.push(("result", Json::str(r.to_string_lossy().into_owned())));
        }
        Json::Obj(
            entries
                .into_iter()
                .map(|(k, v)| (k.to_owned(), v))
                .collect(),
        )
        .canonical()
    }
}

/// 入力を読む。symlink は開始時に解決し、通常ファイルだけを読む。
fn read_input(path: &Path) -> std::io::Result<Vec<u8>> {
    if !std::fs::metadata(path)?.is_file() {
        return Err(std::io::Error::other("通常ファイルではない"));
    }
    std::fs::read(path)
}

/// path が(symlink 自体も含めて)存在するか。
fn exists(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

fn is_dir(path: &Path) -> bool {
    std::fs::metadata(path).is_ok_and(|m| m.is_dir())
}

/// 出力先は存在しない path で、親は既存の directory。
fn out_ok(out: &Path) -> Result<(), String> {
    if out.as_os_str().is_empty() {
        return Err("出力先が空".to_owned());
    }
    // `d/.` などは新しい名前を持たない。Path は末尾の `.` を正規化するので、綴りで見る。
    let last = out
        .as_os_str()
        .to_string_lossy()
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .map(str::to_owned);
    if matches!(last.as_deref(), Some("." | "..")) {
        return Err("出力先は新しい名前で終わる".to_owned());
    }
    if exists(out) {
        return Err("出力先が既に存在する".to_owned());
    }
    let parent = match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => PathBuf::from("."),
    };
    if !is_dir(&parent) {
        return Err("出力先の親 directory がない".to_owned());
    }
    Ok(())
}

pub fn usage_outcome(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    err: UsageError,
    started: Instant,
) -> Outcome {
    let issue = ResultIssue::Usage {
        argument: err.argument.clone(),
        message: err.message.clone(),
    };
    let mut stderr = vec![format!("archsig: {}: {}", err.argument, err.message)];
    let Some(out) = err.out else {
        let signal = signals.freeze();
        let status = if signal.is_some() {
            Status::Interrupted
        } else {
            Status::Invalid
        };
        return Outcome {
            status,
            exit_code: exit_code(status, signal, &[issue]),
            result: None,
            stderr,
        };
    };
    if let Err(m) = out_ok(&out) {
        stderr.push(format!("archsig: {}: {m}", out.display()));
        let signal = signals.freeze();
        let status = if signal.is_some() {
            Status::Interrupted
        } else {
            Status::Invalid
        };
        return Outcome {
            status,
            exit_code: exit_code(status, signal, &[issue]),
            result: None,
            stderr,
        };
    }
    let result = CheckResult {
        status: Status::Invalid,
        exit_code: 64,
        inputs: Vec::new(),
        declarations: Vec::new(),
        vocabularies: Vec::new(),
        issues: vec![issue],
        elapsed_ms: 0,
        peak_bytes: 0,
    };
    finalize(io, signals, &out, result, None, None, started, stderr)
}

/// 内部障害。出力先が使えれば error/70 の結果を残す。
pub fn internal_outcome(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &CheckArgs,
    started: Instant,
) -> Outcome {
    let issue = ResultIssue::Internal {
        operation: "check".to_owned(),
        message: "検査の途中で内部障害が起きた".to_owned(),
    };
    let stderr = vec!["archsig: 検査の途中で内部障害が起きた".to_owned()];
    if exists(&args.out) {
        let signal = signals.freeze();
        let status = if signal.is_some() {
            Status::Interrupted
        } else {
            Status::Error
        };
        return Outcome {
            status,
            exit_code: exit_code(status, signal, &[issue]),
            result: None,
            stderr,
        };
    }
    let result = CheckResult {
        status: Status::Error,
        exit_code: 70,
        inputs: Vec::new(),
        declarations: Vec::new(),
        vocabularies: Vec::new(),
        issues: vec![issue],
        elapsed_ms: 0,
        peak_bytes: 0,
    };
    finalize(io, signals, &args.out, result, None, None, started, stderr)
}

/// `check --law L [--archmap A] --out OUT`。
pub fn run_check(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &CheckArgs,
    started: Instant,
) -> Outcome {
    let mut stderr = Vec::new();
    if let Err(m) = out_ok(&args.out) {
        let issue = ResultIssue::Usage {
            argument: "--out".to_owned(),
            message: m.clone(),
        };
        stderr.push(format!("archsig: {}: {m}", args.out.display()));
        let signal = signals.freeze();
        let status = if signal.is_some() {
            Status::Interrupted
        } else {
            Status::Invalid
        };
        return Outcome {
            status,
            exit_code: exit_code(status, signal, &[issue]),
            result: None,
            stderr,
        };
    }
    // 開始時に両入力を読み切る。
    let mut issues = Vec::new();
    let law_bytes = read(&args.law, &mut issues);
    let map_bytes = args.archmap.as_ref().map(|p| read(p, &mut issues));
    let mut law_id = InputIdentity {
        kind: "law",
        read: law_bytes.is_some(),
        bytes_digest: law_bytes.as_ref().map(|b| sha256_digest(b)),
        model_digest: None,
        path: law_bytes.as_ref().map(|_| "inputs/law.law"),
    };
    let mut map_id = map_bytes.as_ref().map(|b| InputIdentity {
        kind: "archmap",
        read: b.is_some(),
        bytes_digest: b.as_ref().map(|b| sha256_digest(b)),
        model_digest: None,
        path: b.as_ref().map(|_| "inputs/archmap.json"),
    });
    let mut declarations = Vec::new();
    let mut vocabularies = Vec::new();
    let mut status = Status::Complete;
    if !issues.is_empty() {
        status = Status::Error;
    } else {
        let law_bytes = law_bytes.as_ref().expect("読めた Law");
        match check_law(law_bytes) {
            Err(f) => {
                law_id.model_digest = f.model_digest.clone();
                status = if f.issue.code == crate::issue::Code::UnsupportedVersion {
                    Status::Unsupported
                } else {
                    Status::Invalid
                };
                issues.push(ResultIssue::Input(f.issue));
            }
            Ok(law) => {
                law_id.model_digest = Some(law.model_digest.clone());
                declarations = law.infos.clone();
                vocabularies = law.vocabularies.clone();
                if let Some(Some(bytes)) = &map_bytes {
                    match check_archmap(bytes, &law) {
                        Err(f) => {
                            status = if f.issue.code == crate::issue::Code::UnsupportedVersion {
                                Status::Unsupported
                            } else {
                                Status::Invalid
                            };
                            issues.push(ResultIssue::Input(f.issue));
                        }
                        Ok(map) => {
                            if let Some(id) = map_id.as_mut() {
                                id.model_digest = Some(map.model_digest.clone());
                            }
                        }
                    }
                }
            }
        }
    }
    let mut inputs = vec![law_id];
    inputs.extend(map_id);
    let result = CheckResult {
        status,
        exit_code: 0,
        inputs,
        declarations,
        vocabularies,
        issues,
        elapsed_ms: 0,
        peak_bytes: 0,
    };
    finalize(
        io,
        signals,
        &args.out,
        result,
        law_bytes.as_deref(),
        map_bytes.flatten().as_deref(),
        started,
        stderr,
    )
}

fn read(path: &Path, issues: &mut Vec<ResultIssue>) -> Option<Vec<u8>> {
    match read_input(path) {
        Ok(b) => Some(b),
        Err(e) => {
            issues.push(ResultIssue::Io {
                operation: "read",
                path: path.to_string_lossy().into_owned(),
                message: format!("入力を読めない: {e}"),
            });
            None
        }
    }
}

/// finalize: signal を確定してから結果を一時 directory に書き、置き換えない rename で公開する。
#[allow(clippy::too_many_arguments)]
fn finalize(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    out: &Path,
    mut result: CheckResult,
    law: Option<&[u8]>,
    archmap: Option<&[u8]>,
    started: Instant,
    mut stderr: Vec<String>,
) -> Outcome {
    if let Some(signal) = signals.freeze() {
        result.status = Status::Interrupted;
        result.issues.push(ResultIssue::Cancelled(signal));
        result.exit_code = exit_code(Status::Interrupted, Some(signal), &result.issues);
    } else {
        result.exit_code = exit_code(result.status, None, &result.issues);
    }
    result.elapsed_ms = started.elapsed().as_millis();
    result.peak_bytes = peak_rss_bytes();
    let tmp = temp_dir(out);
    let written = (|| -> Result<(), (&'static str, PathBuf, std::io::Error)> {
        let step = |op: &'static str, p: &Path, r: std::io::Result<()>| {
            r.map_err(|e| (op, p.to_path_buf(), e))
        };
        step("create", &tmp, io.create_dir(&tmp))?;
        let inputs = tmp.join("inputs");
        step("create", &inputs, io.create_dir(&inputs))?;
        for (name, bytes) in [("law.law", law), ("archmap.json", archmap)] {
            if let Some(bytes) = bytes {
                let p = inputs.join(name);
                step("write", &p, io.write(&p, bytes))?;
                step("flush", &p, io.flush(&p))?;
            }
        }
        let p = tmp.join("result.json");
        step(
            "write",
            &p,
            io.write(&p, result.wire().canonical().as_bytes()),
        )?;
        step("flush", &p, io.flush(&p))?;
        step("flush", &inputs, io.flush(&inputs))?;
        step("flush", &tmp, io.flush(&tmp))?;
        step("rename", out, io.rename_noreplace(&tmp, out))?;
        Ok(())
    })();
    match written {
        Ok(()) => Outcome {
            status: result.status,
            exit_code: result.exit_code,
            result: Some(out.join("result.json")),
            stderr,
        },
        Err((op, path, e)) => {
            stderr.push(format!(
                "archsig: 出力の{op}に失敗した({}): {e}。出力先は変更していない。一時 directory: {}",
                path.display(),
                tmp.display()
            ));
            Outcome {
                status: Status::Error,
                exit_code: 74,
                result: None,
                stderr,
            }
        }
    }
}

fn temp_dir(out: &Path) -> PathBuf {
    let name = out
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_owned());
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let tmp = format!(".{name}.archsig-{}-{nanos}", std::process::id());
    match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.join(tmp),
        _ => PathBuf::from(tmp),
    }
}

/// process の peak RSS(byte)。
pub fn peak_rss_bytes() -> u64 {
    use nix::sys::resource::{UsageWho, getrusage};
    let Ok(usage) = getrusage(UsageWho::RUSAGE_SELF) else {
        return 0;
    };
    let max = usage.max_rss().max(0) as u64;
    if cfg!(target_os = "macos") {
        max
    } else {
        max * 1024
    }
}
