//! `check` と `version` の実行(実行仕様 §§1・5–7)。

mod args;
mod output;

pub use args::parse_args;
pub use output::peak_rss_bytes;

use crate::archmap::check_archmap_controlled;
use crate::canonical::{Json, sha256_digest};
use crate::definition::check_definitions_controlled;
use crate::issue::Code;
use crate::law::check_law_controlled;
use crate::observed::control::{CheckFailure, Control, StopReason};
use crate::result::*;
use output::{finalize, out_ok, usage_without_result};
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
    /// この実行が作成した未完成 directory だけを片付ける。
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()>;
}

/// 実行の中で捕捉した signal。finalize の開始時に一度だけ確定する。
pub trait Signals {
    /// 以後の signal を状態へ反映しないようにし、受信済み・pending の signal を確定する。
    fn freeze(&mut self) -> Option<Signal>;
}

#[derive(Debug, PartialEq, Eq)]
pub struct CheckArgs {
    pub atom_definitions: Vec<PathBuf>,
    pub law: PathBuf,
    pub archmap: Option<PathBuf>,
    pub out: PathBuf,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    Check(CheckArgs),
    Version,
}

/// CLI の不正。成果物を生成せず receipt へ返す。
#[derive(Debug, PartialEq, Eq)]
pub struct UsageError {
    pub argument: String,
    pub message: String,
}

/// 実行の結果。stdout の receipt と終了コード、stderr の自然文。
#[derive(Debug)]
pub struct Outcome {
    pub status: Status,
    pub exit_code: u8,
    pub result: Option<PathBuf>,
    pub stderr: Vec<String>,
    pub issues: Vec<ResultIssue>,
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
        if !self.issues.is_empty() {
            let mut issues: Vec<_> = self.issues.iter().collect();
            issues.sort_by_key(|i| i.sort_key());
            entries.push((
                "issues",
                Json::Arr(issues.into_iter().map(ResultIssue::wire).collect()),
            ));
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

pub fn usage_outcome(
    _io: &mut dyn Io,
    signals: &mut dyn Signals,
    err: UsageError,
    _started: Instant,
) -> Outcome {
    let stderr = vec![format!("archsig: {}: {}", err.argument, err.message)];
    usage_without_result(
        signals,
        ResultIssue::Usage {
            message: format!("{}: {}", err.argument, err.message),
            argument: err.argument,
        },
        stderr,
    )
}

/// 内部障害を stdout へ返す。失敗記録ファイルは生成しない。
pub fn internal_outcome(
    _io: &mut dyn Io,
    signals: &mut dyn Signals,
    _args: &CheckArgs,
    _started: Instant,
) -> Outcome {
    output::without_result(
        signals,
        Status::Error,
        vec![ResultIssue::Internal {
            operation: "check".to_owned(),
            message: "検査の途中で内部障害が起きた".to_owned(),
        }],
        vec!["archsig: 検査の途中で内部障害が起きた".to_owned()],
    )
}

/// `check --atom-definition D [--atom-definition D ...] --law L [--archmap A] --out OUT`。
pub fn run_check(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &CheckArgs,
    started: Instant,
    control: &mut Control,
) -> Outcome {
    if args.atom_definitions.is_empty() {
        return usage_outcome(
            io,
            signals,
            UsageError {
                argument: "--atom-definition".to_owned(),
                message: "--atom-definition が一つ以上必要".to_owned(),
            },
            started,
        );
    }
    let mut stderr = Vec::new();
    if let Err(m) = out_ok(&args.out) {
        let issue = ResultIssue::Usage {
            argument: "--out".to_owned(),
            message: format!("{}: {m}", args.out.display()),
        };
        stderr.push(format!("archsig: {}: {m}", args.out.display()));
        return usage_without_result(signals, issue, stderr);
    }
    // 開始時に明示された全入力を読み切る。検査中に再読しない。
    let mut issues = Vec::new();
    let definition_bytes: Vec<_> = args
        .atom_definitions
        .iter()
        .map(|p| read(p, &mut issues))
        .collect();
    let mut definition_ids: Vec<_> = definition_bytes
        .iter()
        .enumerate()
        .map(|(i, b)| InputIdentity {
            id: format!("definition{i}"),
            kind: "atom_definition",
            read: b.is_some(),
            bytes_digest: b.as_ref().map(|b| sha256_digest(b)),
            model_digest: None,
            path: b.as_ref().map(|_| format!("inputs/definitions/{i}.json")),
        })
        .collect();
    let law_bytes = read(&args.law, &mut issues);
    let map_bytes = args.archmap.as_ref().map(|p| read(p, &mut issues));
    let mut law_id = InputIdentity {
        id: "law".to_owned(),
        kind: "law",
        read: law_bytes.is_some(),
        bytes_digest: law_bytes.as_ref().map(|b| sha256_digest(b)),
        model_digest: None,
        path: law_bytes.as_ref().map(|_| "inputs/law.law".to_owned()),
    };
    let mut map_id = map_bytes.as_ref().map(|b| InputIdentity {
        id: "archmap".to_owned(),
        kind: "archmap",
        read: b.is_some(),
        bytes_digest: b.as_ref().map(|b| sha256_digest(b)),
        model_digest: None,
        path: b.as_ref().map(|_| "inputs/archmap.json".to_owned()),
    });
    let mut declarations = Vec::new();
    let mut primitives = Vec::new();
    let mut vocabularies = Vec::new();
    let mut status = Status::Complete;
    if !issues.is_empty() {
        status = Status::Error;
    } else {
        let files: Vec<_> = definition_ids
            .iter()
            .zip(&definition_bytes)
            .map(|(id, bytes)| (id.id.as_str(), bytes.as_deref().expect("読めた定義")))
            .collect();
        let definitions = check_definitions_controlled(&files, control);
        let identities = match &definitions {
            Ok(d) => &d.inputs,
            Err(CheckFailure::Input(f)) => &f.inputs,
            Err(CheckFailure::Stopped(reason)) => return stopped(signals, reason.clone()),
        };
        for (id, checked) in definition_ids.iter_mut().zip(identities) {
            id.model_digest = checked.model_digest.clone();
        }
        match definitions {
            Err(CheckFailure::Stopped(reason)) => return stopped(signals, reason),
            Err(CheckFailure::Input(f)) => {
                status = input_failure_status(f.issue.code);
                issues.push(ResultIssue::Input(f.issue));
            }
            Ok(definitions) => {
                let law_bytes = law_bytes.as_ref().expect("読めた Law");
                match check_law_controlled(law_bytes, &definitions, control) {
                    Err(CheckFailure::Stopped(reason)) => return stopped(signals, reason),
                    Err(CheckFailure::Input(f)) => {
                        law_id.model_digest = f.model_digest.clone();
                        status = input_failure_status(f.issue.code);
                        issues.push(ResultIssue::Input(f.issue));
                    }
                    Ok(law) => {
                        law_id.model_digest = Some(law.model_digest.clone());
                        declarations = law.infos.clone();
                        primitives = definitions.declarations.values().cloned().collect();
                        vocabularies = definitions.vocabularies.values().cloned().collect();
                        if let Some(Some(bytes)) = &map_bytes {
                            match check_archmap_controlled(bytes, &definitions, control) {
                                Err(CheckFailure::Stopped(reason)) => {
                                    return stopped(signals, reason);
                                }
                                Err(CheckFailure::Input(f)) => {
                                    status = input_failure_status(f.issue.code);
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
        }
    }
    let mut inputs = definition_ids;
    inputs.push(law_id);
    inputs.extend(map_id);
    let result = CheckResult {
        status,
        exit_code: 0,
        inputs,
        declarations,
        primitives,
        vocabularies,
        issues,
        elapsed_ms: 0,
        peak_bytes: 0,
    };
    let mut owned_copies = Vec::new();
    for (i, bytes) in definition_bytes.iter().enumerate() {
        if let Some(bytes) = bytes {
            owned_copies.push((format!("inputs/definitions/{i}.json"), bytes.as_slice()));
        }
    }
    if let Some(bytes) = &law_bytes {
        owned_copies.push(("inputs/law.law".to_owned(), bytes.as_slice()));
    }
    if let Some(Some(bytes)) = &map_bytes {
        owned_copies.push(("inputs/archmap.json".to_owned(), bytes.as_slice()));
    }
    let copies: Vec<_> = owned_copies.iter().map(|(p, b)| (p.as_str(), *b)).collect();
    finalize(io, signals, &args.out, result, &copies, started, stderr)
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

fn input_failure_status(code: Code) -> Status {
    match code {
        Code::UnsupportedVersion => Status::Unsupported,
        _ => Status::Invalid,
    }
}

fn stopped(signals: &mut dyn Signals, reason: StopReason) -> Outcome {
    let issue = match reason {
        StopReason::Cancelled(signal) => ResultIssue::Cancelled(signal),
        StopReason::BudgetExhausted {
            resource,
            limit,
            observed,
        } => ResultIssue::BudgetExhausted {
            resource,
            limit,
            observed,
        },
    };
    output::without_result(signals, Status::Interrupted, vec![issue], Vec::new())
}
