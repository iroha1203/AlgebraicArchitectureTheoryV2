//! CLI の入力検査・要求評価・成果物配送(実行仕様 §§1・5–7)。

mod args;
pub(crate) mod diagnostics;
mod evaluate;
pub(crate) mod output;
mod reobserve;
mod reuse;
mod shigure;
pub use evaluate::{run_internal_outcome, run_requests};

pub use crate::cli::help::{CHECK_HELP, HELP, REOBSERVE_HELP, RUN_HELP};
pub use args::{Checked, parse_args};

use archsig_common::canonical::{Json, sha256_digest};
use archsig_common::control::{CheckFailure, Control};
use archsig_common::diagnostic::{DEFAULT_MAX_COLLECTED_ERRORS, SourceSnippet};
use archsig_common::issue::Code;
use archsig_input::archmap::check_archmap_batch_controlled;
use archsig_input::definition::check_definitions_batch_controlled;
use archsig_input::law::check_law_batch_controlled;
use archsig_input::result::*;
use output::{finalize, usage_without_result};
use std::path::{Path, PathBuf};

pub const VERSION_LINE: &str =
    r#"{"product":"archsig","version":"0.6.0","semantics":["archsig/0.6.0"]}"#;

/// 出力のファイル操作。テストで失敗を差し込めるように分ける。
pub trait Io {
    fn create_dir(&mut self, path: &Path) -> std::io::Result<()>;
    fn create_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::create_dir_all(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()>;
    /// 確定済みJSONの配送。既定実装は従来のwrite失敗注入を保つ。
    /// FileIoは全文Stringを作らずstreamする。独自Ioの既定実装はStringを保持する。
    fn write_json(&mut self, path: &Path, document: &Json) -> std::io::Result<()> {
        self.write(path, document.canonical().as_bytes())
    }
    /// 書いたファイルまたは directory を永続化する。
    fn flush(&mut self, path: &Path) -> std::io::Result<()>;
    /// 既存の path を置き換えずに rename する。
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()>;
    /// この実行が作成した未完成 directory だけを片付ける。
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()>;
}

/// 実ファイルの操作。
pub struct FileIo;

impl Io for FileIo {
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(path)
    }

    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::create_dir(path)
    }

    fn create_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::create_dir_all(path)
    }

    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        use std::io::Write;
        std::fs::File::create_new(path)?.write_all(bytes)
    }

    fn write_json(&mut self, path: &Path, document: &Json) -> std::io::Result<()> {
        write_json_to(std::fs::File::create_new(path)?, document)
    }

    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::File::open(path)?.sync_all()
    }

    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        crate::platform::rename_noreplace(from, to)
    }
}

// 小さなbufferの書出失敗も配送失敗として返し、Dropの暗黙flushへ任せない。
fn write_json_to(writer: impl std::io::Write, document: &Json) -> std::io::Result<()> {
    use std::io::Write;
    let mut writer = std::io::BufWriter::with_capacity(8 * 1024, writer);
    document.write_canonical(&mut writer)?;
    writer.flush()
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
    pub out: Option<PathBuf>,
}

/// 実行要求。
#[derive(Debug, PartialEq, Eq)]
pub struct RunArgs {
    pub inputs: CheckArgs,
    pub asks: Vec<String>,
    pub reuse: Option<PathBuf>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ReobserveArgs {
    previous: Checked<RunArgs>,
    current: Checked<RunArgs>,
    alignment: Option<PathBuf>,
}

impl ReobserveArgs {
    pub(crate) fn from_parts(
        previous: Checked<RunArgs>,
        current: Checked<RunArgs>,
        alignment: Option<PathBuf>,
    ) -> Self {
        Self {
            previous,
            current,
            alignment,
        }
    }

    pub fn max_file_bytes(&self) -> u64 {
        self.current.max_file_bytes()
    }

    pub fn shigure_limits(&self) -> &archsig_shigure::ShigureLimits {
        self.current.shigure_limits()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    Check(Checked<CheckArgs>),
    Run(Checked<RunArgs>),
    Reobserve(ReobserveArgs),
    Version,
    Help(&'static str),
}

/// CLI の不正。成果物を生成せず receipt へ返す。
#[derive(Debug, PartialEq, Eq)]
pub struct UsageError {
    pub argument: String,
    pub message: String,
    pub(super) prefix_argument: bool,
}

/// 実行の結果。CLI通知と計算の終了コード。
#[derive(Debug)]
pub struct Outcome {
    pub status: Status,
    pub exit_code: u8,
    pub result: Option<PathBuf>,
    pub issues: Vec<Json>,
    pub summary: Option<Json>,
    pub snippets: Vec<Option<SourceSnippet>>,
}

impl Outcome {
    pub fn receipt(&self) -> String {
        if let Some(summary) = &self.summary {
            let mut summary = summary.clone();
            if let (Some(result), Json::Obj(fields)) = (&self.result, &mut summary) {
                fields.insert("result".into(), Json::str(result.to_string_lossy()));
            }
            return summary.canonical();
        }
        let mut entries = vec![
            ("format", Json::str("archsig.receipt/1")),
            ("status", Json::str(self.status.wire())),
            ("exit_code", Json::Nat(u64::from(self.exit_code))),
        ];
        if let Some(r) = &self.result {
            entries.push(("result", Json::str(r.to_string_lossy().into_owned())));
        }
        if !self.issues.is_empty() {
            entries.push(("issues", Json::Arr(self.issues.clone())));
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

thread_local! {
    static ACTIVE_MAX_FILE_BYTES: std::cell::Cell<u64> =
        const { std::cell::Cell::new(archsig_common::limits::DEFAULT_MAX_FILE_BYTES) };
}

struct MaxFileBytesGuard(u64);

impl Drop for MaxFileBytesGuard {
    fn drop(&mut self) {
        ACTIVE_MAX_FILE_BYTES.with(|cell| cell.set(self.0));
    }
}

pub fn active_max_file_bytes() -> u64 {
    ACTIVE_MAX_FILE_BYTES.with(std::cell::Cell::get)
}

pub fn with_max_file_bytes<T>(max_bytes: u64, f: impl FnOnce() -> T) -> T {
    let prev = active_max_file_bytes();
    ACTIVE_MAX_FILE_BYTES.with(|cell| cell.set(max_bytes));
    let _guard = MaxFileBytesGuard(prev);
    f()
}

/// 入力を読む。symlink は開始時に解決し、通常ファイルかつ上限サイズ内だけを読む。
fn read_input_bounded(path: &Path, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    archsig_common::limits::read_regular_file_bounded(path, max_bytes)
}

pub fn usage_outcome(_io: &mut dyn Io, signals: &mut dyn Signals, err: UsageError) -> Outcome {
    usage_without_result(
        signals,
        ResultIssue::Usage {
            message: if !err.prefix_argument || err.argument.is_empty() {
                err.message
            } else {
                format!("{}: {}", err.argument, err.message)
            },
            argument: err.argument,
        },
    )
}

/// 内部障害の通知を返す。失敗記録ファイルは生成しない。
pub fn internal_outcome(_io: &mut dyn Io, signals: &mut dyn Signals, _args: &CheckArgs) -> Outcome {
    output::without_result(
        signals,
        Status::Error,
        vec![ResultIssue::Internal {
            operation: "check".to_owned(),
            message: "internal failure during input validation".to_owned(),
        }],
    )
}

/// `check --atom-definition D [--atom-definition D ...] --law L [--archmap A] --out OUT`。
pub fn run_check(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &CheckArgs,
    control: &Control,
) -> Outcome {
    if let Err(error) = args::validate_check(args) {
        return usage_outcome(io, signals, error);
    }
    run_check_validated(io, signals, args, control)
}

fn run_check_validated(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &CheckArgs,
    control: &Control,
) -> Outcome {
    crate::cli::emit_progress("check: reading input files");
    let out = args.out.as_deref();
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
        let definitions =
            check_definitions_batch_controlled(&files, control, DEFAULT_MAX_COLLECTED_ERRORS);
        let identities = match &definitions {
            Ok(d) => d.inputs(),
            Err(CheckFailure::Input(f)) => &f.inputs,
            Err(CheckFailure::Stopped(reason)) => return stopped(signals, *reason),
        };
        for (id, checked) in definition_ids.iter_mut().zip(identities) {
            id.model_digest = checked.model_digest.clone();
        }
        match definitions {
            Err(CheckFailure::Stopped(reason)) => return stopped(signals, reason),
            Err(CheckFailure::Input(f)) => {
                status = if f
                    .issues
                    .iter()
                    .any(|issue| issue.code == Code::UnsupportedVersion)
                {
                    Status::Unsupported
                } else {
                    Status::Invalid
                };
                for issue in f.issues {
                    issues.push(ResultIssue::Input(issue));
                }
            }
            Ok(definitions) => {
                let law_bytes = law_bytes.as_ref().expect("読めた Law");
                match check_law_batch_controlled(
                    law_bytes,
                    &definitions,
                    control,
                    DEFAULT_MAX_COLLECTED_ERRORS,
                ) {
                    Err(CheckFailure::Stopped(reason)) => return stopped(signals, reason),
                    Err(CheckFailure::Input(f)) => {
                        law_id.model_digest = f.model_digest.clone();
                        for issue in f.issues {
                            issues.push(ResultIssue::Input(issue));
                        }
                        status = if issues.iter().any(|item| {
                            matches!(
                                item,
                                ResultIssue::Input(i) if i.code == Code::UnsupportedVersion
                            )
                        }) {
                            Status::Unsupported
                        } else {
                            Status::Invalid
                        };
                    }
                    Ok(law) => {
                        law_id.model_digest = Some(law.model_digest().to_owned());
                        declarations = law.infos().to_vec();
                        primitives = definitions.declarations().values().cloned().collect();
                        vocabularies = definitions.vocabularies().values().cloned().collect();
                        if let Some(Some(bytes)) = &map_bytes {
                            match check_archmap_batch_controlled(
                                bytes,
                                &definitions,
                                control,
                                DEFAULT_MAX_COLLECTED_ERRORS,
                            ) {
                                Err(CheckFailure::Stopped(reason)) => {
                                    return stopped(signals, reason);
                                }
                                Err(CheckFailure::Input(f)) => {
                                    status = if f
                                        .issues
                                        .iter()
                                        .any(|issue| issue.code == Code::UnsupportedVersion)
                                    {
                                        Status::Unsupported
                                    } else {
                                        Status::Invalid
                                    };
                                    for issue in f.issues {
                                        issues.push(ResultIssue::Input(issue));
                                    }
                                }
                                Ok(map) => {
                                    if let Some(id) = map_id.as_mut() {
                                        id.model_digest = Some(map.model_digest().to_owned());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if issues.len() > DEFAULT_MAX_COLLECTED_ERRORS {
        issues.sort_by_key(ResultIssue::sort_key);
        issues.truncate(DEFAULT_MAX_COLLECTED_ERRORS);
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
    let mut outcome = finalize(io, signals, out, result, &copies);
    if !outcome.issues.is_empty() {
        let def_slices: Vec<&[u8]> = definition_bytes
            .iter()
            .flatten()
            .map(Vec::as_slice)
            .collect();
        let map_slice = map_bytes.as_ref().and_then(|o| o.as_deref());
        let ctx = diagnostics::DiagnosticContext::from_raw_inputs(
            &def_slices,
            law_bytes.as_deref(),
            map_slice,
        );
        diagnostics::enrich_issues(&mut outcome.issues, &ctx);
    }
    outcome
}

fn read(path: &Path, issues: &mut Vec<ResultIssue>) -> Option<Vec<u8>> {
    match read_input_bounded(path, active_max_file_bytes()) {
        Ok(b) => Some(b),
        Err(e) => {
            issues.push(ResultIssue::Io {
                operation: "read",
                path: path.to_string_lossy().into_owned(),
                message: format!("cannot read input {}: {e}", path.display()),
            });
            None
        }
    }
}

fn stopped(signals: &mut dyn Signals, signal: Signal) -> Outcome {
    output::without_result(
        signals,
        Status::Interrupted,
        vec![ResultIssue::Cancelled(signal)],
    )
}

/// 検査済みコマンドを実行し、内部障害をコマンド固有のreceiptへ変換する。
/// Version は成果物を作らず None を返す。
pub fn execute_command(
    command: &Command,
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    control: &Control,
) -> Option<Outcome> {
    if matches!(command, Command::Version | Command::Help(_)) {
        return None;
    }
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match command {
        Command::Check(args) => with_max_file_bytes(args.max_file_bytes(), || {
            run_check_validated(io, signals, args, control)
        }),
        Command::Run(args) => with_max_file_bytes(args.max_file_bytes(), || {
            archsig_shigure::limits::with_active_limits(args.shigure_limits(), || {
                evaluate::run_requests_validated(io, signals, args, control)
            })
        }),
        Command::Reobserve(args) => with_max_file_bytes(args.max_file_bytes(), || {
            archsig_shigure::limits::with_active_limits(args.shigure_limits(), || {
                reobserve::execute(io, signals, args, control)
            })
        }),
        Command::Version | Command::Help(_) => unreachable!("versionは実行前に返す"),
    }));
    Some(outcome.unwrap_or_else(|payload| {
        let (operation, message) = match command {
            Command::Check(_) => ("check", "internal failure during input validation"),
            Command::Run(_) => ("run", "internal failure during computation"),
            Command::Reobserve(_) => ("reobserve", "internal failure during computation"),
            Command::Version | Command::Help(_) => unreachable!("versionは実行前に返す"),
        };
        output::without_result(
            signals,
            Status::Error,
            vec![diagnostics::panic_internal_issue(
                operation, message, payload,
            )],
        )
    }))
}

#[cfg(test)]
mod command_tests {
    use super::*;
    use std::ffi::OsString;

    struct NoSignals(usize);
    impl Signals for NoSignals {
        fn freeze(&mut self) -> Option<Signal> {
            self.0 += 1;
            None
        }
    }

    #[test]
    fn shared_execution_catches_panics_with_command_specific_receipts() {
        archsig_common::diagnostic::install_panic_hook();
        archsig_common::diagnostic::clear_last_panic();
        let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
        for kind in ["check", "run"] {
            let out =
                std::env::temp_dir().join(format!("archsig-6092-{}-{kind}", std::process::id()));
            let mut args: Vec<OsString> = vec![
                kind.into(),
                "--atom-definition".into(),
                fixtures.join("counter.atoms.json").into(),
                "--law".into(),
                fixtures.join("counter.law").into(),
                "--archmap".into(),
                fixtures.join("counter.archmap.json").into(),
                "--out".into(),
                out.clone().into(),
            ];
            if kind == "run" {
                args.extend([
                    "--ask".into(),
                    "n=evaluate(CountCheck.amount,s=@v/s)".into(),
                ]);
            }
            let command = parse_args(&args).unwrap();
            let mut signals = NoSignals(0);
            let control = Control::new(|_| panic!("injected computation failure"));
            let outcome = execute_command(&command, &mut FileIo, &mut signals, &control).unwrap();
            assert_eq!(outcome.status, Status::Error);
            assert_eq!(outcome.exit_code, 70);
            let expected = if kind == "check" {
                "internal failure during input validation"
            } else {
                "internal failure during computation"
            };
            assert_eq!(outcome.issues.len(), 1);
            let receipt = outcome.receipt();
            assert!(receipt.contains("\"code\":\"internal\""), "{receipt}");
            assert!(receipt.contains(expected), "{receipt}");
            assert!(
                receipt.contains("\"panic_message\":\"injected computation failure\""),
                "{receipt}"
            );
            assert!(receipt.contains("\"panic_location\":\""), "{receipt}");
            assert!(
                !receipt.contains("\"panic_location\":\"unknown\""),
                "{receipt}"
            );
            assert_eq!(signals.0, 1);
            assert!(outcome.result.is_none());
            assert!(!out.exists());
        }
    }
}

#[cfg(test)]
mod owner_delivery_tests;
