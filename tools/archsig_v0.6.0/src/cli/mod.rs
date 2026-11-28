//! 統一 CLI パーサ・出力整形・ヘルプおよび実行コンテキストオプション（AC3）。

pub mod format;
pub mod help;
pub mod parser;
mod parser_sub;

use crate::platform;
use crate::run::{CheckArgs, Checked, Outcome, ReobserveArgs, RunArgs, UsageError};
use archsig_common::issue::Code;
use archsig_input::result::{ResultIssue, Status};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

/// 標準出力の出力形式。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OutputFormat {
    /// 既定の 1 行 canonical JSON。
    #[default]
    Json,
    /// 字下げ済み canonical JSON。
    Pretty,
    /// 人間可読テキスト。
    Human,
}

impl OutputFormat {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "json" => Some(Self::Json),
            "pretty" => Some(Self::Pretty),
            "human" => Some(Self::Human),
            _ => None,
        }
    }
}

/// 出力の詳細度。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DetailLevel {
    Concise,
    Full,
}

impl DetailLevel {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "concise" => Some(Self::Concise),
            "full" => Some(Self::Full),
            _ => None,
        }
    }
}

/// `--out` の出力ディレクトリ制御オプション。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OutOptions {
    pub create_parents: bool,
    pub overwrite: bool,
    pub no_fsync: bool,
}

/// 全サブコマンド共通の実行オプション。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliOptions {
    pub format: OutputFormat,
    pub detail: Option<DetailLevel>,
    pub out_options: OutOptions,
    pub verbose: bool,
    pub progress: bool,
    pub max_file_bytes: u64,
    pub shigure_limits: Box<archsig_shigure::ShigureLimits>,
}

impl Default for CliOptions {
    fn default() -> Self {
        Self {
            format: OutputFormat::Json,
            detail: None,
            out_options: OutOptions::default(),
            verbose: false,
            progress: false,
            max_file_bytes: archsig_common::limits::DEFAULT_MAX_FILE_BYTES,
            shigure_limits: Box::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvidenceArgs {
    pub archmap: PathBuf,
    pub atoms: Vec<String>,
    pub sources: BTreeMap<String, PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FibersArgs {
    pub table: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigestArgs {
    pub atom_definitions: Vec<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InspectInputsArgs {
    pub atom_definitions: Vec<PathBuf>,
    pub law: Option<PathBuf>,
    pub archmap: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InspectResultArgs {
    pub result_dir: PathBuf,
    pub answers: Vec<String>,
    pub evidence: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum CliCommand {
    Check(Checked<CheckArgs>),
    Run(Checked<RunArgs>),
    Reobserve(ReobserveArgs),
    Evidence(EvidenceArgs),
    LawFibers(FibersArgs),
    Digest(DigestArgs),
    InspectInputs(InspectInputsArgs),
    InspectResult(InspectResultArgs),
    Version,
    Help(&'static str),
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParsedCli {
    pub command: CliCommand,
    pub options: CliOptions,
}

#[derive(Debug)]
pub enum CliError {
    Usage(Box<UsageError>),
    Io(Box<ResultIssue>),
    Input(Box<ResultIssue>),
}

impl CliError {
    pub fn into_outcome(self, signals: &mut dyn crate::run::Signals) -> Outcome {
        match self {
            CliError::Usage(err) => {
                let err = *err;
                let message = if !err.prefix_argument || err.argument.is_empty() {
                    err.message
                } else {
                    format!("{}: {}", err.argument, err.message)
                };
                crate::run::output::usage_without_result(
                    signals,
                    ResultIssue::Usage {
                        argument: err.argument,
                        message,
                    },
                )
            }
            CliError::Io(issue) => {
                crate::run::output::without_result(signals, Status::Error, vec![*issue])
            }
            CliError::Input(issue) => {
                let issue = *issue;
                let status = match &issue {
                    ResultIssue::Input(inner) if inner.code == Code::UnsupportedVersion => {
                        Status::Unsupported
                    }
                    _ => Status::Invalid,
                };
                crate::run::output::without_result(signals, status, vec![issue])
            }
        }
    }
}

pub fn parse_cli(args: &[OsString]) -> Result<ParsedCli, CliError> {
    parser::parse_cli(args)
}

thread_local! {
    static ACTIVE_OUT_OPTIONS: std::cell::Cell<OutOptions> = const {
        std::cell::Cell::new(OutOptions {
            create_parents: false,
            overwrite: false,
            no_fsync: false,
        })
    };
    static ACTIVE_DETAIL_LEVEL: std::cell::Cell<Option<DetailLevel>> =
        const { std::cell::Cell::new(None) };
    static ACTIVE_PROGRESS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

struct CellReset<T: Copy + 'static>(&'static std::thread::LocalKey<std::cell::Cell<T>>, T);

impl<T: Copy + 'static> Drop for CellReset<T> {
    fn drop(&mut self) {
        self.0.with(|cell| cell.set(self.1));
    }
}

pub fn active_out_options() -> OutOptions {
    ACTIVE_OUT_OPTIONS.with(std::cell::Cell::get)
}

pub fn with_out_options<R>(opts: OutOptions, f: impl FnOnce() -> R) -> R {
    let prev = active_out_options();
    ACTIVE_OUT_OPTIONS.with(|cell| cell.set(opts));
    let _guard = CellReset(&ACTIVE_OUT_OPTIONS, prev);
    f()
}

pub fn active_detail_level() -> Option<DetailLevel> {
    ACTIVE_DETAIL_LEVEL.with(std::cell::Cell::get)
}

pub fn with_detail_level<R>(detail: Option<DetailLevel>, f: impl FnOnce() -> R) -> R {
    let prev = active_detail_level();
    ACTIVE_DETAIL_LEVEL.with(|cell| cell.set(detail));
    let _guard = CellReset(&ACTIVE_DETAIL_LEVEL, prev);
    f()
}

pub fn progress_enabled() -> bool {
    ACTIVE_PROGRESS.with(std::cell::Cell::get)
}

pub fn with_progress<R>(enabled: bool, f: impl FnOnce() -> R) -> R {
    let prev = progress_enabled();
    ACTIVE_PROGRESS.with(|cell| cell.set(enabled));
    let _guard = CellReset(&ACTIVE_PROGRESS, prev);
    f()
}

/// `--verbose` または `--progress` が有効な場合にのみ、進捗を stderr へ出力する。
pub fn emit_progress(message: &str) {
    if progress_enabled() {
        let _ = platform::write_stderr_line(&format!("[archsig] {message}"));
    }
}
