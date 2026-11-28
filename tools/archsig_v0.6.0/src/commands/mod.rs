//! 発見性サブコマンド（`archsig digest`・`archsig inspect`・`archsig inspect --result`）。

pub mod digest;
pub mod inspect;
pub mod inspect_result;

use crate::cli::{CliCommand, DigestArgs, InspectInputsArgs, InspectResultArgs};
use crate::run::{Outcome, Signals, output};
use archsig_common::canonical::Json;
use archsig_common::control::{Control, Signal};
use archsig_common::limits::read_regular_file_bounded;
use archsig_input::result::{ResultIssue, Status};
use std::path::Path;

/// サブコマンドの実行結果（構造化 JSON と終了コード）。
#[derive(Debug)]
pub struct CommandOutput {
    pub json: Json,
    pub exit_code: u8,
}

/// 発見性サブコマンドを実行する。
pub fn execute_cli_command(
    command: &CliCommand,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<CommandOutput, Outcome> {
    match command {
        CliCommand::Digest(args) => digest::execute(args, max_file_bytes, signals, control),
        CliCommand::InspectInputs(args) => inspect::execute(args, max_file_bytes, signals, control),
        CliCommand::InspectResult(args) => {
            inspect_result::execute(args, max_file_bytes, signals, control)
        }
        _ => Err(output::without_result(
            signals,
            Status::Error,
            vec![ResultIssue::Internal {
                operation: "commands".to_owned(),
                message: "unexpected command passed to commands dispatcher".to_owned(),
            }],
        )),
    }
}

pub(crate) fn read_bounded(
    path: &Path,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
) -> Result<Vec<u8>, Outcome> {
    read_regular_file_bounded(path, max_file_bytes).map_err(|err| {
        output::without_result(
            signals,
            Status::Error,
            vec![ResultIssue::Io {
                operation: "read",
                path: path.to_string_lossy().into_owned(),
                message: format!("cannot read input {}: {err}", path.display()),
            }],
        )
    })
}

pub(crate) fn stopped(signals: &mut dyn Signals, signal: Signal) -> Outcome {
    output::without_result(
        signals,
        Status::Interrupted,
        vec![ResultIssue::Cancelled(signal)],
    )
}

pub(crate) fn input_status(code: archsig_common::issue::Code) -> (Status, u8) {
    if code == archsig_common::issue::Code::UnsupportedVersion {
        (Status::Unsupported, 69)
    } else {
        (Status::Invalid, 65)
    }
}

/// 引数型の再エクスポート用プレースホルダー。
#[allow(dead_code)]
fn _check_exports(_: &DigestArgs, _: &InspectInputsArgs, _: &InspectResultArgs) {}
