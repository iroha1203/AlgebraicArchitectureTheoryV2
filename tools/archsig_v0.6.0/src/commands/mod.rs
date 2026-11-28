//! 発見性サブコマンド（`archsig digest`・`archsig inspect`・`archsig inspect --result`）。

pub mod digest;
pub mod inspect;
pub mod inspect_result;

use crate::cli::CliCommand;
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

/// 発見性サブコマンドを実行する（内部パニック時は構造化 exit 70 receipt へ変換）。
pub fn execute_cli_command(
    command: &CliCommand,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<CommandOutput, Outcome> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match command {
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
    }));
    match result {
        Ok(res) => res,
        Err(_) => Err(output::without_result(
            signals,
            Status::Error,
            vec![ResultIssue::Internal {
                operation: "commands".to_owned(),
                message: "internal failure during discoverability command".to_owned(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::DigestArgs;
    use archsig_input::result::Signal;

    struct NoSignals;
    impl Signals for NoSignals {
        fn freeze(&mut self) -> Option<Signal> {
            None
        }
    }

    #[test]
    fn catch_unwind_returns_structured_exit_70_receipt_on_panic() {
        let def = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/counter.atoms.json");
        let cmd = CliCommand::Digest(DigestArgs {
            atom_definitions: vec![def],
        });
        let control = Control::new(|_| panic!("injected panic in digest"));
        let mut signals = NoSignals;
        let outcome = execute_cli_command(&cmd, 1024 * 1024, &mut signals, &control).unwrap_err();
        assert_eq!(outcome.status, Status::Error);
        assert_eq!(outcome.exit_code, 70);
        assert!(outcome.receipt().contains("\"code\":\"internal\""));
    }
}
