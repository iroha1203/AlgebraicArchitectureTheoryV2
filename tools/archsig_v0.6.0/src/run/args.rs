//! check/run/version の CLI 引数解析(実行仕様 §1)。

use super::{CheckArgs, Command, RunArgs, UsageError};
use std::ffi::OsString;

/// 引数検査を通過した値。外部からの構築・変更は許さない。
#[derive(Debug, PartialEq, Eq)]
pub struct Checked<T> {
    inner: T,
    max_file_bytes: u64,
    shigure_limits: Box<archsig_shigure::ShigureLimits>,
}

impl<T> Checked<T> {
    pub(crate) fn from_parts(
        inner: T,
        max_file_bytes: u64,
        shigure_limits: Box<archsig_shigure::ShigureLimits>,
    ) -> Self {
        Self {
            inner,
            max_file_bytes,
            shigure_limits,
        }
    }

    pub fn max_file_bytes(&self) -> u64 {
        self.max_file_bytes
    }

    pub fn shigure_limits(&self) -> &archsig_shigure::ShigureLimits {
        &self.shigure_limits
    }
}

impl<T> std::ops::Deref for Checked<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}

fn validate_output(out: Option<&std::path::Path>) -> Result<(), UsageError> {
    if let Some(out) = out {
        super::output::out_ok(out)
            .map_err(|message| raw_usage("--out", format!("--out {}: {message}", out.display())))?;
    }
    Ok(())
}

pub(super) fn validate_check(args: &CheckArgs) -> Result<(), UsageError> {
    if args.atom_definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    validate_output(args.out.as_deref())
}

pub(super) fn validate_run(args: &RunArgs) -> Result<(), UsageError> {
    validate_output(args.inputs.out.as_deref())?;
    if args.inputs.archmap.is_none() {
        return Err(raw_usage("--archmap", "run requires --archmap"));
    }
    if args.inputs.atom_definitions.is_empty() {
        return Err(raw_usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    if args.asks.is_empty() {
        return Err(raw_usage("--ask", "at least one --ask is required"));
    }
    Ok(())
}

fn usage(argument: &str, message: impl Into<String>) -> UsageError {
    UsageError {
        argument: argument.to_owned(),
        message: message.into(),
        prefix_argument: true,
    }
}

fn raw_usage(argument: &str, message: impl Into<String>) -> UsageError {
    UsageError {
        prefix_argument: false,
        ..usage(argument, message)
    }
}

/// 統一パーサ経由で既存 CLI コマンド形式を解析する。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    crate::cli::parser::parse_legacy_command(args)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(items: &[&str]) -> Vec<OsString> {
        items.iter().map(OsString::from).collect()
    }

    #[test]
    fn parse_rejects_output_before_execution_without_changing_its_message() {
        for command in ["check", "run"] {
            let mut input = words(&[
                command,
                "--atom-definition",
                "d",
                "--law",
                "l",
                "--out",
                ".",
            ]);
            if command == "run" {
                input.extend(words(&["--archmap", "a", "--ask", "q"]));
            }
            let error = parse_args(&input).unwrap_err();
            assert_eq!(error.argument, "--out");
            assert_eq!(
                error.message,
                "--out .: output path must end with a new name"
            );
            assert!(!error.prefix_argument);
        }
    }

    #[test]
    fn parse_keeps_required_argument_priority_and_run_message() {
        let input = words(&["run", "--atom-definition", "d", "--law", "l", "--out", "."]);
        let error = parse_args(&input).unwrap_err();
        assert_eq!(error.argument, "--archmap");
        assert_eq!(error.message, "run requires --archmap");
        assert!(error.prefix_argument);
        let mut input = input;
        input.extend(words(&["--archmap", "a"]));
        assert_eq!(
            parse_args(&input).unwrap_err().message,
            "run requires at least one --ask"
        );
    }
}
