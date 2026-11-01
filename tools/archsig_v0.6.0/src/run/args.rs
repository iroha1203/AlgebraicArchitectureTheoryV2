//! check/run/version の CLI 引数解析(実行仕様 §1)。

use super::{CheckArgs, Command, RunArgs, UsageError};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

/// 引数検査を通過した値。外部からの構築・変更は許さない。
#[derive(Debug, PartialEq, Eq)]
pub struct Checked<T>(T);

impl<T> std::ops::Deref for Checked<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
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
    if args.out.is_none() {
        return Err(raw_usage("--out", "check requires --out"));
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

/// 既知flagの次の語を値として読む。pathはOS文字列、問いはUTF-8で扱う。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    let running = match args.first().and_then(|a| a.to_str()) {
        Some("version") if args.len() == 1 => return Ok(Command::Version),
        Some("version") => {
            return Err(usage(
                &args[1].to_string_lossy(),
                "version takes no arguments",
            ));
        }
        Some("check") => false,
        Some("run") => true,
        Some(other) => return Err(usage(other, "expected command check, run, or version")),
        None => return Err(usage("", "specify command check, run, or version")),
    };
    let mut singles = BTreeMap::new();
    let mut definitions = Vec::new();
    let mut asks = Vec::new();
    let mut index = 1;
    while index < args.len() {
        let flag = args[index].to_string_lossy();
        let known = matches!(
            flag.as_ref(),
            "--atom-definition" | "--law" | "--archmap" | "--out"
        ) || (running && matches!(flag.as_ref(), "--ask" | "--reuse"));
        if !known {
            return Err(usage(
                &flag,
                format!("unknown flag or positional argument `{flag}`"),
            ));
        }
        let value = args
            .get(index + 1)
            .ok_or_else(|| usage(&flag, "flag requires a value"))?;
        if flag == "--atom-definition" {
            definitions.push(PathBuf::from(value));
        } else if flag == "--ask" {
            asks.push(
                value
                    .to_str()
                    .ok_or_else(|| usage(&flag, "request must be UTF-8"))?
                    .to_owned(),
            );
        } else {
            if singles.contains_key(flag.as_ref()) {
                return Err(usage(&flag, "duplicate flag"));
            }
            singles.insert(flag.into_owned(), value.clone());
        }
        index += 2;
    }
    if definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    let law = singles
        .remove("--law")
        .ok_or_else(|| usage("--law", "--law is required"))?;
    let archmap = singles.remove("--archmap").map(PathBuf::from);
    if running && archmap.is_none() {
        return Err(usage("--archmap", "run requires --archmap"));
    }
    if running && asks.is_empty() {
        return Err(usage("--ask", "run requires at least one --ask"));
    }
    let out = singles.remove("--out").map(PathBuf::from);
    if !running && out.is_none() {
        return Err(usage("--out", "check requires --out"));
    }
    let inputs = CheckArgs {
        atom_definitions: definitions,
        law: PathBuf::from(law),
        archmap,
        out,
    };
    if running {
        let args = RunArgs {
            inputs,
            asks,
            reuse: singles.remove("--reuse").map(PathBuf::from),
        };
        validate_run(&args)?;
        Ok(Command::Run(Checked(args)))
    } else {
        validate_check(&inputs)?;
        Ok(Command::Check(Checked(inputs)))
    }
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
