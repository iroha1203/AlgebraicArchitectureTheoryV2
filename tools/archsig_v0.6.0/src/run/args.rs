//! check/run/version の CLI 引数解析(実行仕様 §1)。

use super::{CheckArgs, Command, ReobserveArgs, RunArgs, UsageError};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

/// 引数検査を通過した値。外部からの構築・変更は許さない。
#[derive(Debug, PartialEq, Eq)]
pub struct Checked<T> {
    inner: T,
    max_file_bytes: u64,
    shigure_limits: Box<archsig_shigure::ShigureLimits>,
}

impl<T> Checked<T> {
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

/// 既知flagの次の語を値として読む。pathはOS文字列、問いはUTF-8で扱う。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    let words: Vec<_> = args.iter().map(|a| a.to_str()).collect();
    match words.as_slice() {
        [Some("--help" | "-h" | "help")] => return Ok(Command::Help(super::HELP)),
        [Some("run"), Some("--help" | "-h")] | [Some("help"), Some("run")] => {
            return Ok(Command::Help(super::RUN_HELP));
        }
        [Some("reobserve"), Some("--help" | "-h")] | [Some("help"), Some("reobserve")] => {
            return Ok(Command::Help(super::REOBSERVE_HELP));
        }
        [Some("check"), Some("--help" | "-h")] | [Some("help"), Some("check")] => {
            return Ok(Command::Help(super::CHECK_HELP));
        }
        [Some("version"), Some("--help" | "-h")] | [Some("help"), Some("version")] => {
            return Ok(Command::Help(
                "Usage: archsig version (or archsig --version)\nPrint product and semantics versions as JSON.",
            ));
        }
        _ => {}
    }
    let running = match args.first().and_then(|a| a.to_str()) {
        Some("version" | "--version") if args.len() == 1 => return Ok(Command::Version),
        Some("version") => {
            return Err(usage(
                &args[1].to_string_lossy(),
                "version takes no arguments",
            ));
        }
        Some("check") => false,
        Some("run") => true,
        Some("reobserve") => return reobserve_args(&args[1..]),
        Some(other) => {
            return Err(usage(
                other,
                "expected command check, run, reobserve, evidence, law-fibers, or version",
            ));
        }
        None => {
            return Err(usage(
                "",
                "specify command check, run, reobserve, evidence, law-fibers, or version",
            ));
        }
    };
    let mut singles = BTreeMap::new();
    let mut definitions = Vec::new();
    let mut asks = Vec::new();
    let mut max_file_bytes = archsig_common::limits::DEFAULT_MAX_FILE_BYTES;
    let mut saw_max_file_bytes = false;
    let mut shigure_limits = archsig_shigure::ShigureLimits::default();
    let mut index = 1;
    while index < args.len() {
        let flag = args[index].to_string_lossy();
        let known = matches!(
            flag.as_ref(),
            "--atom-definition" | "--law" | "--archmap" | "--out" | "--max-file-bytes"
        ) || (running
            && matches!(flag.as_ref(), "--ask" | "--reuse" | "--shigure-limit"));
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
        } else if flag == "--max-file-bytes" {
            if saw_max_file_bytes {
                return Err(usage(&flag, "duplicate flag"));
            }
            let text = value
                .to_str()
                .ok_or_else(|| usage(&flag, "byte limit must be UTF-8"))?;
            let parsed = text
                .parse::<u64>()
                .ok()
                .filter(|&n| n > 0)
                .ok_or_else(|| usage(&flag, "byte limit must be a positive integer"))?;
            max_file_bytes = parsed;
            saw_max_file_bytes = true;
        } else if flag == "--shigure-limit" {
            let text = value
                .to_str()
                .ok_or_else(|| usage(&flag, "shigure limit must be UTF-8"))?;
            let (name, raw_val) = text
                .split_once('=')
                .ok_or_else(|| usage(&flag, "expected LIMIT_NAME=POSITIVE_INT"))?;
            let val = raw_val
                .parse::<u64>()
                .map_err(|_| usage(&flag, format!("invalid integer for `{name}`: `{raw_val}`")))?;
            shigure_limits
                .set(name, val)
                .map_err(|msg| usage(&flag, msg))?;
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
        Ok(Command::Run(Checked {
            inner: args,
            max_file_bytes,
            shigure_limits: Box::new(shigure_limits),
        }))
    } else {
        validate_check(&inputs)?;
        Ok(Command::Check(Checked {
            inner: inputs,
            max_file_bytes,
            shigure_limits: Box::new(shigure_limits),
        }))
    }
}

fn reobserve_args(args: &[OsString]) -> Result<Command, UsageError> {
    let mut previous = vec![OsString::from("run")];
    let mut current = vec![OsString::from("run")];
    let mut alignment = None;
    let mut saw_max_file_bytes = false;
    let mut pairs = args.chunks_exact(2);
    for pair in &mut pairs {
        let flag = pair[0].to_string_lossy();
        let value = &pair[1];
        if flag == "--alignment" {
            if alignment.replace(PathBuf::from(value)).is_some() {
                return Err(usage(&flag, "duplicate flag"));
            }
            continue;
        }
        if flag == "--max-file-bytes" {
            if saw_max_file_bytes {
                return Err(usage(&flag, "duplicate flag"));
            }
            saw_max_file_bytes = true;
            previous.extend([OsString::from("--max-file-bytes"), value.clone()]);
            current.extend([OsString::from("--max-file-bytes"), value.clone()]);
            continue;
        }
        let (destination, option) = if let Some(option) = flag.strip_prefix("--before-") {
            let option = match option {
                "atom-definition" => "--atom-definition",
                "law" => "--law",
                "archmap" => "--archmap",
                "ask" => "--ask",
                _ => return Err(usage(&flag, "unknown reobservation flag")),
            };
            (&mut previous, option)
        } else {
            if !matches!(
                flag.as_ref(),
                "--atom-definition" | "--law" | "--archmap" | "--ask" | "--out" | "--shigure-limit"
            ) {
                return Err(usage(&flag, "unknown reobservation flag"));
            }
            (&mut current, flag.as_ref())
        };
        destination.extend([OsString::from(option), value.clone()]);
    }
    if let [flag] = pairs.remainder() {
        return Err(usage(&flag.to_string_lossy(), "flag requires a value"));
    }
    let Command::Run(previous) = parse_args(&previous).map_err(|error| {
        usage(
            &format!("--before-{}", error.argument.trim_start_matches("--")),
            error.message,
        )
    })?
    else {
        unreachable!("previous arguments use the run parser")
    };
    let Command::Run(current) = parse_args(&current)? else {
        unreachable!("current arguments use the run parser")
    };
    Ok(Command::Reobserve(ReobserveArgs {
        previous,
        current,
        alignment,
    }))
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
