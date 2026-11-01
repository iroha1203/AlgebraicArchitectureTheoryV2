//! check/run/version の CLI 引数解析(実行仕様 §1)。

use super::{CheckArgs, Command, RunArgs, UsageError};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

fn usage(argument: &str, message: impl Into<String>) -> UsageError {
    UsageError {
        argument: argument.to_owned(),
        message: message.into(),
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
            return Err(usage(&flag, format!("unknown flag or positional argument `{flag}`")));
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
        Ok(Command::Run(RunArgs {
            inputs,
            asks,
            reuse: singles.remove("--reuse").map(PathBuf::from),
        }))
    } else {
        Ok(Command::Check(inputs))
    }
}
