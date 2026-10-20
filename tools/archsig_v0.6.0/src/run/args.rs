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

/// 既知flagの次の語を値として読む。pathはOS文字列、問い・予算はUTF-8で扱う。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    let running = match args.first().and_then(|a| a.to_str()) {
        Some("version") if args.len() == 1 => return Ok(Command::Version),
        Some("version") => {
            return Err(usage(
                &args[1].to_string_lossy(),
                "version は引数を取らない",
            ));
        }
        Some("check") => false,
        Some("run") => true,
        Some(other) => return Err(usage(other, "コマンドは check・run・version")),
        None => return Err(usage("", "コマンドは check・run・version を指定する")),
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
        ) || (running
            && matches!(
                flag.as_ref(),
                "--ask" | "--reuse" | "--time-ms" | "--memory-mib"
            ));
        if !known {
            return Err(usage(&flag, format!("未知のflagまたは位置引数 `{flag}`")));
        }
        let value = args
            .get(index + 1)
            .ok_or_else(|| usage(&flag, "flag に値が必要"))?;
        if flag == "--atom-definition" {
            definitions.push(PathBuf::from(value));
        } else if flag == "--ask" {
            asks.push(
                value
                    .to_str()
                    .ok_or_else(|| usage(&flag, "問いはUTF-8で指定する"))?
                    .to_owned(),
            );
        } else {
            if singles.contains_key(flag.as_ref()) {
                return Err(usage(&flag, "flag が重複している"));
            }
            if matches!(flag.as_ref(), "--time-ms" | "--memory-mib") {
                let text = value
                    .to_str()
                    .ok_or_else(|| usage(&flag, "予算は [1-9][0-9]* の整数"))?;
                if !matches!(text.as_bytes().first(), Some(b'1'..=b'9'))
                    || !text.bytes().all(|b| b.is_ascii_digit())
                {
                    return Err(usage(
                        &flag,
                        format!("予算 `{text}` は [1-9][0-9]* の整数で指定する"),
                    ));
                }
            }
            singles.insert(flag.into_owned(), value.clone());
        }
        index += 2;
    }
    if definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "--atom-definition が一つ以上必要",
        ));
    }
    let law = singles
        .remove("--law")
        .ok_or_else(|| usage("--law", "--law が必要"))?;
    let archmap = singles.remove("--archmap").map(PathBuf::from);
    if running && archmap.is_none() {
        return Err(usage("--archmap", "run は --archmap が必要"));
    }
    if running && asks.is_empty() {
        return Err(usage("--ask", "run は --ask が一つ以上必要"));
    }
    let out = singles
        .remove("--out")
        .ok_or_else(|| usage("--out", "--out が必要"))?;
    let inputs = CheckArgs {
        atom_definitions: definitions,
        law: PathBuf::from(law),
        archmap,
        out: PathBuf::from(out),
    };
    if running {
        Ok(Command::Run(RunArgs {
            inputs,
            asks,
            reuse: singles.remove("--reuse").map(PathBuf::from),
            time_ms: singles
                .remove("--time-ms")
                .map(|s| s.to_string_lossy().into_owned()),
            memory_mib: singles
                .remove("--memory-mib")
                .map(|s| s.to_string_lossy().into_owned()),
        }))
    } else {
        Ok(Command::Check(inputs))
    }
}
