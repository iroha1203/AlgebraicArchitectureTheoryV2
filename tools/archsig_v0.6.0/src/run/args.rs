//! check/version の CLI 引数解析(実行仕様 §1)。

use super::{CheckArgs, Command, UsageError};
use std::ffi::OsString;
use std::path::PathBuf;

/// 全コマンドと全 flag(実行仕様 §1)のうち、この版が提供する check と version を読む。
/// 引数は OS の文字列で受け取る。flag は文字列として照合し、path の値は UTF-8 に限らない。
pub fn parse_args(args: &[OsString]) -> Result<Command, UsageError> {
    let usage = |argument: &str, message: &str, out: Option<PathBuf>| UsageError {
        argument: argument.to_owned(),
        message: message.to_owned(),
        out,
    };
    let text = |a: &OsString| a.to_string_lossy().into_owned();
    match args.first().map(|a| a.to_str().unwrap_or("\u{FFFD}")) {
        Some("version") if args.len() == 1 => return Ok(Command::Version),
        Some("version") => {
            return Err(usage(&text(&args[1]), "version は引数を取らない", None));
        }
        Some("check") => {}
        Some(other) => return Err(usage(other, "コマンドは check か version", None)),
        None => return Err(usage("", "コマンドが必要", None)),
    }
    let mut law = None;
    let mut atom_definitions = Vec::new();
    let mut archmap = None;
    let mut out: Option<PathBuf> = None;
    let mut outs = 0;
    let mut first_error: Option<(String, String)> = None;
    let mut i = 1;
    while i < args.len() {
        let flag = text(&args[i]);
        if flag == "--atom-definition" {
            let Some(value) = args.get(i + 1) else {
                first_error.get_or_insert((flag.clone(), "flag に値が必要".to_owned()));
                break;
            };
            atom_definitions.push(PathBuf::from(value));
            i += 2;
            continue;
        }
        if flag == "--out" {
            outs += 1;
        }
        let slot = match flag.as_str() {
            "--law" => Some(&mut law),
            "--archmap" => Some(&mut archmap),
            "--out" => Some(&mut out),
            _ => None,
        };
        let Some(slot) = slot else {
            first_error.get_or_insert((
                flag.clone(),
                "check の flag は --atom-definition・--law・--archmap・--out".to_owned(),
            ));
            i += 1;
            continue;
        };
        let Some(value) = args.get(i + 1) else {
            first_error.get_or_insert((flag.clone(), "flag に値が必要".to_owned()));
            break;
        };
        if slot.is_some() {
            first_error.get_or_insert((flag.clone(), "flag が重複している".to_owned()));
        } else {
            *slot = Some(PathBuf::from(value));
        }
        i += 2;
    }
    let confirmed = if outs == 1 { out.clone() } else { None };
    if let Some((argument, message)) = first_error {
        return Err(usage(&argument, &message, confirmed));
    }
    if atom_definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "--atom-definition が一つ以上必要",
            confirmed,
        ));
    }
    let Some(law) = law else {
        return Err(usage("--law", "--law が必要", confirmed));
    };
    let Some(out) = out else {
        return Err(usage("--out", "--out が必要", None));
    };
    Ok(Command::Check(CheckArgs {
        atom_definitions,
        law,
        archmap,
        out,
    }))
}
