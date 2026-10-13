//! 出力先の検査と、状態の確定・入力コピー・result.json の公開(実行仕様 §§5–7)。

use super::{Io, Outcome, Signals};
use crate::result::{CheckResult, ResultIssue, Status, exit_code};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// path が(symlink 自体も含めて)存在するか。
fn exists(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

fn is_dir(path: &Path) -> bool {
    std::fs::metadata(path).is_ok_and(|m| m.is_dir())
}

/// 出力先は存在しない path で、親は既存の directory。
pub(super) fn out_ok(out: &Path) -> Result<(), String> {
    if out.as_os_str().is_empty() {
        return Err("出力先が空".to_owned());
    }
    // `d/.` などは新しい名前を持たない。Path は末尾の `.` を正規化するので、綴りで見る。
    let last = out
        .as_os_str()
        .to_string_lossy()
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .map(str::to_owned);
    if matches!(last.as_deref(), Some("." | "..")) {
        return Err("出力先は新しい名前で終わる".to_owned());
    }
    if exists(out) {
        return Err("出力先が既に存在する".to_owned());
    }
    let parent = match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => PathBuf::from("."),
    };
    if !is_dir(&parent) {
        return Err("出力先の親 directory がない".to_owned());
    }
    Ok(())
}

/// 出力先のない usage を、捕捉済み signal とともに一度だけ確定する。
pub(super) fn usage_without_result(
    signals: &mut dyn Signals,
    issue: ResultIssue,
    stderr: Vec<String>,
) -> Outcome {
    let signal = signals.freeze();
    let status = if signal.is_some() {
        Status::Interrupted
    } else {
        Status::Invalid
    };
    Outcome {
        status,
        exit_code: exit_code(status, signal, &[issue]),
        result: None,
        stderr,
    }
}

/// finalize: signal を確定してから結果を一時 directory に書き、置き換えない rename で公開する。
#[allow(clippy::too_many_arguments)]
pub(super) fn finalize(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    out: &Path,
    mut result: CheckResult,
    copies: &[(&str, &[u8])],
    started: Instant,
    mut stderr: Vec<String>,
) -> Outcome {
    if let Some(signal) = signals.freeze() {
        result.status = Status::Interrupted;
        result.issues.push(ResultIssue::Cancelled(signal));
        result.exit_code = exit_code(Status::Interrupted, Some(signal), &result.issues);
    } else {
        result.exit_code = exit_code(result.status, None, &result.issues);
    }
    result.elapsed_ms = started.elapsed().as_millis();
    result.peak_bytes = peak_rss_bytes();
    let tmp = temp_dir(out);
    let written = (|| -> Result<(), (&'static str, PathBuf, std::io::Error)> {
        let step = |op: &'static str, p: &Path, r: std::io::Result<()>| {
            r.map_err(|e| (op, p.to_path_buf(), e))
        };
        step("create", &tmp, io.create_dir(&tmp))?;
        let inputs = tmp.join("inputs");
        step("create", &inputs, io.create_dir(&inputs))?;
        let definitions = inputs.join("definitions");
        if copies
            .iter()
            .any(|(p, _)| p.starts_with("inputs/definitions/"))
        {
            step("create", &definitions, io.create_dir(&definitions))?;
        }
        for (name, bytes) in copies {
            let p = tmp.join(name);
            step("write", &p, io.write(&p, bytes))?;
            step("flush", &p, io.flush(&p))?;
        }
        if copies
            .iter()
            .any(|(p, _)| p.starts_with("inputs/definitions/"))
        {
            step("flush", &definitions, io.flush(&definitions))?;
        }
        let p = tmp.join("result.json");
        step(
            "write",
            &p,
            io.write(&p, result.wire().canonical().as_bytes()),
        )?;
        step("flush", &p, io.flush(&p))?;
        step("flush", &inputs, io.flush(&inputs))?;
        step("flush", &tmp, io.flush(&tmp))?;
        step("rename", out, io.rename_noreplace(&tmp, out))?;
        Ok(())
    })();
    match written {
        Ok(()) => Outcome {
            status: result.status,
            exit_code: result.exit_code,
            result: Some(out.join("result.json")),
            stderr,
        },
        Err((op, path, e)) => {
            stderr.push(format!(
                "archsig: 出力の{op}に失敗した({}): {e}。出力先は変更していない。一時 directory: {}",
                path.display(),
                tmp.display()
            ));
            Outcome {
                status: Status::Error,
                exit_code: 74,
                result: None,
                stderr,
            }
        }
    }
}

fn temp_dir(out: &Path) -> PathBuf {
    let name = out
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_owned());
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let tmp = format!(".{name}.archsig-{}-{nanos}", std::process::id());
    match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.join(tmp),
        _ => PathBuf::from(tmp),
    }
}

/// process の peak RSS(byte)。
pub fn peak_rss_bytes() -> u64 {
    use nix::sys::resource::{UsageWho, getrusage};
    let Ok(usage) = getrusage(UsageWho::RUSAGE_SELF) else {
        return 0;
    };
    let max = usage.max_rss().max(0) as u64;
    if cfg!(target_os = "macos") {
        max
    } else {
        max * 1024
    }
}
