//! 出力先の検査と、状態の確定・入力コピー・result.json の公開(実行仕様 §§5–7)。

use super::{Io, Outcome, Signals};
use archsig_common::canonical::Json;
use archsig_input::result::{CheckResult, ResultIssue, Status, exit_code};
use std::path::{Path, PathBuf};

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
        return Err("output path is empty".to_owned());
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
        return Err("output path must end with a new name".to_owned());
    }
    if exists(out) {
        return Err("output path already exists".to_owned());
    }
    let parent = match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => PathBuf::from("."),
    };
    if !is_dir(&parent) {
        return Err("output parent directory does not exist".to_owned());
    }
    Ok(())
}

/// 出力先のない usage を、捕捉済み signal とともに一度だけ確定する。
pub(super) fn usage_without_result(signals: &mut dyn Signals, issue: ResultIssue) -> Outcome {
    without_result(signals, Status::Invalid, vec![issue])
}

/// 成果物のない実行失敗・中断を一度だけ確定する。
pub(super) fn without_result(
    signals: &mut dyn Signals,
    status: Status,
    mut issues: Vec<ResultIssue>,
) -> Outcome {
    let prior_signal = issues.iter().find_map(|i| match i {
        ResultIssue::Cancelled(signal) => Some(*signal),
        _ => None,
    });
    let code = exit_code(status, prior_signal, &issues);
    issues.sort_by_key(ResultIssue::sort_key);
    notify(
        signals,
        status,
        code,
        prior_signal,
        issues.iter().map(ResultIssue::wire).collect(),
    )
}

/// 検査・要求解決の失敗通知。JSONは出力だけに使い、状態判断は呼出し側の型付き結果に従う。
pub(super) fn notify(
    signals: &mut dyn Signals,
    mut status: Status,
    mut code: u8,
    prior_signal: Option<archsig_input::result::Signal>,
    mut issues: Vec<Json>,
) -> Outcome {
    let frozen = signals.freeze();
    if let Some(signal) = prior_signal.or(frozen) {
        status = Status::Interrupted;
        code = exit_code(status, Some(signal), &[]);
        if prior_signal.is_none() {
            issues.push(signal.issue());
        }
    }
    sort_issues(&mut issues);
    Outcome {
        status,
        exit_code: code,
        result: None,
        summary: None,
        issues,
    }
}

/// Issueの表示順。状態や意味の再判定には使わない。
pub(super) fn sort_issues(issues: &mut [Json]) {
    fn text(fields: &std::collections::BTreeMap<String, Json>, key: &str) -> String {
        match fields.get(key) {
            Some(Json::Str(s)) => s.clone(),
            _ => String::new(),
        }
    }
    issues.sort_by_key(|issue| {
        let Json::Obj(fields) = issue else {
            return (String::new(), String::new(), String::new(), 0);
        };
        let (input, pointer, start) = match fields.get("location") {
            Some(Json::Obj(loc)) => {
                let start = match loc.get("span") {
                    Some(Json::Arr(v)) => match v.first() {
                        Some(Json::Nat(n)) => *n,
                        _ => 0,
                    },
                    _ => 0,
                };
                (text(loc, "input"), text(loc, "pointer"), start)
            }
            _ => (String::new(), String::new(), 0),
        };
        (text(fields, "code"), input, pointer, start)
    });
}

/// finalize: signal を確定してから結果を一時 directory に書き、置き換えない rename で公開する。
pub(super) fn finalize(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    out: &Path,
    mut result: CheckResult,
    copies: &[(&str, &[u8])],
) -> Outcome {
    if result.status != Status::Complete {
        let mut outcome = without_result(signals, result.status, result.issues);
        for issue in &mut outcome.issues {
            input_positions(issue, copies);
        }
        return outcome;
    }
    if let Some(signal) = signals.freeze() {
        result.status = Status::Interrupted;
        result.issues.push(ResultIssue::Cancelled(signal));
        result.exit_code = exit_code(Status::Interrupted, Some(signal), &result.issues);
    } else {
        result.exit_code = exit_code(result.status, None, &result.issues);
    }
    let outcome = Outcome {
        status: result.status,
        exit_code: result.exit_code,
        result: Some(out.join("result.json")),
        summary: None,
        issues: result.issues.iter().map(ResultIssue::wire).collect(),
    };
    let mut document = result.wire();
    input_positions(&mut document, copies);
    publish(io, out, document, copies, outcome)
}

fn input_positions(document: &mut Json, copies: &[(&str, &[u8])]) {
    let sources: Vec<_> = copies
        .iter()
        .filter_map(|(name, bytes)| {
            let id = match *name {
                "inputs/law.law" => "law".to_owned(),
                "inputs/archmap.json" => "archmap".to_owned(),
                name => format!(
                    "definition{}",
                    name.strip_prefix("inputs/definitions/")?
                        .strip_suffix(".json")?
                ),
            };
            Some((id, *bytes))
        })
        .collect();
    archsig_input::result::add_location_positions(
        document,
        sources.iter().map(|(id, bytes)| (id.as_str(), *bytes)),
    );
}

/// 確定した成果物の配送だけを担う。表示JSONを意味計算へ戻さない。
pub(super) fn publish(
    io: &mut dyn Io,
    out: &Path,
    document: Json,
    copies: &[(&str, &[u8])],
    outcome: Outcome,
) -> Outcome {
    let tmp = temp_dir(out);
    let mut created = false;
    let written = (|| -> Result<(), (&'static str, PathBuf, std::io::Error)> {
        let step = |op: &'static str, p: &Path, r: std::io::Result<()>| {
            r.map_err(|e| (op, p.to_path_buf(), e))
        };
        step("create", &tmp, io.create_dir(&tmp))?;
        created = true;
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
        step("write", &p, io.write(&p, document.canonical().as_bytes()))?;
        step("flush", &p, io.flush(&p))?;
        step("flush", &inputs, io.flush(&inputs))?;
        step("flush", &tmp, io.flush(&tmp))?;
        step("rename", out, io.rename_noreplace(&tmp, out))?;
        Ok(())
    })();
    match written {
        Ok(()) => outcome,
        Err((op, path, e)) => {
            let mut message = format!("output {op} failed ({}): {e}", path.display());
            if created {
                if let Err(cleanup) = io.remove_dir_all(&tmp) {
                    message.push_str(&format!(
                        "; cannot clean up incomplete temporary directory ({}): {cleanup}",
                        tmp.display()
                    ));
                }
            }
            let issue = ResultIssue::Io {
                operation: op,
                path: path.to_string_lossy().into_owned(),
                message,
            };

            Outcome {
                status: Status::Error,
                exit_code: 74,
                result: None,
                summary: None,
                issues: vec![issue.wire()],
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
