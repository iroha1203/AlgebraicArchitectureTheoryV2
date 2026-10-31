//! CLI を実行して receipt と result.json を読む補助。

use archsig::json::{JNode, JValue, parse};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

#[path = "watchdog.rs"]
mod watchdog;

// 通常の120秒の製品予算に、起動・保存・負荷の余裕を加えた独立した上限。
// 製品の予算引数から延長せず、超過はテスト失敗にする。
pub const CHILD_DEADLINE: Duration = Duration::from_secs(180);

pub fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
}

/// テストごとの空の作業 directory。
pub fn workdir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("archsig-cli-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

pub struct Run {
    pub code: i32,
    pub receipt: JNode,
    pub stdout: String,
    pub stderr: String,
    files_unchanged: bool,
}

pub fn run(dir: &Path, args: &[&str]) -> Run {
    run_with_deadline(dir, args, CHILD_DEADLINE)
}

/// 長時間テストは製品予算と独立した監視時間を呼出箇所で明示する。
pub fn run_with_deadline(dir: &Path, args: &[&str], deadline: Duration) -> Run {
    let captured = watchdog::output(bin().current_dir(dir).args(args), deadline)
        .expect("CLIテストの子プロセスを実行");
    assert!(!captured.timed_out, "CLIテストの子プロセスが独立監視時間{deadline:?}を超過");
    let out = captured.output;
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert_eq!(stdout.matches('\n').count(), 1, "stdout は一行: {stdout:?}");
    Run {
        code: out.status.code().unwrap(),
        receipt: parse(stdout.trim_end().as_bytes()).unwrap(),
        stdout,
        stderr: String::from_utf8(out.stderr).unwrap(),
        files_unchanged: false,
    }
}

#[derive(Debug, PartialEq, Eq)]
enum FixtureEntry {
    File(Vec<u8>),
    Directory,
    Link(PathBuf),
    Other,
}
fn fixture_entries(dir: &Path) -> std::collections::BTreeMap<PathBuf, FixtureEntry> {
    fn visit(
        root: &Path,
        dir: &Path,
        entries: &mut std::collections::BTreeMap<PathBuf, FixtureEntry>,
    ) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            let kind = entry.file_type().unwrap();
            let value = if kind.is_file() {
                FixtureEntry::File(std::fs::read(&path).unwrap())
            } else if kind.is_dir() {
                FixtureEntry::Directory
            } else if kind.is_symlink() {
                FixtureEntry::Link(std::fs::read_link(&path).unwrap())
            } else {
                FixtureEntry::Other
            };
            entries.insert(path.strip_prefix(root).unwrap().to_owned(), value);
            if kind.is_dir() {
                visit(root, &path, entries);
            }
        }
    }
    let mut entries = std::collections::BTreeMap::new();
    visit(dir, dir, &mut entries);
    entries
}
/// 失敗を期待する実行だけ、入力・既存出力を含むfixture全体の非変更を確認する。
pub fn without_file_changes(dir: &Path, execute: impl FnOnce() -> Run) -> Run {
    let before = fixture_entries(dir);
    let mut result = execute();
    assert_eq!(fixture_entries(dir), before, "失敗実行がfixtureを変更した");
    result.files_unchanged = true;
    result
}

pub fn get<'a>(n: &'a JNode, key: &str) -> &'a JNode {
    match &n.value {
        JValue::Obj(entries) => {
            &entries
                .iter()
                .find(|(k, _)| k == key)
                .unwrap_or_else(|| panic!("欄 {key}"))
                .1
        }
        _ => panic!("object ではない"),
    }
}

pub fn has(n: &JNode, key: &str) -> bool {
    matches!(&n.value, JValue::Obj(entries) if entries.iter().any(|(k, _)| k == key))
}

pub fn s(n: &JNode) -> &str {
    match &n.value {
        JValue::Str(s) => s,
        other => panic!("文字列ではない: {other:?}"),
    }
}

pub fn num(n: &JNode) -> u64 {
    match &n.value {
        JValue::Num(t) => t.parse().unwrap(),
        other => panic!("number ではない: {other:?}"),
    }
}

pub fn arr(n: &JNode) -> &[JNode] {
    match &n.value {
        JValue::Arr(items) => items,
        other => panic!("array ではない: {other:?}"),
    }
}

pub fn result_json(dir: &Path, r: &Run) -> JNode {
    let path = dir.join(s(get(&r.receipt, "result")));
    parse(&std::fs::read(path).unwrap()).unwrap()
}

/// receipt・result.json・実際の終了コードがそろい、check の requests/answers/nodes は空。
pub fn consistent(dir: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stderr);
    assert_eq!(s(get(&r.receipt, "format")), "archsig.receipt/1");
    assert_eq!(s(get(&r.receipt, "status")), status);
    assert_eq!(num(get(&r.receipt, "exit_code")), code as u64);
    let res = result_json(dir, r);
    assert_eq!(s(get(&res, "format")), "archsig.result/4");
    assert_eq!(s(get(&res, "command")), "check");
    assert_eq!(s(get(&res, "status")), status);
    assert_eq!(num(get(&res, "exit_code")), code as u64);
    for k in ["requests", "answers", "nodes"] {
        assert!(arr(get(&res, k)).is_empty(), "{k} は空");
    }
    res
}

/// 実行失敗は非空の stdout issues を返し、失敗成果物を作らない。
pub fn notified(_dir: &Path, r: &Run, status: &str, code: i32) -> JNode {
    assert!(r.files_unchanged, "失敗実行はwithout_file_changesで囲む");
    assert!(r.stderr.is_empty(), "エラーは stdout のみ: {}", r.stderr);
    assert_eq!(r.code, code, "{}", r.stderr);
    assert_eq!(s(get(&r.receipt, "format")), "archsig.receipt/1");
    assert_eq!(s(get(&r.receipt, "status")), status);
    assert_eq!(num(get(&r.receipt, "exit_code")), code as u64);
    assert!(!has(&r.receipt, "result"));
    let issues = arr(get(&r.receipt, "issues"));
    assert!(!issues.is_empty());
    for issue in issues {
        assert!(!s(get(issue, "message")).is_empty());
        assert!(arr(get(issue, "dependencies")).is_empty());
        assert!(arr(get(issue, "missing")).is_empty());
    }
    parse(r.stdout.trim_end().as_bytes()).unwrap()
}
pub fn warnings(result: &JNode) -> &[JNode] {
    if has(result, "warnings") { arr(get(result, "warnings")) } else { &[] }
}

/// 導出の検査は内部APIで行い、利用者用の保存形式に証明データを要求しない。
pub fn internal_graph(dir: &Path, saved: &JNode) -> JNode {
    let sources = archsig::input::InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let asks: Vec<_> = arr(get(saved, "requests")).iter().map(|r| s(get(r,"text"))).collect();
    let result = archsig::observed::evaluate_observed_bytes(sources, &asks,
        &mut archsig::control::Control::unlimited()).unwrap();
    parse(result.wire().canonical().as_bytes()).unwrap()
}
