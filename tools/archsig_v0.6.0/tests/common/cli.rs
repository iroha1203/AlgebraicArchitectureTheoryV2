//! CLI を実行して receipt と result.json を読む補助。

use archsig::json::{JNode, JValue, parse};
use std::path::{Path, PathBuf};
use std::process::Command;

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
}

pub fn run(dir: &Path, args: &[&str]) -> Run {
    let out = bin().current_dir(dir).args(args).output().unwrap();
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert_eq!(stdout.matches('\n').count(), 1, "stdout は一行: {stdout:?}");
    Run {
        code: out.status.code().unwrap(),
        receipt: parse(stdout.trim_end().as_bytes()).unwrap(),
        stdout,
        stderr: String::from_utf8(out.stderr).unwrap(),
    }
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
    assert_eq!(s(get(&r.receipt, "status")), status);
    assert_eq!(num(get(&r.receipt, "exit_code")), code as u64);
    let res = result_json(dir, r);
    assert_eq!(s(get(&res, "format")), "archsig.result/1");
    assert_eq!(s(get(&res, "command")), "check");
    assert_eq!(s(get(&res, "status")), status);
    assert_eq!(num(get(&res, "exit_code")), code as u64);
    for k in ["requests", "answers", "nodes"] {
        assert!(arr(get(&res, k)).is_empty(), "{k} は空");
    }
    res
}
