//! 引数fixtureの明示期待値で、実CLIのusage通知と既存データ保護を検査する。
mod common;
use archsig::json::{JNode, parse};
use common::cli::*;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

const CASES: &[u8] = include_bytes!("fixtures/cli-arguments.json");

fn cases() -> JNode {
    parse(CASES).unwrap()
}
fn strings(node: &JNode) -> Vec<&str> {
    arr(node).iter().map(s).collect()
}
fn setup(name: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/counter.atoms.json").as_slice(),
        ),
        ("l.law", include_bytes!("fixtures/counter.law").as_slice()),
        (
            "a.json",
            include_bytes!("fixtures/counter.archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[derive(Debug, PartialEq, Eq)]
enum Entry {
    Directory,
    File(Vec<u8>),
}
fn tree(dir: &Path) -> BTreeMap<PathBuf, Entry> {
    fn walk(root: &Path, dir: &Path, result: &mut BTreeMap<PathBuf, Entry>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            let ty = std::fs::symlink_metadata(&path).unwrap().file_type();
            let key = path.strip_prefix(root).unwrap().to_path_buf();
            if ty.is_dir() {
                result.insert(key, Entry::Directory);
                walk(root, &path, result);
            } else {
                assert!(ty.is_file(), "予期しないsymlink/特殊file: {key:?}");
                result.insert(key, Entry::File(std::fs::read(&path).unwrap()));
            }
        }
    }
    let mut result = BTreeMap::new();
    walk(dir, dir, &mut result);
    result
}
fn usage(dir: &Path, args: &[&str], case: &JNode) {
    let before = tree(dir);
    let r = run(dir, args);
    assert_eq!(r.code, 64, "{args:?}: {}", r.stdout);
    assert_eq!(s(get(&r.receipt, "format")), "archsig.receipt/1");
    assert_eq!(s(get(&r.receipt, "status")), "invalid");
    assert_eq!(num(get(&r.receipt, "exit_code")), 64);
    assert!(!has(&r.receipt, "result"));
    let issues = arr(get(&r.receipt, "issues"));
    let issue = issues
        .iter()
        .find(|issue| {
            s(get(issue, "code")) == "usage"
                && s(get(get(issue, "details"), "argument")) == s(get(case, "argument"))
        })
        .unwrap_or_else(|| panic!("具体的な引数のusageがない: {}", r.stdout));
    assert!(
        s(get(issue, "message")).contains(s(get(case, "message"))),
        "{}",
        r.stdout
    );
    assert_eq!(
        tree(dir),
        before,
        "失敗通知がfile/directoryを変更した: {args:?}"
    );
}
fn group(name: &str) {
    let fixture = cases();
    for case in arr(get(&fixture, name)) {
        let dir = setup(s(get(case, "name")));
        usage(&dir, &strings(get(case, "args")), case);
    }
}

#[test]
fn every_singleton_flag_duplicate_is_a_concrete_usage_error() {
    group("single_duplicates");
}
#[test]
fn every_flag_requires_its_value() {
    group("missing_values");
}
#[test]
fn each_required_flag_missing_is_reported_without_files() {
    group("required_missing");
}
#[test]
fn commands_unknown_flags_positionals_and_run_only_flags_are_closed() {
    group("unexpected");
}
#[test]
fn both_budget_flags_reject_nonpositive_noncanonical_and_noninteger_values() {
    group("invalid_budgets");
}
#[test]
fn invalid_check_and_run_arguments_ignore_output_state_and_preserve_existing_data() {
    let fixture = cases();
    for case in arr(get(&fixture, "out_independent")) {
        for (index, out) in [
            None,
            Some("fresh"),
            Some("existing"),
            Some("missing-parent/out"),
            Some(""),
        ]
        .into_iter()
        .enumerate()
        {
            let dir = workdir(&format!("{}-{index}", s(get(case, "name"))));
            std::fs::create_dir_all(dir.join("existing/nested")).unwrap();
            std::fs::write(dir.join("existing/result.json"), b"existing artifact\n").unwrap();
            std::fs::write(dir.join("existing/nested/data"), b"keep nested bytes\0\xff").unwrap();
            std::fs::write(dir.join("unrelated"), b"keep unrelated data").unwrap();
            let mut args = strings(get(case, "prefix"));
            if let Some(out) = out {
                args.extend(["--out", out]);
            }
            args.extend(strings(get(case, "tail")));
            usage(&dir, &args, case);
        }
    }
}
