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

/// 呼出しごとの空の作業 directory。同じ名前で並行に呼ばれても共有しない。
pub fn workdir(name: &str) -> PathBuf {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let serial = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "archsig-cli-{}-{serial}-{name}",
        std::process::id()
    ));
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

/// 実ファイルの操作。製品の `FileIo` と同じく、既存の path を置き換えずに rename する。
struct FileIo;
impl archsig::run::Io for FileIo {
    fn create_dir(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::create_dir(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
        std::fs::write(path, bytes)
    }
    fn flush(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::File::open(path)?.sync_all()
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> std::io::Result<()> {
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            from,
            rustix::fs::CWD,
            to,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(std::io::Error::from)
    }
    fn remove_dir_all(&mut self, path: &Path) -> std::io::Result<()> {
        std::fs::remove_dir_all(path)
    }
}
struct NoSignal;
impl archsig::run::Signals for NoSignal {
    fn freeze(&mut self) -> Option<archsig::result::Signal> {
        None
    }
}

/// 同じ引数を、プロセスを起動せずに run 層へ渡す。path の引数は `dir` から読む。
pub fn run(dir: &Path, args: &[&str]) -> Run {
    use archsig::control::{Control, Limits, Usage};
    use archsig::run::{Command, parse_args, run_check, run_requests, usage_outcome};
    let mut words: Vec<std::ffi::OsString> = Vec::new();
    let mut path_value = false;
    for arg in args {
        words.push(if path_value {
            dir.join(arg).into_os_string()
        } else {
            arg.into()
        });
        path_value = matches!(
            *arg,
            "--atom-definition" | "--law" | "--archmap" | "--out" | "--reuse"
        );
    }
    let started = std::time::Instant::now();
    let control = |limits: Limits| {
        Control::new(limits, move |_| Usage {
            elapsed_ms: started.elapsed().as_millis(),
            ..Usage::default()
        })
    };
    let (io, signals) = (&mut FileIo, &mut NoSignal);
    let outcome = match parse_args(&words) {
        Ok(Command::Check(check)) => {
            run_check(io, signals, &check, started, &mut control(Limits::default()))
        }
        Ok(Command::Run(request)) => {
            run_requests(io, signals, &request, started, &mut control(request.limits()))
        }
        Ok(Command::Version) => panic!("version は run_binary で確かめる"),
        Err(error) => usage_outcome(io, signals, error, started),
    };
    let stdout = format!("{}\n", outcome.receipt());
    Run {
        code: i32::from(outcome.exit_code),
        receipt: parse(stdout.trim_end().as_bytes()).unwrap(),
        stdout,
        stderr: String::new(),
        files_unchanged: false,
    }
}

/// 実バイナリを起動する。main の責務(receipt の書出し・終了コード・signal・実ファイル)の確認に限る。
pub fn run_binary(dir: &Path, args: &[&str]) -> Run {
    run_binary_with_deadline(dir, args, CHILD_DEADLINE)
}

/// 長時間テストは製品予算と独立した監視時間を呼出箇所で明示する。
pub fn run_binary_with_deadline(dir: &Path, args: &[&str], deadline: Duration) -> Run {
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
