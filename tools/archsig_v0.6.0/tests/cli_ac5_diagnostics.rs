//! AC5: 構造化パニック診断、複数エラー一括収集（上限 50）、ソース抜粋・類似候補・SilenceReason 案内の E2E テスト。

use crate::common;
use archsig_common::diagnostic::{
    DEFAULT_MAX_COLLECTED_ERRORS, capture_panic_from_unwind, clear_last_panic,
    format_panic_backtrace_stderr, install_panic_hook, with_verbose_panic_backtrace,
};
use archsig_common::json::{JNode, JValue, parse};
use common::cli::*;
use std::path::{Path, PathBuf};
use std::process::Stdio;

const COUNTER_DEF: &str = include_str!("fixtures/counter.atoms.json");
const COUNTER_LAW: &str = include_str!("fixtures/counter.law");
const COUNTER_MAP: &str = include_str!("fixtures/counter.archmap.json");

fn shigure_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-ledger")
        .join(name)
}

fn run_raw(dir: &Path, args: &[&str]) -> (i32, String, String) {
    let out = bin()
        .current_dir(dir)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

fn has_key(node: &JNode, key: &str) -> bool {
    match &node.value {
        JValue::Obj(entries) => entries.iter().any(|(k, _)| k == key),
        _ => false,
    }
}

struct TestNoSignals;
impl archsig::run::Signals for TestNoSignals {
    fn freeze(&mut self) -> Option<archsig_input::result::Signal> {
        None
    }
}

#[test]
fn structured_panic_captures_message_location_human_format_and_verbose_backtrace() {
    install_panic_hook();
    clear_last_panic();

    let dir = workdir("ac5-panic-structured");
    std::fs::write(dir.join("d.json"), COUNTER_DEF).unwrap();
    std::fs::write(dir.join("l.law"), COUNTER_LAW).unwrap();
    std::fs::write(dir.join("a.json"), COUNTER_MAP).unwrap();

    // `reobserve` で panic_message / panic_location を保持
    let out = dir.join("out");
    let reobserve_cmd = archsig::run::parse_args(&[
        "reobserve".into(),
        "--before-atom-definition".into(),
        dir.join("d.json").into(),
        "--before-law".into(),
        dir.join("l.law").into(),
        "--before-archmap".into(),
        dir.join("a.json").into(),
        "--before-ask".into(),
        "v=evaluate(CountCheck.amount,s=@v/s)".into(),
        "--atom-definition".into(),
        dir.join("d.json").into(),
        "--law".into(),
        dir.join("l.law").into(),
        "--archmap".into(),
        dir.join("a.json").into(),
        "--ask".into(),
        "v=evaluate(CountCheck.amount,s=@v/s)".into(),
        "--out".into(),
        out.into(),
    ])
    .unwrap();
    let control = archsig_common::control::Control::new(|_| panic!("injected reobserve panic"));
    let mut io = archsig::run::FileIo;
    let mut signals = TestNoSignals;
    let outcome = archsig::run::execute_command(&reobserve_cmd, &mut io, &mut signals, &control)
        .expect("reobserve produces outcome");
    assert_eq!(outcome.exit_code, 70);
    let receipt = outcome.receipt();
    let doc = parse(receipt.as_bytes()).unwrap();
    let issue = &arr(get(&doc, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "internal");
    let details = get(issue, "details");
    assert_eq!(s(get(details, "panic_message")), "injected reobserve panic");
    let panic_loc = s(get(details, "panic_location"));
    assert!(
        panic_loc.contains("cli_ac5_diagnostics.rs:"),
        "panic_location={panic_loc}"
    );

    let human = archsig::cli::format::render_outcome(&outcome, archsig::cli::OutputFormat::Human);
    assert!(human.contains("panic: injected reobserve panic"), "{human}");
    assert!(human.contains("cli_ac5_diagnostics.rs:"), "{human}");

    // --verbose 有効時のみ backtrace summary を生成する
    clear_last_panic();
    let no_bt = std::panic::catch_unwind(|| panic!("silent bt panic"));
    let info_no_bt = capture_panic_from_unwind(no_bt.unwrap_err());
    if std::env::var("RUST_BACKTRACE")
        .ok()
        .is_none_or(|v| v.is_empty() || v == "0")
    {
        assert!(format_panic_backtrace_stderr(&info_no_bt).is_none());
    }

    let with_bt = with_verbose_panic_backtrace(true, || {
        std::panic::catch_unwind(|| panic!("verbose bt panic"))
    });
    let info_bt = capture_panic_from_unwind(with_bt.unwrap_err());
    let summary = format_panic_backtrace_stderr(&info_bt).unwrap();
    assert!(summary.contains("verbose bt panic"), "{summary}");
    assert!(summary.contains("backtrace summary:"), "{summary}");
}

#[test]
fn multi_error_batch_collects_across_definitions_law_and_archmap() {
    let dir = workdir("ac5-multi-error-inputs");
    std::fs::write(dir.join("d0.json"), b"{\"bad\":").unwrap();
    std::fs::write(dir.join("d1.json"), b"{\"also_bad\":").unwrap();
    std::fs::write(dir.join("d.json"), COUNTER_DEF).unwrap();
    std::fs::write(dir.join("l.law"), COUNTER_LAW).unwrap();
    std::fs::write(dir.join("a.json"), COUNTER_MAP).unwrap();

    // 1. 複数定義ファイルの構文エラーを両方一括収集
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d0.json",
            "--atom-definition",
            "d1.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ],
    );
    assert_eq!(code, 65, "stderr={stderr}");
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    let issues = arr(get(&rec, "issues"));
    assert_eq!(issues.len(), 2, "stderr={stderr}");
    let inputs: Vec<&str> = issues
        .iter()
        .map(|i| s(get(get(i, "location"), "input")))
        .collect();
    assert_eq!(inputs, vec!["definition0", "definition1"]);

    // 2. Law Phase 1（view 署名群）の複数独立エラー一括収集 + fuzzy suggestions
    let bad_law = COUNTER_LAW.replace(
        "view amount(s: State): Z = s.count;",
        "view bad1(s: Counter.Stat): Z = 1;\n  view bad2(s: Counter.Stte): Z = 2;",
    );
    std::fs::write(dir.join("bad.law"), &bad_law).unwrap();

    for cmd in ["check", "run"] {
        let mut args = vec![
            cmd,
            "--atom-definition",
            "d.json",
            "--law",
            "bad.law",
            "--archmap",
            "a.json",
        ];
        if cmd == "run" {
            args.extend(["--ask", "n=evaluate(CountCheck.bad1,s=@v/s)"]);
        }
        let (code, _, stderr) = run_raw(&dir, &args);
        assert_eq!(code, 65, "cmd={cmd} stderr={stderr}");
        let rec = parse(stderr.trim().as_bytes()).unwrap();
        let issues = arr(get(&rec, "issues"));
        assert_eq!(issues.len(), 2, "cmd={cmd} stderr={stderr}");
        for issue in issues {
            assert_eq!(s(get(get(issue, "location"), "input")), "law");
            let details = get(issue, "details");
            assert!(has_key(details, "suggestions"), "stderr={stderr}");
            assert!(has_key(details, "hint"), "stderr={stderr}");
        }
    }

    // 3. ArchMap 内の複数独立エラー（型typo + origin typo + source欠落）一括収集 + fuzzy suggestions
    let bad_map = COUNTER_MAP
        .replace(r#""type": "Counter.State""#, r#""type": "Counter.Stat""#)
        .replace(
            r#""value": "2", "origin": "model""#,
            r#""value": "2", "origin": "modle""#,
        );
    std::fs::write(dir.join("bad.archmap.json"), &bad_map).unwrap();
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "bad.archmap.json",
        ],
    );
    assert_eq!(code, 65, "stderr={stderr}");
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    let issues = arr(get(&rec, "issues"));
    assert_eq!(issues.len(), 2, "stderr={stderr}");
    for issue in issues {
        assert_eq!(s(get(get(issue, "location"), "input")), "archmap");
        let details = get(issue, "details");
        assert!(has_key(details, "suggestions"), "stderr={stderr}");
        assert!(has_key(details, "hint"), "stderr={stderr}");
    }

    // 4. Law の Phase 2 本文チェックでの複数独立エラー一括収集（view 2つとも型/参照エラー）
    let body_bad_law = COUNTER_LAW.replace(
        "view amount(s: State): Z = s.count;",
        "view amount(s: State): Z = s.counts;\n  view bad_ret(s: State): Bool = s.count;",
    );
    std::fs::write(dir.join("body_bad.law"), &body_bad_law).unwrap();
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "body_bad.law",
            "--archmap",
            "a.json",
        ],
    );
    assert_eq!(code, 65, "stderr={stderr}");
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    let issues = arr(get(&rec, "issues"));
    assert_eq!(issues.len(), 2, "stderr={stderr}");
}

#[test]
fn multi_error_batch_collects_asks_and_caps_at_50() {
    let dir = workdir("ac5-batch-asks-cap");
    std::fs::write(dir.join("d.json"), COUNTER_DEF).unwrap();
    std::fs::write(dir.join("l.law"), COUNTER_LAW).unwrap();
    std::fs::write(dir.join("a.json"), COUNTER_MAP).unwrap();

    // Observed の複数 --ask 構文エラー + duplicate id 一括収集
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "a=evaluate(CountCheck.amount,s=@v/s)",
            "--ask",
            "a=evaluate(CountCheck.amount,s=@v/s)",
            "--ask",
            "bad1=evaluate()",
            "--ask",
            "bad2=",
        ],
    );
    assert_eq!(code, 64, "stderr={stderr}");
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    assert_eq!(arr(get(&rec, "issues")).len(), 3, "stderr={stderr}");

    // SHIGURE の複数 --ask 構文エラー + argument hint の一括収集
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            shigure_fixture("ledger.atoms.json").to_str().unwrap(),
            "--law",
            shigure_fixture("ledger.law").to_str().unwrap(),
            "--archmap",
            shigure_fixture("ledger.archmap.json").to_str().unwrap(),
            "--ask",
            "q1=shigure_solve(BadTask, bogus=1)",
            "--ask",
            "q2=shigure_preservation(NoParens",
        ],
    );
    assert_eq!(code, 64, "stderr={stderr}");
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    let issues = arr(get(&rec, "issues"));
    assert_eq!(issues.len(), 2, "stderr={stderr}");
    assert!(stderr.contains("snapshot=<SnapshotId>"), "stderr={stderr}");

    // SHIGURE resolve 段階の複数エラー（未知宣言 + 未知スナップショット）と suggestions
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            shigure_fixture("ledger.atoms.json").to_str().unwrap(),
            "--law",
            shigure_fixture("ledger.law").to_str().unwrap(),
            "--archmap",
            shigure_fixture("ledger.archmap.json").to_str().unwrap(),
            "--ask",
            "q1=shigure_preservation(P1AtomicUncod)",
            "--ask",
            "q2=shigure_preservation(LedgerMigration.P1AtomicUncond, snapshot=missing_snap)",
            "--format=human",
        ],
    );
    assert_eq!(code, 64, "stderr={stderr}");
    assert!(stderr.contains("suggestions:"), "stderr={stderr}");
    assert!(stderr.contains("P1AtomicUncond"), "stderr={stderr}");
    assert!(stderr.contains("missing_snap"), "stderr={stderr}");

    // 50 件超のエラー上限キャップ確認
    let mut big_law = String::from(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading R {\n  use vocabulary Counter version \"1\" digest \"sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11\";\n",
    );
    for i in 0..60 {
        big_law.push_str(&format!("  view bad_{i}(x: MissingType_{i}): Z = 1;\n"));
    }
    big_law.push_str("}\n");
    std::fs::write(dir.join("many.law"), &big_law).unwrap();
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "many.law",
            "--archmap",
            "a.json",
        ],
    );
    assert_eq!(code, 65);
    let rec = parse(stderr.trim().as_bytes()).unwrap();
    assert_eq!(
        arr(get(&rec, "issues")).len(),
        DEFAULT_MAX_COLLECTED_ERRORS,
        "stderr={stderr}"
    );
}

#[test]
fn human_format_shows_snippet_suggestions_and_silence_reason_hints() {
    let dir = workdir("ac5-human-hints");
    std::fs::write(dir.join("d.json"), COUNTER_DEF).unwrap();
    let typo_law = COUNTER_LAW.replace("s.count", "s.coun");
    std::fs::write(dir.join("typo.law"), &typo_law).unwrap();
    std::fs::write(dir.join("a.json"), COUNTER_MAP).unwrap();

    // --format human に 行番号・抜粋・キャレット・suggestions・hint がすべて表示される
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "typo.law",
            "--archmap",
            "a.json",
            "--format=human",
        ],
    );
    assert_eq!(code, 65, "stderr={stderr}");
    assert!(stderr.contains("location: law:"), "stderr={stderr}");
    assert!(stderr.contains(" | "), "stderr={stderr}");
    assert!(stderr.contains('^'), "stderr={stderr}");
    assert!(stderr.contains("suggestions:"), "stderr={stderr}");
    assert!(stderr.contains("count"), "stderr={stderr}");
    assert!(stderr.contains("hint:"), "stderr={stderr}");

    // SHIGURE ResourceLimitExceeded の SilenceReason に具体的な --shigure-limit 案内が付くこと
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            shigure_fixture("ledger.atoms.json").to_str().unwrap(),
            "--law",
            shigure_fixture("ledger.law").to_str().unwrap(),
            "--archmap",
            shigure_fixture("ledger.archmap.json").to_str().unwrap(),
            "--ask",
            "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)",
            "--shigure-limit",
            "max_poly_terms=1",
            "--detail=full",
        ],
    );
    assert_eq!(code, 2, "stdout={stdout} stderr={stderr}");
    let sum_lim = parse(stdout.trim().as_bytes()).unwrap();
    let sr_lim = get(
        get(get(&arr(get(&sum_lim, "answers"))[0], "outputs"), "shigure"),
        "silence_reason",
    );
    assert_eq!(s(get(sr_lim, "code")), "resource_limit_exceeded");
    assert!(s(get(sr_lim, "hint")).contains("--shigure-limit max_poly_terms"));

    let (code_h, stdout_h, stderr_h) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            shigure_fixture("ledger.atoms.json").to_str().unwrap(),
            "--law",
            shigure_fixture("ledger.law").to_str().unwrap(),
            "--archmap",
            shigure_fixture("ledger.archmap.json").to_str().unwrap(),
            "--ask",
            "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)",
            "--shigure-limit",
            "max_poly_terms=1",
            "--detail=full",
            "--format=human",
        ],
    );
    assert_eq!(code_h, 2, "stdout={stdout_h} stderr={stderr_h}");
    assert!(stdout_h.contains("hint: "), "stdout={stdout_h}");
    assert!(
        stdout_h.contains("--shigure-limit max_poly_terms"),
        "stdout={stdout_h}"
    );

    // SHIGURE UnobservedDependency の SilenceReason に観測スロット案内と human 表示が付くこと
    let raw_map = std::fs::read_to_string(shigure_fixture("ledger.archmap.json")).unwrap();
    let stripped = raw_map.replace(
        r#"        {
          "id": "a_bal",
          "subject": "acc1",
          "field": "LedgerVocab.Account.balance",
          "value": ["3", "2"],
          "origin": "o_static"
        },
"#,
        "",
    );
    assert_ne!(stripped, raw_map);
    let missing_map = dir.join("missing_balance.archmap.json");
    std::fs::write(&missing_map, &stripped).unwrap();
    let (code_u, stdout_u, stderr_u) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            shigure_fixture("ledger.atoms.json").to_str().unwrap(),
            "--law",
            shigure_fixture("ledger.law").to_str().unwrap(),
            "--archmap",
            missing_map.to_str().unwrap(),
            "--ask",
            "obs=shigure_solve(LedgerMigration.ObservedBalanceTask)",
            "--format=human",
        ],
    );
    assert_eq!(code_u, 2, "stdout={stdout_u} stderr={stderr_u}");
    assert!(
        stdout_u.contains("unobserved_dependency"),
        "stdout={stdout_u}"
    );
    assert!(stdout_u.contains("hint:"), "stdout={stdout_u}");
    assert!(
        stdout_u.contains("ArchMap") || stdout_u.contains("inspect"),
        "stdout={stdout_u}"
    );
}
