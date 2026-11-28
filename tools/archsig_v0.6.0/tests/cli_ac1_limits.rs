//! AC1 リソース暴走ガード・`--max-file-bytes`・`--shigure-limit`・JSON 深さ制限の実バイナリ CLI E2E テスト。

use crate::common::cli::{arr, bin, get, num, run_binary, s, workdir};
use archsig_common::{canonical::sha256_digest, json::parse};
use std::path::{Path, PathBuf};

fn shigure_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-ledger")
        .join(name)
}

fn write_tiny_ledger_law(dir: &Path) -> PathBuf {
    let law_path = dir.join("tiny_ledger.law");
    std::fs::write(
        &law_path,
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading TinyLedger {
  use vocabulary LedgerVocab version "1" digest "sha256:cb35ebe9d9af7271972225abdcd0993b4ae6051104a331f094dd45cea9f4daae";
  view read_balance(a: Account): Q = a.balance;
}
"#,
    )
    .unwrap();
    law_path
}

fn assert_stderr_code(run: &crate::common::cli::BinaryRun, exit_code: i32, err_code: &str) {
    assert_eq!(
        run.code, exit_code,
        "stdout={}\nstderr={}",
        run.stdout, run.stderr
    );
    assert!(
        run.stdout.is_empty(),
        "expected empty stdout, got {}",
        run.stdout
    );
    let receipt = parse(run.stderr.as_bytes()).unwrap();
    assert_eq!(num(get(&receipt, "exit_code")), exit_code as u64);
    let issue = &arr(get(&receipt, "issues"))[0];
    assert_eq!(s(get(issue, "code")), err_code);
}

#[test]
fn cli_max_file_bytes_bounds_check_run_evidence_fibers_and_reuse() {
    let dir = workdir("ac1-file-bytes");
    let def = shigure_fixture("ledger.atoms.json");
    let law = write_tiny_ledger_law(&dir);
    let map = shigure_fixture("ledger.archmap.json");

    // check: input exceeding --max-file-bytes fails cleanly with exit 74
    let r_check = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--max-file-bytes",
            "32",
        ],
    );
    assert_stderr_code(&r_check, 74, "io");

    // run: input exceeding --max-file-bytes fails cleanly with exit 74
    let r_run = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--ask",
            "bal=evaluate(TinyLedger.read_balance,a=@snap1/acc1)",
            "--max-file-bytes",
            "32",
        ],
    );
    assert_stderr_code(&r_run, 74, "io");

    // evidence: oversized source file fails with exit 74
    let ev_data = "0123456789abcdef0123456789abcdef0123456789abcdef";
    let ev_src = dir.join("ev_src");
    std::fs::write(&ev_src, ev_data).unwrap();
    let ev_map = dir.join("ev_map.json");
    std::fs::write(
        &ev_map,
        format!(
            r#"{{"sources":[{{"id":"code","digest":"{}","revision":"r1"}}],"origins":[{{"id":"o","locations":[{{"source":"code"}}]}}],"snapshots":[{{"id":"v","atoms":[{{"id":"a","value":true,"origin":"o"}}]}}]}}"#,
            sha256_digest(ev_data.as_bytes())
        ),
    )
    .unwrap();
    let r_ev = run_binary(
        &dir,
        &[
            "evidence",
            "--archmap",
            ev_map.to_str().unwrap(),
            "--atom",
            "v/a",
            "--source",
            &format!("code={}", ev_src.display()),
            "--max-file-bytes",
            "16",
        ],
    );
    assert_stderr_code(&r_ev, 74, "io");

    // law-fibers: oversized table fails with exit 74
    let table = dir.join("table.json");
    std::fs::write(
        &table,
        r#"{"scope":"m","sources":["a"],"laws":["l"],"q":{"a":"1"},"v":{"a":{"l":"ok"}}}"#,
    )
    .unwrap();
    let r_fib = run_binary(
        &dir,
        &[
            "law-fibers",
            "--table",
            table.to_str().unwrap(),
            "--max-file-bytes",
            "16",
        ],
    );
    assert_stderr_code(&r_fib, 74, "io");

    // --reuse: baseline result.json larger than --max-file-bytes triggers warning & recomputes
    let saved_dir = dir.join("saved");
    let baseline = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--ask",
            "bal=evaluate(TinyLedger.read_balance,a=@snap1/acc1)",
            "--out",
            saved_dir.to_str().unwrap(),
        ],
    );
    assert_eq!(baseline.code, 0, "stderr={}", baseline.stderr);
    let reuse_limit = [def.as_path(), law.as_path(), map.as_path()]
        .into_iter()
        .map(|p| std::fs::metadata(p).unwrap().len())
        .max()
        .unwrap();
    let res_path = saved_dir.join("result.json");
    let res_len = std::fs::metadata(&res_path).unwrap().len();
    if res_len <= reuse_limit {
        use std::io::Write;
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .open(&res_path)
            .unwrap();
        let pad = " ".repeat((reuse_limit - res_len) as usize + 64);
        f.write_all(pad.as_bytes()).unwrap();
    }
    assert!(std::fs::metadata(&res_path).unwrap().len() > reuse_limit);
    let limit_arg = reuse_limit.to_string();
    let r_reuse = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--ask",
            "bal=evaluate(TinyLedger.read_balance,a=@snap1/acc1)",
            "--reuse",
            saved_dir.to_str().unwrap(),
            "--max-file-bytes",
            &limit_arg,
        ],
    );
    assert_eq!(r_reuse.code, 0, "stderr={}", r_reuse.stderr);
    let summary = parse(r_reuse.stdout.as_bytes()).unwrap();
    let warnings = arr(get(&summary, "warnings"));
    assert_eq!(warnings.len(), 1);
    assert_eq!(s(get(get(&warnings[0], "details"), "argument")), "--reuse");
}

#[test]
fn cli_rejects_excessive_json_nesting_depth_without_abort() {
    let dir = workdir("ac1-json-depth");
    let def = shigure_fixture("ledger.atoms.json");
    let law = write_tiny_ledger_law(&dir);
    let deep_val = format!("{}0{}", "[".repeat(260), "]".repeat(260));

    let deep_json = dir.join("deep.json");
    std::fs::write(&deep_json, format!(r#"{{"extra":{deep_val}}}"#)).unwrap();

    let r_check = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            deep_json.to_str().unwrap(),
        ],
    );
    assert_stderr_code(&r_check, 65, "syntax");

    let r_ev = run_binary(
        &dir,
        &[
            "evidence",
            "--archmap",
            deep_json.to_str().unwrap(),
            "--atom",
            "v1/a",
        ],
    );
    assert_stderr_code(&r_ev, 65, "syntax");

    let r_fib = run_binary(
        &dir,
        &["law-fibers", "--table", deep_json.to_str().unwrap()],
    );
    assert_stderr_code(&r_fib, 65, "syntax");
}

#[test]
fn cli_shigure_limit_flag_bounds_solver_and_rejects_invalid_limit_args() {
    let dir = workdir("ac1-shigure-limit");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    let r_limit = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--ask",
            "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)",
            "--shigure-limit",
            "max_poly_terms=1",
        ],
    );
    assert_eq!(
        r_limit.code, 2,
        "stdout={}\nstderr={}",
        r_limit.stdout, r_limit.stderr
    );
    assert!(
        r_limit.stderr.is_empty(),
        "unexpected stderr={}",
        r_limit.stderr
    );
    let summary = parse(r_limit.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "status")), "partial");
    let answers = arr(get(&summary, "answers"));
    let shig = get(get(&answers[0], "outputs"), "shigure");
    assert_eq!(s(get(shig, "verdict")), "undetermined");
    let reason = get(shig, "silence_reason");
    assert_eq!(s(get(reason, "code")), "resource_limit_exceeded");
    assert_eq!(s(get(reason, "limit_name")), "max_poly_terms");

    // 不正な引数群は全て exit 64 (`usage`)
    let tiny_law = write_tiny_ledger_law(&dir);
    for extra in [
        vec!["--max-file-bytes", "0"],
        vec!["--max-file-bytes", "not-a-number"],
        vec!["--shigure-limit", "unknown_limit=10"],
        vec!["--shigure-limit", "max_bigint_bits=0"],
        vec!["--shigure-limit", "missing_equals"],
    ] {
        let mut args = vec![
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            tiny_law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
        ];
        args.extend(extra);
        let r = run_binary(&dir, &args);
        assert_stderr_code(&r, 64, "usage");
    }

    for help_args in [
        vec!["run", "--help"],
        vec!["check", "--help"],
        vec!["evidence", "--help"],
        vec!["law-fibers", "--help"],
    ] {
        let out = bin().current_dir(&dir).args(&help_args).output().unwrap();
        assert!(out.status.success(), "{help_args:?}");
        let stdout = String::from_utf8(out.stdout).unwrap();
        assert!(stdout.contains("--max-file-bytes"), "{help_args:?}");
    }
}
