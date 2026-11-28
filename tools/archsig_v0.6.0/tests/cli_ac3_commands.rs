//! AC3: 統一 CLI パーサ、`--flag=value`、`--ask-file`、`--project`、`reobserve` 省略補完、
//! `digest` / `inspect` / `inspect --result`、`--format` / `--detail`、`--out` オプション、進捗出力の E2E テスト。

use crate::common;
use archsig_common::json::{JNode, JValue, parse};
use common::cli::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn shigure_fixture(name: &str) -> PathBuf {
    fixture("shigure-ledger").join(name)
}

fn run_raw(dir: &Path, args: &[&str], stdin_bytes: Option<&[u8]>) -> (i32, String, String) {
    let mut cmd = bin();
    cmd.current_dir(dir)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if stdin_bytes.is_some() {
        cmd.stdin(Stdio::piped());
    } else {
        cmd.stdin(Stdio::null());
    }
    let mut child = cmd.spawn().unwrap();
    if let Some(bytes) = stdin_bytes {
        child.stdin.take().unwrap().write_all(bytes).unwrap();
    }
    let out = child.wait_with_output().unwrap();
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

#[test]
fn equals_syntax_and_ask_file_including_stdin_work_uniformly() {
    let dir = workdir("ac3-equals-ask-file");
    let def = fixture("counter.atoms.json");
    let law = fixture("counter.law");
    let map = fixture("counter.archmap.json");

    let ask_file = dir.join("asks.txt");
    std::fs::write(
        &ask_file,
        "# header comment\n\n  n1=evaluate(CountCheck.amount,s=@v/s)  \n# trailing\n",
    )
    .unwrap();

    // `--flag=value` と `--ask-file` + `--ask` の混在（出現順維持）
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "run",
            &format!("--atom-definition={}", def.display()),
            &format!("--law={}", law.display()),
            &format!("--archmap={}", map.display()),
            &format!("--ask-file={}", ask_file.display()),
            "--ask=n2=check(CountAudit.bounded,s=@v/s)",
            "--format=json",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(stderr.is_empty());
    let summary = parse(stdout.trim().as_bytes()).unwrap();
    let answers = arr(get(&summary, "answers"));
    assert_eq!(answers.len(), 2);
    assert_eq!(s(get(&answers[0], "id")), "n1");
    assert_eq!(s(get(&answers[1], "id")), "n2");

    // `--ask-file -`（stdin 読込、コメント・空行無視）
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "run",
            &format!("--atom-definition={}", def.display()),
            &format!("--law={}", law.display()),
            &format!("--archmap={}", map.display()),
            "--ask-file=-",
        ],
        Some(b"# stdin asks\n\nq=evaluate(CountCheck.amount,s=@v/s)\n"),
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let summary = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&arr(get(&summary, "answers"))[0], "id")), "q");

    // `-` の上限超過は exit 74
    let (code, _stdout, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--max-file-bytes=8",
            &format!("--atom-definition={}", def.display()),
            &format!("--law={}", law.display()),
            &format!("--archmap={}", map.display()),
            "--ask-file",
            "-",
        ],
        Some(b"q=evaluate(CountCheck.amount,s=@v/s)\n"),
    );
    assert_eq!(code, 74, "stderr={stderr}");

    // `-` の 2 回指定は usage exit 64
    let (code, _stdout, _stderr) = run_raw(
        &dir,
        &[
            "run",
            &format!("--atom-definition={}", def.display()),
            &format!("--law={}", law.display()),
            &format!("--archmap={}", map.display()),
            "--ask-file=-",
            "--ask-file",
            "-",
        ],
        None,
    );
    assert_eq!(code, 64);

    // `law-fibers` でも `--flag=value` と `--format=pretty` が通る。範囲外の `--overwrite` は exit 64 で拒否。
    let table_file = dir.join("fibers.json");
    std::fs::write(
        &table_file,
        r#"{"scope":"models","sources":["b","a"],"laws":["x"],"q":{"b":"same","a":"same"},"v":{"b":{"x":"yes"},"a":{"x":"yes"}}}"#,
    )
    .unwrap();
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "law-fibers",
            &format!("--table={}", table_file.display()),
            "--format=pretty",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(stdout.contains('\n'));
    assert!(parse(stdout.as_bytes()).is_ok());

    let (code, _, _) = run_raw(
        &dir,
        &[
            "law-fibers",
            &format!("--table={}", table_file.display()),
            "--overwrite",
        ],
        None,
    );
    assert_eq!(code, 64);

    let (code, _, _) = run_raw(
        &dir,
        &[
            "digest",
            &format!("--atom-definition={}", def.display()),
            "--detail=concise",
        ],
        None,
    );
    assert_eq!(code, 64);

    // 空の入力パス（`--law=""` 等）も全サブコマンド共通で exit 64 になること
    let (code, _, _) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law=",
        ],
        None,
    );
    assert_eq!(code, 64);
}

#[test]
fn project_manifest_resolves_relative_paths_and_rejects_implicit_discovery() {
    let dir = workdir("ac3-project");
    let sub = dir.join("proj");
    std::fs::create_dir(&sub).unwrap();
    std::fs::write(
        sub.join("c.atoms.json"),
        std::fs::read(fixture("counter.atoms.json")).unwrap(),
    )
    .unwrap();
    std::fs::write(
        sub.join("c.law"),
        std::fs::read(fixture("counter.law")).unwrap(),
    )
    .unwrap();
    std::fs::write(
        sub.join("c.archmap.json"),
        std::fs::read(fixture("counter.archmap.json")).unwrap(),
    )
    .unwrap();
    std::fs::write(
        sub.join("archsig.project.json"),
        r#"{
            "format": "archsig.project/1",
            "semantics": "archsig/0.6.0",
            "atom_definitions": ["c.atoms.json"],
            "law": "c.law",
            "archmap": "c.archmap.json",
            "asks": ["p=evaluate(CountCheck.amount,s=@v/s)"]
        }"#,
    )
    .unwrap();

    // カレントディレクトリ（dir）に置いたファイルを暗黙探索しないこと
    std::fs::write(
        dir.join("archsig.project.json"),
        std::fs::read(sub.join("archsig.project.json")).unwrap(),
    )
    .unwrap();
    let (code, _stdout, _stderr) = run_raw(&dir, &["check"], None);
    assert_eq!(code, 64, "implicit discovery must not occur");

    // 明示 `--project` では別 CWD からでも相対パスをマニフェスト基準で解決できる
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--project",
            sub.join("archsig.project.json").to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let summary = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&arr(get(&summary, "answers"))[0], "id")), "p");

    // 非互換 semantics は exit 69
    let bad_sem = sub.join("bad_sem.json");
    std::fs::write(
        &bad_sem,
        r#"{"format":"archsig.project/1","semantics":"archsig/0.5.0","atom_definitions":["c.atoms.json"],"law":"c.law"}"#,
    )
    .unwrap();
    let (code, _stdout, _stderr) = run_raw(
        &dir,
        &["check", "--project", bad_sem.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 69);
}

#[test]
fn reobserve_inherits_current_definition_and_law_when_before_flags_omitted() {
    let dir = workdir("ac3-reobserve-inherit");
    let def = fixture("counter.atoms.json");
    let law = fixture("counter.law");
    let map = fixture("counter.archmap.json");
    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "reobserve",
            "--before-archmap",
            map.to_str().unwrap(),
            "--before-ask",
            "prev=evaluate(CountCheck.amount,s=@v/s)",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--ask",
            "curr=evaluate(CountCheck.amount,s=@v/s)",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let doc = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&doc, "format")), "archsig.reobservation.summary/1");
    assert_eq!(s(get(&doc, "status")), "complete");
}

#[test]
fn digest_and_inspect_commands_work_for_inputs_and_saved_results() {
    let dir = workdir("ac3-digest-inspect");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    // 1. archsig digest (JSON + human)
    let (code, stdout, stderr) = run_raw(
        &dir,
        &["digest", "--atom-definition", def.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let dig = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&dig, "format")), "archsig.digest/1");
    let vocabs = arr(get(&dig, "vocabularies"));
    assert_eq!(vocabs.len(), 1);
    assert_eq!(s(get(&vocabs[0], "namespace")), "LedgerVocab");
    let digest_str = s(get(&vocabs[0], "digest"));
    assert!(digest_str.starts_with("sha256:"));

    let (code, human_out, _) = run_raw(
        &dir,
        &[
            "digest",
            "--atom-definition",
            def.to_str().unwrap(),
            "--format",
            "human",
        ],
        None,
    );
    assert_eq!(code, 0);
    assert!(human_out.contains(&format!("use LedgerVocab \"1\" \"{digest_str}\"")));

    // 2. archsig inspect (通常宣言 + SHIGURE 宣言 + snapshot/subject + 欠測スロット)
    let c_def = fixture("counter.atoms.json");
    let c_law = fixture("counter.law");
    let c_map_missing = dir.join("missing.archmap.json");
    let orig_map = std::fs::read_to_string(fixture("counter.archmap.json")).unwrap();
    let stripped_map = orig_map.replace(
        r#"{"id": "count", "subject": "s", "field": "Counter.State.count", "value": "2", "origin": "model"}"#,
        "",
    );
    std::fs::write(&c_map_missing, stripped_map).unwrap();

    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "inspect",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let ins = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&ins, "format")), "archsig.inspect/1");
    let shig = get(&ins, "shigure_declarations");
    assert!(arr(get(shig, "tasks")).contains(&JNode {
        value: JValue::Str("LedgerMigration.P1AtomicUncond".into())
    }));

    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "inspect",
            "--atom-definition",
            c_def.to_str().unwrap(),
            "--law",
            c_law.to_str().unwrap(),
            "--archmap",
            c_map_missing.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let c_ins = parse(stdout.trim().as_bytes()).unwrap();
    assert!(!arr(get(&c_ins, "missing_slots")).is_empty());

    // `inspect --result` で evaluate の outputs 参照 (`n0`) と refuted check の counterexamples / --evidence を解決
    let refuted_map = dir.join("refuted.archmap.json");
    std::fs::write(
        &refuted_map,
        orig_map.replace("\"value\": \"2\"", "\"value\": \"12\""),
    )
    .unwrap();
    let obs_out = dir.join("obs_out");
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            c_def.to_str().unwrap(),
            "--law",
            c_law.to_str().unwrap(),
            "--archmap",
            refuted_map.to_str().unwrap(),
            "--ask",
            "n=evaluate(CountCheck.amount,s=@v/s)",
            "--ask",
            "b=check(CountAudit.bounded,s=@v/s)",
            "--out",
            obs_out.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 1, "stderr={stderr}");

    let (code, stdout_eval, stderr) = run_raw(
        &dir,
        &[
            "inspect",
            "--result",
            obs_out.to_str().unwrap(),
            "--answer",
            "n",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let eval_ins = parse(stdout_eval.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&eval_ins, "format")), "archsig.inspect-result/1");
    let eval_answers = arr(get(&eval_ins, "answers"));
    assert_eq!(eval_answers.len(), 1);
    assert_eq!(s(get(&eval_answers[0], "id")), "n");
    assert!(stdout_eval.contains("\"node_id\":\"n"));

    let (code, stdout, stderr) = run_raw(
        &dir,
        &[
            "inspect",
            "--result",
            obs_out.to_str().unwrap(),
            "--answer",
            "b",
            "--evidence",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    let res_ins = parse(stdout.trim().as_bytes()).unwrap();
    assert_eq!(s(get(&res_ins, "format")), "archsig.inspect-result/1");
    let sel_answers = arr(get(&res_ins, "answers"));
    assert_eq!(sel_answers.len(), 1);
    assert_eq!(s(get(&sel_answers[0], "id")), "b");
    assert_eq!(s(get(&sel_answers[0], "status")), "refuted");
    assert!(has_key(&sel_answers[0], "evidence"));
    assert!(stdout.contains("\"node_id\":\"n"));

    // 未知 `--answer` は exit 65
    let (code, _, _) = run_raw(
        &dir,
        &[
            "inspect",
            "--result",
            obs_out.to_str().unwrap(),
            "--answer",
            "does_not_exist",
        ],
        None,
    );
    assert_eq!(code, 65);

    // 4. `inspect --result` (SHIGURE: デフォルトは重い証明配列を省き、`--evidence` で全展開)
    let shig_out = dir.join("shig_out");
    let (code, _, stderr) = run_raw(
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
            "p1u=shigure_preservation(LedgerMigration.P1AtomicUncond)",
            "--out",
            shig_out.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");

    let (code, slim_out, _) = run_raw(
        &dir,
        &["inspect", "--result", shig_out.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 0);
    assert!(!slim_out.contains("\"residual_ideal\""));
    assert!(slim_out.contains("\"verdict\":\"established\""));

    let (code, full_out, _) = run_raw(
        &dir,
        &[
            "inspect",
            "--result",
            shig_out.to_str().unwrap(),
            "--evidence",
            "--format",
            "pretty",
        ],
        None,
    );
    assert_eq!(code, 0);
    assert!(full_out.contains("\"residual_ideal\""));
    assert!(full_out.contains("\"evidence\""));

    // 5. `inspect --result` の fail-closed スキーマ・版検証（他形式 JSON / 非互換 result 版）
    let wrong_format_dir = dir.join("wrong_fmt");
    std::fs::create_dir(&wrong_format_dir).unwrap();
    std::fs::write(
        wrong_format_dir.join("result.json"),
        r#"{"format":"archsig.atom-definition/1"}"#,
    )
    .unwrap();
    let (code, _, _) = run_raw(
        &dir,
        &["inspect", "--result", wrong_format_dir.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 65);

    let unsupported_ver_dir = dir.join("unsupported_ver");
    std::fs::create_dir(&unsupported_ver_dir).unwrap();
    std::fs::write(
        unsupported_ver_dir.join("result.json"),
        r#"{"format":"archsig.result/99","status":"complete","exit_code":0,"answers":[]}"#,
    )
    .unwrap();
    let (code, _, _) = run_raw(
        &dir,
        &["inspect", "--result", unsupported_ver_dir.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 69);

    let missing_answers_dir = dir.join("missing_answers");
    std::fs::create_dir(&missing_answers_dir).unwrap();
    std::fs::write(
        missing_answers_dir.join("result.json"),
        r#"{"format":"archsig.result/4","status":"complete","exit_code":0}"#,
    )
    .unwrap();
    let (code, _, _) = run_raw(
        &dir,
        &["inspect", "--result", missing_answers_dir.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 65);
}

#[test]
fn format_pretty_human_detail_concise_and_progress_behave_cleanly() {
    let dir = workdir("ac3-format-detail-progress");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");
    let out_dir = dir.join("saved");

    // 明示 `--detail concise` では過剰エビデンスが stdout から省略され、`--out/result.json` には完全保持される
    let (code, stdout, stderr) = run_raw(
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
            "--detail",
            "concise",
            "--progress",
            "--out",
            out_dir.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(stderr.contains("[archsig]"), "stderr={stderr}");
    // stdout は単一行の valid canonical JSON で進捗が混入しない
    assert_eq!(stdout.trim_end().lines().count(), 1);
    let summary = parse(stdout.trim().as_bytes()).unwrap();
    let p1m = get(get(&arr(get(&summary, "answers"))[0], "outputs"), "shigure");
    assert_eq!(s(get(p1m, "verdict")), "established");
    assert!(!has_key(p1m, "residual_ideal"));
    assert!(!has_key(p1m, "provenance"));
    assert!(has_key(p1m, "omitted_fields"));
    assert!(has_key(p1m, "detail_hint"));

    // result.json 側には完全データ（residual_ideal / applicability / provenance）が残る
    let saved_txt = std::fs::read_to_string(out_dir.join("result.json")).unwrap();
    assert!(saved_txt.contains("\"residual_ideal\""));
    assert!(saved_txt.contains("\"provenance\""));

    // `--format human`（SHIGURE concise の由来・省略案内 + Observed 反例描画）
    let (code, human, stderr) = run_raw(
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
            "--detail=concise",
            "--format=human",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(human.contains("Status: complete"));
    assert!(human.contains("verdict: established"));
    assert!(human.contains("origins:"));
    assert!(human.contains("detail_hint:"));

    let c_def = fixture("counter.atoms.json");
    let c_law = fixture("counter.law");
    let refuted_map = dir.join("human_refuted.archmap.json");
    std::fs::write(
        &refuted_map,
        std::fs::read_to_string(fixture("counter.archmap.json"))
            .unwrap()
            .replace("\"value\": \"2\"", "\"value\": \"12\""),
    )
    .unwrap();
    let (code, obs_human, _) = run_raw(
        &dir,
        &[
            "run",
            "--atom-definition",
            c_def.to_str().unwrap(),
            "--law",
            c_law.to_str().unwrap(),
            "--archmap",
            refuted_map.to_str().unwrap(),
            "--ask",
            "b=check(CountAudit.bounded,s=@v/s)",
            "--format=human",
        ],
        None,
    );
    assert_eq!(code, 1);
    assert!(
        obs_human.contains("counterexamples (showing 1 of 1):"),
        "obs_human={obs_human}"
    );
    assert!(obs_human.contains("12"), "obs_human={obs_human}");
}

#[test]
fn out_create_parents_overwrite_and_no_fsync_respect_safety_contracts() {
    let dir = workdir("ac3-out-options");
    let def = fixture("counter.atoms.json");
    let law = fixture("counter.law");
    let map = fixture("counter.archmap.json");
    let nested = dir.join("a/b/c/out");

    // 既定は親不在で exit 64
    let (code, _, _) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--out",
            nested.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 64);

    // `--create-parents --no-fsync` で成功
    let (code, _, stderr) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--out",
            nested.to_str().unwrap(),
            "--create-parents",
            "--no-fsync",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(nested.join("result.json").is_file());
    std::fs::write(nested.join("stale.txt"), "old").unwrap();

    // 既定は既存先上書き拒否 exit 64
    let (code, _, _) = run_raw(
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
            "q=evaluate(CountCheck.amount,s=@v/s)",
            "--out",
            nested.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(code, 64);

    // `--overwrite` で古いディレクトリが差し替わること
    let (code, _, stderr) = run_raw(
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
            "q=evaluate(CountCheck.amount,s=@v/s)",
            "--out",
            nested.to_str().unwrap(),
            "--overwrite",
            "--no-fsync",
        ],
        None,
    );
    assert_eq!(code, 0, "stderr={stderr}");
    assert!(!nested.join("stale.txt").exists());
    let saved = parse(&std::fs::read(nested.join("result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "command")), "run");

    // 通常ファイルに対する `--overwrite` は拒否
    let reg_file = dir.join("regular_file");
    std::fs::write(&reg_file, "do not clobber").unwrap();
    let (code, _, _) = run_raw(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--out",
            reg_file.to_str().unwrap(),
            "--overwrite",
        ],
        None,
    );
    assert_eq!(code, 64);
    assert_eq!(
        std::fs::read_to_string(&reg_file).unwrap(),
        "do not clobber"
    );

    // 残存一時ディレクトリなし
    assert!(
        std::fs::read_dir(nested.parent().unwrap())
            .unwrap()
            .all(|e| !e
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".archsig-"))
    );

    // 無駄な Command 未使用警告回避
    let _ = Command::new("true");
}
