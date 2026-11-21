//! AC3・AC4・AC5(b): 実バイナリ `archsig` による SHIGURE CLI E2E 検証。
//!
//! - AC3(a)–(d): 台帳移行（G-140 P0–P6）の通し垂直スライス（残差 ideal、空性 witness、操作/h/τ 復元と再評価一致）
//! - AC4: 相互作用解析（G-141 F10–F12: `mu*delta`, `t^3`, `mu*delta*(1-rho)` の `rho=0`/`rho=1` 面、開条件沈黙）
//! - AC5(b): 沈黙規律（`x^2+1=0` の代数閉包 vs `Q_points`/`Z_points`、未観測欠測 `Slot::Missing`）
//! - CLI 境界: `archsig check` 正例/負例（結論注入・`editable semantic_law`・非素数 `Fp(4)`）、
//!   `--out` 保存（`archsig.result/4`）、`--reuse` 警告、`Origin.kind` 欠落拒否、混在問い・不正構文拒否。

use crate::common;
use archsig_common::json::{JNode, JValue, parse};
use common::cli::*;
use std::path::{Path, PathBuf};

fn shigure_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-ledger")
        .join(name)
}

fn contains_null(node: &JNode) -> bool {
    match &node.value {
        JValue::Null => true,
        JValue::Arr(items) => items.iter().any(contains_null),
        JValue::Obj(entries) => entries.iter().any(|(_, v)| contains_null(v)),
        _ => false,
    }
}

fn has_key(node: &JNode, key: &str) -> bool {
    match &node.value {
        JValue::Obj(entries) => entries.iter().any(|(k, _)| k == key),
        _ => false,
    }
}

fn bool_val(node: &JNode) -> bool {
    match &node.value {
        JValue::Bool(v) => *v,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn num_str(node: &JNode) -> &str {
    match &node.value {
        JValue::Num(v) => v.as_str(),
        other => panic!("expected Num, got {other:?}"),
    }
}

fn str_list(node: &JNode) -> Vec<&str> {
    arr(node).iter().map(s).collect()
}

#[test]
fn shigure_check_accepts_ledger_fixture_and_rejects_invalid_inputs() {
    let dir = workdir("shigure-check");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    let ok = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
            "--out",
            "checked",
        ],
    );
    let saved = consistent(&dir, &ok, "complete", 0);
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert_eq!(s(get(&saved, "command")), "check");
    assert!(!contains_null(&saved));

    let vocab = &arr(get(&saved, "vocabularies"))[0];
    let digest = s(get(vocab, "digest"));

    // 結論注入（residual_ideal）を `archsig check` が exit 65 で拒否
    let bad_conclusion = dir.join("bad_conclusion.law");
    std::fs::write(
        &bad_conclusion,
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Bad {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure task T {{
    residual_ideal ["mu*delta"];
  }}
}}
"#
        ),
    )
    .unwrap();
    let r = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            bad_conclusion.to_str().unwrap(),
        ],
    );
    assert_eq!(r.code, 65, "stderr={}", r.stderr);
    assert!(
        r.stdout.is_empty(),
        "errors go to stderr, got stdout={}",
        r.stdout
    );
    let receipt = parse(r.stderr.as_bytes()).unwrap();
    assert_eq!(s(get(&receipt, "status")), "invalid");

    // `editable semantic_law` を `archsig check` が exit 65 で拒否
    let bad_semantic = dir.join("bad_semantic.law");
    std::fs::write(
        &bad_semantic,
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadSem {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation P {{
    domain Q;
    sort D;
    phase S {{ coord x: D; law semantic inv: x = 0; }}
    op nop(): S -> S {{ x = x; }}
    obs r on S = (x);
  }}
  shigure change_spec C {{
    domain Q;
    param k: Q;
    editable semantic_law P.S.inv;
  }}
}}
"#
        ),
    )
    .unwrap();
    let r = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            bad_semantic.to_str().unwrap(),
        ],
    );
    assert_eq!(r.code, 65, "stderr={}", r.stderr);

    // 非素数 Fp(4) を `archsig check` が exit 65 で拒否
    let bad_prime = dir.join("bad_prime.law");
    std::fs::write(
        &bad_prime,
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading BadPrime {{
  use vocabulary LedgerVocab version "1" digest "{digest}";
  shigure presentation P {{
    domain Fp(4);
    sort D;
    phase S {{ coord x: D; }}
    op nop(): S -> S {{ x = x; }}
    obs r on S = (x);
  }}
}}
"#
        ),
    )
    .unwrap();
    let r = run_binary(
        &dir,
        &[
            "check",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            bad_prime.to_str().unwrap(),
        ],
    );
    assert_eq!(r.code, 65, "stderr={}", r.stderr);
}

#[test]
fn shigure_ac3_ledger_migration_vertical_slice_via_cli() {
    let dir = workdir("shigure-ac3");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    // AC3(a): 原子操作の保存方程式 ac+bd=1, ar+bs=0 と p=(1,1) marked fiber 復元
    let r = run_binary(
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
            "--ask",
            "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)",
            "--out",
            "ac3a",
        ],
    );
    assert_eq!(r.code, 0, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "unexpected stderr={}", r.stderr);
    let summary = parse(r.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "format")), "archsig.summary/1");
    assert_eq!(s(get(&summary, "status")), "complete");
    assert!(!contains_null(&summary));

    let answers = arr(get(&summary, "answers"));
    assert_eq!(answers.len(), 2);

    let p1u = get(get(&answers[0], "outputs"), "shigure");
    assert_eq!(s(get(p1u, "verdict")), "established");
    assert_eq!(s(get(p1u, "coeff_domain")), "Q");
    assert_eq!(s(get(p1u, "point_domain")), "algebraic_closure");
    let p1u_res = str_list(get(p1u, "residual_ideal"));
    assert!(p1u_res.contains(&"a*c + b*d - 1"), "p1u={p1u_res:?}");
    assert!(p1u_res.contains(&"a*r + b*s"), "p1u={p1u_res:?}");

    let p1m = get(get(&answers[1], "outputs"), "shigure");
    assert_eq!(s(get(p1m, "verdict")), "established");
    let p1m_restored = get(p1m, "restored");
    let p1m_assign = get(p1m_restored, "parameter_assignments");
    assert_eq!(s(get(p1m_assign, "a")), "1");
    assert_eq!(s(get(p1m_assign, "b")), "1");
    assert_eq!(s(get(p1m_assign, "c")), "-d + 1");
    assert_eq!(s(get(p1m_assign, "r")), "-s");
    assert_eq!(
        str_list(get(p1m_restored, "free_parameters")),
        vec!["d", "s"]
    );
    let p1m_reeval = get(p1m_restored, "reevaluation");
    assert!(bool_val(get(p1m_reeval, "checked")));
    assert!(bool_val(get(p1m_reeval, "matched")));
    assert_eq!(
        s(get(p1m_reeval, "scope")),
        "mathematical_model_reevaluation"
    );
    assert_eq!(
        s(get(
            get(get(p1m_restored, "state_comparisons"), "Active"),
            "x"
        )),
        "x + y"
    );

    // `--out ac3a/result.json` が `archsig.result/4` 準拠で保存されていること
    let saved_path = dir.join("ac3a/result.json");
    let saved = parse(&std::fs::read(&saved_path).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert_eq!(s(get(&saved, "semantics")), "archsig/0.6.0");
    assert_eq!(s(get(&saved, "command")), "run");
    assert_eq!(s(get(&saved, "status")), "complete");
    assert_eq!(arr(get(&saved, "nodes")).len(), 2);
    assert!(!contains_null(&saved));
    assert!(dir.join("ac3a/inputs/law.law").is_file());
    assert!(dir.join("ac3a/inputs/archmap.json").is_file());
    assert!(dir.join("ac3a/inputs/definitions/0.json").is_file());

    // AC3(b): V(mu*delta) と D(mu) / D(delta) / D(mu*delta) 空性証明
    let r = run_binary(
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
            "uncond=shigure_preservation(LedgerMigration.P3SnapshotUncond)",
            "--ask",
            "dmu=shigure_solve(LedgerMigration.P3SnapshotDMu)",
            "--ask",
            "ddelta=shigure_solve(LedgerMigration.P3SnapshotDDelta)",
            "--ask",
            "dmudelta=shigure_solve(LedgerMigration.P3SnapshotDMuDelta)",
        ],
    );
    // dmudelta が refuted なので全体 exit 1 / status complete
    assert_eq!(r.code, 1, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "unexpected stderr={}", r.stderr);
    let summary = parse(r.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "status")), "complete");
    let answers = arr(get(&summary, "answers"));
    assert_eq!(
        str_list(get(
            get(get(&answers[0], "outputs"), "shigure"),
            "residual_ideal"
        )),
        vec!["mu*delta"]
    );
    let dmu = get(get(&answers[1], "outputs"), "shigure");
    assert_eq!(s(get(dmu, "verdict")), "established");
    assert_eq!(
        s(get(
            get(get(dmu, "restored"), "parameter_assignments"),
            "delta"
        )),
        "0"
    );
    let ddelta = get(get(&answers[2], "outputs"), "shigure");
    assert_eq!(s(get(ddelta, "verdict")), "established");
    assert_eq!(
        s(get(
            get(get(ddelta, "restored"), "parameter_assignments"),
            "mu"
        )),
        "0"
    );
    let dmudelta = get(get(&answers[3], "outputs"), "shigure");
    assert_eq!(s(get(dmudelta, "verdict")), "refuted");
    let witness = get(dmudelta, "empty_witness");
    assert!(bool_val(get(witness, "verified")));
    assert!(!arr(get(witness, "generators")).is_empty());
    assert_eq!(
        arr(get(witness, "generators")).len(),
        arr(get(witness, "cofactors")).len()
    );

    // AC3(c) & AC3(d): finish_rho + Busy 編集可 → rho=1 導出・finish_snap & 全状態 Busy 復元 / 固定対照は空
    let r = run_binary(
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
            "p6c=shigure_solve(LedgerMigration.P6cEditableBusy)",
            "--ask",
            "p6d=shigure_solve(LedgerMigration.P6dFixedOldBusy)",
            "--out",
            "ac3cd",
        ],
    );
    assert_eq!(r.code, 1, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "unexpected stderr={}", r.stderr);
    let summary = parse(r.stdout.as_bytes()).unwrap();
    let answers = arr(get(&summary, "answers"));

    let p6c = get(get(&answers[0], "outputs"), "shigure");
    assert_eq!(s(get(p6c, "verdict")), "established");
    assert_eq!(str_list(get(p6c, "residual_ideal")), vec!["rho - 1"]);
    let p6c_restored = get(p6c, "restored");
    assert_eq!(
        s(get(get(p6c_restored, "parameter_assignments"), "rho")),
        "1"
    );
    assert_eq!(
        str_list(get(p6c_restored, "free_parameters")),
        vec!["mu", "delta"]
    );
    let finish_ops = get(get(p6c_restored, "operations"), "finish");
    assert_eq!(s(get(finish_ops, "B")), "h*mu + B");
    assert_eq!(s(get(finish_ops, "C")), "-h*mu + C");
    assert_eq!(
        str_list(get(get(p6c_restored, "state_laws"), "Busy")),
        vec!["0"]
    );
    let p6c_reeval = get(p6c_restored, "reevaluation");
    assert!(bool_val(get(p6c_reeval, "checked")));
    assert!(bool_val(get(p6c_reeval, "matched")));
    assert_eq!(
        s(get(p6c_reeval, "scope")),
        "mathematical_model_reevaluation"
    );

    let p6d = get(get(&answers[1], "outputs"), "shigure");
    assert_eq!(s(get(p6d, "verdict")), "refuted");
    assert!(bool_val(get(get(p6d, "empty_witness"), "verified")));
}

#[test]
fn shigure_ac4_interaction_analysis_via_cli() {
    let dir = workdir("shigure-ac4");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    // 閉条件の 4 例（mu*delta、t^3、rho=0 面、rho=1 面）はすべて established / exit 0
    let r = run_binary(
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
            "mudelta=shigure_interaction(LedgerMigration.P3SnapshotUncond)",
            "--ask",
            "cube=shigure_interaction(LedgerMigration.InteractionUnivariateCube)",
            "--ask",
            "rho0=shigure_interaction(LedgerMigration.InteractionFace0)",
            "--ask",
            "rho1=shigure_interaction(LedgerMigration.InteractionFace1)",
        ],
    );
    assert_eq!(r.code, 0, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "unexpected stderr={}", r.stderr);
    let summary = parse(r.stdout.as_bytes()).unwrap();
    let answers = arr(get(&summary, "answers"));

    // mu*delta: 2 変数相互作用、極小不成立部分族 [["delta","mu"]]
    let i_md = get(get(get(&answers[0], "outputs"), "shigure"), "interaction");
    assert_eq!(num_str(get(i_md, "min_interacting_variables")), "2");
    assert_eq!(num_str(get(i_md, "max_vanishing_subset_size")), "1");
    let md_subsets = arr(get(i_md, "minimal_failing_subsets"));
    assert_eq!(md_subsets.len(), 1);
    assert_eq!(str_list(&md_subsets[0]), vec!["delta", "mu"]);

    // t^3: 1 変数相互作用、極小不成立部分族 [["t"]]
    let i_cube = get(get(get(&answers[1], "outputs"), "shigure"), "interaction");
    assert_eq!(num_str(get(i_cube, "min_interacting_variables")), "1");
    assert_eq!(num_str(get(i_cube, "max_vanishing_subset_size")), "0");
    let cube_subsets = arr(get(i_cube, "minimal_failing_subsets"));
    assert_eq!(cube_subsets.len(), 1);
    assert_eq!(str_list(&cube_subsets[0]), vec!["t"]);

    // mu*delta*(1-rho) の rho=0 面: 不成立 [["delta","mu"]]
    let i_rho0 = get(get(get(&answers[2], "outputs"), "shigure"), "interaction");
    assert_eq!(num_str(get(i_rho0, "min_interacting_variables")), "2");
    let rho0_subsets = arr(get(i_rho0, "minimal_failing_subsets"));
    assert_eq!(rho0_subsets.len(), 1);
    assert_eq!(str_list(&rho0_subsets[0]), vec!["delta", "mu"]);

    // mu*delta*(1-rho) の rho=1 面: 解消（極小不成立部分族なし）
    let i_rho1 = get(get(get(&answers[3], "outputs"), "shigure"), "interaction");
    assert_eq!(arr(get(i_rho1, "minimal_failing_subsets")).len(), 0);
    assert_eq!(num_str(get(i_rho1, "max_vanishing_subset_size")), "2");
    assert!(!has_key(i_rho1, "min_interacting_variables"));

    // 開条件 D(mu*delta) を伴う相互作用解析は閉条件へ丸めず undetermined / exit 2
    let r_open = run_binary(
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
            "open_sil=shigure_interaction(LedgerMigration.P6cEditableBusy)",
        ],
    );
    assert_eq!(
        r_open.code, 2,
        "stdout={}\nstderr={}",
        r_open.stdout, r_open.stderr
    );
    assert!(
        r_open.stderr.is_empty(),
        "undetermined is a normal stdout result"
    );
    let open_sum = parse(r_open.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&open_sum, "status")), "partial");
    let sh = get(
        get(&arr(get(&open_sum, "answers"))[0], "outputs"),
        "shigure",
    );
    assert_eq!(s(get(sh, "verdict")), "undetermined");
    assert_eq!(
        s(get(get(sh, "silence_reason"), "code")),
        "open_condition_in_interaction"
    );
}

#[test]
fn shigure_ac5b_silence_provenance_and_cli_guards() {
    let dir = workdir("shigure-ac5b");
    let def = shigure_fixture("ledger.atoms.json");
    let law = shigure_fixture("ledger.law");
    let map = shigure_fixture("ledger.archmap.json");

    // AC5(b): x^2 + 1 = 0 の代数閉包非空 vs Q_points / Z_points 沈黙（partial / exit 2）
    let r = run_binary(
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
            "alg=shigure_solve(LedgerMigration.X2Plus1AlgClosure)",
            "--ask",
            "rat=shigure_solve(LedgerMigration.X2Plus1Rational)",
            "--ask",
            "intg=shigure_solve(LedgerMigration.X2Plus1Integer)",
        ],
    );
    assert_eq!(r.code, 2, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "undetermined must be normal stdout");
    let summary = parse(r.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "status")), "partial");
    let answers = arr(get(&summary, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "established");
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert_eq!(s(get(&answers[2], "status")), "undetermined");
    assert_eq!(
        s(get(
            get(
                get(get(&answers[1], "outputs"), "shigure"),
                "silence_reason"
            ),
            "code"
        )),
        "nonlinear_point_existence_out_of_scope"
    );
    assert_eq!(
        s(get(
            get(
                get(get(&answers[2], "outputs"), "shigure"),
                "silence_reason"
            ),
            "code"
        )),
        "nonlinear_point_existence_out_of_scope"
    );

    // 観測座標（observed Account.balance）の由来（Origin.kind = static_analysis）保持と snapshot 指定
    let r_obs = run_binary(
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
            "obs=shigure_solve(ObservedBalanceTask, snapshot=snap1)",
        ],
    );
    assert_eq!(
        r_obs.code, 0,
        "stdout={}\nstderr={}",
        r_obs.stdout, r_obs.stderr
    );
    let obs_sum = parse(r_obs.stdout.as_bytes()).unwrap();
    let obs_sh = get(get(&arr(get(&obs_sum, "answers"))[0], "outputs"), "shigure");
    assert_eq!(s(get(obs_sh, "verdict")), "established");
    assert_eq!(
        s(get(
            get(get(obs_sh, "restored"), "parameter_assignments"),
            "k"
        )),
        "1"
    );
    let origins = arr(get(get(obs_sh, "provenance"), "origins"));
    assert!(
        origins.iter().any(|o| {
            s(get(o, "origin_id")) == "o_static"
                && s(get(o, "kind")) == "static_analysis"
                && has_key(o, "path")
                && s(get(o, "path")) == "src/ledger.rs"
        }),
        "observed static_analysis origin must be preserved: {origins:?}"
    );

    // 未観測欠測（balance 欠落 ArchMap）は零補完せず unobserved_dependency で沈黙（exit 2）
    let raw_map = std::fs::read_to_string(&map).unwrap();
    let missing_map = dir.join("missing_balance.archmap.json");
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
    std::fs::write(&missing_map, &stripped).unwrap();
    let r_miss = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            missing_map.to_str().unwrap(),
            "--ask",
            "obs=shigure_solve(LedgerMigration.ObservedBalanceTask)",
        ],
    );
    assert_eq!(
        r_miss.code, 2,
        "stdout={}\nstderr={}",
        r_miss.stdout, r_miss.stderr
    );
    let miss_sum = parse(r_miss.stdout.as_bytes()).unwrap();
    let miss_sh = get(
        get(&arr(get(&miss_sum, "answers"))[0], "outputs"),
        "shigure",
    );
    assert_eq!(s(get(miss_sh, "verdict")), "undetermined");
    assert_eq!(
        s(get(get(miss_sh, "silence_reason"), "code")),
        "unobserved_dependency"
    );

    // 旧形式 ArchMap（Origin.kind 省略）を SHIGURE observed 座標へ結合すると fail-closed（exit 65）
    let legacy_map = dir.join("legacy_no_kind.archmap.json");
    let no_kind = raw_map.replace("      \"kind\": \"static_analysis\",\n", "");
    assert_ne!(no_kind, raw_map);
    std::fs::write(&legacy_map, &no_kind).unwrap();
    let r_legacy = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            legacy_map.to_str().unwrap(),
            "--ask",
            "obs=shigure_solve(LedgerMigration.ObservedBalanceTask)",
        ],
    );
    assert_eq!(r_legacy.code, 65, "stderr={}", r_legacy.stderr);
    assert!(r_legacy.stdout.is_empty());

    // `--reuse` 指定時は再利用せず警告付きで現在入力から再計算（Non-Goals 整合）
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
            "--reuse",
            dir.to_str().unwrap(),
            "--ask",
            "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)",
        ],
    );
    assert_eq!(
        r_reuse.code, 0,
        "stdout={}\nstderr={}",
        r_reuse.stdout, r_reuse.stderr
    );
    let reuse_sum = parse(r_reuse.stdout.as_bytes()).unwrap();
    let warnings = arr(get(&reuse_sum, "warnings"));
    assert_eq!(warnings.len(), 1);
    assert_eq!(s(get(get(&warnings[0], "details"), "argument")), "--reuse");

    // SHIGURE 問いと通常問いの混在・未知タスク・未知 snapshot・重複 ID・不正構文は exit 64
    for bad_args in [
        vec![
            "--ask",
            "a=evaluate(LedgerMigration.read_balance,a=@snap1/acc1)",
            "--ask",
            "b=shigure_solve(LedgerMigration.P1AtomicMarked)",
        ],
        vec!["--ask", "x=shigure_solve(LedgerMigration.NoSuchTask)"],
        vec![
            "--ask",
            "x=shigure_solve(LedgerMigration.P1AtomicMarked, snapshot=no_snap)",
        ],
        vec![
            "--ask",
            "dup=shigure_solve(LedgerMigration.P1AtomicMarked)",
            "--ask",
            "dup=shigure_interaction(LedgerMigration.P3SnapshotUncond)",
        ],
        vec!["--ask", "bad=shigure_solve()"],
    ] {
        let mut cmd = vec![
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
        ];
        cmd.extend(bad_args);
        let r_bad = run_binary(&dir, &cmd);
        assert_eq!(r_bad.code, 64, "cmd={cmd:?}\nstderr={}", r_bad.stderr);
        assert!(r_bad.stdout.is_empty());
    }
}
