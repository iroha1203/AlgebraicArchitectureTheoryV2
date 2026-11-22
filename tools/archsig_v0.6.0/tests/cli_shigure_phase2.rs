//! AC3・AC4・AC5・AC6: 実バイナリ `archsig` による SHIGURE Phase 2 CLI E2E 検証。
//!
//! - AC3: `shigure_diagram`（両向き四角形補完・鎖補完・不成立空性 witness・観測偽装拒否・商環・由来保持）
//! - AC4: `shigure_path`（P5.1 4 順序＋2 順序残差 1・P5.2 拡大 protocol・`n=0`・連結・細分化・F3.1）
//! - AC5: `shigure_transfer`（G1 lift と観測偽装・G2 `word_check` / `old_word_lift`・G3 合成 2/3 段・P5.3 Busy 拒否）
//! - AC6: 沈黙規律（未観測欠測・無界探索・非線形 `Q_points`・`Z` 商環沈黙 exit 2）、混在・不正構文（exit 64）、
//!   結論注入・固定編集・$X_0$ 変更・名前空間衝突・`Origin.kind` 欠落（exit 65）、cross-reading `scope.readings`。

use crate::common;
use archsig_common::json::{JNode, JValue, parse};
use common::cli::*;
use std::path::{Path, PathBuf};

fn phase2_fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-phase2")
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

fn run_p2(dir: &Path, def: &Path, law: &Path, map: &Path, extra: &[&str]) -> BinaryRun {
    let mut args = vec![
        "run",
        "--atom-definition",
        def.to_str().unwrap(),
        "--law",
        law.to_str().unwrap(),
        "--archmap",
        map.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    run_binary(dir, &args)
}

#[test]
fn shigure_phase2_check_validates_fixtures_and_rejects_invalid_inputs() {
    let dir = workdir("shigure-p2-check");
    let def = phase2_fixture("phase2.atoms.json");
    let map = phase2_fixture("phase2.archmap.json");

    for (idx, law_name) in ["diagrams.law", "paths.law", "transfers.law"]
        .iter()
        .enumerate()
    {
        let law = phase2_fixture(law_name);
        let out_name = format!("checked_{idx}");
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
                &out_name,
            ],
        );
        let saved = consistent(&dir, &ok, "complete", 0);
        assert_eq!(s(get(&saved, "format")), "archsig.result/4");
        assert_eq!(s(get(&saved, "command")), "check");
        assert!(!contains_null(&saved));
    }

    let digest = "sha256:3c4d12e5b45460e139353d29832053551ec840b1e905e3c876476d9db9b7bd69";
    let base_pres = r#"
  shigure presentation P { domain Q; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Q; }"#;
    let invalid_bodies = [
        // 結論注入（diagram / path / transfer）
        format!(
            "{base_pres} shigure diagram D {{ direction state_map; vertex fixed V: P; commutativity_residuals = 0; change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure path Pa {{ kind fixed_protocol_change_path; direction state_map; vertex V: P; start V; end V; restored_paths = []; change_spec H; }}"
        ),
        format!(
            "{base_pres} shigure transfer Tr {{ step s1 {{ before P; after P; identity; source_phase S; target_phase S; lift {{ x = x; }} }} transfer_verdict = 1; change_spec H; }}"
        ),
        // 固定頂点の編集指定
        r#"
  shigure presentation P { domain Q; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Q; editable operation P.act; }
  shigure diagram D { direction state_map; vertex fixed V: P; edge fixed e: V -> V { identity; } change_spec H; }"#
            .to_owned(),
        // 移送初段基準表示 X0 の編集指定
        r#"
  shigure presentation X0 { domain Q; sort D; phase S { coord x: D; law representation rep: x = 0; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure presentation X1 { domain Q; sort D; phase S { coord x: D; } op act(): S -> S { x = x; } obs r on S = (x); }
  shigure change_spec H { domain Q; editable representation_law X0.S.rep; }
  shigure transfer Tr { step s1 { before X0; after X1; identity; source_phase S; target_phase S; lift { x = x; } } change_spec H; }"#
            .to_owned(),
        // 名前空間衝突（固定頂点座標 k vs param k）
        r#"
  shigure presentation PF { domain Z; sort D; phase S { coord k: D; } op act(): S -> S { k = k; } obs r on S = (k); }
  shigure presentation PV { domain Z; sort D; phase S { coord y: D; } op act(): S -> S { y = y; } obs r on S = (y); }
  shigure change_spec H { domain Z; param k: Z; }
  shigure diagram D { direction state_map; vertex fixed V0: PF; vertex V1: PV; edge e: V0 -> V1 { state_map S -> S { y = 0; } translate act -> [act()]; } change_spec H; }"#
            .to_owned(),
    ];

    for (idx, body) in invalid_bodies.iter().enumerate() {
        let bad_law = dir.join(format!("invalid_{idx}.law"));
        std::fs::write(
            &bad_law,
            format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Bad{idx} {{\n  use vocabulary Phase2Vocab version \"1\" digest \"{digest}\";\n{body}\n}}\n"
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
                bad_law.to_str().unwrap(),
            ],
        );
        assert_eq!(r.code, 65, "idx={idx} stderr={}", r.stderr);
        assert!(r.stdout.is_empty(), "idx={idx} stdout={}", r.stdout);
        let receipt = parse(r.stderr.as_bytes()).unwrap();
        assert_eq!(s(get(&receipt, "status")), "invalid");
    }
}

#[test]
fn shigure_phase2_ac3_diagram_completion_via_cli() {
    let dir = workdir("shigure-p2-ac3");
    let def = phase2_fixture("phase2.atoms.json");
    let law = phase2_fixture("diagrams.law");
    let map = phase2_fixture("phase2.archmap.json");

    // 成立系: state_map 四角形・time_order 四角形・鎖補完・商環・観測由来・代数閉包
    let r = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "sq_sm=shigure_diagram(DiagSuite.ForkSquareStateMap, snapshot=snap1)",
            "--ask",
            "sq_to=shigure_diagram(ForkSquareTimeOrder)",
            "--ask",
            "chain=shigure_diagram(DiagSuite.ChainCompletion)",
            "--ask",
            "quot=shigure_diagram(DiagSuite.QuotientIdealSquare)",
            "--ask",
            "obs=shigure_diagram(DiagSuite.ObservedCoordDiagram)",
            "--ask",
            "alg=shigure_diagram(DiagSuite.NonlinearAlgClosureOk)",
            "--out",
            "ac3_ok",
        ],
    );
    assert_eq!(r.code, 0, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty(), "stderr={}", r.stderr);
    let summary = parse(r.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "format")), "archsig.summary/1");
    assert_eq!(s(get(&summary, "status")), "complete");
    assert!(!contains_null(&summary));

    let answers = arr(get(&summary, "answers"));
    assert_eq!(answers.len(), 6);

    let sq_sm = get(get(&answers[0], "outputs"), "shigure");
    assert_eq!(s(get(sq_sm, "verdict")), "established");
    let d_sm = get(sq_sm, "diagram");
    assert_eq!(s(get(d_sm, "direction")), "state_map");
    let rd_sm = get(d_sm, "restored_diagram");
    assert_eq!(s(get(get(rd_sm, "parameter_assignments"), "k")), "1");
    assert!(bool_val(get(get(rd_sm, "reevaluation"), "checked")));
    assert!(bool_val(get(get(rd_sm, "reevaluation"), "matched")));
    assert_eq!(
        s(get(get(rd_sm, "reevaluation"), "scope")),
        "mathematical_model_reevaluation"
    );

    let sq_to = get(get(&answers[1], "outputs"), "shigure");
    assert_eq!(s(get(sq_to, "verdict")), "established");
    let d_to = get(sq_to, "diagram");
    assert_eq!(s(get(d_to, "direction")), "time_order");
    assert!(bool_val(get(
        get(get(d_to, "restored_diagram"), "reevaluation"),
        "matched"
    )));

    let ch = get(get(get(&answers[2], "outputs"), "shigure"), "diagram");
    let rd_ch = get(ch, "restored_diagram");
    assert_eq!(s(get(get(rd_ch, "parameter_assignments"), "k")), "1");
    assert_eq!(s(get(get(rd_ch, "parameter_assignments"), "c_shift")), "0");
    assert!(bool_val(get(get(rd_ch, "reevaluation"), "matched")));

    let qt = get(get(&answers[3], "outputs"), "shigure");
    assert_eq!(s(get(qt, "verdict")), "established");

    let obs = get(get(&answers[4], "outputs"), "shigure");
    assert_eq!(s(get(obs, "verdict")), "established");
    let origins = arr(get(get(obs, "provenance"), "origins"));
    assert!(origins.iter().any(|o| {
        s(get(o, "origin_id")) == "o_static"
            && s(get(o, "kind")) == "static_analysis"
            && s(get(o, "path")) == "src/phase2_model.rs"
    }));

    let alg = get(get(&answers[5], "outputs"), "shigure");
    assert_eq!(s(get(alg, "verdict")), "established");
    assert_eq!(s(get(alg, "point_domain")), "algebraic_closure");
    assert_eq!(str_list(get(alg, "residual_ideal")), vec!["k^2 + 1"]);
    assert!(arr(get(alg, "applicability")).iter().any(|c| {
        s(get(c, "condition")) == "closure_stratum_nonempty_verified"
            && bool_val(get(c, "satisfied"))
    }));
    let alg_rd = get(get(alg, "diagram"), "restored_diagram");
    assert!(arr(get(alg_rd, "free_parameters")).is_empty());
    assert!(bool_val(get(get(alg_rd, "reevaluation"), "matched")));

    // --out の archsig.result/4 と cross-reading `scope.readings`
    let saved = parse(&std::fs::read(dir.join("ac3_ok/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert_eq!(s(get(&saved, "command")), "run");
    assert!(!contains_null(&saved));
    let saved_answers = arr(get(&saved, "answers"));
    let readings = str_list(get(get(&saved_answers[0], "scope"), "readings"));
    assert_eq!(readings, vec!["DiagBase", "DiagSuite"]);

    // 反証系: 両立不能四角形（空性 witness 検算済み）＋観測一致のみの偽装可換（拒否）
    let r_ref = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "bad=shigure_diagram(DiagSuite.IncompatibleSquare)",
            "--ask",
            "fake=shigure_diagram(DiagSuite.ObsOnlyFakeContrast)",
        ],
    );
    assert_eq!(
        r_ref.code, 1,
        "stdout={}\nstderr={}",
        r_ref.stdout, r_ref.stderr
    );
    assert!(r_ref.stderr.is_empty());
    let sum_ref = parse(r_ref.stdout.as_bytes()).unwrap();
    let ans_ref = arr(get(&sum_ref, "answers"));

    let bad = get(get(&ans_ref[0], "outputs"), "shigure");
    assert_eq!(s(get(bad, "verdict")), "refuted");
    let witness = get(bad, "empty_witness");
    assert!(bool_val(get(witness, "verified")));
    assert!(!arr(get(witness, "generators")).is_empty());

    let fake = get(get(&ans_ref[1], "outputs"), "shigure");
    assert_eq!(s(get(fake, "verdict")), "refuted");
    let comm_res = get(get(fake, "diagram"), "commutativity_residuals");
    assert!(!arr(get(comm_res, "comm")).is_empty());
}

#[test]
fn shigure_phase2_ac4_paths_and_subdivision_via_cli() {
    let dir = workdir("shigure-p2-ac4");
    let def = phase2_fixture("phase2.atoms.json");
    let law = phase2_fixture("paths.law");
    let map = phase2_fixture("phase2.archmap.json");

    let r = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "p51=shigure_path(PathSuite.LedgerP51Paths)",
            "--ask",
            "p52=shigure_path(LedgerP52ProtocolPaths)",
            "--ask",
            "z_ok=shigure_path(ZeroLengthMatch)",
            "--ask",
            "cat=shigure_path(ConcatPath)",
            "--ask",
            "sub_ok=shigure_path(SubdivideOk)",
            "--out",
            "ac4_ok",
        ],
    );
    assert_eq!(r.code, 0, "stdout={}\nstderr={}", r.stdout, r.stderr);
    assert!(r.stderr.is_empty());
    let summary = parse(r.stdout.as_bytes()).unwrap();
    assert!(!contains_null(&summary));
    let answers = arr(get(&summary, "answers"));
    assert_eq!(answers.len(), 5);

    // P5.1: 4 順序成立・2 順序第 2 段残差 1 で拒否
    let p51 = get(get(&answers[0], "outputs"), "shigure");
    assert_eq!(s(get(p51, "verdict")), "established");
    let p51_det = get(p51, "path");
    assert_eq!(s(get(p51_det, "path_kind")), "fixed_protocol_change_path");
    let valid_p51 = arr(get(p51_det, "valid_paths"));
    assert_eq!(valid_p51.len(), 4);
    for vp in valid_p51 {
        assert!(bool_val(get(get(vp, "reevaluation"), "matched")));
    }
    let mut p51_seqs: Vec<Vec<&str>> = valid_p51
        .iter()
        .map(|vp| str_list(get(vp, "steps")))
        .collect();
    p51_seqs.sort();
    assert_eq!(
        p51_seqs,
        vec![
            vec!["set_d", "set_r", "set_m"],
            vec!["set_m", "set_r", "set_d"],
            vec!["set_r", "set_d", "set_m"],
            vec!["set_r", "set_m", "set_d"],
        ]
    );
    let rej_p51 = arr(get(p51_det, "rejected_candidates"));
    assert!(
        rej_p51.iter().any(|rej| {
            str_list(get(rej, "steps")) == vec!["set_d", "set_m", "set_r"]
                && num_str(get(rej, "failed_step")) == "2"
                && str_list(get(rej, "residuals"))
                    .iter()
                    .any(|x| *x == "1" || *x == "-1")
        }),
        "missing [set_d, set_m, set_r] rejection"
    );
    assert!(
        rej_p51.iter().any(|rej| {
            str_list(get(rej, "steps")) == vec!["set_m", "set_d", "set_r"]
                && num_str(get(rej, "failed_step")) == "2"
                && str_list(get(rej, "residuals"))
                    .iter()
                    .any(|x| *x == "1" || *x == "-1")
        }),
        "missing [set_m, set_d, set_r] rejection"
    );

    // P5.2: enlarged protocol 4 経路・protocol 保存検証・kind の区別
    let p52 = get(get(&answers[1], "outputs"), "shigure");
    assert_eq!(s(get(p52, "verdict")), "established");
    let p52_det = get(p52, "path");
    assert_eq!(
        s(get(p52_det, "path_kind")),
        "enlarged_protocol_execution_path"
    );
    assert!(bool_val(get(p52_det, "protocol_preservation_verified")));
    assert_eq!(arr(get(p52_det, "valid_paths")).len(), 4);
    let rej_p52 = arr(get(p52_det, "rejected_candidates"));
    assert!(rej_p52.iter().any(|rej| {
        str_list(get(rej, "steps")) == vec!["sw_d", "sw_m", "sw_r"]
            && num_str(get(rej, "failed_step")) == "2"
    }));
    assert!(rej_p52.iter().any(|rej| {
        str_list(get(rej, "steps")) == vec!["sw_m", "sw_d", "sw_r"]
            && num_str(get(rej, "failed_step")) == "2"
    }));

    // n=0 / concatenate / subdivide
    assert_eq!(
        s(get(get(get(&answers[2], "outputs"), "shigure"), "verdict")),
        "established"
    );
    let cat_sh = get(get(&answers[3], "outputs"), "shigure");
    assert_eq!(s(get(cat_sh, "verdict")), "established");
    let cat_det = get(cat_sh, "path");
    assert_eq!(s(get(cat_det, "query_mode")), "concatenate");
    let cat_valid = arr(get(cat_det, "valid_paths"));
    assert_eq!(cat_valid.len(), 1);
    assert_eq!(
        str_list(get(&cat_valid[0], "steps")),
        vec!["set_r", "set_d", "set_m"]
    );
    assert!(!bool_val(get(&cat_valid[0], "composite_is_one_step")));
    assert!(bool_val(get(get(&cat_valid[0], "reevaluation"), "matched")));
    let cat_idle = get(get(&cat_valid[0], "composite_state_comparisons"), "Idle");
    assert_eq!(s(get(cat_idle, "B")), "B + C");
    assert_eq!(s(get(cat_idle, "C")), "0");

    let sub_ok = get(get(&answers[4], "outputs"), "shigure");
    assert_eq!(s(get(sub_ok, "verdict")), "established");
    let sub_det = get(sub_ok, "path");
    assert_eq!(s(get(sub_det, "query_mode")), "subdivide");
    let sub_valid = arr(get(sub_det, "valid_paths"));
    assert_eq!(sub_valid.len(), 4);
    for vp in sub_valid {
        assert!(bool_val(get(get(vp, "reevaluation"), "matched")));
        let st = get(get(vp, "composite_state_comparisons"), "S");
        assert_eq!(s(get(st, "a")), "a + 2");
        assert_eq!(s(get(st, "b")), "b - 2");
    }
    let s1_s1 = sub_valid
        .iter()
        .find(|vp| str_list(get(vp, "steps")) == vec!["s1", "s1"])
        .expect("missing [s1, s1] subdivision path");
    assert_eq!(s(get(get(s1_s1, "parameter_assignments"), "a1")), "1");

    let saved = parse(&std::fs::read(dir.join("ac4_ok/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert!(!contains_null(&saved));

    // 不成立系: n=0 不一致・細分化不成立・F3.1 恒等規則のみ
    let r_ref = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "z_bad=shigure_path(ZeroLengthMismatch)",
            "--ask",
            "sub_bad=shigure_path(SubdivideFail)",
            "--ask",
            "f31=shigure_path(F31IdentityOnlyRefuted)",
        ],
    );
    assert_eq!(
        r_ref.code, 1,
        "stdout={}\nstderr={}",
        r_ref.stdout, r_ref.stderr
    );
    let sum_ref = parse(r_ref.stdout.as_bytes()).unwrap();
    for ans in arr(get(&sum_ref, "answers")) {
        assert_eq!(s(get(ans, "status")), "refuted");
    }
}

#[test]
fn shigure_phase2_ac5_transfer_and_composition_via_cli() {
    let dir = workdir("shigure-p2-ac5");
    let def = phase2_fixture("phase2.atoms.json");
    let law = phase2_fixture("transfers.law");
    let map = phase2_fixture("phase2.archmap.json");

    let r_ok = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "g12=shigure_transfer(TransferSuite.G1G2LiftAndWords)",
            "--ask",
            "g3_full=shigure_transfer(G3TwoStepFull)",
            "--ask",
            "g3_sub=shigure_transfer(G3TwoStepProperSubdomain)",
            "--ask",
            "g3_chain=shigure_transfer(G3ThreeStepChain)",
            "--ask",
            "p53_idle=shigure_transfer(P53IdleOk)",
            "--out",
            "ac5_ok",
        ],
    );
    assert_eq!(
        r_ok.code, 0,
        "stdout={}\nstderr={}",
        r_ok.stdout, r_ok.stderr
    );
    assert!(r_ok.stderr.is_empty());
    let sum_ok = parse(r_ok.stdout.as_bytes()).unwrap();
    assert!(!contains_null(&sum_ok));
    let ans_ok = arr(get(&sum_ok, "answers"));
    assert_eq!(ans_ok.len(), 5);

    let g12 = get(get(&ans_ok[0], "outputs"), "shigure");
    assert_eq!(s(get(g12, "verdict")), "established");
    let t_g12 = get(g12, "transfer");
    assert_eq!(s(get(t_g12, "domain_relation")), "full_isomorphic");
    assert!(bool_val(get(
        get(get(t_g12, "restored_transfer"), "reevaluation"),
        "matched"
    )));
    let wc = &arr(get(t_g12, "word_checks"))[0];
    assert!(bool_val(get(wc, "domain_nonempty")));
    assert!(bool_val(get(wc, "state_commutativity_matched")));
    assert!(bool_val(get(wc, "observation_preserved")));
    let lifts = arr(get(t_g12, "old_word_lifts"));
    assert_eq!(lifts.len(), 2);
    assert!(bool_val(get(&lifts[0], "lift_found")));
    assert_eq!(
        str_list(get(&lifts[0], "lifted_new_word")),
        vec!["add_idle(u)"]
    );
    assert!(!bool_val(get(&lifts[1], "lift_found")));

    let g3_full = get(get(get(&ans_ok[1], "outputs"), "shigure"), "transfer");
    assert_eq!(s(get(g3_full, "domain_relation")), "full_isomorphic");

    let g3_sub = get(get(get(&ans_ok[2], "outputs"), "shigure"), "transfer");
    assert_eq!(s(get(g3_sub, "domain_relation")), "proper_subdomain");

    let g3_chain = get(get(get(&ans_ok[3], "outputs"), "shigure"), "transfer");
    assert_eq!(s(get(g3_chain, "domain_relation")), "full_isomorphic");
    assert!(bool_val(get(
        get(get(g3_chain, "restored_transfer"), "reevaluation"),
        "matched"
    )));

    let g3_empty_ok = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &["--ask", "e=shigure_transfer(G3TwoStepEmpty)"],
    );
    assert_eq!(g3_empty_ok.code, 0, "stderr={}", g3_empty_ok.stderr);
    let g3_empty_doc = parse(g3_empty_ok.stdout.as_bytes()).unwrap();
    let empty_tr = get(
        get(
            get(&arr(get(&g3_empty_doc, "answers"))[0], "outputs"),
            "shigure",
        ),
        "transfer",
    );
    assert_eq!(s(get(empty_tr, "domain_relation")), "empty");

    // 反証系: G1 観測一致のみ偽装・proper_subdomain で require_full_domain・P5.3 Busy (0,1,0)
    let r_ref = run_p2(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "obs_only=shigure_transfer(G1ObsOnlyRefuted)",
            "--ask",
            "req_full=shigure_transfer(G3TwoStepRequireFull)",
            "--ask",
            "p53_busy=shigure_transfer(P53BusyRefuted)",
        ],
    );
    assert_eq!(
        r_ref.code, 1,
        "stdout={}\nstderr={}",
        r_ref.stdout, r_ref.stderr
    );
    let r_ref_doc = parse(r_ref.stdout.as_bytes()).unwrap();
    let ans_ref = arr(get(&r_ref_doc, "answers"));
    for a in ans_ref {
        assert_eq!(s(get(a, "status")), "refuted");
    }
    let obs_only = get(get(&ans_ref[0], "outputs"), "shigure");
    assert_eq!(s(get(obs_only, "verdict")), "refuted");
    let obs_wit = get(obs_only, "empty_witness");
    assert!(bool_val(get(obs_wit, "verified")));
    let obs_gens = str_list(get(obs_wit, "generators"));
    assert_eq!(obs_gens.len(), 1, "obs_gens={obs_gens:?}");
    assert!(obs_gens[0] == "1" || obs_gens[0] == "-1");
    let obs_diags = arr(get(get(obs_only, "transfer"), "step_diagnostics"));
    assert_eq!(obs_diags.len(), 1);
    assert!(arr(get(&obs_diags[0], "target_law_residuals")).is_empty());
    let obs_lift_res = str_list(get(&obs_diags[0], "lift_residuals"));
    assert!(
        obs_lift_res.iter().any(|x| *x == "1" || *x == "-1"),
        "obs_lift_res={obs_lift_res:?}"
    );
    let p53 = get(get(&ans_ref[2], "outputs"), "shigure");
    assert!(bool_val(get(get(p53, "empty_witness"), "verified")));
    let diags = arr(get(get(p53, "transfer"), "step_diagnostics"));
    let step2_res = str_list(get(&diags[1], "target_law_residuals"));
    assert!(
        step2_res.iter().any(|x| *x == "-1" || *x == "1"),
        "step2_res={step2_res:?}"
    );

    let saved = parse(&std::fs::read(dir.join("ac5_ok/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert!(!contains_null(&saved));
}

#[test]
fn shigure_phase2_ac6_silence_multi_ask_and_cli_guards() {
    let dir = workdir("shigure-p2-ac6");
    let def = phase2_fixture("phase2.atoms.json");
    let map = phase2_fixture("phase2.archmap.json");
    let diag_law = phase2_fixture("diagrams.law");
    let path_law = phase2_fixture("paths.law");
    let tr_law = phase2_fixture("transfers.law");

    // 1. 非線形 Q_points / 無界 path length / 無界 old_word_lift / Z 商環 / universal_ring の各沈黙（exit 2 / partial）
    for (label, law, ask, expected_silence_code, expected_issue_code) in [
        (
            "qpts",
            &diag_law,
            "q=shigure_diagram(DiagSuite.NonlinearQPointsSilence)",
            "nonlinear_point_existence_out_of_scope",
            "unsupported_algorithm",
        ),
        (
            "unb_path",
            &path_law,
            "p=shigure_path(PathSuite.UnboundedPathSilence)",
            "unbounded_search_out_of_scope",
            "unsupported_algorithm",
        ),
        (
            "unb_lift",
            &tr_law,
            "t=shigure_transfer(TransferSuite.UnboundedOldWordLiftSilence)",
            "unbounded_search_out_of_scope",
            "unsupported_algorithm",
        ),
        (
            "z_quot",
            &tr_law,
            "z=shigure_transfer(TransferSuite.ZQuotientSilence)",
            "quotient_ideal_out_of_scope",
            "unsupported_algorithm",
        ),
        (
            "univ_ring",
            &diag_law,
            "u=shigure_diagram(DiagSuite.UniversalRingSilence)",
            "applicability_condition_not_met",
            "unsupported_algorithm",
        ),
    ] {
        let r = run_p2(&dir, &def, law, &map, &["--ask", ask]);
        assert_eq!(
            r.code, 2,
            "{label}: stdout={}\nstderr={}",
            r.stdout, r.stderr
        );
        assert!(
            r.stderr.is_empty(),
            "{label} unexpected stderr={}",
            r.stderr
        );
        let sum = parse(r.stdout.as_bytes()).unwrap();
        assert_eq!(s(get(&sum, "status")), "partial");
        let ans0 = &arr(get(&sum, "answers"))[0];
        let sh = get(get(ans0, "outputs"), "shigure");
        assert_eq!(s(get(sh, "verdict")), "undetermined");
        assert_eq!(
            s(get(get(sh, "silence_reason"), "code")),
            expected_silence_code
        );
        let reasons = arr(get(ans0, "reasons"));
        assert_eq!(reasons.len(), 1, "{label}: reasons={}", reasons.len());
        assert_eq!(s(get(&reasons[0], "code")), expected_issue_code);
        assert_eq!(
            s(get(get(&reasons[0], "details"), "code")),
            expected_silence_code
        );
    }

    // 2. 未観測座標（balance 欠落 ArchMap）-> unobserved_dependency / exit 2
    let raw_map = std::fs::read_to_string(&map).unwrap();
    let missing_map = dir.join("missing_balance.archmap.json");
    let stripped = raw_map.replace(
        r#"        {
          "id": "a_bal",
          "subject": "acc1",
          "field": "Phase2Vocab.Account.balance",
          "value": ["2", "1"],
          "origin": "o_static"
        },
"#,
        "",
    );
    assert_ne!(stripped, raw_map);
    std::fs::write(&missing_map, &stripped).unwrap();
    let r_miss = run_p2(
        &dir,
        &def,
        &diag_law,
        &missing_map,
        &[
            "--ask",
            "obs=shigure_diagram(DiagSuite.ObservedCoordDiagram)",
        ],
    );
    assert_eq!(
        r_miss.code, 2,
        "stdout={}\nstderr={}",
        r_miss.stdout, r_miss.stderr
    );
    let r_miss_doc = parse(r_miss.stdout.as_bytes()).unwrap();
    let miss_ans0 = &arr(get(&r_miss_doc, "answers"))[0];
    let miss_sh = get(get(miss_ans0, "outputs"), "shigure");
    assert_eq!(s(get(miss_sh, "verdict")), "undetermined");
    assert_eq!(
        s(get(get(miss_sh, "silence_reason"), "code")),
        "unobserved_dependency"
    );
    let miss_reasons = arr(get(miss_ans0, "reasons"));
    assert_eq!(miss_reasons.len(), 1);
    assert_eq!(s(get(&miss_reasons[0], "code")), "unobserved");
    assert_eq!(
        s(get(get(&miss_reasons[0], "details"), "code")),
        "unobserved_dependency"
    );

    // 3. 1 回の `archsig run` へ 3 種（diagram + path + transfer）＋ `--reuse` 警告 ＋ `--out` 保存
    let multi_law = dir.join("multi.law");
    let digest = "sha256:3c4d12e5b45460e139353d29832053551ec840b1e905e3c876476d9db9b7bd69";
    std::fs::write(
        &multi_law,
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading MultiBase {{
  use vocabulary Phase2Vocab version "1" digest "{digest}";
  shigure presentation P {{
    domain Q; sort D;
    phase S {{ coord x: D; coord bal: D observed Phase2Vocab.Account.balance; }}
    op step(): S -> S {{ x = x; bal = bal; }}
    obs r on S = (x);
  }}
}}
reading MultiRun {{
  use MultiBase as B;
  shigure change_spec H {{ domain Q; }}
  shigure diagram Dg {{ direction state_map; vertex fixed V0: B.P; edge fixed e: V0 -> V0 {{ identity; }} change_spec H; }}
  shigure path Pa {{ kind fixed_protocol_change_path; direction state_map; length 0; vertex V0: B.P; start V0; end V0; change_spec H; }}
  shigure transfer Tr {{ step s1 {{ before B.P; after B.P; identity; source_phase S; target_phase S; lift {{ x = x; bal = bal; }} }} change_spec H; }}
}}
"#
        ),
    )
    .unwrap();
    let r_multi = run_p2(
        &dir,
        &def,
        &multi_law,
        &map,
        &[
            "--reuse",
            dir.to_str().unwrap(),
            "--ask",
            "d=shigure_diagram(MultiRun.Dg)",
            "--ask",
            "p=shigure_path(MultiRun.Pa)",
            "--ask",
            "t=shigure_transfer(MultiRun.Tr)",
            "--out",
            "multi_out",
        ],
    );
    assert_eq!(
        r_multi.code, 0,
        "stdout={}\nstderr={}",
        r_multi.stdout, r_multi.stderr
    );
    let msum = parse(r_multi.stdout.as_bytes()).unwrap();
    assert_eq!(arr(get(&msum, "answers")).len(), 3);
    let warnings = arr(get(&msum, "warnings"));
    assert_eq!(warnings.len(), 1);
    assert_eq!(s(get(get(&warnings[0], "details"), "argument")), "--reuse");
    let msaved = parse(&std::fs::read(dir.join("multi_out/result.json")).unwrap()).unwrap();
    assert!(!contains_null(&msaved));
    for ans in arr(get(&msaved, "answers")) {
        assert_eq!(
            str_list(get(get(ans, "scope"), "readings")),
            vec!["MultiBase", "MultiRun"]
        );
    }

    // 4. exit 64 ガード（混在問い・未知宣言名・未知 snapshot・重複 ID・不正構文）
    for bad_args in [
        vec![
            "--ask",
            "a=evaluate(MultiRun.x,s=@snap1/acc1)",
            "--ask",
            "d=shigure_diagram(MultiRun.Dg)",
        ],
        vec!["--ask", "p=shigure_path(MultiRun.NoSuchPath)"],
        vec!["--ask", "t=shigure_transfer(MultiRun.Tr, snapshot=no_snap)"],
        vec![
            "--ask",
            "dup=shigure_diagram(MultiRun.Dg)",
            "--ask",
            "dup=shigure_transfer(MultiRun.Tr)",
        ],
        vec!["--ask", "bad=shigure_path()"],
    ] {
        let mut cmd = vec![
            "run",
            "--atom-definition",
            def.to_str().unwrap(),
            "--law",
            multi_law.to_str().unwrap(),
            "--archmap",
            map.to_str().unwrap(),
        ];
        cmd.extend(bad_args);
        let r_bad = run_binary(&dir, &cmd);
        assert_eq!(r_bad.code, 64, "cmd={cmd:?}\nstderr={}", r_bad.stderr);
        assert!(r_bad.stdout.is_empty());
    }

    // 5. Origin.kind 省略の ArchMap を Phase 2 observed 座標へ結合すると exit 65
    let no_kind_map = dir.join("no_kind.archmap.json");
    let no_kind = raw_map.replace("      \"kind\": \"static_analysis\",\n", "");
    assert_ne!(no_kind, raw_map);
    std::fs::write(&no_kind_map, &no_kind).unwrap();
    let r_legacy = run_p2(
        &dir,
        &def,
        &diag_law,
        &no_kind_map,
        &[
            "--ask",
            "obs=shigure_diagram(DiagSuite.ObservedCoordDiagram)",
        ],
    );
    assert_eq!(r_legacy.code, 65, "stderr={}", r_legacy.stderr);
    assert!(r_legacy.stdout.is_empty());
}
