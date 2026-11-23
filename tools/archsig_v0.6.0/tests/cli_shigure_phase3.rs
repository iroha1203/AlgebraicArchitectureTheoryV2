//! SHIGURE Phase 3（複数解釈族・頑健判定・Chevalley 四分類・追加観測）CLI E2E 統合テスト。

use crate::common::cli::{BinaryRun, arr, consistent, get, has, num, run_binary, s, workdir};
use archsig_common::json::{JNode, JValue, parse};
use std::path::{Path, PathBuf};

fn phase3_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-phase3")
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
        JValue::Bool(b) => *b,
        other => panic!("expected bool, got {other:?}"),
    }
}

fn str_list(node: &JNode) -> Vec<String> {
    arr(node).iter().map(|n| s(n).to_owned()).collect()
}

fn run_p3(dir: &Path, def: &Path, law: &Path, map: &Path, extra: &[&str]) -> BinaryRun {
    let mut args = vec![
        "run",
        "--atom-definition",
        def.to_str().unwrap(),
        "--law",
        law.to_str().unwrap(),
        "--archmap",
        map.to_str().unwrap(),
    ];
    args.extend(extra);
    run_binary(dir, &args)
}

#[test]
fn shigure_phase3_ac1_check_accepts_all_fixtures_and_rejects_invalid_phase3_laws() {
    let dir = workdir("shigure-p3-ac1");
    let def = phase3_fixture("phase3.atoms.json");
    let map = phase3_fixture("phase3.archmap.json");

    for (idx, law_name) in [
        "robustness.law",
        "chevalley.law",
        "observations.law",
        "silence.law",
    ]
    .iter()
    .enumerate()
    {
        let out_dir = dir.join(format!("check_out_{idx}"));
        let ok = run_binary(
            &dir,
            &[
                "check",
                "--atom-definition",
                def.to_str().unwrap(),
                "--law",
                phase3_fixture(law_name).to_str().unwrap(),
                "--archmap",
                map.to_str().unwrap(),
                "--out",
                out_dir.to_str().unwrap(),
            ],
        );
        let saved = consistent(&dir, &ok, "complete", 0);
        assert_eq!(s(get(&saved, "format")), "archsig.result/4");
        assert!(!contains_null(&saved));
    }

    let digest = "sha256:9ca606765399fff56548db031f6bec968722a0d2c8ef573bd3a4426f148b1a41";
    let base_fam = r#"
  shigure family F {
    domain Q;
    realizations U { u_vars [u]; b_vars [b]; reading_q [0]; member u0 { origin static_analysis "o-u"; set u = 0; } }
    candidates C { c_vars [c]; pi [0]; member c0 { origin human_adopted "o-c"; set c = 0; } }
    goodness direct { equation eq: u - c = 0; }
  }"#;
    let invalid_bodies = [
        // 結論注入（robustness / chevalley / observations）
        format!(
            "{base_fam} shigure robustness R {{ family F; point_domain rational_points; base_value [0]; robust_all_pass = []; }}"
        ),
        format!(
            "{base_fam} shigure chevalley Ch {{ family F; point_domain algebraic_closure; distinguishing_pairs = []; }}"
        ),
        format!(
            "{base_fam} shigure observations Ob {{ family F; point_domain rational_points; base_value [0]; minimal_sufficient_sets = []; observe e {{ origin static_analysis \"oe\"; component v: u; }} }}"
        ),
        // universal_ring トップレベル拒否・chevalley 非閉包・負 cost・空 witness_vars
        format!(
            "{base_fam} shigure robustness R {{ family F; point_domain universal_ring; base_value [0]; }}"
        ),
        format!("{base_fam} shigure chevalley Ch {{ family F; point_domain rational_points; }}"),
        format!(
            "{base_fam} shigure observations Ob {{ family F; point_domain rational_points; base_value [0]; observe e {{ origin static_analysis \"oe\"; cost -1; component v: u; }} }}"
        ),
        r#"
  shigure family EmptyW {
    domain Q;
    realizations U { u_vars [u]; b_vars []; reading_q []; member u0 { origin static_analysis "o-u"; set u = 0; } }
    candidates C { c_vars [c]; pi []; member c0 { origin human_adopted "o-c"; set c = 0; } }
    goodness existential { witness_vars []; equation eq: u = 0; }
  }"#
            .to_owned(),
        // before 側編集を含む preservation 参照
        r#"
  shigure presentation B { domain Q; sort N; phase S { coord x: N; } op act(): S -> S { x = x; } obs q on S = (x); }
  shigure presentation A { domain Q; sort N; phase S { coord x: N; } op act(): S -> S { x = x; } obs q on S = (x); }
  shigure comparison Cmp { before B; after A; state_map S -> S { x = x; } translate act -> [act()]; }
  shigure change_spec BadSpec { domain Q; editable op B.act; }
  shigure family BadPres {
    domain Q;
    realizations U { u_vars [u]; b_vars [b]; reading_q [0]; member u0 { origin static_analysis "o-u"; set u = 0; } }
    candidates C { c_vars [c]; pi [0]; member c0 { origin human_adopted "o-c"; set c = 0; } }
    goodness direct { preservation { comparison Cmp; change_spec BadSpec; } }
  }"#
            .to_owned(),
    ];

    for (idx, body) in invalid_bodies.iter().enumerate() {
        let bad_law = dir.join(format!("invalid_p3_{idx}.law"));
        std::fs::write(
            &bad_law,
            format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Bad{idx} {{\n  use vocabulary Phase3Vocab version \"1\" digest \"{digest}\";\n{body}\n}}\n"
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
fn shigure_phase3_ac3_robustness_and_provenance_via_cli() {
    let dir = workdir("shigure-p3-ac3");
    let def = phase3_fixture("phase3.atoms.json");
    let law = phase3_fixture("robustness.law");
    let map = phase3_fixture("phase3.archmap.json");

    // 1. 成立系: 存在型 E_exists witness 復元・再評価 + ArchMap 複数由来と scope.modes
    let ok = run_p3(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "ex=shigure_robustness(RobustnessSuite.ExistentialRob)",
            "--ask",
            "prov=shigure_robustness(RobustnessSuite.ProvenanceRob, snapshot=snap1)",
            "--out",
            "ac3_ok",
        ],
    );
    assert_eq!(ok.code, 0, "stdout={}\nstderr={}", ok.stdout, ok.stderr);
    assert!(ok.stderr.is_empty());
    let sum = parse(ok.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&sum, "format")), "archsig.summary/1");
    assert_eq!(s(get(&sum, "status")), "complete");
    assert!(!contains_null(&sum));

    let ans = arr(get(&sum, "answers"));
    let ex_out = get(get(&ans[0], "outputs"), "shigure");
    assert_eq!(s(get(ex_out, "verdict")), "established");
    let ex_w = &arr(get(
        get(get(ex_out, "robustness"), "pointwise"),
        "witnesses",
    ))[0];
    let rc = get(ex_w, "restored_completion");
    assert_eq!(s(get(get(rc, "witness_assignments"), "w")), "2");
    assert!(bool_val(get(get(rc, "reevaluation"), "checked")));
    assert!(bool_val(get(get(rc, "reevaluation"), "matched")));
    assert_eq!(
        s(get(get(rc, "reevaluation"), "scope")),
        "mathematical_model_reevaluation"
    );

    let prov_out = get(get(&ans[1], "outputs"), "shigure");
    assert_eq!(s(get(prov_out, "verdict")), "established");
    let origins = arr(get(get(prov_out, "provenance"), "origins"));
    assert!(origins.iter().any(|o| {
        s(get(o, "kind")) == "static_analysis" && s(get(o, "path")) == "src/service.rs"
    }));
    assert!(origins.iter().any(|o| {
        s(get(o, "kind")) == "runtime_observation" && s(get(o, "path")) == "src/runtime.rs"
    }));
    assert!(origins.iter().any(|o| s(get(o, "kind")) == "llm_candidate"));
    assert!(origins.iter().any(|o| s(get(o, "kind")) == "human_adopted"));

    let saved = parse(&std::fs::read(dir.join("ac3_ok/result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert!(!contains_null(&saved));
    assert!(dir.join("ac3_ok/inputs/definitions/0.json").is_file());
    assert!(dir.join("ac3_ok/inputs/law.law").is_file());
    assert!(dir.join("ac3_ok/inputs/archmap.json").is_file());
    let saved_ans = arr(get(&saved, "answers"));
    assert_eq!(
        str_list(get(get(&saved_ans[1], "scope"), "modes")),
        vec!["observed", "proposed", "specification"]
    );

    // 2. 反証系: W4 3 量化分離・空 fiber 分離・R(R) 分離・P7 raw 候補・cross-reading scope
    let ref_run = run_p3(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "w4=shigure_robustness(RobustnessSuite.W4Separation)",
            "--ask",
            "ef=shigure_robustness(RobustnessSuite.EmptyFiberRob)",
            "--ask",
            "ufp=shigure_robustness(RobustnessSuite.UnivFpRob)",
            "--ask",
            "w6=shigure_robustness(RobustnessSuite.W6DualRob)",
            "--ask",
            "p7=shigure_robustness(RobustnessSuite.P7Rob)",
            "--out",
            "ac3_ref",
        ],
    );
    assert_eq!(ref_run.code, 1, "stdout={}", ref_run.stdout);
    let rsum = parse(ref_run.stdout.as_bytes()).unwrap();
    let rans = arr(get(&rsum, "answers"));

    let w4_rob = get(get(get(&rans[0], "outputs"), "shigure"), "robustness");
    assert!(bool_val(get(get(w4_rob, "pointwise"), "satisfied")));
    assert!(!bool_val(get(get(w4_rob, "valid_designated"), "satisfied")));
    assert!(!bool_val(get(get(w4_rob, "common_candidate"), "satisfied")));

    let ef_rob = get(get(get(&rans[1], "outputs"), "shigure"), "robustness");
    assert!(!bool_val(get(get(ef_rob, "fiber_non_empty"), "non_empty")));
    assert!(bool_val(get(
        get(ef_rob, "pointwise"),
        "vacuously_true_empty_fiber"
    )));

    let ufp_rob = get(get(get(&rans[2], "outputs"), "shigure"), "robustness");
    assert!(bool_val(get(get(ufp_rob, "pointwise"), "satisfied")));
    assert!(!bool_val(get(get(ufp_rob, "universal_ring"), "stable")));

    let w6_rob = get(get(get(&rans[3], "outputs"), "shigure"), "robustness");
    assert!(bool_val(get(get(w6_rob, "pointwise"), "satisfied")));
    let w6_ur = get(w6_rob, "universal_ring");
    assert!(!bool_val(get(w6_ur, "stable")));
    assert_eq!(
        s(get(
            get(get(w6_ur, "dual_number_counterexample"), "assignments"),
            "rho"
        )),
        "1 + eps"
    );

    let p7_rob = get(get(get(&rans[4], "outputs"), "shigure"), "robustness");
    let rcmp = get(p7_rob, "reading_comparison");
    assert!(bool_val(get(rcmp, "commutativity_verified")));
    assert!(bool_val(get(rcmp, "coarse_implies_fine_preserved")));
    let raw_evals = arr(get(rcmp, "raw_candidate_evaluations"));
    assert_eq!(raw_evals.len(), 2);
    assert!(!bool_val(get(&raw_evals[0], "passed")));
    assert!(bool_val(get(&raw_evals[1], "passed")));

    let rsaved = parse(&std::fs::read(dir.join("ac3_ref/result.json")).unwrap()).unwrap();
    let rsaved_ans = arr(get(&rsaved, "answers"));
    assert_eq!(
        str_list(get(get(&rsaved_ans[0], "scope"), "readings")),
        vec!["Phase3Base", "RobustnessSuite"]
    );
}

#[test]
fn shigure_phase3_ac4_chevalley_and_ac5_observations_via_cli() {
    let dir = workdir("shigure-p3-ac45");
    let def = phase3_fixture("phase3.atoms.json");
    let map = phase3_fixture("phase3.archmap.json");

    // 1. Chevalley 成立系: 4 領域 + mixed_witness_pair + W5 有理 probe / Laurent 障害 + W6 対照
    let chev_ok = run_p3(
        &dir,
        &def,
        &phase3_fixture("chevalley.law"),
        &map,
        &[
            "--ask",
            "four=shigure_chevalley(ChevalleySuite.FourRegionsChev)",
            "--ask",
            "w5=shigure_chevalley(ChevalleySuite.W5Chev)",
            "--ask",
            "w6=shigure_chevalley(ChevalleySuite.W6Chev)",
        ],
    );
    assert_eq!(chev_ok.code, 0, "stdout={}", chev_ok.stdout);
    let csum = parse(chev_ok.stdout.as_bytes()).unwrap();
    let cans = arr(get(&csum, "answers"));

    let four = get(get(get(&cans[0], "outputs"), "shigure"), "chevalley");
    for region in ["robust_all_pass", "all_fail", "mixed", "empty_realizations"] {
        assert!(!bool_val(get(get(four, region), "is_empty")), "{region}");
    }
    let mwp = get(four, "mixed_witness_pair");
    assert!(bool_val(get(get(mwp, "pass_witness"), "passed")));
    assert!(!bool_val(get(get(mwp, "fail_witness"), "passed")));

    let w5 = get(get(get(&cans[1], "outputs"), "shigure"), "chevalley");
    let probes = arr(get(w5, "rational_fiber_probes"));
    assert_eq!(s(get(&probes[0], "verdict")), "established");
    assert_eq!(s(get(&probes[1], "verdict")), "refuted");
    assert!(!bool_val(get(get(w5, "global_regular_section"), "exists")));

    let w6 = get(get(get(&cans[2], "outputs"), "shigure"), "chevalley");
    assert_eq!(s(get(w6, "designated_candidate_class")), "robust_all_pass");
    assert!(!bool_val(get(get(w6, "universal_ring_contrast"), "stable")));

    // 2. D6 構成可能像 D(x) (閉包 A^1 ではない)
    let d6_run = run_p3(
        &dir,
        &def,
        &phase3_fixture("chevalley.law"),
        &map,
        &["--ask", "d6=shigure_chevalley(ChevalleySuite.D6Chev)"],
    );
    assert_eq!(d6_run.code, 1, "stdout={}", d6_run.stdout);
    let d6_sum = parse(d6_run.stdout.as_bytes()).unwrap();
    let d6_eff = get(
        get(
            get(get(&arr(get(&d6_sum, "answers"))[0], "outputs"), "shigure"),
            "chevalley",
        ),
        "effective_image_e",
    );
    let d6_strata = arr(get(d6_eff, "strata"));
    assert!(d6_strata.iter().any(|st| {
        str_list(get(st, "equations")) == vec!["c"] && str_list(get(st, "invertibles")) == vec!["x"]
    }));

    // 3. 追加観測 AC5: W4 2 包含極小集合 + removal_counterexamples + 費用順 + 空解
    let obs_law = phase3_fixture("observations.law");
    let obs_ok = run_p3(
        &dir,
        &def,
        &obs_law,
        &map,
        &[
            "--ask",
            "w4=shigure_observations(ObsSuite.W4Obs)",
            "--ask",
            "nd=shigure_observations(ObsSuite.NoDiffObs)",
        ],
    );
    assert_eq!(obs_ok.code, 0, "stdout={}", obs_ok.stdout);
    let osum = parse(obs_ok.stdout.as_bytes()).unwrap();
    let oans = arr(get(&osum, "answers"));

    let o_w4 = get(get(get(&oans[0], "outputs"), "shigure"), "observations");
    assert!(bool_val(get(o_w4, "sufficient")));
    let mins = arr(get(o_w4, "minimal_sufficient_sets"));
    assert_eq!(mins.len(), 2);
    assert_eq!(str_list(get(&mins[0], "observations")), vec!["e1"]);
    assert_eq!(arr(get(&mins[0], "removal_counterexamples")).len(), 1);
    assert_eq!(str_list(get(&mins[1], "observations")), vec!["e2", "e3"]);
    assert_eq!(arr(get(&mins[1], "removal_counterexamples")).len(), 2);
    let ranked = arr(get(o_w4, "cost_ranked_sets"));
    assert_eq!(num(get(&ranked[0], "rank")), 1);
    assert_eq!(str_list(get(&ranked[0], "observations")), vec!["e2", "e3"]);
    assert_eq!(s(get(&ranked[0], "total_cost")), "5");
    assert_eq!(num(get(&ranked[1], "rank")), 2);
    assert_eq!(str_list(get(&ranked[1], "observations")), vec!["e1"]);
    assert_eq!(s(get(&ranked[1], "total_cost")), "10");

    let o_nd = get(get(get(&oans[1], "outputs"), "shigure"), "observations");
    let nd_mins = arr(get(o_nd, "minimal_sufficient_sets"));
    assert_eq!(nd_mins.len(), 1);
    assert!(arr(get(&nd_mins[0], "observations")).is_empty());

    // 4. 追加観測 反証: 不足 witness + W6 law_readout 対照
    let obs_ref = run_p3(
        &dir,
        &def,
        &obs_law,
        &map,
        &[
            "--ask",
            "ins=shigure_observations(ObsSuite.InsufficientObs)",
            "--ask",
            "w6=shigure_observations(ObsSuite.W6ObsInsuff)",
        ],
    );
    assert_eq!(obs_ref.code, 1, "stdout={}", obs_ref.stdout);
    let orsum = parse(obs_ref.stdout.as_bytes()).unwrap();
    let orans = arr(get(&orsum, "answers"));
    let o_ins = get(get(get(&orans[0], "outputs"), "shigure"), "observations");
    assert!(!bool_val(get(o_ins, "sufficient")));
    assert!(has(o_ins, "insufficiency_witness"));
    let o_w6 = get(get(get(&orans[1], "outputs"), "shigure"), "observations");
    let lrc = get(o_w6, "law_readout_comparison");
    assert!(bool_val(get(lrc, "coarse_adequate_for_law_readout")));
    assert!(!bool_val(get(lrc, "coarse_adequate_for_decision")));
}

#[test]
fn shigure_phase3_ac6_silence_multi_ask_and_exit_guards_via_cli() {
    let dir = workdir("shigure-p3-ac6");
    let def = phase3_fixture("phase3.atoms.json");
    let map = phase3_fixture("phase3.archmap.json");

    // 1. 沈黙境界: 未観測座標依存 + 非線形有理点存在範囲外 -> exit 2 / status partial
    let sil = run_p3(
        &dir,
        &def,
        &phase3_fixture("silence.law"),
        &map,
        &[
            "--ask",
            "miss=shigure_robustness(SilenceSuite.MissingObsRob, snapshot=snap_missing)",
            "--ask",
            "nl=shigure_robustness(SilenceSuite.NonlinearRob, snapshot=snap1)",
        ],
    );
    assert_eq!(sil.code, 2, "stdout={}\nstderr={}", sil.stdout, sil.stderr);
    let ssum = parse(sil.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&ssum, "status")), "partial");
    let sans = arr(get(&ssum, "answers"));
    assert_eq!(
        s(get(
            get(get(get(&sans[0], "outputs"), "shigure"), "silence_reason"),
            "code"
        )),
        "unobserved_dependency"
    );
    assert_eq!(
        s(get(
            get(get(get(&sans[1], "outputs"), "shigure"), "silence_reason"),
            "code"
        )),
        "nonlinear_point_existence_out_of_scope"
    );

    // 2. 同一 run で robustness + chevalley + observations 同時実行（cross-reading・--reuse 警告）
    let digest = "sha256:9ca606765399fff56548db031f6bec968722a0d2c8ef573bd3a4426f148b1a41";
    let multi_law = dir.join("multi_p3.law");
    std::fs::write(
        &multi_law,
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading MultiBase {{
  use vocabulary Phase3Vocab version "1" digest "{digest}";
  shigure family F {{
    domain Q;
    realizations U {{ u_vars [u]; b_vars [b]; reading_q [0]; member u0 {{ origin static_analysis "mu"; set u = 0; }} }}
    candidates C {{ c_vars [c]; pi [0]; member c0 {{ origin human_adopted "mc"; set c = 0; }} }}
    goodness direct {{ equation ok: u - c = 0; }}
  }}
}}
reading MultiRunP3 {{
  use MultiBase as Base;
  shigure robustness Rob {{ family Base.F; point_domain rational_points; base_value [0]; }}
  shigure chevalley Ch {{ family Base.F; point_domain algebraic_closure; }}
  shigure observations Obs {{
    family Base.F;
    point_domain rational_points;
    base_value [0];
    observe e0 {{ origin static_analysis "me"; component v: u; }}
  }}
}}
"#
        ),
    )
    .unwrap();
    let mrun = run_p3(
        &dir,
        &def,
        &multi_law,
        &map,
        &[
            "--reuse",
            dir.to_str().unwrap(),
            "--ask",
            "r=shigure_robustness(MultiRunP3.Rob)",
            "--ask",
            "c=shigure_chevalley(MultiRunP3.Ch)",
            "--ask",
            "o=shigure_observations(MultiRunP3.Obs)",
            "--out",
            "multi_p3_out",
        ],
    );
    assert_eq!(
        mrun.code, 0,
        "stdout={}\nstderr={}",
        mrun.stdout, mrun.stderr
    );
    let msum = parse(mrun.stdout.as_bytes()).unwrap();
    assert_eq!(arr(get(&msum, "answers")).len(), 3);
    assert_eq!(arr(get(&msum, "warnings")).len(), 1);
    let msaved = parse(&std::fs::read(dir.join("multi_p3_out/result.json")).unwrap()).unwrap();
    for a in arr(get(&msaved, "answers")) {
        assert_eq!(
            str_list(get(get(a, "scope"), "readings")),
            vec!["MultiBase", "MultiRunP3"]
        );
    }

    // 3. exit 64 ガード（混在・未知宣言・未知 snapshot・重複 ID・不正構文）
    for bad in [
        vec![
            "--ask",
            "a=evaluate(MultiRunP3.u, s=@snap1/svc1)",
            "--ask",
            "r=shigure_robustness(MultiRunP3.Rob)",
        ],
        vec!["--ask", "r=shigure_robustness(MultiRunP3.NoSuchRob)"],
        vec![
            "--ask",
            "c=shigure_chevalley(MultiRunP3.Ch, snapshot=no_snap)",
        ],
        vec![
            "--ask",
            "dup=shigure_robustness(MultiRunP3.Rob)",
            "--ask",
            "dup=shigure_observations(MultiRunP3.Obs)",
        ],
        vec!["--ask", "bad=shigure_chevalley()"],
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
        cmd.extend(bad);
        let r_bad = run_binary(&dir, &cmd);
        assert_eq!(r_bad.code, 64, "cmd={cmd:?}\nstderr={}", r_bad.stderr);
        assert!(r_bad.stdout.is_empty());
    }

    // 4. ArchMap Origin.kind 省略を observed 座標へ結合すると exit 65
    let raw_map = std::fs::read_to_string(&map).unwrap();
    let no_kind_map = dir.join("no_kind.archmap.json");
    let stripped = raw_map.replace("      \"kind\": \"static_analysis\",\n", "");
    assert_ne!(stripped, raw_map);
    std::fs::write(&no_kind_map, stripped).unwrap();
    let r_kind = run_p3(
        &dir,
        &def,
        &phase3_fixture("robustness.law"),
        &no_kind_map,
        &[
            "--ask",
            "prov=shigure_robustness(RobustnessSuite.ProvenanceRob, snapshot=snap1)",
        ],
    );
    assert_eq!(r_kind.code, 65, "stderr={}", r_kind.stderr);
    assert!(r_kind.stdout.is_empty());
}
