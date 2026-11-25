//! SHIGURE Phase 4（全 syzygy 平方零 lift・Artin 試験・診断層・Atlas 細分化）実バイナリ CLI E2E 統合テスト（AC3–AC7）。

use crate::common::cli::{BinaryRun, arr, consistent, get, has, num, run_binary, s, workdir};
use archsig_common::json::{JNode, JValue, parse};
use std::path::{Path, PathBuf};

fn phase4_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-phase4")
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

fn run_p4(dir: &Path, def: &Path, law: &Path, map: &Path, extra: &[&str]) -> BinaryRun {
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

fn answer_shigure<'a>(summary: &'a JNode, id: &str) -> &'a JNode {
    let ans = arr(get(summary, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap_or_else(|| panic!("answer `{id}` not found"));
    get(get(ans, "outputs"), "shigure")
}

fn verify_run_output(run: &BinaryRun, out_dir: &Path, status: &str, code: i32) -> (JNode, JNode) {
    assert_eq!(
        run.code, code,
        "stdout={}\nstderr={}",
        run.stdout, run.stderr
    );
    assert!(run.stderr.is_empty(), "stderr={}", run.stderr);
    let summary = parse(run.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&summary, "format")), "archsig.summary/1");
    assert_eq!(s(get(&summary, "status")), status);
    assert_eq!(num(get(&summary, "exit_code")), code as u64);
    assert!(!contains_null(&summary));

    let saved_bytes = std::fs::read(out_dir.join("result.json")).unwrap();
    let saved = parse(&saved_bytes).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert_eq!(s(get(&saved, "command")), "run");
    assert_eq!(s(get(&saved, "status")), status);
    assert_eq!(num(get(&saved, "exit_code")), code as u64);
    assert!(!contains_null(&saved));
    (summary, saved)
}

#[test]
fn shigure_phase4_ac2_check_accepts_all_fixtures_and_rejects_conclusion_injection() {
    let dir = workdir("shigure-p4-ac2");
    let def = phase4_fixture("phase4.atoms.json");
    let map = phase4_fixture("phase4.archmap.json");

    for (idx, law_name) in [
        "lift.law",
        "artin.law",
        "diagnostics.law",
        "atlas.law",
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
                phase4_fixture(law_name).to_str().unwrap(),
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

    let digest = "sha256:c4c4f5bb0c50bcec155a48e2a1402387df5e89c00fe063a568895c9a439c6f83";
    let bad_bodies = [
        r#"shigure lift Bad1 { domain Q; origin human_adopted "o"; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } syzygy_generators []; }"#,
        r#"shigure artin Bad2 { domain Q; origin human_adopted "o"; obs_vars [t]; base_point { t = 0; } max_order 4; detection_order 2; }"#,
        r#"shigure diagnostics Bad3 { diagnostic_coeff Z; origin human_adopted "o"; nerve { chart c0 [s0]; } static_readout { sources [s0]; targets [s0]; reading { s0 -> s0; } } h1_free_rank 1; }"#,
        r#"shigure atlas Bad4 { domain Z; origin human_adopted "o"; vertices [v0, v1]; edge e01 (v0 -> v1) offset 0; mu 1; base_lambdas { v0 = 0; v1 = 0; } condition_c true; }"#,
        // origin 欠落
        r#"shigure lift NoOrig { domain Q; vars [x]; extension truncated(eps, 0); base_point { x = [0]; } }"#,
    ];
    for (idx, body) in bad_bodies.iter().enumerate() {
        let bad_law = dir.join(format!("invalid_p4_{idx}.law"));
        std::fs::write(
            &bad_law,
            format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Bad{idx} {{\n  use vocabulary Phase4Vocab version \"1\" digest \"{digest}\";\n  {body}\n}}\n"
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
        assert!(r.stdout.is_empty());
        let receipt = parse(r.stderr.as_bytes()).unwrap();
        assert_eq!(s(get(&receipt, "status")), "invalid");
    }
}

#[test]
fn shigure_phase4_ac3_lift_h1_h2_h3_h4_h10_e7_c9_via_cli() {
    let dir = workdir("shigure-p4-ac3");
    let def = phase4_fixture("phase4.atoms.json");
    let law = phase4_fixture("lift.law");
    let map = phase4_fixture("phase4.archmap.json");
    let out_dir = dir.join("out_lift");

    let run = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "h1_full=shigure_lift(LiftAC3.H1Full, snapshot=snap1)",
            "--ask",
            "h1_fix_d=shigure_lift(H1FixD)",
            "--ask",
            "h1_fix_all=shigure_lift(H1FixAll)",
            "--ask",
            "h2_q=shigure_lift(H2RedundantQ)",
            "--ask",
            "h2_lin=shigure_lift(H2LinearFree)",
            "--ask",
            "h2_z=shigure_lift(H2RedundantZ)",
            "--ask",
            "h2_f2=shigure_lift(H2RedundantF2)",
            "--ask",
            "h3_dep=shigure_lift(H3Dependent)",
            "--ask",
            "h3_reg=shigure_lift(H3Regular)",
            "--ask",
            "h4=shigure_lift(H4RelativeCone)",
            "--ask",
            "h10_fail=shigure_lift(H10SnapshotFail)",
            "--ask",
            "h10_snap=shigure_lift(H10FinishSnap)",
            "--ask",
            "e7_split=shigure_lift(E7UnclosedCover)",
            "--ask",
            "e7_merged=shigure_lift(E7MergedCover)",
            "--ask",
            "c9=shigure_lift(C9EtaleW5)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    // Refuted を含むため exit 1 / complete
    let (summary, _saved) = verify_run_output(&run, &out_dir, "complete", 1);

    // (a) H1
    let h1_full = get(answer_shigure(&summary, "h1_full"), "lift");
    assert!(bool_val(get(
        get(h1_full, "affine_repair"),
        "repair_exists"
    )));
    assert_eq!(
        arr(get(get(h1_full, "affine_repair"), "torsor_basis")).len(),
        1
    );
    assert!(bool_val(get(
        get(get(h1_full, "affine_repair"), "reevaluation"),
        "matched"
    )));
    let h1_fix_d = get(answer_shigure(&summary, "h1_fix_d"), "lift");
    assert!(bool_val(get(
        get(h1_fix_d, "affine_repair"),
        "repair_exists"
    )));
    assert!(arr(get(get(h1_fix_d, "affine_repair"), "torsor_basis")).is_empty());
    let h1_fix_all = get(answer_shigure(&summary, "h1_fix_all"), "lift");
    assert!(!bool_val(get(
        get(h1_fix_all, "affine_repair"),
        "repair_exists"
    )));

    // (b) H2 (Q, Z, F_2) + linear free
    for id in ["h2_q", "h2_z", "h2_f2"] {
        let out = answer_shigure(&summary, id);
        assert_eq!(s(get(out, "verdict")), "refuted");
        let l = get(out, "lift");
        assert!(bool_val(get(l, "syzygy_identity_verified")));
        assert!(bool_val(get(l, "complex_d1_d0_zero_verified")));
        let red = get(l, "redundant_comparison");
        assert!(bool_val(get(red, "h0_matches")));
        assert!(bool_val(get(red, "h1_matches")));
        assert!(bool_val(get(red, "obstruction_matches")));
    }
    let h2_lin = get(answer_shigure(&summary, "h2_lin"), "lift");
    assert!(bool_val(get(h2_lin, "lift_exists")));

    // (c) H3: H^1(T_raw) vs H^1(D)
    let h3_dep = get(answer_shigure(&summary, "h3_dep"), "lift");
    assert_eq!(num(get(h3_dep, "h1_dim")), 0);
    assert_eq!(
        num(get(get(h3_dep, "raw_cech_comparison"), "h1_t_raw_dim")),
        1
    );
    assert!(bool_val(get(
        get(h3_dep, "raw_cech_comparison"),
        "differs_from_full_syzygy"
    )));
    let h3_reg = get(answer_shigure(&summary, "h3_reg"), "lift");
    assert_eq!(num(get(h3_reg, "h1_dim")), 1);
    assert!(!bool_val(get(h3_reg, "obstruction_is_zero")));

    // (d) H4 & H10 + finish_snap
    let h4 = get(answer_shigure(&summary, "h4"), "lift");
    assert!(!bool_val(get(
        get(h4, "relative_cone"),
        "relative_obstruction_is_zero"
    )));
    assert!(bool_val(get(
        get(h4, "declaration_cover"),
        "matches_relative_obstruction"
    )));
    let h10_fail = get(answer_shigure(&summary, "h10_fail"), "lift");
    let rc10 = get(h10_fail, "relative_cone");
    assert_eq!(s(get(rc10, "raw_read_diff_value")), "-eps^2");
    assert!(bool_val(get(rc10, "raw_read_diff_signed_match")));
    assert!(bool_val(get(
        get(h10_fail, "declaration_cover"),
        "matches_relative_obstruction"
    )));
    let h10_snap = get(answer_shigure(&summary, "h10_snap"), "lift");
    let rc_snap = get(h10_snap, "relative_cone");
    assert!(bool_val(get(rc_snap, "relative_lift_exists")));
    assert!(bool_val(get(get(rc_snap, "reevaluation"), "matched")));
    assert_eq!(
        s(get(get(rc_snap, "reevaluation"), "scope")),
        "mathematical_model_reevaluation"
    );

    // (e) E7 & C9/W5
    let e7_s = get(answer_shigure(&summary, "e7_split"), "lift");
    assert!(!bool_val(get(
        get(e7_s, "declaration_cover"),
        "support_closed"
    )));
    let e7_m = get(answer_shigure(&summary, "e7_merged"), "lift");
    assert!(bool_val(get(
        get(e7_m, "declaration_cover"),
        "support_closed"
    )));
    let c9 = get(answer_shigure(&summary, "c9"), "lift");
    let et = get(c9, "etale_descent");
    assert!(bool_val(get(et, "is_finite_etale")));
    assert!(bool_val(get(et, "cocycle_verified")));
    assert!(!bool_val(get(et, "global_regular_section_exists")));
}

#[test]
fn shigure_phase4_ac4_artin_h4_h5_h10_f4_f6_h6_h7_via_cli() {
    let dir = workdir("shigure-p4-ac4");
    let def = phase4_fixture("phase4.atoms.json");
    let law = phase4_fixture("artin.law");
    let map = phase4_fixture("phase4.archmap.json");
    let out_dir = dir.join("out_artin");

    let run = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "h4=shigure_artin(ArtinAC4.H4Artin, snapshot=snap1)",
            "--ask",
            "h5_chain=shigure_artin(H5Chain3)",
            "--ask",
            "h5_rel=shigure_artin(H5WithRelation)",
            "--ask",
            "h10=shigure_artin(H10Artin)",
            "--ask",
            "f4_1=shigure_artin(F4Nu1)",
            "--ask",
            "f6=shigure_artin(F6Composite)",
            "--ask",
            "h6_f2=shigure_artin(H6BaseChangeF2)",
            "--ask",
            "h6_q=shigure_artin(H6BaseChangeQ)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    let (summary, _saved) = verify_run_output(&run, &out_dir, "complete", 1);

    // (a) H4
    let h4 = get(answer_shigure(&summary, "h4"), "artin");
    assert_eq!(
        s(get(h4, "test_ring_family")),
        "all_local_artin_algebras_universal_quotient"
    );
    assert_eq!(num(get(h4, "detection_order_nu")), 2);
    assert!(bool_val(get(
        get(h4, "universal_first_obstruction"),
        "kappa_u_nonzero"
    )));

    // (b) H5: 2^3 = 8 sharp bound vs existing relation no free bound
    let h5c = get(answer_shigure(&summary, "h5_chain"), "artin");
    assert!(bool_val(get(h5c, "is_free_observation_chart")));
    assert_eq!(num(get(h5c, "detection_order_nu")), 8);
    assert_eq!(num(get(h5c, "syntactic_degree_bound")), 8);
    let h5r = get(answer_shigure(&summary, "h5_rel"), "artin");
    assert!(!bool_val(get(h5r, "is_free_observation_chart")));
    assert_eq!(num(get(h5r, "detection_order_nu")), 3);
    assert!(!has(h5r, "syntactic_degree_bound"));

    // (c) H10
    let h10 = get(answer_shigure(&summary, "h10"), "artin");
    assert_eq!(num(get(h10, "detection_order_nu")), 2);

    // (d) F4 & F6
    let f4_1 = get(answer_shigure(&summary, "f4_1"), "artin");
    assert_eq!(num(get(f4_1, "detection_order_nu")), 1);
    assert_eq!(
        s(get(f4_1, "lift_failure_mode")),
        "nu_eq_1_designated_direction_only_constant_lift_exists"
    );
    assert_eq!(
        s(get(h4, "lift_failure_mode")),
        "nu_ge_2_realization_unliftable"
    );
    let f6 = get(answer_shigure(&summary, "f6"), "artin");
    let comp = get(f6, "composition_law");
    assert_eq!(num(get(comp, "nu_u")), 2);
    assert_eq!(num(get(comp, "nu_v")), 3);
    assert_eq!(num(get(comp, "nu_vu")), 2);
    assert!(bool_val(get(comp, "min_law_verified")));

    // (e) H6
    let h6_f2 = get(answer_shigure(&summary, "h6_f2"), "artin");
    assert_eq!(num(get(h6_f2, "detection_order_nu")), 2);
    let bc_f2 = get(h6_f2, "base_change");
    assert_eq!(num(get(bc_f2, "target_nu")), 3);
    assert!(bool_val(get(bc_f2, "target_image_is_zero")));
    let h6_q = get(answer_shigure(&summary, "h6_q"), "artin");
    assert_eq!(num(get(get(h6_q, "base_change"), "target_nu")), 2);

    // (f) H7: non-Noetherian infinite presentation -> partial / exit 2
    let run_h7 = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &["--ask", "h7=shigure_artin(H7Infinite)"],
    );
    assert_eq!(run_h7.code, 2, "stderr={}", run_h7.stderr);
    let sum_h7 = parse(run_h7.stdout.as_bytes()).unwrap();
    assert_eq!(s(get(&sum_h7, "status")), "partial");
    let ans_h7 = answer_shigure(&sum_h7, "h7");
    assert_eq!(s(get(ans_h7, "verdict")), "undetermined");
    assert_eq!(
        s(get(get(ans_h7, "silence_reason"), "code")),
        "non_noetherian_infinite_presentation"
    );
}

#[test]
fn shigure_phase4_ac5_diagnostics_w1_w2_d1_c2_via_cli() {
    let dir = workdir("shigure-p4-ac5");
    let def = phase4_fixture("phase4.atoms.json");
    let law = phase4_fixture("diagnostics.law");
    let map = phase4_fixture("phase4.archmap.json");
    let out_dir = dir.join("out_diag");

    let run = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "w1_f2=shigure_diagnostics(DiagnosticsAC5.W1NonFlatF2)",
            "--ask",
            "w1_q=shigure_diagnostics(W1TorsionQ)",
            "--ask",
            "w1_cyc=shigure_diagnostics(W1CycleZ)",
            "--ask",
            "w2=shigure_diagnostics(W2SheafQ)",
            "--ask",
            "d1=shigure_diagnostics(D1DimRealization)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    let (summary, _saved) = verify_run_output(&run, &out_dir, "complete", 0);

    // (a) W1
    let w1_f2 = get(answer_shigure(&summary, "w1_f2"), "diagnostics");
    let cc_f2 = get(w1_f2, "coeff_change");
    assert!(!bool_val(get(cc_f2, "is_flat")));
    assert_eq!(num(get(cc_f2, "fixed_label_c0_dim")), 2);
    assert_eq!(num(get(cc_f2, "regenerated_c0_dim")), 1);
    assert!(s(get(cc_f2, "label_collision_map")).contains("a -> (a, a)"));
    assert!(!bool_val(get(
        get(cc_f2, "explicit_complex_check"),
        "flat_preservation_holds"
    )));

    let w1_q = get(answer_shigure(&summary, "w1_q"), "diagnostics");
    let cc_q = get(w1_q, "coeff_change");
    assert!(bool_val(get(cc_q, "is_flat")));
    assert!(!bool_val(get(cc_q, "is_faithfully_flat")));
    assert!(bool_val(get(
        get(cc_q, "explicit_complex_check"),
        "torsion_vanished_in_target"
    )));

    let w1_cyc = get(answer_shigure(&summary, "w1_cyc"), "diagnostics");
    assert_eq!(num(get(w1_cyc, "h1_free_rank")), 1);
    assert!(bool_val(get(w1_cyc, "d1_d0_zero_verified")));

    // (b) W2 + C2 + D3
    let w2 = get(answer_shigure(&summary, "w2"), "diagnostics");
    let strata = arr(get(w2, "strata"));
    assert_eq!(strata.len(), 5);
    assert_eq!(
        strata
            .iter()
            .filter(|st| num(get(st, "h1_free_rank")) == 1)
            .count(),
        1
    );
    let cols = arr(get(w2, "collisions"));
    assert_eq!(num(get(&cols[0], "ker_h1_r_dim")), 1);
    assert!(bool_val(get(&cols[0], "mayer_vietoris_identity_verified")));
    assert_eq!(num(get(&cols[1], "coker_h1_r_dim")), 1);
    assert!(bool_val(get(&cols[1], "mayer_vietoris_identity_verified")));
    assert!(bool_val(get(&cols[2], "multi_stage_order_independent")));
    let rp = get(w2, "r_point_contrast");
    assert!(bool_val(get(rp, "r_values_differ")));
    assert!(bool_val(get(rp, "geometric_stalks_agree")));
    let us = get(w2, "upper_semicontinuity_refutation");
    assert_eq!(num(get(us, "generic_h1_dim")), 1);
    assert_eq!(num(get(us, "special_h1_dim")), 0);

    // (c) D1-D2
    let d1 = get(answer_shigure(&summary, "d1"), "diagnostics");
    let dr = get(d1, "dimension_realization");
    assert!(bool_val(get(dr, "all_probes_matched")));
    assert_eq!(arr(get(dr, "probe_results")).len(), 4);
}

#[test]
fn shigure_phase4_ac6_atlas_h8_w3_f5_f7_h12_via_cli() {
    let dir = workdir("shigure-p4-ac6");
    let def = phase4_fixture("phase4.atoms.json");
    let law = phase4_fixture("atlas.law");
    let map = phase4_fixture("phase4.archmap.json");
    let out_dir = dir.join("out_atlas");

    let run = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "solv=shigure_atlas(AtlasAC6.H8TriangleSolvable, snapshot=snap1)",
            "--ask",
            "one_fix=shigure_atlas(H8TriangleOneFixed)",
            "--ask",
            "all_fix=shigure_atlas(H8TriangleAllFixed)",
            "--ask",
            "obs=shigure_atlas(H8TriangleObstructed)",
            "--ask",
            "edge1=shigure_atlas(H8TriangleEdge1)",
            "--ask",
            "edge_all=shigure_atlas(H8TriangleEdgeAll)",
            "--ask",
            "w3=shigure_atlas(W3Refinement8Pt)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    let (summary, _saved) = verify_run_output(&run, &out_dir, "complete", 1);

    // (a) H8 / W3 triangle
    let solv = get(answer_shigure(&summary, "solv"), "atlas");
    assert!(bool_val(get(solv, "o_b_is_zero")));
    assert!(bool_val(get(solv, "kappa_b_is_zero")));
    assert!(bool_val(get(solv, "saga_sign_commutes_verified")));
    assert_eq!(num(get(solv, "diagnostic_h1_rank")), 1);
    assert!(bool_val(get(solv, "z_to_q_zero_reflection_verified")));
    assert!(bool_val(get(
        get(solv, "unconstrained_reevaluation"),
        "matched"
    )));
    assert_eq!(
        arr(get(get(solv, "vertex_constrained_repair"), "torsor_basis")).len(),
        1
    );

    let one_fix = get(answer_shigure(&summary, "one_fix"), "atlas");
    assert!(bool_val(get(
        get(one_fix, "vertex_constrained_repair"),
        "repair_exists"
    )));
    assert!(
        arr(get(
            get(one_fix, "vertex_constrained_repair"),
            "torsor_basis"
        ))
        .is_empty()
    );

    let all_fix = get(answer_shigure(&summary, "all_fix"), "atlas");
    assert!(bool_val(get(all_fix, "kappa_b_is_zero")));
    assert!(!bool_val(get(
        get(all_fix, "vertex_constrained_repair"),
        "repair_exists"
    )));

    let obs = get(answer_shigure(&summary, "obs"), "atlas");
    assert!(!bool_val(get(obs, "o_b_is_zero")));
    assert!(!bool_val(get(obs, "kappa_b_is_zero")));
    assert_eq!(num(get(obs, "diagnostic_h1_rank")), 1);
    assert!(!bool_val(get(obs, "unconstrained_global_operation_exists")));
    assert!(bool_val(get(obs, "z_to_q_zero_reflection_verified")));

    let edge1 = get(answer_shigure(&summary, "edge1"), "atlas");
    assert!(bool_val(get(
        get(edge1, "edge_constrained_repair"),
        "repair_exists"
    )));
    assert!(arr(get(get(edge1, "edge_constrained_repair"), "torsor_basis")).is_empty());

    let edge_all = get(answer_shigure(&summary, "edge_all"), "atlas");
    assert_eq!(
        arr(get(
            get(edge_all, "edge_constrained_repair"),
            "torsor_basis"
        ))
        .len(),
        2
    );

    // (b) & (c) W3 8-point refinement (C0-C6, F5, F7) & H12
    let w3 = get(answer_shigure(&summary, "w3"), "atlas");
    let r = get(w3, "refinement");
    assert!(bool_val(get(get(r, "condition_c"), "all_passed")));
    assert!(bool_val(get(r, "cochain_map_commutes")));
    assert!(bool_val(get(r, "h0_isomorphism")));
    assert!(bool_val(get(r, "h1_isomorphism")));
    assert!(bool_val(get(r, "designated_o_preserved")));
    assert!(bool_val(get(r, "designated_kappa_preserved")));
    assert!(bool_val(get(r, "repair_fiber_isomorphism_verified")));
    assert!(bool_val(get(r, "inverse_reconstruction_verified")));
    assert!(bool_val(get(r, "eval_condition_fiber_preserved")));
    let fg = get(r, "forgetful_reading_contrast");
    assert!(bool_val(get(fg, "adequacy_and_c0_c6_hold")));
    assert!(!bool_val(get(fg, "eval_descends_to_coarse")));
    assert!(!bool_val(get(fg, "condition_descends_to_coarse")));

    let ext = get(w3, "extended_language_non_transport");
    assert!(bool_val(get(ext, "all_atomic_ops_commute")));
    assert!(!bool_val(get(ext, "all_extended_checks_preserved")));
}

#[test]
fn shigure_phase4_ac7_silence_exit2_mixed_ask_rejection_and_multi_query() {
    let dir = workdir("shigure-p4-ac7");
    let def = phase4_fixture("phase4.atoms.json");
    let law = phase4_fixture("silence.law");
    let map = phase4_fixture("phase4.archmap.json");
    let out_dir = dir.join("out_silence");

    // 6 種すべての適用条件外・上限超過・未観測ケースを同時実行し partial / exit 2 を確認
    let run = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "unobs=shigure_lift(SilenceAC7.LiftUnobserved, snapshot=snap_missing)",
            "--ask",
            "m2=shigure_lift(LiftNotSquareZero)",
            "--ask",
            "artin_b=shigure_artin(ArtinOrderBound)",
            "--ask",
            "h7=shigure_artin(ArtinH7Infinite)",
            "--ask",
            "diag_p=shigure_diagnostics(DiagMaxPartitions)",
            "--ask",
            "disconn=shigure_atlas(AtlasDisconnected)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    let (summary, _saved) = verify_run_output(&run, &out_dir, "partial", 2);

    for (id, expected_kind) in [
        ("unobs", "unobserved_dependency"),
        ("m2", "square_zero_condition_violated"),
        ("artin_b", "artin_order_out_of_scope"),
        ("h7", "non_noetherian_infinite_presentation"),
        ("diag_p", "diagnostics_stratification_out_of_scope"),
        ("disconn", "disconnected_graph_out_of_scope"),
    ] {
        let out = answer_shigure(&summary, id);
        assert_eq!(s(get(out, "verdict")), "undetermined", "id={id}");
        assert_eq!(
            s(get(get(out, "silence_reason"), "code")),
            expected_kind,
            "id={id}"
        );
    }

    // 通常 observed 問いと SHIGURE Phase 4 問いの混在は exit 64 拒否
    let mixed = run_p4(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "a=evaluate(Phase4Vocab.Node, n=@snap1/node1)",
            "--ask",
            "b=shigure_lift(SilenceAC7.LiftNotSquareZero)",
        ],
    );
    assert_eq!(mixed.code, 64, "stderr={}", mixed.stderr);
    assert!(mixed.stdout.is_empty());
}
