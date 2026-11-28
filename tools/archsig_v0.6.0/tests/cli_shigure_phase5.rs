//! SHIGURE Phase 5（出現同定・部分提示・改訂・多源衝突）実バイナリ CLI E2E 統合テスト（AC2–AC7）。

use crate::common::cli::{BinaryRun, arr, consistent, get, has, num, run_binary, s, workdir};
use archsig_common::json::{JNode, JValue, parse};
use std::path::{Path, PathBuf};

fn phase5_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/shigure-phase5")
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

fn json_eq(a: &JNode, b: &JNode) -> bool {
    match (&a.value, &b.value) {
        (JValue::Null, JValue::Null) => true,
        (JValue::Bool(x), JValue::Bool(y)) => x == y,
        (JValue::Num(x), JValue::Num(y)) => x == y,
        (JValue::Str(x), JValue::Str(y)) => x == y,
        (JValue::Arr(xs), JValue::Arr(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| json_eq(x, y))
        }
        (JValue::Obj(xs), JValue::Obj(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|((kx, vx), (ky, vy))| kx == ky && json_eq(vx, vy))
        }
        _ => false,
    }
}

fn str_list(node: &JNode) -> Vec<String> {
    arr(node).iter().map(|n| s(n).to_owned()).collect()
}

fn run_p5(dir: &Path, def: &Path, law: &Path, map: &Path, extra: &[&str]) -> BinaryRun {
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

fn saved_answer<'a>(saved: &'a JNode, id: &str) -> &'a JNode {
    arr(get(saved, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap_or_else(|| panic!("saved answer `{id}` not found"))
}

fn verify_run_output(
    run: &BinaryRun,
    out_dir: &Path,
    status: &str,
    code: i32,
    expected_kind: Option<&str>,
) -> (JNode, JNode) {
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

    let saved = parse(&std::fs::read(out_dir.join("result.json")).unwrap()).unwrap();
    assert_eq!(s(get(&saved, "format")), "archsig.result/4");
    assert_eq!(s(get(&saved, "command")), "run");
    assert_eq!(s(get(&saved, "status")), status);
    assert_eq!(num(get(&saved, "exit_code")), code as u64);
    assert!(!contains_null(&saved));

    let inputs_dir = out_dir.join("inputs");
    assert!(inputs_dir.is_dir());
    assert!(std::fs::read_dir(&inputs_dir).unwrap().count() >= 3);

    let sum_answers = arr(get(&summary, "answers"));
    let reqs = arr(get(&saved, "requests"));
    let saved_answers = arr(get(&saved, "answers"));
    let nodes = arr(get(&saved, "nodes"));
    assert_eq!(reqs.len(), sum_answers.len());
    assert_eq!(saved_answers.len(), sum_answers.len());
    assert_eq!(nodes.len(), sum_answers.len());
    for (idx, sum_ans) in sum_answers.iter().enumerate() {
        let id = s(get(sum_ans, "id"));
        let req = &reqs[idx];
        assert_eq!(s(get(req, "id")), id);
        if let Some(kind) = expected_kind {
            assert_eq!(s(get(req, "kind")), kind);
        }
        let s_ans = &saved_answers[idx];
        assert_eq!(s(get(s_ans, "id")), id);
        assert_eq!(s(get(s_ans, "status")), s(get(sum_ans, "status")));
        let scope = get(s_ans, "scope");
        assert!(!arr(get(scope, "readings")).is_empty());
        assert!(!arr(get(scope, "snapshots")).is_empty());
        assert!(!arr(get(scope, "modes")).is_empty());
        assert_eq!(s(get(scope, "domain")), "shigure_presentation");

        let node_id = s(get(get(get(s_ans, "outputs"), "shigure"), "node"));
        let node = nodes
            .iter()
            .find(|n| s(get(n, "id")) == node_id)
            .unwrap_or_else(|| panic!("node `{node_id}` not found"));
        assert_eq!(s(get(node, "type")), "ShigureOutcome");
        assert_eq!(s(get(node, "state")), "value");
        assert!(json_eq(
            get(node, "value"),
            get(get(sum_ans, "outputs"), "shigure")
        ));
    }
    (summary, saved)
}

#[test]
fn shigure_phase5_ac2_check_accepts_all_fixtures_and_rejects_injection_and_missing_origin() {
    let dir = workdir("shigure-p5-ac2");
    let def = phase5_fixture("phase5.atoms.json");
    let map = phase5_fixture("phase5.archmap.json");

    for (idx, law_name) in [
        "occurrence.law",
        "partial.law",
        "revision.law",
        "multisource.law",
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
                phase5_fixture(law_name).to_str().unwrap(),
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

    let digest = "sha256:d0d6b9efd51420191a25f2c48792cd0957ba3e24d975109154d7024889246b67";
    let bad_bodies = [
        r#"shigure occurrence BadOcc { origin human_adopted "o"; sort S = [a, b]; minimal_functional_classes = {}; }"#,
        r#"shigure partial BadPart { origin human_adopted "o"; finite_table { sort S = [a]; } completion_consistent = true; }"#,
        r#"shigure revision BadRev { kind = span; domain Z; origin human_adopted "o"; umv_verified = true; }"#,
        r#"shigure multisource BadMs { domain Z; origin human_adopted "o"; pairwise_consistent = true; }"#,
        r#"shigure occurrence NoOrigOcc { sort S = [a, b]; }"#,
        r#"shigure partial BadRefPart { origin human_adopted "o"; affine { domain Q; coords [x]; x0 = [0]; direction_t = [[1]]; eval_eq e : [1] = observed Phase5Vocab.Service.missing_field; } }"#,
    ];
    for (idx, body) in bad_bodies.iter().enumerate() {
        let bad_law = dir.join(format!("invalid_p5_{idx}.law"));
        std::fs::write(
            &bad_law,
            format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Bad{idx} {{\n  use vocabulary Phase5Vocab version \"1\" digest \"{digest}\";\n  {body}\n}}\n"
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
fn shigure_phase5_ac3_occurrence_via_cli() {
    let dir = workdir("shigure-p5-ac3");
    let def = phase5_fixture("phase5.atoms.json");
    let law = phase5_fixture("occurrence.law");
    let map = phase5_fixture("phase5.archmap.json");

    let out_ok = dir.join("occ_ok");
    let run_ok = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "quot=shigure_occurrence(OccAC3.Prop17_8Quotient)",
            "--ask",
            "no_coarsest=shigure_occurrence(Ex17_7NoCoarsest)",
            "--ask",
            "attr_ok=shigure_occurrence(Ex17_12AttrOk)",
            "--ask",
            "tags=shigure_occurrence(Ex17_13AliasAndMultiTags)",
            "--out",
            out_ok.to_str().unwrap(),
        ],
    );
    let (sum_ok, _) =
        verify_run_output(&run_ok, &out_ok, "complete", 0, Some("shigure_occurrence"));

    let quot = get(answer_shigure(&sum_ok, "quot"), "occurrence");
    assert!(bool_val(get(quot, "coarsest_sound_exists")));
    assert!(!arr(get(quot, "separating_contexts")).is_empty());
    assert!(has(quot, "coarsest_sound_classes"));

    let no_coarsest = get(answer_shigure(&sum_ok, "no_coarsest"), "occurrence");
    assert_eq!(num(get(no_coarsest, "sound_identifications_count")), 3);
    assert!(!bool_val(get(no_coarsest, "coarsest_sound_exists")));
    assert!(!has(no_coarsest, "coarsest_sound_classes"));

    let attr_ok = get(
        get(answer_shigure(&sum_ok, "attr_ok"), "occurrence"),
        "attribute_realization",
    );
    assert_eq!(num(get(get(attr_ok, "eval_separation_kappa"), "S")), 2);
    assert_eq!(
        num(get(
            &arr(get(attr_ok, "minimal_sound_kappa_tuples"))[0],
            "S"
        )),
        3
    );
    assert!(bool_val(get(get(attr_ok, "reevaluation"), "matched")));

    let tags = get(
        get(answer_shigure(&sum_ok, "tags"), "occurrence"),
        "attribute_realization",
    );
    assert!(bool_val(get(tags, "sound_identification_exists")));
    assert_eq!(
        num(get(&arr(get(tags, "minimal_sound_kappa_tuples"))[0], "S")),
        2
    );

    let out_ref = dir.join("occ_ref");
    let run_ref = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "coll=shigure_occurrence(OccAC3.Thm17_2FixedAndRelColl, snapshot=snap1)",
            "--ask",
            "req_fail=shigure_occurrence(Ex17_12AttrReqFail)",
            "--out",
            out_ref.to_str().unwrap(),
        ],
    );
    let (sum_ref, _) = verify_run_output(
        &run_ref,
        &out_ref,
        "complete",
        1,
        Some("shigure_occurrence"),
    );
    assert_eq!(
        s(get(answer_shigure(&sum_ref, "coll"), "verdict")),
        "refuted"
    );
    let coll = get(answer_shigure(&sum_ref, "coll"), "occurrence");
    assert!(bool_val(get(coll, "derivation_verified")));
    assert!(!arr(get(coll, "collisions")).is_empty());
    let req_fail = get(
        get(answer_shigure(&sum_ref, "req_fail"), "occurrence"),
        "attribute_realization",
    );
    assert!(!bool_val(get(req_fail, "sound_identification_exists")));
}

#[test]
fn shigure_phase5_ac4_partial_via_cli() {
    let dir = workdir("shigure-p5-ac4");
    let def = phase5_fixture("phase5.atoms.json");
    let law = phase5_fixture("partial.law");
    let map = phase5_fixture("phase5.archmap.json");

    let out_ok = dir.join("part_ok");
    let run_ok = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "kleene=shigure_partial(PartAC4.KleeneStrictLet, snapshot=snap1)",
            "--ask",
            "corr=shigure_partial(Ex18_7Correlations)",
            "--ask",
            "aff_q=shigure_partial(AffineProp18_9Q, snapshot=snap1)",
            "--ask",
            "q_uq=shigure_partial(QuantUnotQ)",
            "--ask",
            "q_qu=shigure_partial(QuantQnotU)",
            "--ask",
            "q_g=shigure_partial(QuantGTrue)",
            "--ask",
            "q_e=shigure_partial(QuantEOnly)",
            "--ask",
            "open_f=shigure_partial(OpenEx18_15UniqueFalse)",
            "--ask",
            "open_ne=shigure_partial(OpenEx18_15NonExh)",
            "--ask",
            "open_t=shigure_partial(OpenThm18_18UniqueTrue)",
            "--out",
            out_ok.to_str().unwrap(),
        ],
    );
    let (sum_ok, _) = verify_run_output(&run_ok, &out_ok, "complete", 0, Some("shigure_partial"));

    let kleene = get(answer_shigure(&sum_ok, "kleene"), "partial");
    assert!(bool_val(get(kleene, "kleene_soundness_verified")));
    let kl_laws = arr(get(kleene, "law_evaluations"));
    assert_eq!(s(get(&kl_laws[0], "strong_kleene")), "false");
    assert_eq!(s(get(&kl_laws[1], "strong_kleene")), "unknown");
    assert_eq!(s(get(&kl_laws[1], "supervaluation")), "true");

    let corr_laws = arr(get(
        get(answer_shigure(&sum_ok, "corr"), "partial"),
        "law_evaluations",
    ));
    assert_eq!(
        s(get(&corr_laws[0], "conditional_conclusion_eval")),
        "valid_on_antecedent_domain"
    );
    assert_eq!(
        s(get(&corr_laws[1], "conditional_conclusion_eval")),
        "refuted_on_antecedent_domain"
    );
    assert_eq!(
        s(get(&corr_laws[2], "conditional_conclusion_eval")),
        "indeterminate_on_antecedent_domain"
    );

    let aff_q = arr(get(
        get(answer_shigure(&sum_ok, "aff_q"), "partial"),
        "law_evaluations",
    ));
    assert_eq!(s(get(&aff_q[0], "supervaluation")), "true");
    assert_eq!(s(get(&aff_q[1], "supervaluation")), "indeterminate");

    for (id, e, u, g, q) in [
        ("q_uq", true, true, false, false),
        ("q_qu", true, false, false, true),
        ("q_g", true, true, true, true),
        ("q_e", true, false, false, false),
    ] {
        let qh = get(
            get(answer_shigure(&sum_ok, id), "partial"),
            "quantifier_hierarchy",
        );
        assert_eq!(bool_val(get(qh, "E")), e, "{id}");
        assert_eq!(bool_val(get(qh, "U")), u, "{id}");
        assert_eq!(bool_val(get(qh, "G")), g, "{id}");
        assert_eq!(bool_val(get(qh, "Q")), q, "{id}");
        assert!(bool_val(get(qh, "g_iff_u_and_q_verified")));
    }

    let od_f = get(
        get(answer_shigure(&sum_ok, "open_f"), "partial"),
        "open_domain",
    );
    assert!(bool_val(get(od_f, "is_full_substructure")));
    assert!(bool_val(get(od_f, "all_fibers_locally_exhaustive")));
    assert!(bool_val(get(od_f, "positive_preserved")));
    assert!(!bool_val(get(od_f, "affine_unique_repair_exists")));

    let od_ne = get(
        get(answer_shigure(&sum_ok, "open_ne"), "partial"),
        "open_domain",
    );
    assert!(!bool_val(get(od_ne, "all_fibers_locally_exhaustive")));
    assert_eq!(str_list(get(od_ne, "uncovered_fibers")), vec!["rho(a1)"]);

    let od_t = get(
        get(answer_shigure(&sum_ok, "open_t"), "partial"),
        "open_domain",
    );
    assert!(bool_val(get(od_t, "affine_unique_repair_exists")));

    let out_ref = dir.join("part_ref");
    let run_ref = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "mus=shigure_partial(PartAC4.Ex18_2Mus)",
            "--ask",
            "nomix=shigure_partial(Ex18_2NoEvalMix)",
            "--ask",
            "aff_z=shigure_partial(AffineMusZ)",
            "--out",
            out_ref.to_str().unwrap(),
        ],
    );
    let (sum_ref, _) =
        verify_run_output(&run_ref, &out_ref, "complete", 1, Some("shigure_partial"));
    let mus = get(answer_shigure(&sum_ref, "mus"), "partial");
    assert!(!bool_val(get(mus, "completion_consistent")));
    assert!(bool_val(get(mus, "mus_verified")));
    assert_eq!(
        str_list(&arr(get(mus, "minimal_inconsistent_subsets"))[0]),
        vec!["r1", "r2"]
    );

    let nomix = get(answer_shigure(&sum_ref, "nomix"), "partial");
    assert!(bool_val(get(nomix, "completion_consistent")));
    assert_eq!(num(get(nomix, "completion_count")), 1);

    let aff_z = get(answer_shigure(&sum_ref, "aff_z"), "partial");
    assert!(!bool_val(get(aff_z, "completion_consistent")));
    assert!(bool_val(get(aff_z, "mus_verified")));
    assert_eq!(
        str_list(&arr(get(aff_z, "minimal_inconsistent_subsets"))[0]),
        vec!["even_two"]
    );
}

#[test]
fn shigure_phase5_ac5_revision_via_cli() {
    let dir = workdir("shigure-p5-ac5");
    let def = phase5_fixture("phase5.atoms.json");
    let law = phase5_fixture("revision.law");
    let map = phase5_fixture("phase5.archmap.json");

    let out_ok = dir.join("rev_ok");
    let run_ok = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "mono=shigure_revision(RevAC5.MonotoneCondExt)",
            "--ask",
            "cone=shigure_revision(Ex19_5ConeSpan, snapshot=snap1)",
            "--ask",
            "snf_z2=shigure_revision(Thm19_7SnfZ2Ok)",
            "--ask",
            "snf_q=shigure_revision(Thm19_7SnfQOk)",
            "--out",
            out_ok.to_str().unwrap(),
        ],
    );
    let (sum_ok, _) = verify_run_output(&run_ok, &out_ok, "complete", 0, Some("shigure_revision"));

    let mono = get(answer_shigure(&sum_ok, "mono"), "revision");
    assert!(bool_val(get(mono, "monotonicity_applicable")));
    assert!(bool_val(get(mono, "monotonicity_preserved")));

    let cone = get(answer_shigure(&sum_ok, "cone"), "revision");
    assert_eq!(str_list(get(cone, "invalidation_cone")), vec!["eta", "xi"]);
    assert_eq!(str_list(get(cone, "outside_cone_coords")), vec!["zeta"]);
    assert!(bool_val(get(cone, "outside_projection_equal")));
    let probes = arr(get(cone, "probe_results"));
    assert!(!bool_val(get(&probes[0], "outside_cone")));
    assert!(bool_val(get(&probes[1], "outside_cone")));
    assert!(bool_val(get(&probes[1], "invariant_satisfied")));

    let snf_z2 = get(
        get(answer_shigure(&sum_ok, "snf_z2"), "revision"),
        "snf_reuse",
    );
    assert!(bool_val(get(snf_z2, "umv_verified")));
    assert!(bool_val(get(snf_z2, "reused_snf")));
    assert!(bool_val(get(snf_z2, "after_solvable")));
    assert_eq!(str_list(get(snf_z2, "after_particular")), vec!["2"]);
    assert!(bool_val(get(get(snf_z2, "reevaluation"), "matched")));

    let snf_q = get(
        get(answer_shigure(&sum_ok, "snf_q"), "revision"),
        "snf_reuse",
    );
    assert!(bool_val(get(snf_q, "umv_verified")));
    assert!(bool_val(get(snf_q, "reused_snf")));
    assert!(bool_val(get(get(snf_q, "reevaluation"), "matched")));

    let out_ref = dir.join("rev_ref");
    let run_ref = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "inc=shigure_revision(RevAC5.InconsistentExt)",
            "--ask",
            "snf_z3=shigure_revision(Thm19_7SnfZ3Bad)",
            "--out",
            out_ref.to_str().unwrap(),
        ],
    );
    let (sum_ref, _) =
        verify_run_output(&run_ref, &out_ref, "complete", 1, Some("shigure_revision"));
    let inc = get(answer_shigure(&sum_ref, "inc"), "revision");
    assert!(!bool_val(get(inc, "after_consistent")));
    assert!(!bool_val(get(inc, "monotonicity_applicable")));

    let snf_z3 = get(
        get(answer_shigure(&sum_ref, "snf_z3"), "revision"),
        "snf_reuse",
    );
    assert!(bool_val(get(snf_z3, "umv_verified")));
    assert!(!bool_val(get(snf_z3, "after_solvable")));
    assert_eq!(num(get(snf_z3, "inconsistency_cert_row")), 0);
}

#[test]
fn shigure_phase5_ac6_multisource_via_cli() {
    let dir = workdir("shigure-p5-ac6");
    let def = phase5_fixture("phase5.atoms.json");
    let law = phase5_fixture("multisource.law");
    let map = phase5_fixture("phase5.archmap.json");

    let out_ok = dir.join("ms_ok");
    let run_ok = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "ex13=shigure_multisource(MultiAC6.Ex19_13MinimalSupports)",
            "--out",
            out_ok.to_str().unwrap(),
        ],
    );
    let (sum_ok, _) =
        verify_run_output(&run_ok, &out_ok, "complete", 0, Some("shigure_multisource"));
    let sg = get(
        get(answer_shigure(&sum_ok, "ex13"), "multisource"),
        "support_goal",
    );
    assert_eq!(arr(get(sg, "minimal_supports")).len(), 2);
    assert_eq!(
        str_list(get(&arr(get(sg, "min_cost_supports"))[0], "support")),
        vec!["h_e", "h_x"]
    );
    assert!(bool_val(get(
        &arr(get(sg, "min_cost_supports"))[0],
        "stability_verified"
    )));

    let out_ref = dir.join("ms_ref");
    let run_ref = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--ask",
            "conf=shigure_multisource(MultiAC6.Thm19_9ThreeWayConflict)",
            "--ask",
            "reeval=shigure_multisource(Prop19_12Reeval, snapshot=snap1)",
            "--ask",
            "insuff=shigure_multisource(Prop19_12Insufficient)",
            "--out",
            out_ref.to_str().unwrap(),
        ],
    );
    let (sum_ref, _) = verify_run_output(
        &run_ref,
        &out_ref,
        "complete",
        1,
        Some("shigure_multisource"),
    );
    let conf = get(answer_shigure(&sum_ref, "conf"), "multisource");
    assert!(bool_val(get(conf, "pairwise_consistent")));
    assert!(!bool_val(get(conf, "all_sources_consistent")));
    assert!(bool_val(get(conf, "minimal_conflicts_verified")));
    assert_eq!(
        str_list(&arr(get(conf, "minimal_conflict_sets"))[0]),
        vec!["s_ab", "s_ac", "s_bc"]
    );

    let reeval_sg = get(
        get(answer_shigure(&sum_ref, "reeval"), "multisource"),
        "support_goal",
    );
    assert!(bool_val(get(reeval_sg, "post_verification_reeval_needed")));

    let insuff_sg = get(
        get(answer_shigure(&sum_ref, "insuff"), "multisource"),
        "support_goal",
    );
    assert!(has(insuff_sg, "insufficiency_witness"));
}

#[test]
fn shigure_phase5_ac7_silence_exit2_and_cli_rejections() {
    let dir = workdir("shigure-p5-ac7");
    let def = phase5_fixture("phase5.atoms.json");
    let law = phase5_fixture("silence.law");
    let map = phase5_fixture("phase5.archmap.json");
    let out_dir = dir.join("out_silence");

    let run = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &[
            "--reuse",
            dir.to_str().unwrap(),
            "--ask",
            "unobs=shigure_occurrence(SilenceAC7.OccUnobs, snapshot=snap_missing)",
            "--ask",
            "maxp=shigure_occurrence(OccMaxPart)",
            "--ask",
            "unsup=shigure_partial(PartUnsup)",
            "--ask",
            "op_unobs=shigure_revision(RevOpUnobs)",
            "--ask",
            "force=shigure_revision(RevForceReuse)",
            "--ask",
            "app=shigure_revision(RevApplicability)",
            "--out",
            out_dir.to_str().unwrap(),
        ],
    );
    let (summary, saved) = verify_run_output(&run, &out_dir, "partial", 2, None);
    let warnings = arr(get(&summary, "warnings"));
    assert_eq!(warnings.len(), 1);
    assert_eq!(s(get(get(&warnings[0], "details"), "argument")), "--reuse");

    for (id, expected_kind) in [
        ("unobs", "unobserved_dependency"),
        ("maxp", "finite_enumeration_out_of_scope"),
        ("unsup", "unsupported_completion_class"),
        ("op_unobs", "operator_not_uniquely_determined"),
        ("force", "operator_revision_reuse_rejected"),
        ("app", "applicability_condition_not_met"),
    ] {
        let out = answer_shigure(&summary, id);
        assert_eq!(s(get(out, "verdict")), "undetermined", "id={id}");
        assert_eq!(
            s(get(get(out, "silence_reason"), "code")),
            expected_kind,
            "id={id}"
        );
        let reasons = arr(get(saved_answer(&saved, id), "reasons"));
        assert_eq!(reasons.len(), 1);
        assert_eq!(
            s(get(get(&reasons[0], "details"), "code")),
            expected_kind,
            "id={id}"
        );
    }
    assert_eq!(
        str_list(get(
            get(answer_shigure(&summary, "unobs"), "silence_reason"),
            "missing_slots",
        )),
        vec!["Phase5Vocab.Service.quota"]
    );

    let bad_64_cases: &[&[&str]] = &[
        &[
            "--ask",
            "a=evaluate(Phase5Vocab.Service, svc1=@snap1/svc1)",
            "--ask",
            "b=shigure_partial(SilenceAC7.PartUnsup)",
        ],
        &["--ask", "x=shigure_occurrence(NoSuchTask)"],
        &[
            "--ask",
            "x=shigure_occurrence(SilenceAC7.OccUnobs, snapshot=no_such_snap)",
        ],
        &[
            "--ask",
            "dup=shigure_partial(SilenceAC7.PartUnsup)",
            "--ask",
            "dup=shigure_revision(SilenceAC7.RevOpUnobs)",
        ],
        &["--ask", "x=shigure_partial(SilenceAC7.OccUnobs)"],
    ];
    for case in bad_64_cases {
        let r = run_p5(&dir, &def, &law, &map, case);
        assert_eq!(r.code, 64, "case={case:?}\nstderr={}", r.stderr);
        assert!(r.stdout.is_empty());
    }

    // 曖昧 snapshot（複数 snapshot を持つ ArchMap で observed 解決時に snapshot 省略） -> exit 65
    let ambig = run_p5(
        &dir,
        &def,
        &law,
        &map,
        &["--ask", "u=shigure_occurrence(SilenceAC7.OccUnobs)"],
    );
    assert_eq!(ambig.code, 65, "stderr={}", ambig.stderr);
    assert!(ambig.stdout.is_empty());

    // Origin.kind 欠落 ArchMap の結合 -> exit 65
    let raw_map = std::fs::read_to_string(&map).unwrap();
    let no_kind = raw_map.replace("      \"kind\": \"runtime_observation\",\n", "");
    assert_ne!(no_kind, raw_map);
    let no_kind_map = dir.join("no_kind_p5.archmap.json");
    std::fs::write(&no_kind_map, &no_kind).unwrap();
    let r_kind = run_p5(
        &dir,
        &def,
        &phase5_fixture("partial.law"),
        &no_kind_map,
        &[
            "--ask",
            "kl=shigure_partial(PartAC4.KleeneStrictLet, snapshot=snap1)",
        ],
    );
    assert_eq!(r_kind.code, 65, "stderr={}", r_kind.stderr);
    assert!(r_kind.stdout.is_empty());
}
