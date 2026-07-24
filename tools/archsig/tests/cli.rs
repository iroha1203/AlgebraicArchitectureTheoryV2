use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use archsig::{
    ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
    ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT, ARCHSIG_COMPARISON_CONCLUSION_CODES,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA, ARCHSIG_GATE_REPORT_DECISIONS,
    ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS, ARCHSIG_REPAIR_TARGETS_IDENTIFIED,
    ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS, ARCHSIG_SAGA_CONCLUSION_CODES,
    ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL,
    ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX, ArchMapDocumentV2, ArchSigRunManifestV1,
    RepairPlanDocumentV1, compare_archmap_v2_doctrine, validate_measurement_packet_value_v1,
    validate_refactor_morphism_v1, validate_refinement_comparison_v1,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn practical_rust_service_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/practical-rust-service")
}

fn ag_measurement_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/ag_measurement")
}

#[test]
fn cli_law_surface_v052_validates_contract_and_rejects_shortcuts() {
    let out_dir = temp_dir("law-surface-v052");
    let root = ag_measurement_root();
    let input = root.join("law_surface_v052.json");
    let report = out_dir.join("law-surface-validation.json");

    run_sig0(&[
        "law-surface",
        "--law-surface",
        input.to_str().expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);
    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "pass");
    assert_eq!(
        json["schema"],
        "law-equation-surface-validation-report/v0.5.4"
    );

    let mut stage3 = read_json(&input);
    stage3["skeleton"] = json!([{
        "simplex": "vertex:order",
        "supportAtomRef": "atom:order",
        "requiredLawId": "ag.square-free-equation"
    }]);
    stage3["defectSources"] = json!([{
        "lawId": "ag.square-free-equation",
        "coverRef": "cover:order-inventory",
        "chartDefects": [{
            "chart": "ctx:order",
            "defectObservable": { "axis": "cech", "predicate": "sectionValue" }
        }],
        "holdsCriterion": {
            "kind": "defect-raw-value-zero",
            "zeroSense": "empty-witness-set"
        }
    }]);
    stage3["quotientSheafCondition"] = json!({"mode": "single-context-theorem"});
    let stage3_path = out_dir.join("stage3.json");
    fs::write(
        &stage3_path,
        serde_json::to_vec_pretty(&stage3).expect("stage3 surface serializes"),
    )
    .expect("stage3 surface writes");
    let stage3_report = out_dir.join("stage3-report.json");
    run_sig0(&[
        "law-surface",
        "--law-surface",
        stage3_path.to_str().expect("path is utf-8"),
        "--out",
        stage3_report.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(read_json(&stage3_report)["summary"]["result"], "pass");

    let mut reserved = read_json(&input);
    reserved["skeleton"] = json!([]);
    let reserved_path = out_dir.join("reserved.json");
    fs::write(
        &reserved_path,
        serde_json::to_vec_pretty(&reserved).expect("reserved fixture serializes"),
    )
    .expect("reserved fixture writes");
    let reserved_report = out_dir.join("reserved-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            reserved_path.to_str().expect("path is utf-8"),
            "--out",
            reserved_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let reserved_json = read_json(&reserved_report);
    assert_eq!(reserved_json["summary"]["result"], "fail");
    assert!(reserved_json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-equation-surface-v052-stage3-contract" && check["result"] == "fail"
        })
    }));

    for field in ["defectSources", "quotientSheafCondition"] {
        let mut reserved = read_json(&input);
        reserved[field] = if field == "quotientSheafCondition" {
            json!({"mode": "invalid"})
        } else {
            json!([])
        };
        let reserved_path = out_dir.join(format!("reserved-{field}.json"));
        fs::write(
            &reserved_path,
            serde_json::to_vec_pretty(&reserved).expect("reserved field serializes"),
        )
        .expect("reserved field writes");
        let reserved_report = out_dir.join(format!("reserved-{field}-report.json"));
        run_sig0_expect_code(
            &[
                "law-surface",
                "--law-surface",
                reserved_path.to_str().expect("path is utf-8"),
                "--out",
                reserved_report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        assert_eq!(read_json(&reserved_report)["summary"]["result"], "fail");
    }

    for field in ["skeleton", "defectSources", "quotientSheafCondition"] {
        let mut null_reserved = read_json(&input);
        null_reserved[field] = Value::Null;
        let null_reserved_path = out_dir.join(format!("reserved-{field}-null.json"));
        fs::write(
            &null_reserved_path,
            serde_json::to_vec_pretty(&null_reserved).expect("null reserved field serializes"),
        )
        .expect("null reserved field writes");
        let null_reserved_report = out_dir.join(format!("reserved-{field}-null-report.json"));
        run_sig0_expect_code(
            &[
                "law-surface",
                "--law-surface",
                null_reserved_path.to_str().expect("path is utf-8"),
                "--out",
                null_reserved_report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        assert_eq!(
            read_json(&null_reserved_report)["summary"]["result"],
            "fail"
        );
    }

    let mut weakened = read_json(&input);
    weakened["laws"][0]["conditionType"] = json!("open");
    let weakened_path = out_dir.join("weakened.json");
    fs::write(
        &weakened_path,
        serde_json::to_vec_pretty(&weakened).expect("weakened fixture serializes"),
    )
    .expect("weakened fixture writes");
    let weakened_report = out_dir.join("weakened-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            weakened_path.to_str().expect("path is utf-8"),
            "--out",
            weakened_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let weakened_json = read_json(&weakened_report);
    assert_eq!(weakened_json["summary"]["result"], "fail");
    assert!(weakened_json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-equation-surface-v052-shape-rules" && check["result"] == "fail"
        })
    }));

    let mut null_evaluator = read_json(&input);
    null_evaluator["laws"][0]["evaluatorRef"] = Value::Null;
    let null_evaluator_path = out_dir.join("null-evaluator.json");
    fs::write(
        &null_evaluator_path,
        serde_json::to_vec_pretty(&null_evaluator).expect("null evaluator fixture serializes"),
    )
    .expect("null evaluator fixture writes");
    let null_evaluator_report = out_dir.join("null-evaluator-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            null_evaluator_path.to_str().expect("path is utf-8"),
            "--out",
            null_evaluator_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&null_evaluator_report)["summary"]["result"],
        "fail"
    );

    let mut empty_ideal = read_json(&input);
    empty_ideal["laws"][0]["forbiddenSupportGenerators"] = json!([]);
    let empty_ideal_path = out_dir.join("empty-ideal.json");
    fs::write(
        &empty_ideal_path,
        serde_json::to_vec_pretty(&empty_ideal).expect("empty ideal fixture serializes"),
    )
    .expect("empty ideal fixture writes");
    let empty_ideal_report = out_dir.join("empty-ideal-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            empty_ideal_path.to_str().expect("path is utf-8"),
            "--out",
            empty_ideal_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(read_json(&empty_ideal_report)["summary"]["result"], "fail");

    for (name, shortcut) in [
        ("camel-boundary", "ag.boundaryMembership"),
        ("camel-coherent", "ag.globalCoherent"),
        ("snake-zero", "ag.measured_zero"),
        ("nsdepth", "ag.nsdepth"),
        ("risk", "ag.risk"),
        ("debt", "ag.debt"),
        ("unsafe", "ag.unsafe"),
        ("failure", "ag.failure"),
        ("fail", "ag.fail"),
        ("failed", "ag.failed"),
        ("failing", "ag.failing"),
        ("obstructive", "ag.obstructive"),
        ("risky", "ag.risky"),
        ("certificate", "ag.certificate"),
        ("h1zero", "ag.h1zero"),
        ("lawful", "ag.lawful"),
        ("mismatch", "ag.mismatch"),
        ("minimal-forbidden-supports", "ag.minimalForbiddenSupports"),
        ("measured-nonzero", "ag.measuredNonzero"),
        ("nonzero", "ag.nonzero"),
        ("obstruction", "ag.obstruction"),
        ("violation", "ag.violation"),
        ("violate", "ag.violate"),
        ("violated", "ag.violated"),
        ("violates", "ag.violates"),
        ("violating", "ag.violating"),
        ("verdict", "ag.verdict"),
    ] {
        let mut shortcut_input = read_json(&input);
        shortcut_input["laws"][0]["lawId"] = json!(shortcut);
        let shortcut_path = out_dir.join(format!("{name}.json"));
        fs::write(
            &shortcut_path,
            serde_json::to_vec_pretty(&shortcut_input).expect("shortcut fixture serializes"),
        )
        .expect("shortcut fixture writes");
        let shortcut_report = out_dir.join(format!("{name}-report.json"));
        run_sig0_expect_code(
            &[
                "law-surface",
                "--law-surface",
                shortcut_path.to_str().expect("path is utf-8"),
                "--out",
                shortcut_report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        assert_eq!(read_json(&shortcut_report)["summary"]["result"], "fail");
    }

    let mut non_shortcut = read_json(&input);
    non_shortcut["laws"][0]["lawId"] = json!("ag.nonzeroish");
    let non_shortcut_path = out_dir.join("non-shortcut.json");
    fs::write(
        &non_shortcut_path,
        serde_json::to_vec_pretty(&non_shortcut).expect("non-shortcut fixture serializes"),
    )
    .expect("non-shortcut fixture writes");
    let non_shortcut_report = out_dir.join("non-shortcut-report.json");
    run_sig0(
        [
            "law-surface",
            "--law-surface",
            non_shortcut_path.to_str().expect("path is utf-8"),
            "--out",
            non_shortcut_report.to_str().expect("path is utf-8"),
        ]
        .as_slice(),
    );
    assert_eq!(read_json(&non_shortcut_report)["summary"]["result"], "pass");

    let mut alias_shortcut = read_json(&input);
    alias_shortcut["laws"][0]["witnessVariables"][0]["binding"]["archmapVariable"] =
        json!("ag.nsdepth");
    let alias_shortcut_path = out_dir.join("alias-shortcut.json");
    fs::write(
        &alias_shortcut_path,
        serde_json::to_vec_pretty(&alias_shortcut).expect("alias shortcut serializes"),
    )
    .expect("alias shortcut writes");
    let alias_shortcut_report = out_dir.join("alias-shortcut-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            alias_shortcut_path.to_str().expect("path is utf-8"),
            "--out",
            alias_shortcut_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&alias_shortcut_report)["summary"]["result"],
        "fail"
    );

    let mut empty_alias = read_json(&input);
    empty_alias["laws"][0]["witnessVariables"][0]["binding"]["archmapVariable"] = json!("");
    let empty_alias_path = out_dir.join("empty-alias.json");
    fs::write(
        &empty_alias_path,
        serde_json::to_vec_pretty(&empty_alias).expect("empty alias fixture serializes"),
    )
    .expect("empty alias fixture writes");
    let empty_alias_report = out_dir.join("empty-alias-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            empty_alias_path.to_str().expect("path is utf-8"),
            "--out",
            empty_alias_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(read_json(&empty_alias_report)["summary"]["result"], "fail");

    let mut omitted_alias = read_json(&input);
    omitted_alias["laws"][0]["witnessVariables"][0]["binding"]
        .as_object_mut()
        .expect("binding is object")
        .remove("archmapVariable");
    let omitted_alias_path = out_dir.join("omitted-alias.json");
    fs::write(
        &omitted_alias_path,
        serde_json::to_vec_pretty(&omitted_alias).expect("omitted alias fixture serializes"),
    )
    .expect("omitted alias fixture writes");
    run_sig0(&[
        "law-surface",
        "--law-surface",
        omitted_alias_path.to_str().expect("path is utf-8"),
    ]);

    let mut null_alias_edge = read_json(&input);
    null_alias_edge["laws"][0]["witnessVariables"][0]["binding"]["archmapVariable"] = Value::Null;
    null_alias_edge["laws"][0]["witnessVariables"][0]["binding"]["edge"] =
        json!(["ctx:a", "ctx:b"]);
    null_alias_edge["laws"][0]["witnessVariables"][0]["binding"]["axis"] = json!("cech");
    null_alias_edge["laws"][0]["witnessVariables"][0]["binding"]["predicate"] =
        json!("sectionValue");
    let null_alias_edge_path = out_dir.join("null-alias-edge.json");
    fs::write(
        &null_alias_edge_path,
        serde_json::to_vec_pretty(&null_alias_edge).expect("null alias edge serializes"),
    )
    .expect("null alias edge writes");
    let null_alias_edge_report = out_dir.join("null-alias-edge-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            null_alias_edge_path.to_str().expect("path is utf-8"),
            "--out",
            null_alias_edge_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&null_alias_edge_report)["summary"]["result"],
        "fail"
    );

    let mut mismatched_binding = read_json(&input);
    let binding = mismatched_binding["laws"][0]["witnessVariables"][0]["binding"]
        .as_object_mut()
        .expect("binding is object");
    binding.remove("archmapVariable");
    binding.insert("edge".to_string(), json!(["ctx:a", "ctx:b"]));
    let mismatched_binding_path = out_dir.join("mismatched-binding.json");
    fs::write(
        &mismatched_binding_path,
        serde_json::to_vec_pretty(&mismatched_binding).expect("mismatched binding serializes"),
    )
    .expect("mismatched binding writes");
    let mismatched_binding_report = out_dir.join("mismatched-binding-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            mismatched_binding_path.to_str().expect("path is utf-8"),
            "--out",
            mismatched_binding_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&mismatched_binding_report)["summary"]["result"],
        "fail"
    );

    let mut wrong_pair = read_json(&input);
    wrong_pair["laws"][0]["witnessVariables"][0]["binding"]["predicate"] = json!("sectionValue");
    let wrong_pair_path = out_dir.join("wrong-pair.json");
    fs::write(
        &wrong_pair_path,
        serde_json::to_vec_pretty(&wrong_pair).expect("wrong pair serializes"),
    )
    .expect("wrong pair writes");
    let wrong_pair_report = out_dir.join("wrong-pair-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            wrong_pair_path.to_str().expect("path is utf-8"),
            "--out",
            wrong_pair_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let wrong_pair_json = read_json(&wrong_pair_report);
    assert!(wrong_pair_json["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-equation-surface-v052-bindings" && check["result"] == "fail"
        })
    }));

    let mut duplicate_variable = read_json(&input);
    duplicate_variable["laws"][0]["witnessVariables"][1]["variable"] = json!("p");
    duplicate_variable["laws"][0]["witnessVariables"][1]["binding"]["archmapVariable"] = json!("p");
    let duplicate_variable_path = out_dir.join("duplicate-variable.json");
    fs::write(
        &duplicate_variable_path,
        serde_json::to_vec_pretty(&duplicate_variable)
            .expect("duplicate variable fixture serializes"),
    )
    .expect("duplicate variable fixture writes");
    let duplicate_variable_report = out_dir.join("duplicate-variable-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            duplicate_variable_path.to_str().expect("path is utf-8"),
            "--out",
            duplicate_variable_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&duplicate_variable_report)["summary"]["result"],
        "fail"
    );

    let mut duplicate_alias = read_json(&input);
    duplicate_alias["laws"][0]["witnessVariables"][1]["binding"]["archmapVariable"] = json!("p");
    let duplicate_alias_path = out_dir.join("duplicate-alias.json");
    fs::write(
        &duplicate_alias_path,
        serde_json::to_vec_pretty(&duplicate_alias).expect("duplicate alias serializes"),
    )
    .expect("duplicate alias writes");
    let duplicate_alias_report = out_dir.join("duplicate-alias-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            duplicate_alias_path.to_str().expect("path is utf-8"),
            "--out",
            duplicate_alias_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&duplicate_alias_report)["summary"]["result"],
        "fail"
    );

    let mut self_edge = read_json(&input);
    self_edge["laws"][0]["witnessVariables"][0]["binding"]
        .as_object_mut()
        .expect("binding is object")
        .remove("archmapVariable");
    self_edge["laws"][0]["witnessVariables"][0]["binding"]["edge"] = json!(["ctx:a", "ctx:a"]);
    self_edge["laws"][0]["witnessVariables"][0]["binding"]["axis"] = json!("cech");
    self_edge["laws"][0]["witnessVariables"][0]["binding"]["predicate"] = json!("sectionValue");
    let self_edge_path = out_dir.join("self-edge.json");
    fs::write(
        &self_edge_path,
        serde_json::to_vec_pretty(&self_edge).expect("self edge serializes"),
    )
    .expect("self edge writes");
    let self_edge_report = out_dir.join("self-edge-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            self_edge_path.to_str().expect("path is utf-8"),
            "--out",
            self_edge_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(read_json(&self_edge_report)["summary"]["result"], "fail");

    for (name, axis, predicate) in [
        ("square-free-support", "square-free", "support"),
        ("square-free-cooccurrence", "square-free", "cooccurrence"),
        ("cech-section-value", "cech", "sectionValue"),
        (
            "section-factorization-support",
            "section-factorization",
            "support",
        ),
        (
            "section-factorization-cooccurrence",
            "section-factorization",
            "cooccurrence",
        ),
    ] {
        let mut accepted = read_json(&input);
        let binding_object = accepted["laws"][0]["witnessVariables"][0]["binding"]
            .as_object_mut()
            .expect("binding is object");
        binding_object.insert("axis".to_string(), json!(axis));
        binding_object.insert("predicate".to_string(), json!(predicate));
        if axis == "cech" {
            binding_object.remove("archmapVariable");
            binding_object.insert("edge".to_string(), json!(["ctx:a", "ctx:b"]));
        } else {
            binding_object.remove("edge");
            binding_object.insert("archmapVariable".to_string(), json!("p"));
        }
        let accepted_path = out_dir.join(format!("accepted-{name}.json"));
        fs::write(
            &accepted_path,
            serde_json::to_vec_pretty(&accepted).expect("accepted binding serializes"),
        )
        .expect("accepted binding writes");
        run_sig0(&[
            "law-surface",
            "--law-surface",
            accepted_path.to_str().expect("path is utf-8"),
        ]);
    }

    let mut unknown_evaluator = read_json(&input);
    unknown_evaluator["laws"][1]["evaluatorRef"] = json!("ag.not-registered");
    let unknown_evaluator_path = out_dir.join("unknown-evaluator.json");
    fs::write(
        &unknown_evaluator_path,
        serde_json::to_vec_pretty(&unknown_evaluator)
            .expect("unknown evaluator fixture serializes"),
    )
    .expect("unknown evaluator fixture writes");
    let unknown_evaluator_report = out_dir.join("unknown-evaluator-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            unknown_evaluator_path.to_str().expect("path is utf-8"),
            "--out",
            unknown_evaluator_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let unknown_evaluator_json = read_json(&unknown_evaluator_report);
    assert!(
        unknown_evaluator_json["checks"]
            .as_array()
            .is_some_and(|checks| {
                checks.iter().any(|check| {
                    check["id"] == "law-equation-surface-v052-evaluator-refs"
                        && check["result"] == "fail"
                })
            })
    );

    let mut mismatched_evaluator = read_json(&input);
    mismatched_evaluator["laws"][1]["conditionType"] = json!("open");
    mismatched_evaluator["laws"][1]["evaluatorRef"] = json!("ag.square-free-repair");
    let mismatched_evaluator_path = out_dir.join("mismatched-evaluator.json");
    fs::write(
        &mismatched_evaluator_path,
        serde_json::to_vec_pretty(&mismatched_evaluator)
            .expect("mismatched evaluator fixture serializes"),
    )
    .expect("mismatched evaluator fixture writes");
    let mismatched_evaluator_report = out_dir.join("mismatched-evaluator-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            mismatched_evaluator_path.to_str().expect("path is utf-8"),
            "--out",
            mismatched_evaluator_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&mismatched_evaluator_report)["summary"]["result"],
        "fail"
    );

    let mut open_section = read_json(&input);
    open_section["laws"][1]["conditionType"] = json!("open");
    let open_section_path = out_dir.join("open-section.json");
    fs::write(
        &open_section_path,
        serde_json::to_vec_pretty(&open_section).expect("open section fixture serializes"),
    )
    .expect("open section fixture writes");
    run_sig0(&[
        "law-surface",
        "--law-surface",
        open_section_path.to_str().expect("path is utf-8"),
    ]);

    let mut unknown = read_json(&input);
    unknown["laws"][0]["verdict"] = json!("measured_zero");
    let unknown_path = out_dir.join("unknown.json");
    fs::write(
        &unknown_path,
        serde_json::to_vec_pretty(&unknown).expect("unknown fixture serializes"),
    )
    .expect("unknown fixture writes");
    let unknown_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        unknown_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(unknown_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&unknown_output.stderr).contains("unknown field"));

    let duplicate_key_path = out_dir.join("duplicate-key.json");
    fs::write(
        &duplicate_key_path,
        r#"{"schema":"law-equation-surface/v0.5.4","id":"law-surface:duplicate","laws":[{"lawId":"law:first","lawId":"law:second","conditionType":"descent","evaluatorRef":"ag.section-factorization"}]}"#,
    )
    .expect("duplicate key fixture writes");
    let duplicate_key_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        duplicate_key_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(duplicate_key_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&duplicate_key_output.stderr).contains("duplicate JSON object key")
    );

    let same_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        input.to_str().expect("path is utf-8"),
        "--out",
        input.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(same_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&same_output.stderr).contains("output path must differ"));

    let hard_link = out_dir.join("law-surface-hard-link.json");
    fs::hard_link(&input, &hard_link).expect("hard link fixture creates");
    let hard_link_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        input.to_str().expect("path is utf-8"),
        "--out",
        hard_link.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(hard_link_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&hard_link_output.stderr).contains("output path must differ"));
}

#[test]
fn cli_law_policy_ag_evaluator_requires_measurement_profile() {
    let out_dir = temp_dir("ag-policy-missing-profile");
    let root = ag_measurement_root();
    let report = out_dir.join("law-policy-validation.json");

    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            root.join("law_policy_missing_profile.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ],
        1,
    );

    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"].as_array().unwrap().iter().any(|check| {
            check["id"] == "law-policy-schema052-ag-evaluator-profile-required"
                && check["result"] == "fail"
        }),
        "AG evaluator execution must fail closed without MeasurementProfile"
    );
}

#[test]
fn cli_law_policy_registry_keeps_ag_evaluator_after_split() {
    let out_dir = temp_dir("ag-policy-registry");
    let root = ag_measurement_root();
    let report = out_dir.join("law-policy-validation.json");

    run_sig0(&[
        "law-policy",
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report.to_str().expect("path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["id"] == "law-policy-schema052-registry-vocabulary"
                    && check["result"] == "pass"
            })
        }),
        "AG evaluator ids must still resolve through the split registry"
    );
    assert!(
        json["expandedPolicies"].as_array().is_some_and(|entries| {
            entries.iter().any(|entry| {
                entry["law"] == "surface:cech-surface-v052"
                    && entry["evaluator"] == "ag.cech-obstruction"
            })
        }),
        "AG evaluator policy must survive registry module split"
    );
}

#[test]
fn cli_law_policy_rejects_retired_pack_selector() {
    let out_dir = temp_dir("law-policy-retired-pack");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    policy["policies"][0] = json!({
        "pack": "legacy-ag-pack",
        "scope": ["/computedInvariants"],
        "severity": "blocking"
    });
    let policy_path = out_dir.join("retired-pack.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy writes");
    let report_path = out_dir.join("retired-pack-report.json");
    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let report = read_json(&report_path);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(report["checks"].as_array().unwrap().iter().any(|check| {
        check["id"] == "law-policy-schema052-registry-vocabulary" && check["result"] == "fail"
    }));
}

#[test]
fn cli_law_policy_stage1_reserved_fields_fail_closed_and_basis_ledger_resolves() {
    let out_dir = temp_dir("ag-policy-stage1-reserved-basis");
    let root = ag_measurement_root();
    let profile = root.join("measurement_profile_ag.json");

    let mut selected = read_json(&root.join("law_policy_ag.json"));
    selected["policies"][0]["profileRef"] = json!("profile:ag-default@1");
    let selected_path = out_dir.join("law_policy_profile_ref.json");
    fs::write(
        &selected_path,
        serde_json::to_vec_pretty(&selected).expect("selected profile policy serializes"),
    )
    .expect("selected profile policy writes");
    let selected_report = out_dir.join("profile-ref-report.json");
    run_sig0(&[
        "law-policy",
        "--law-policy",
        selected_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        selected_report.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(read_json(&selected_report)["summary"]["result"], "pass");

    let mut reserved = read_json(&root.join("law_policy_ag.json"));
    reserved["lawSurfaceRef"] = json!("law-surface:future");
    reserved["policies"][0]["profileRef"] = json!("profile:future");
    let reserved_path = out_dir.join("law_policy_reserved.json");
    fs::write(
        &reserved_path,
        serde_json::to_vec_pretty(&reserved).expect("policy serializes"),
    )
    .expect("reserved policy writes");
    let reserved_report = out_dir.join("reserved-report.json");
    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            reserved_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            profile.to_str().expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            reserved_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let reserved_json = read_json(&reserved_report);
    assert_eq!(
        check_by_id(
            &reserved_json,
            "law-policy-schema052-law-surface-resolution"
        )["result"],
        "fail"
    );
    assert_eq!(
        check_by_id(
            &reserved_json,
            "law-policy-schema052-policy-profile-resolution",
        )["result"],
        "fail"
    );

    let mut unresolved = read_json(&root.join("law_policy_ag.json"));
    unresolved["policies"][0]["basis"] = json!(["policy-basis:missing"]);
    unresolved["basisLedger"][0]["path"] = json!("does/not/need/to/exist.md");
    let unresolved_path = out_dir.join("law_policy_unresolved_basis.json");
    fs::write(
        &unresolved_path,
        serde_json::to_vec_pretty(&unresolved).expect("policy serializes"),
    )
    .expect("unresolved policy writes");
    let unresolved_report = out_dir.join("unresolved-report.json");
    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            unresolved_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            profile.to_str().expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            unresolved_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let unresolved_json = read_json(&unresolved_report);
    assert_eq!(
        check_by_id(&unresolved_json, "law-policy-schema052-basis-recorded")["result"],
        "fail"
    );

    let mut declared = read_json(&root.join("law_policy_ag.json"));
    declared["basisLedger"][0]["path"] = json!("does/not/need/to/exist.md");
    let declared_path = out_dir.join("law_policy_declared_missing_path.json");
    fs::write(
        &declared_path,
        serde_json::to_vec_pretty(&declared).expect("policy serializes"),
    )
    .expect("declared policy writes");
    let declared_report = out_dir.join("declared-report.json");
    run_sig0(&[
        "law-policy",
        "--law-policy",
        declared_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        declared_report.to_str().expect("path is utf-8"),
    ]);
    let declared_json = read_json(&declared_report);
    assert_eq!(
        check_by_id(&declared_json, "law-policy-schema052-basis-recorded")["result"],
        "pass",
        "basisLedger path is declarative and is not checked for filesystem existence"
    );
}

#[test]
fn cli_repair_plan_stage1_validates_supplied_input_boundary() {
    let out_dir = temp_dir("ag-repair-plan-stage1");
    let root = ag_measurement_root();
    let repair_plan_path = root.join("repair_plan_complete_support.json");
    let valid_report = out_dir.join("repair-plan-valid.json");

    run_sig0(&[
        "repair-plan",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--out",
        valid_report.to_str().expect("path is utf-8"),
    ]);
    let valid = read_json(&valid_report);
    assert_eq!(valid["summary"]["result"], "warn");
    assert_eq!(
        check_by_id(&valid, "repair-plan-schema052-complete-support-cross-check")["result"],
        "pass"
    );
    assert_eq!(
        check_by_id(&valid, "repair-plan-schema052-overlap-primitive-bijection")["result"],
        "pass"
    );
    assert_eq!(
        valid["assumptionLedger"][0]["assumedBy"], "repair-plan author",
        "enumerationComplete is recorded as author assumption, not verified"
    );

    let supplied_path = root.join("repair_plan_supplied_faithfulness.json");
    let supplied_report = out_dir.join("repair-plan-supplied-valid.json");
    run_sig0(&[
        "repair-plan",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        supplied_path.to_str().expect("path is utf-8"),
        "--out",
        supplied_report.to_str().expect("path is utf-8"),
    ]);
    let supplied = read_json(&supplied_report);
    assert_eq!(supplied["summary"]["result"], "warn");
    assert_eq!(
        check_by_id(&supplied, "repair-plan-schema052-supplied-slots")["result"],
        "pass"
    );

    let mut explicit_comparison = read_json(&supplied_path);
    let typed_explicit: RepairPlanDocumentV1 = serde_json::from_value(explicit_comparison.clone())
        .expect("explicit comparison base plan matches RepairPlan schema");
    let explicit_fingerprint = format!(
        "{:x}",
        Sha256::digest(
            serde_json::to_vec(&typed_explicit.complex)
                .expect("explicit comparison complex serializes")
        )
    );
    let explicit_target_support = typed_explicit
        .primitives
        .iter()
        .map(|primitive| {
            json!({
                "overlapRef": primitive.overlap_ref,
                "support": primitive.support.variables
            })
        })
        .collect::<Vec<_>>();
    let explicit_variables = typed_explicit
        .primitives
        .iter()
        .flat_map(|primitive| primitive.support.variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let explicit_variable_map = explicit_variables
        .iter()
        .map(|variable| {
            json!({
                "source": variable,
                "target": variable
            })
        })
        .collect::<Vec<_>>();
    explicit_comparison["comparison"] = json!({
        "kind": "saga-comparison",
        "incidenceBridge": {
            "kind": "explicit",
            "sourceComplexRef": "complex:repair",
            "targetComplexRef": "complex:cech",
            "targetComplex": serde_json::to_value(&typed_explicit.complex)
                .expect("explicit target complex serializes")
        },
        "h1ComparisonData": {
            "schema": "h1-comparison-data/v0.5.4",
            "kind": "explicit",
            "cochainMapRef": "comparison:cochain-map",
            "sourceComplexFingerprint": explicit_fingerprint,
            "targetComplexFingerprint": explicit_fingerprint,
            "targetCochainSupport": explicit_target_support,
            "cochainMap": {
                "degreeZero": typed_explicit.complex.charts.iter().map(|chart| json!({
                    "sourceChartRef": chart,
                    "targetChartRef": chart,
                    "variableMap": explicit_variable_map.clone()
                })).collect::<Vec<_>>(),
                "degreeOne": typed_explicit.complex.overlaps.iter().map(|overlap| json!({
                    "sourceOverlapRef": overlap.id,
                    "targetOverlapRef": overlap.id,
                    "variableMap": explicit_variable_map.clone()
                })).collect::<Vec<_>>(),
                "degreeTwo": {
                    "basisMap": typed_explicit.complex.triple_overlaps.iter().map(|triple| json!({
                        "sourceTripleRef": triple.id,
                        "targetTripleRef": triple.id
                    })).collect::<Vec<_>>(),
                    "zeroImage": []
                }
            }
        }
    });
    let explicit_comparison_path = out_dir.join("repair_plan_comparison_explicit.json");
    fs::write(
        &explicit_comparison_path,
        serde_json::to_vec_pretty(&explicit_comparison).expect("comparison plan serializes"),
    )
    .expect("comparison plan writes");
    let explicit_comparison_report = out_dir.join("repair-plan-comparison-explicit.json");
    run_sig0(&[
        "repair-plan",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        explicit_comparison_path.to_str().expect("path is utf-8"),
        "--out",
        explicit_comparison_report.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(
        check_by_id(
            &read_json(&explicit_comparison_report),
            "repair-plan-schema052-supplied-slots"
        )["result"],
        "pass"
    );

    for (case, mutation) in [
        ("comparison-identity-fingerprint", json!("sha256:wrong")),
        (
            "comparison-identity-target-fingerprint",
            json!("sha256:target-wrong"),
        ),
        (
            "comparison-explicit-map-difference",
            json!("overlap:inventory-shared"),
        ),
        (
            "comparison-explicit-zero-image",
            json!("triple:order-inventory-shared"),
        ),
        ("comparison-target-star-incidence", Value::Null),
        ("comparison-legacy-degreeOneLeftInverse", json!(true)),
        ("comparison-legacy-degreeOneRightInverse", json!(true)),
        ("comparison-legacy-differencePreserving", json!(true)),
        ("comparison-legacy-degreeTwoZeroPreserving", json!(true)),
        ("comparison-legacy-differentialCommutative", json!(true)),
        ("comparison-unknown-field", json!("forged")),
        ("comparison-unresolved-reference", json!("complex:forged")),
        ("comparison-target-support-mismatch", json!([])),
    ] {
        let mut invalid = explicit_comparison.clone();
        if case == "comparison-identity-fingerprint" {
            invalid["comparison"]["incidenceBridge"]["kind"] = json!("chart-indexed");
            invalid["comparison"]["incidenceBridge"]["repairChartRefs"] =
                json!(["ctx:order", "ctx:inventory", "ctx:shared"]);
            invalid["comparison"]["incidenceBridge"]["cechChartRefs"] =
                json!(["ctx:order", "ctx:inventory", "ctx:shared"]);
            invalid["comparison"]["h1ComparisonData"] = json!({
                "schema": "h1-comparison-data/v0.5.4",
                "kind": "identity",
                "sourceComplexFingerprint": mutation,
                "targetComplexFingerprint": explicit_fingerprint,
                "targetCochainSupport": explicit_target_support
            });
        } else if case == "comparison-identity-target-fingerprint" {
            invalid["comparison"]["incidenceBridge"]["kind"] = json!("chart-indexed");
            invalid["comparison"]["incidenceBridge"]["repairChartRefs"] =
                json!(["ctx:order", "ctx:inventory", "ctx:shared"]);
            invalid["comparison"]["incidenceBridge"]["cechChartRefs"] =
                json!(["ctx:order", "ctx:inventory", "ctx:shared"]);
            invalid["comparison"]["h1ComparisonData"] = json!({
                "schema": "h1-comparison-data/v0.5.4",
                "kind": "identity",
                "sourceComplexFingerprint": explicit_fingerprint,
                "targetComplexFingerprint": mutation,
                "targetCochainSupport": explicit_target_support
            });
        } else if case == "comparison-explicit-map-difference" {
            invalid["comparison"]["h1ComparisonData"]["cochainMap"]["degreeOne"][0]["targetOverlapRef"] =
                mutation.clone();
            invalid["comparison"]["h1ComparisonData"]["cochainMap"]["degreeOne"][1]["targetOverlapRef"] =
                json!("overlap:order-inventory");
        } else if case == "comparison-explicit-zero-image" {
            invalid["comparison"]["h1ComparisonData"]["cochainMap"]["degreeTwo"]["zeroImage"] =
                json!([mutation]);
        } else if case == "comparison-target-star-incidence" {
            let mut target = invalid["comparison"]["incidenceBridge"]["targetComplex"].clone();
            target["overlaps"][2]["right"] = json!("ctx:inventory");
            let target_fingerprint = format!(
                "{:x}",
                Sha256::digest(serde_json::to_vec(&target).expect("star target serializes"))
            );
            invalid["comparison"]["incidenceBridge"]["targetComplex"] = target;
            invalid["comparison"]["h1ComparisonData"]["targetComplexFingerprint"] =
                json!(target_fingerprint);
        } else if let Some(legacy_key) = case.strip_prefix("comparison-legacy-") {
            invalid["comparison"]["h1ComparisonData"][legacy_key] = mutation;
        } else if case == "comparison-unresolved-reference" {
            invalid["comparison"]["incidenceBridge"]["sourceComplexRef"] = mutation;
        } else if case == "comparison-target-support-mismatch" {
            invalid["comparison"]["h1ComparisonData"]["targetCochainSupport"] = mutation;
        } else {
            invalid["comparison"]["incidenceBridge"]["forgedField"] = mutation;
        }
        let path = out_dir.join(format!("{case}.json"));
        fs::write(
            &path,
            serde_json::to_vec_pretty(&invalid).expect("invalid comparison serializes"),
        )
        .expect("invalid comparison writes");
        let report = out_dir.join(format!("{case}.report.json"));
        run_sig0_expect_code(
            &[
                "repair-plan",
                "--archmap",
                root.join("archmap_v2.json")
                    .to_str()
                    .expect("path is utf-8"),
                "--repair-plan",
                path.to_str().expect("path is utf-8"),
                "--out",
                report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        let report_json = read_json(&report);
        assert_eq!(
            check_by_id(&report_json, "repair-plan-schema052-supplied-slots")["result"],
            "fail",
            "invalid comparison case {case} must fail closed"
        );
        if case == "comparison-unresolved-reference" {
            assert_eq!(
                check_by_id(&report_json, "repair-plan-schema052-reference-resolution")["result"],
                "fail",
                "unresolved comparison references must fail the reference-resolution check"
            );
        }
        if case == "comparison-explicit-map-difference" {
            assert!(
                json_contains_substring(&report_json, "differencePreserving=false"),
                "difference-breaking map must report differencePreserving=false"
            );
        }
        if case == "comparison-explicit-zero-image" {
            assert!(
                json_contains_substring(&report_json, "degreeTwoZeroPreserving=false"),
                "nonzero zeroImage must report degreeTwoZeroPreserving=false"
            );
        }
        assert!(
            json_contains_substring(&report_json, "COMPARISON_DATA_CONTRACT_VIOLATION"),
            "invalid comparison case {case} must retain the comparison contract violation code"
        );
    }

    for fixture in [
        "repair_plan_supplied_coefficient.json",
        "repair_plan_true_sheaf.json",
        "repair_plan_gluing_data.json",
        "repair_plan_comparison.json",
    ] {
        let report = out_dir.join(format!("{fixture}.report.json"));
        run_sig0(&[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            root.join(fixture).to_str().expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ]);
        assert_eq!(
            check_by_id(&read_json(&report), "repair-plan-schema052-supplied-slots")["result"],
            "pass",
            "supplied slot fixture {fixture} must pass its contract"
        );
    }

    for (case, field, expected) in [
        (
            "zero-primitive-not-empty",
            "zeroPrimitiveRef",
            "zeroPrimitiveRef must resolve to a primitive with empty support",
        ),
        (
            "predicate-not-zero",
            "zeroOnZeroPrimitive",
            "faithfulness requires Q(r)=0 on the supplied zero primitive",
        ),
        (
            "predicate-forged-support",
            "supportVariables",
            "Q(r) must match the finite residual support generated by the supplied primitives",
        ),
    ] {
        let mut candidate = read_json(&supplied_path);
        if field == "zeroPrimitiveRef" {
            candidate["faithfulness"]["supplied"][field] = json!("primitive:order-inventory");
        } else if field == "zeroOnZeroPrimitive" {
            candidate["faithfulness"]["supplied"]["residualSupportPredicate"][field] = json!(false);
        } else {
            candidate["faithfulness"]["supplied"]["residualSupportPredicate"][field] =
                json!(["forged-variable"]);
        }
        let path = out_dir.join(format!("repair_plan_{case}.json"));
        fs::write(
            &path,
            serde_json::to_vec_pretty(&candidate).expect("invalid supplied plan serializes"),
        )
        .expect("invalid supplied plan writes");
        let report = out_dir.join(format!("repair-plan-{case}.json"));
        run_sig0_expect_code(
            &[
                "repair-plan",
                "--archmap",
                root.join("archmap_v2.json")
                    .to_str()
                    .expect("path is utf-8"),
                "--repair-plan",
                path.to_str().expect("path is utf-8"),
                "--out",
                report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        let report_json = read_json(&report);
        assert_eq!(
            check_by_id(&report_json, "repair-plan-schema052-supplied-slots")["result"],
            "fail",
            "invalid supplied faithfulness field {field} must fail: {expected}"
        );
    }

    let mut invalid_certificate = read_json(&root.join("repair_plan_true_sheaf.json"));
    invalid_certificate["trueSheafCertificate"]["globalCondition"] = json!("claimed");
    let invalid_certificate_path = out_dir.join("repair_plan_invalid_true_sheaf.json");
    fs::write(
        &invalid_certificate_path,
        serde_json::to_vec_pretty(&invalid_certificate).expect("invalid certificate serializes"),
    )
    .expect("invalid certificate writes");
    let invalid_certificate_report = out_dir.join("repair-plan-invalid-true-sheaf.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            invalid_certificate_path.to_str().expect("path is utf-8"),
            "--out",
            invalid_certificate_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&invalid_certificate_report),
            "repair-plan-schema052-supplied-slots"
        )["result"],
        "fail"
    );

    for (case, mutation) in [
        (
            "discharged-without-finite-model",
            json!("discharged-by-finite-model"),
        ),
        (
            "non-string-member-chart",
            json!(["ctx:order", 42, "ctx:shared"]),
        ),
    ] {
        let mut candidate = read_json(&root.join("repair_plan_true_sheaf.json"));
        if case == "discharged-without-finite-model" {
            candidate["trueSheafCertificate"]["globalCondition"] = mutation;
        } else {
            candidate["trueSheafCertificate"]["memberCharts"] = mutation;
        }
        let path = out_dir.join(format!("repair_plan_invalid_true_sheaf_{case}.json"));
        fs::write(
            &path,
            serde_json::to_vec_pretty(&candidate).expect("invalid true-sheaf plan serializes"),
        )
        .expect("invalid true-sheaf plan writes");
        let report = out_dir.join(format!("repair-plan-invalid-true-sheaf-{case}.json"));
        run_sig0_expect_code(
            &[
                "repair-plan",
                "--archmap",
                root.join("archmap_v2.json")
                    .to_str()
                    .expect("path is utf-8"),
                "--repair-plan",
                path.to_str().expect("path is utf-8"),
                "--out",
                report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        assert_eq!(
            check_by_id(&read_json(&report), "repair-plan-schema052-supplied-slots")["result"],
            "fail",
            "malformed true-sheaf input {case} must fail closed"
        );
    }

    let mut invalid_gluing = read_json(&root.join("repair_plan_gluing_data.json"));
    invalid_gluing["gluingData"]["sectionRefs"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "overlapRef": "overlap:order-inventory",
            "sectionRef": "section:duplicate"
        }));
    let invalid_gluing_path = out_dir.join("repair_plan_invalid_gluing.json");
    fs::write(
        &invalid_gluing_path,
        serde_json::to_vec_pretty(&invalid_gluing).expect("invalid gluing serializes"),
    )
    .expect("invalid gluing writes");
    let invalid_gluing_report = out_dir.join("repair-plan-invalid-gluing.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            invalid_gluing_path.to_str().expect("path is utf-8"),
            "--out",
            invalid_gluing_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&invalid_gluing_report),
            "repair-plan-schema052-supplied-slots"
        )["result"],
        "fail"
    );

    let mut measured_residual = read_json(&repair_plan_path);
    measured_residual["residual"] = json!({
        "kind": "measured",
        "packetRef": "measurement:residual-test",
        "invariantRef": "residual:invariant"
    });
    let measured_residual_path = out_dir.join("repair_plan_measured_residual.json");
    fs::write(
        &measured_residual_path,
        serde_json::to_vec_pretty(&measured_residual).expect("measured residual plan serializes"),
    )
    .expect("measured residual plan writes");
    let residual_packet_path = out_dir.join("residual_packet.json");
    fs::write(
        &residual_packet_path,
        serde_json::to_vec_pretty(&json!({
            "packetId": "measurement:residual-test",
            "computedInvariants": [{"invariantId": "residual:invariant"}]
        }))
        .expect("residual packet serializes"),
    )
    .expect("residual packet writes");
    let missing_residual_report = out_dir.join("repair-plan-missing-residual-packet.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            measured_residual_path.to_str().expect("path is utf-8"),
            "--out",
            missing_residual_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&missing_residual_report),
            "repair-plan-schema052-measured-residual-binding"
        )["result"],
        "fail"
    );
    let supplied_residual_report = out_dir.join("repair-plan-supplied-residual-packet.json");
    run_sig0(&[
        "repair-plan",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        measured_residual_path.to_str().expect("path is utf-8"),
        "--residual-packet",
        residual_packet_path.to_str().expect("path is utf-8"),
        "--out",
        supplied_residual_report.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(
        check_by_id(
            &read_json(&supplied_residual_report),
            "repair-plan-schema052-measured-residual-binding"
        )["result"],
        "pass"
    );
    let residual_runs = [
        out_dir.join("residual-run-a"),
        out_dir.join("residual-run-b"),
    ];
    for residual_run in &residual_runs {
        run_sig0(&[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--repair-plan",
            measured_residual_path.to_str().expect("path is utf-8"),
            "--residual-packet",
            residual_packet_path.to_str().expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            residual_run.to_str().expect("path is utf-8"),
        ]);
    }
    let residual_manifest = read_json(&residual_runs[0].join("archsig-run-manifest.json"));
    assert_eq!(
        residual_manifest["inputDigests"]["residualPacket"]["path"],
        "input:residual_packet.json"
    );
    assert!(
        residual_manifest["inputDigests"]["residualPacket"]["sha256"]
            .as_str()
            .is_some_and(|digest| !digest.is_empty())
    );
    let residual_measurement = read_json(&residual_runs[0].join("archsig-measurement-packet.json"));
    assert_eq!(
        residual_measurement["suppliedData"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["kind"] == "residual-packet")
            .expect("residual packet ledger entry")["sourceArtifactRef"],
        "input:residual_packet.json"
    );
    let residual_compare = out_dir.join("residual-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        residual_runs[0].to_str().expect("path is utf-8"),
        "--head-run",
        residual_runs[1].to_str().expect("path is utf-8"),
        "--out-dir",
        residual_compare.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(
        read_json(&residual_compare.join("archsig-comparison-report.json"))["comparability"]["level"],
        "identical"
    );

    let mut missing_primitive = read_json(&repair_plan_path);
    missing_primitive["primitives"]
        .as_array_mut()
        .expect("primitives array")
        .pop();
    let missing_primitive_path = out_dir.join("repair_plan_missing_primitive.json");
    fs::write(
        &missing_primitive_path,
        serde_json::to_vec_pretty(&missing_primitive).expect("repair plan serializes"),
    )
    .expect("missing primitive repair plan writes");
    let missing_primitive_report = out_dir.join("repair-plan-missing-primitive.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            missing_primitive_path.to_str().expect("path is utf-8"),
            "--out",
            missing_primitive_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let missing_primitive_json = read_json(&missing_primitive_report);
    assert_eq!(
        check_by_id(
            &missing_primitive_json,
            "repair-plan-schema052-overlap-primitive-bijection"
        )["result"],
        "fail"
    );

    let mut duplicate_primitive = read_json(&repair_plan_path);
    let first_primitive = duplicate_primitive["primitives"][0].clone();
    duplicate_primitive["primitives"]
        .as_array_mut()
        .expect("primitives array")
        .push(first_primitive);
    duplicate_primitive["primitives"][3]["id"] = json!("primitive:duplicate-overlap");
    let duplicate_primitive_path = out_dir.join("repair_plan_duplicate_primitive.json");
    fs::write(
        &duplicate_primitive_path,
        serde_json::to_vec_pretty(&duplicate_primitive).expect("repair plan serializes"),
    )
    .expect("duplicate primitive repair plan writes");
    let duplicate_primitive_report = out_dir.join("repair-plan-duplicate-primitive.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            duplicate_primitive_path.to_str().expect("path is utf-8"),
            "--out",
            duplicate_primitive_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let duplicate_primitive_json = read_json(&duplicate_primitive_report);
    assert_eq!(
        check_by_id(
            &duplicate_primitive_json,
            "repair-plan-schema052-overlap-primitive-bijection"
        )["result"],
        "fail"
    );

    let mut reserved = read_json(&repair_plan_path);
    reserved["trueSheafCertificate"] = json!({"claim": "future"});
    reserved["faithfulness"]["mode"] = json!("supplied");
    let reserved_path = out_dir.join("repair_plan_reserved.json");
    fs::write(
        &reserved_path,
        serde_json::to_vec_pretty(&reserved).expect("repair plan serializes"),
    )
    .expect("reserved repair plan writes");
    let reserved_report = out_dir.join("repair-plan-reserved.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            reserved_path.to_str().expect("path is utf-8"),
            "--out",
            reserved_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let reserved_json = read_json(&reserved_report);
    assert_eq!(
        check_by_id(&reserved_json, "repair-plan-schema052-supplied-slots")["result"],
        "fail"
    );

    for field in ["comparison", "grounding"] {
        let mut reserved_field = read_json(&repair_plan_path);
        reserved_field[field] = json!({"future": true});
        let reserved_field_path = out_dir.join(format!("repair_plan_reserved_{field}.json"));
        fs::write(
            &reserved_field_path,
            serde_json::to_vec_pretty(&reserved_field).expect("reserved field plan serializes"),
        )
        .expect("reserved field plan writes");
        let reserved_field_report = out_dir.join(format!("repair-plan-reserved-{field}.json"));
        run_sig0_expect_code(
            &[
                "repair-plan",
                "--archmap",
                root.join("archmap_v2.json")
                    .to_str()
                    .expect("path is utf-8"),
                "--repair-plan",
                reserved_field_path.to_str().expect("path is utf-8"),
                "--out",
                reserved_field_report.to_str().expect("path is utf-8"),
            ],
            1,
        );
        assert_eq!(
            check_by_id(
                &read_json(&reserved_field_report),
                "repair-plan-schema052-supplied-slots"
            )["result"],
            "fail",
            "reserved field {field} must be rejected independently"
        );
    }

    let mut supplied_faithfulness = read_json(&repair_plan_path);
    supplied_faithfulness["faithfulness"]["mode"] = json!("supplied");
    let supplied_faithfulness_path = out_dir.join("repair_plan_supplied_faithfulness.json");
    fs::write(
        &supplied_faithfulness_path,
        serde_json::to_vec_pretty(&supplied_faithfulness)
            .expect("supplied faithfulness plan serializes"),
    )
    .expect("supplied faithfulness plan writes");
    let supplied_faithfulness_report = out_dir.join("repair-plan-supplied-faithfulness.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            supplied_faithfulness_path.to_str().expect("path is utf-8"),
            "--out",
            supplied_faithfulness_report
                .to_str()
                .expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&supplied_faithfulness_report),
            "repair-plan-schema052-supplied-slots"
        )["result"],
        "fail"
    );

    let mut unknown_field = read_json(&repair_plan_path);
    unknown_field["complex"]["unclaimedField"] = json!(true);
    let unknown_field_path = out_dir.join("repair_plan_unknown_field.json");
    fs::write(
        &unknown_field_path,
        serde_json::to_vec_pretty(&unknown_field).expect("unknown field plan serializes"),
    )
    .expect("unknown field plan writes");
    let unknown_field_output = run_sig0_output(&[
        "repair-plan",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        unknown_field_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(unknown_field_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&unknown_field_output.stderr).contains("unknown field"));

    let mut conclusion_token = read_json(&repair_plan_path);
    conclusion_token["semanticProjection"]["k"][0] = json!("glues");
    let conclusion_path = out_dir.join("repair_plan_conclusion_token.json");
    fs::write(
        &conclusion_path,
        serde_json::to_vec_pretty(&conclusion_token).expect("repair plan serializes"),
    )
    .expect("conclusion repair plan writes");
    let conclusion_report = out_dir.join("repair-plan-conclusion-token.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            conclusion_path.to_str().expect("path is utf-8"),
            "--out",
            conclusion_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let conclusion_json = read_json(&conclusion_report);
    assert_eq!(
        check_by_id(
            &conclusion_json,
            "repair-plan-schema052-no-conclusion-tokens"
        )["result"],
        "fail"
    );

    let mut partial_support = read_json(&repair_plan_path);
    partial_support["primitives"][0]["support"]["kind"] = json!("partial");
    let partial_path = out_dir.join("repair_plan_partial_support.json");
    fs::write(
        &partial_path,
        serde_json::to_vec_pretty(&partial_support).expect("repair plan serializes"),
    )
    .expect("partial repair plan writes");
    let partial_report = out_dir.join("repair-plan-partial-support.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            partial_path.to_str().expect("path is utf-8"),
            "--out",
            partial_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let partial_json = read_json(&partial_report);
    assert_eq!(
        check_by_id(
            &partial_json,
            "repair-plan-schema052-complete-support-cross-check"
        )["result"],
        "fail"
    );

    let mut unresolved_archmap_ref = read_json(&repair_plan_path);
    unresolved_archmap_ref["complex"]["charts"][0] = json!("ctx:not-in-archmap");
    unresolved_archmap_ref["semanticProjection"]["lambda"][0] = json!("atom:not-in-archmap");
    let unresolved_path = out_dir.join("repair_plan_unresolved_archmap_ref.json");
    fs::write(
        &unresolved_path,
        serde_json::to_vec_pretty(&unresolved_archmap_ref).expect("repair plan serializes"),
    )
    .expect("unresolved repair plan writes");
    let unresolved_report = out_dir.join("repair-plan-unresolved-archmap-ref.json");
    run_sig0_expect_code(
        &[
            "repair-plan",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--repair-plan",
            unresolved_path.to_str().expect("path is utf-8"),
            "--out",
            unresolved_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let unresolved_json = read_json(&unresolved_report);
    assert_eq!(
        check_by_id(&unresolved_json, "repair-plan-schema052-archmap-bindings")["result"],
        "fail"
    );
}

#[test]
fn cli_analyze_saga_descent_without_repair_plan_is_silence_by_design() {
    let out_dir = temp_dir("ag-saga-descent-no-repair-plan");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let row = packet["structuralVerdict"]
        .as_array()
        .expect("structural verdict array")
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-descent")
        .expect("saga descent row exists");
    assert_eq!(row["verdict"], "not_computed");
    assert_eq!(
        row["verdictData"]["methodStatus"],
        "repair_plan_not_supplied"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .expect("boundary statements")
            .iter()
            .any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "repair_plan_not_supplied"
            }),
        "missing repair-plan must be modeled as silence_by_design, not validation failure"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_saga_summary_has_no_class_vocabulary(&summary);
}

#[test]
fn cli_analyze_saga_descent_complete_support_measures_boundary_membership() {
    let out_dir = temp_dir("ag-saga-descent-complete-support");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        root.join("repair_plan_complete_support.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let membership = saga_row(&packet, "saga.residual-boundary-membership");
    assert_eq!(membership["verdict"], "measured_zero");
    assert_eq!(membership["verdictData"]["methodStatus"], "residual_in_b1");
    let global = saga_row(&packet, "saga.global-coherence");
    assert_eq!(global["verdict"], "measured_zero");
    assert_eq!(
        global["verdictData"]["methodStatus"],
        "complete_support_global_coherent"
    );
    let comparison = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-comparison:h1-transfer")
        .expect("saga comparison silence invariant exists");
    assert_eq!(comparison["status"], "silence_by_design");
    assert_eq!(comparison["reason"], "comparison_data_not_supplied");
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentCovered"],
        true
    );
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentFaithful"],
        true
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    );
    assert_saga_summary_has_no_class_vocabulary(&summary);
    assert_eq!(
        summary["translationRule"]["conclusionCode"],
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    );
    assert_eq!(summary["translationRule"]["theoremRef"], "part10/3.5");
    assert_eq!(
        summary["translationRule"]["emitsLawSatisfiedWithoutLawCheck"],
        false
    );
    assert!(
        summary["translationRule"]["concreteSupportRefs"]
            .as_array()
            .expect("active support refs are array")
            .is_empty(),
        "zero/gluing conclusion must not invent nonzero concrete support refs"
    );
    assert!(
        summary["translationRule"]["principalText"]
            .as_str()
            .is_some_and(|text| {
                text.contains("selected SAGA residual") && text.contains("covered and faithful")
            }),
        "translation principal text must stay inside the selected profile"
    );
    assert!(
        summary["translationRule"]["boundary"]
            .as_str()
            .is_some_and(|text| text.contains("Supply Stage 2 law surface")),
        "translation boundary must say what must be supplied next"
    );
    assert!(
        summary["translationRuleTable"]
            .as_array()
            .is_some_and(|rules| rules.iter().all(|rule| {
                rule.get("conclusionCode").and_then(Value::as_str).is_some()
                    && rule.get("principalText").and_then(Value::as_str).is_some()
                    && rule.get("boundary").and_then(Value::as_str).is_some()
                    && rule
                        .get("supportDiscipline")
                        .and_then(Value::as_str)
                        .is_some()
                    && rule["emitsLawSatisfiedWithoutLawCheck"] == false
            })),
        "summary must expose a fixed translation rule table"
    );
    let generic_rule = summary["translationRuleTable"]
        .as_array()
        .expect("translation rule table")
        .iter()
        .find(|rule| rule["conclusionCode"] == "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE")
        .expect("generic obstruction rule exists");
    assert_eq!(generic_rule["theoremRef"], Value::Null);
    assert!(
        generic_rule["principalText"].as_str().is_some_and(|text| {
            text.contains("Review the theoremRef-bearing structural verdict rows")
                && !text.contains("measured a selected AG obstruction")
        }),
        "theoremRef-free generic rule must not emit a measurement claim as principal text"
    );
    assert!(
        !json_contains_substring(&summary, &["law ", "is satisfied"].concat()),
        "Stage 1 summary must not emit law-satisfied prose without a law-check row"
    );
    assert!(
        !json_contains_substring(&summary, &["law ", "が守られている"].concat()),
        "Stage 1 summary must not emit Japanese law-satisfied prose without a law-check row"
    );
    assert!(
        !json_contains_substring(&summary, &["証", "明する"].concat()),
        "tool first-person proof prose must not appear without theoremRef attribution"
    );
}

fn supplied_triple_saga_plan(root: &Path, nonzero_class: bool) -> Value {
    let mut plan = read_json(&root.join("repair_plan_complete_support.json"));
    plan["trueSheafCertificate"] = json!({
        "kind": "true-sheaf-certificate",
        "coverRef": "cover:order-inventory",
        "memberCharts": ["ctx:order", "ctx:inventory", "ctx:shared"],
        "globalCondition": "assumed"
    });
    plan["gluingData"] = json!({
        "kind": "gluing-data",
        "overlapRefs": [
            "overlap:order-inventory",
            "overlap:inventory-shared",
            "overlap:order-shared",
            "overlap:order-inventory-alt"
        ],
        "sectionRefs": [
            {"overlapRef":"overlap:order-inventory","sectionRef":"section:order-inventory"},
            {"overlapRef":"overlap:inventory-shared","sectionRef":"section:inventory-shared"},
            {"overlapRef":"overlap:order-shared","sectionRef":"section:order-shared"},
            {"overlapRef":"overlap:order-inventory-alt","sectionRef":"section:order-inventory-alt"}
        ]
    });
    plan["complex"]["overlaps"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "id": "overlap:order-inventory-alt",
            "left": "ctx:order",
            "right": "ctx:inventory"
        }));
    plan["complex"]["tripleOverlaps"] = json!([{"id":"triple:class","overlapRefs":[
        "overlap:order-inventory",
        "overlap:inventory-shared",
        "overlap:order-shared"
    ]}]);
    plan["primitives"].as_array_mut().unwrap().push(json!({
        "id": "primitive:order-inventory-alt",
        "overlapRef": "overlap:order-inventory-alt",
        "resL": ["repair:cycle"],
        "resR": [],
        "support": {"kind": "supplied", "variables": ["repair:cycle"]}
    }));
    for index in 0..3 {
        plan["primitives"][index]["resL"] = json!([]);
        plan["primitives"][index]["resR"] = json!([]);
        plan["primitives"][index]["support"]["variables"] = json!([]);
    }
    if nonzero_class {
        plan["primitives"][3]["resL"] = json!(["repair:cycle"]);
        plan["primitives"][3]["support"]["variables"] = json!(["repair:cycle"]);
    } else {
        plan["primitives"][3]["resL"] = json!([]);
        plan["primitives"][3]["support"]["variables"] = json!([]);
    }
    let support_variables = if nonzero_class {
        json!(["repair:cycle"])
    } else {
        json!([])
    };
    plan["faithfulness"] = json!({
        "mode": "supplied",
        "supplied": {
            "zeroPrimitiveRef": "primitive:inventory-shared",
            "residualSupportPredicate": {
                "kind": "finite-support",
                "supportVariables": support_variables,
                "zeroOnZeroPrimitive": true
            },
            "faithfulnessLaw": "Q is faithful on the supplied residual support"
        }
    });
    let typed_plan: RepairPlanDocumentV1 =
        serde_json::from_value(plan.clone()).expect("comparison plan matches RepairPlan schema");
    let complex_fingerprint = format!(
        "{:x}",
        Sha256::digest(
            serde_json::to_vec(&typed_plan.complex).expect("comparison complex serializes")
        )
    );
    let saga_variable_map = typed_plan
        .primitives
        .iter()
        .flat_map(|primitive| primitive.support.variables.iter().cloned())
        .collect::<BTreeSet<_>>()
        .iter()
        .map(|variable| json!({"source": variable, "target": variable}))
        .collect::<Vec<_>>();
    let saga_cochain_map = json!({
        "degreeZero": typed_plan.complex.charts.iter().map(|chart| json!({
            "sourceChartRef": chart,
            "targetChartRef": chart,
            "variableMap": saga_variable_map.clone()
        })).collect::<Vec<_>>(),
        "degreeOne": typed_plan.complex.overlaps.iter().map(|overlap| json!({
            "sourceOverlapRef": overlap.id,
            "targetOverlapRef": overlap.id,
            "variableMap": saga_variable_map.clone()
        })).collect::<Vec<_>>(),
        "degreeTwo": {
            "basisMap": typed_plan.complex.triple_overlaps.iter().map(|triple| json!({
                "sourceTripleRef": triple.id,
                "targetTripleRef": triple.id
            })).collect::<Vec<_>>(),
            "zeroImage": []
        }
    });
    plan["comparison"] = json!({
        "kind": "saga-comparison",
        "incidenceBridge": {
            "kind": "explicit",
            "sourceComplexRef": "complex:repair",
            "targetComplexRef": "complex:cech",
            "targetComplex": serde_json::to_value(&typed_plan.complex)
                .expect("explicit target complex serializes")
        },
        "h1ComparisonData": {
            "schema": "h1-comparison-data/v0.5.4",
            "kind": "explicit",
            "cochainMapRef": "comparison:cochain-map",
            "sourceComplexFingerprint": complex_fingerprint,
            "targetComplexFingerprint": complex_fingerprint,
            "targetCochainSupport": plan["primitives"]
                .as_array()
                .expect("comparison primitives are an array")
                .iter()
                .map(|primitive| {
                    json!({
                        "overlapRef": primitive["overlapRef"],
                        "support": primitive["support"]["variables"]
                    })
                })
                .collect::<Vec<_>>(),
            "cochainMap": saga_cochain_map
        }
    });
    assert_eq!(typed_plan.complex.charts.len(), 3);
    plan
}

fn presentation_generated_saga_plan(root: &Path, nonzero_class: bool) -> Value {
    let mut plan = supplied_triple_saga_plan(root, nonzero_class);
    let typed_plan: RepairPlanDocumentV1 =
        serde_json::from_value(plan.clone()).expect("presentation plan matches RepairPlan schema");
    let complex_fingerprint = format!(
        "{:x}",
        Sha256::digest(
            serde_json::to_vec(&typed_plan.complex).expect("presentation complex serializes")
        )
    );
    let cells = typed_plan
        .complex
        .charts
        .iter()
        .cloned()
        .chain(typed_plan.complex.overlaps.iter().map(|overlap| overlap.id.clone()))
        .chain(
            typed_plan
                .complex
                .triple_overlaps
                .iter()
                .map(|triple| triple.id.clone()),
        )
        .map(|cell_ref| {
            json!({
                "cellRef": cell_ref,
                "semanticGenerators": ["repair:cycle"],
                "repairRelationMatrix": [],
                "equationGenerators": ["equation:cycle"],
                "equationRelationMatrix": [],
                "generatorMap": [[1]]
            })
        })
        .collect::<Vec<_>>();
    let mut restrictions = Vec::new();
    for overlap in &typed_plan.complex.overlaps {
        for chart in [&overlap.left, &overlap.right] {
            restrictions.push(json!({
                "fromRef": chart,
                "toRef": overlap.id,
                "semanticMatrix": [[1]],
                "equationMatrix": [[1]]
            }));
        }
    }
    for triple in &typed_plan.complex.triple_overlaps {
        for overlap_ref in &triple.overlap_refs {
            restrictions.push(json!({
                "fromRef": overlap_ref,
                "toRef": triple.id,
                "semanticMatrix": [[1]],
                "equationMatrix": [[1]]
            }));
        }
    }
    plan["comparison"] = json!({
        "kind": "saga-comparison",
        "incidenceBridge": {
            "kind": "chart-indexed",
            "repairChartRefs": typed_plan.complex.charts,
            "cechChartRefs": typed_plan.complex.charts
        },
        "h1ComparisonData": {
            "schema": "h1-comparison-data/v0.5.4",
            "kind": "presentation-generated",
            "sourceComplexFingerprint": complex_fingerprint,
            "targetComplexFingerprint": complex_fingerprint,
            "presentation": {
                "cells": cells,
                "restrictions": restrictions,
                "equationLiftAtlas": {
                    "localLifts": typed_plan.complex.charts.iter().map(|chart| json!({
                        "chartRef": chart,
                        "coefficients": [0]
                    })).collect::<Vec<_>>(),
                    "transitionDifferences": typed_plan.complex.overlaps.iter().map(|overlap| {
                        let active = typed_plan.primitives.iter().find(|primitive| {
                            primitive.overlap_ref == overlap.id
                        }).is_some_and(|primitive| {
                            primitive.support.variables.iter().any(|variable| variable == "repair:cycle")
                        });
                        json!({
                            "overlapRef": overlap.id,
                            "coefficients": [u8::from(active)]
                        })
                    }).collect::<Vec<_>>()
                }
            }
        }
    });
    plan
}

fn presentation_generated_circle_archmap(root: &Path) -> Value {
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["sources"]
        .as_object_mut()
        .expect("sources are an object")
        .insert(
            "src:circle".to_string(),
            json!({
                "kind": "rust",
                "path": "src/circle.rs",
                "symbol": "CircleContext",
                "line": 1
            }),
        );
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms are an array")
        .push(json!({
            "id": "atom:circle",
            "kind": "component",
            "subject": "src:circle",
            "axis": "static",
            "predicate": "component",
            "refs": ["src:circle"]
        }));
    archmap["contexts"]
        .as_array_mut()
        .expect("contexts are an array")
        .push(json!({
            "id": "ctx:circle",
            "atoms": ["atom:circle"],
            "refs": ["src:circle"]
        }));
    archmap["covers"][0]["contexts"]
        .as_array_mut()
        .expect("cover contexts are an array")
        .push(json!("ctx:circle"));
    archmap
}

#[test]
fn cli_analyze_saga_descent_supplied_triple_and_gluing_measure_residual_class() {
    let root = ag_measurement_root();
    let plan = supplied_triple_saga_plan(&root, true);
    let out_dir = run_saga_fixture_lock("ag-saga-descent-supplied-class", plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let class = saga_row(&packet, "saga.residual-class");
    assert_eq!(class["verdict"], "measured_nonzero");
    assert_eq!(
        class["verdictData"]["methodStatus"],
        "nonzero_class_representative"
    );
    let invariant = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:residual-class")
        .expect("residual class invariant");
    assert_eq!(invariant["kind"], "residual-class-support");
    assert_eq!(invariant["residualClassSupport"]["quotient"], "Z1/B1");
    assert_eq!(
        invariant["residualClassSupport"]["cocycle"]["checked"],
        true
    );
    assert_eq!(
        invariant["residualClassSupport"]["cocycle"]["deltaOne"],
        "zero"
    );
    let comparison = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-comparison:h1-transfer")
        .expect("SAGA comparison invariant");
    assert_eq!(comparison["kind"], "h1-comparison-transfer");
    assert_eq!(comparison["status"], "established");
    assert_eq!(
        comparison["conclusionCode"],
        "SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA"
    );
    assert_eq!(comparison["contract"]["targetClassComputed"], true);
    assert_eq!(comparison["contract"]["contractChecked"], true);
    assert_eq!(comparison["suppliedCochainMap"]["level"], "cochain");
    assert_eq!(comparison["suppliedCochainMap"]["contractChecked"], true);
    for property in [
        "degreeOneLeftInverse",
        "degreeOneRightInverse",
        "differencePreserving",
        "degreeTwoZeroPreserving",
        "differentialCommutative",
    ] {
        assert_eq!(
            comparison["suppliedCochainMap"]["checkedProperties"][property],
            true
        );
    }
    assert_eq!(comparison["generatedQuotientTransfer"]["level"], "quotient");
    assert_eq!(
        comparison["generatedQuotientTransfer"]["preservesZeroPredicate"],
        true
    );
    assert_eq!(
        comparison["generatedQuotientTransfer"]["targetClassNonZero"],
        true
    );
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(closure["faithfulnessBasis"]["basis"], "supplied-data");
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| { row["theoremRef"] == "part4/4.6" && row["status"] == "assumed" })
    );
    assert!(packet["assumptions"].as_array().unwrap().iter().any(|row| {
        row["assumption"]
            .as_str()
            .is_some_and(|text| text.contains("comparison target complex enumeration"))
            && row["theoremRef"] == "part10/6.2"
            && row["status"] == "assumed"
    }));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
    );
    assert!(
        summary["translationRule"]["principalText"]
            .as_str()
            .is_some_and(|text| text.contains("Z1/B1"))
    );
}

#[test]
fn cli_analyze_saga_comparison_generates_transfer_from_presentations() {
    let root = ag_measurement_root();
    let plan = presentation_generated_saga_plan(&root, true);
    let out_dir = run_saga_fixture_lock("ag-saga-presentation-generated", plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let comparison = invariant_by_id(&packet, "saga-comparison:h1-transfer");
    assert_eq!(comparison["status"], "established");
    assert_eq!(
        comparison["conclusionCode"],
        ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS
    );
    assert_eq!(comparison["contract"]["h1ComparisonDataKind"], "presentation-generated");
    assert_eq!(comparison["contract"]["contractChecked"], true);
    assert_eq!(
        comparison["presentationGenerated"]["presentationExactness"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["generatorCompleteness"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["comparisonInput"]["kind"],
        "canonical-presentation-repair-plan"
    );
    assert_eq!(
        packet["inputDigests"]["repairPlan"]["path"],
        "input:repair_plan.json"
    );
    assert_eq!(
        comparison["presentationGenerated"]["generatedCochainMap"]["degreeZeroCommutative"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["generatedCochainMap"]["degreeOneCommutative"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["residualWitness"]["kind"],
        "computed-quotient-atlas-witness"
    );
    assert_eq!(
        comparison["generatedQuotientTransfer"]["kind"],
        "presentation-derived-Z1/B1-class-transfer"
    );
    assert!(
        validate_measurement_packet_value_v1(&packet)
            .iter()
            .all(|check| check.result == "pass")
    );
}

#[test]
fn cli_presentation_generated_packet_validator_rejects_tampered_evidence() {
    let root = ag_measurement_root();
    let plan = presentation_generated_saga_plan(&root, true);
    let out_dir = run_saga_fixture_lock("ag-saga-presentation-generated-packet-validator", plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let validator_failure = |candidate: &Value, path: &str| {
        validate_measurement_packet_value_v1(candidate)
            .iter()
            .any(|check| {
                check.id == "measurement-packet-schema052-saga-presentation-generated-evidence"
                    && check.result == "fail"
                    && check.examples.iter().any(|example| {
                        example
                            .source
                            .as_deref()
                            .is_some_and(|source| source.contains(path))
                    })
            })
    };

    let mut missing_witness = packet.clone();
    invariant_by_id_mut(&mut missing_witness, "saga-comparison:h1-transfer")["presentationGenerated"]
        ["residualWitness"] = Value::Null;
    assert!(validator_failure(
        &missing_witness,
        "presentationGenerated.residualWitness"
    ));

    let mut malformed_witness = packet.clone();
    invariant_by_id_mut(&mut malformed_witness, "saga-comparison:h1-transfer")["presentationGenerated"]
        ["residualWitness"]["h"] = Value::Null;
    assert!(validator_failure(
        &malformed_witness,
        "presentationGenerated.residualWitness.h"
    ));

    let mut coordinated_class_forgery = packet.clone();
    let comparison = invariant_by_id_mut(&mut coordinated_class_forgery, "saga-comparison:h1-transfer");
    comparison["presentationGenerated"]["semanticResidual"]["sourceClassNonZero"] = json!(false);
    comparison["presentationGenerated"]["equationResidual"]["targetClassNonZero"] = json!(false);
    comparison["generatedQuotientTransfer"]["sourceClassNonZero"] = json!(false);
    comparison["generatedQuotientTransfer"]["targetClassNonZero"] = json!(false);
    assert!(validator_failure(
        &coordinated_class_forgery,
        "presentationGenerated"
    ));

    let mut empty_derived_evidence = packet.clone();
    let generated = &mut invariant_by_id_mut(
        &mut empty_derived_evidence,
        "saga-comparison:h1-transfer",
    )["presentationGenerated"];
    generated["generatedCochainMap"]["degreeZero"] = json!([]);
    generated["generatedCochainMap"]["degreeOne"] = json!([]);
    generated["generatedCochainMap"]["degreeTwo"] = json!([]);
    generated["residualWitness"]["sourceImage"] = json!([]);
    generated["residualWitness"]["equationResidual"] = json!([]);
    generated["residualWitness"]["h"] = json!([]);
    assert!(validator_failure(
        &empty_derived_evidence,
        "presentationGenerated"
    ));

    let mut altered_comparison_input = packet.clone();
    invariant_by_id_mut(&mut altered_comparison_input, "saga-comparison:h1-transfer")
        ["presentationGenerated"]["comparisonInput"]["repairPlan"]["id"] =
        json!("repair-plan:forged-input");
    assert!(validator_failure(
        &altered_comparison_input,
        "inputDigests.repairPlan.sha256"
    ));
}

#[test]
fn cli_presentation_generated_packet_validator_rejects_valid_f2_witness_forgery() {
    let root = ag_measurement_root();
    let plan = read_json(&root.join("repair_plan_presentation_generated_circle.json"));
    let archmap = presentation_generated_circle_archmap(&root);
    let out_dir = run_saga_fixture_lock_with_archmap(
        "ag-saga-presentation-generated-circle-packet-validator",
        plan,
        archmap,
    );
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let mut forged = packet.clone();
    invariant_by_id_mut(&mut forged, "saga-comparison:h1-transfer")["presentationGenerated"]
        ["residualWitness"]["h"][0]["coefficients"] = json!([1]);
    assert!(validate_measurement_packet_value_v1(&forged)
        .iter()
        .any(|check| {
            check.id == "measurement-packet-schema052-saga-presentation-generated-evidence"
                && check.result == "fail"
                && check.examples.iter().any(|example| {
                    example
                        .source
                        .as_deref()
                        .is_some_and(|source| source.contains("presentationGenerated"))
                })
        }));
}

#[test]
fn cli_analyze_presentation_generated_circle_establishes_independent_h1_transfer() {
    let root = ag_measurement_root();
    let plan = read_json(&root.join("repair_plan_presentation_generated_circle.json"));
    let archmap = presentation_generated_circle_archmap(&root);
    let out_dir =
        run_saga_fixture_lock_with_archmap("ag-saga-presentation-generated-circle", plan, archmap);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let comparison = invariant_by_id(&packet, "saga-comparison:h1-transfer");
    assert_eq!(comparison["status"], "established");
    assert_eq!(
        comparison["conclusionCode"],
        ARCHSIG_SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS
    );
    assert_eq!(
        comparison["presentationGenerated"]["semanticResidual"]["sourceCocycle"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["semanticResidual"]["sourceClassNonZero"],
        true
    );
    assert_eq!(
        comparison["presentationGenerated"]["equationResidual"]["targetClassNonZero"],
        true
    );
}

#[test]
fn cli_compare_records_repair_plan_provenance_without_suppressing_verdict_rows() {
    let root = ag_measurement_root();
    let base_plan = presentation_generated_saga_plan(&root, true);
    let mut changed_atlas_plan = base_plan.clone();
    changed_atlas_plan["comparison"]["h1ComparisonData"]["presentation"]
        ["equationLiftAtlas"]["localLifts"][0]["coefficients"] = json!([1]);

    let base_run = run_saga_fixture_lock("ag-saga-compare-repair-plan-base", base_plan);
    let head_run = run_saga_fixture_lock(
        "ag-saga-compare-repair-plan-changed-atlas",
        changed_atlas_plan,
    );
    let base_manifest = read_json(&base_run.join("archsig-run-manifest.json"));
    let head_manifest = read_json(&head_run.join("archsig-run-manifest.json"));
    assert_ne!(
        base_manifest["inputDigests"]["repairPlan"]["sha256"],
        head_manifest["inputDigests"]["repairPlan"]["sha256"]
    );
    assert_ne!(base_manifest["runId"], head_manifest["runId"]);

    let compare_out = temp_dir("ag-saga-compare-repair-plan-provenance");
    run_sig0(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base run path is utf-8"),
        "--head-run",
        head_run.to_str().expect("head run path is utf-8"),
        "--out-dir",
        compare_out.to_str().expect("comparison output path is utf-8"),
    ]);
    let report = read_json(&compare_out.join("archsig-comparison-report.json"));
    assert_eq!(report["comparability"]["level"], "verdict-row");
    assert_eq!(report["comparability"]["sameRepairPlanDigest"], false);
    assert!(report["boundaryStatements"]
        .as_array()
        .expect("comparison boundaries are an array")
        .iter()
        .any(|boundary| boundary["kind"] == "repair_plan_changed_between_runs"));
}

#[test]
fn cli_compare_rejects_measurement_packet_and_manifest_provenance_mismatches() {
    let root = ag_measurement_root();
    let base_plan = presentation_generated_saga_plan(&root, true);
    let mut changed_plan = base_plan.clone();
    changed_plan["comparison"]["h1ComparisonData"]["presentation"]["equationLiftAtlas"]
        ["localLifts"][0]["coefficients"] = json!([1]);
    let base_run = run_saga_fixture_lock("ag-saga-compare-manifest-binding-base", base_plan);
    let packet_mismatch_run = run_saga_fixture_lock(
        "ag-saga-compare-manifest-binding-packet-mismatch",
        changed_plan.clone(),
    );
    fs::copy(
        base_run.join("archsig-measurement-packet.json"),
        packet_mismatch_run.join("archsig-measurement-packet.json"),
    )
    .expect("different-run packet can be substituted for negative test");
    let packet_mismatch_out = temp_dir("ag-saga-compare-manifest-binding-packet-output");
    run_sig0_expect_code(
        &[
            "compare",
            "--base-run",
            base_run.to_str().expect("base run path is utf-8"),
            "--head-run",
            packet_mismatch_run
                .to_str()
                .expect("packet mismatch run path is utf-8"),
            "--out-dir",
            packet_mismatch_out
                .to_str()
                .expect("packet mismatch output path is utf-8"),
        ],
        2,
    );

    let digest_mismatch_run = run_saga_fixture_lock(
        "ag-saga-compare-manifest-binding-digest-mismatch",
        changed_plan,
    );
    let manifest_path = digest_mismatch_run.join("archsig-run-manifest.json");
    let mut manifest = read_json(&manifest_path);
    manifest["artifactDigests"]["measurementPacket"]["sha256"] =
        json!("0000000000000000000000000000000000000000000000000000000000000000");
    fs::write(
        &manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("manifest serializes"),
    )
    .expect("tampered manifest writes");
    let digest_mismatch_out = temp_dir("ag-saga-compare-manifest-binding-digest-output");
    run_sig0_expect_code(
        &[
            "compare",
            "--base-run",
            base_run.to_str().expect("base run path is utf-8"),
            "--head-run",
            digest_mismatch_run
                .to_str()
                .expect("digest mismatch run path is utf-8"),
            "--out-dir",
            digest_mismatch_out
                .to_str()
                .expect("digest mismatch output path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_presentation_generated_transfer_uses_equation_quotient_for_target_h1() {
    let root = ag_measurement_root();
    let mut plan = presentation_generated_saga_plan(&root, true);
    for cell in plan["comparison"]["h1ComparisonData"]["presentation"]["cells"]
        .as_array_mut()
        .expect("presentation cells")
    {
        cell["repairRelationMatrix"] = json!([[1]]);
        cell["equationRelationMatrix"] = json!([[1]]);
    }
    let out_dir = run_saga_fixture_lock("ag-saga-presentation-quotient-zero", plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let comparison = invariant_by_id(&packet, "saga-comparison:h1-transfer");
    assert_eq!(comparison["contract"]["contractChecked"], true);
    assert_eq!(comparison["contract"]["targetClassComputed"], true);
    assert_eq!(
        comparison["presentationGenerated"]["equationResidual"]["targetClassNonZero"],
        false
    );
    assert_eq!(comparison["status"], "established");
    assert_eq!(
        comparison["generatedQuotientTransfer"]["sourceClassNonZero"],
        false
    );
    assert_eq!(
        comparison["generatedQuotientTransfer"]["targetClassNonZero"],
        false
    );
}

#[test]
fn cli_analyze_saga_descent_supplied_zero_class_measures_no_residual_class() {
    let root = ag_measurement_root();
    let plan = supplied_triple_saga_plan(&root, false);
    let out_dir = run_saga_fixture_lock("ag-saga-descent-supplied-zero-class", plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let class = saga_row(&packet, "saga.residual-class");
    assert_eq!(class["verdict"], "measured_zero");
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(closure["faithfulnessBasis"]["basis"], "supplied-data");
}

#[test]
fn cli_saga_comparison_separates_missing_class_from_contract_violation() {
    let root = ag_measurement_root();

    let missing_class_plan = read_json(&root.join("repair_plan_comparison.json"));
    let missing_class_out = run_saga_fixture_lock(
        "ag-saga-comparison-class-prerequisite-missing",
        missing_class_plan,
    );
    let missing_class_packet =
        read_json(&missing_class_out.join("archsig-measurement-packet.json"));
    let missing_class = invariant_by_id(&missing_class_packet, "saga-comparison:h1-transfer");
    assert_eq!(missing_class["status"], "silence_by_design");
    assert_eq!(
        missing_class["reason"],
        "residual_class_prerequisite_not_measured"
    );
    let what_next = missing_class["whatNext"]
        .as_str()
        .expect("missing source class explains required input slots");
    for slot in [
        "complex.tripleOverlaps",
        "coefficient",
        "trueSheafCertificate",
        "gluingData",
    ] {
        assert!(
            what_next.contains(slot),
            "whatNext omits required slot {slot}"
        );
    }
    assert!(!what_next.contains("saga.residual-class"));
    assert!(missing_class.get("failureCode").is_none());
}

#[test]
fn cli_analyze_saga_descent_uncovered_residual_blocks_global_coherence() {
    let out_dir = temp_dir("ag-saga-descent-uncovered");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["primitives"][0]["resL"] = json!(["repair:a"]);
    repair_plan["primitives"][0]["resR"] = json!(["repair:b"]);
    repair_plan["primitives"][0]["support"]["variables"] = json!(["repair:a", "repair:b"]);
    repair_plan["primitives"][1]["resL"] = json!(["repair:b"]);
    repair_plan["primitives"][1]["resR"] = json!(["repair:c"]);
    repair_plan["primitives"][1]["support"]["variables"] = json!(["repair:b", "repair:c"]);
    repair_plan["primitives"][2]["resL"] = json!(["repair:a"]);
    repair_plan["primitives"][2]["resR"] = json!(["repair:c"]);
    repair_plan["primitives"][2]["support"]["variables"] = json!(["repair:a", "repair:c"]);
    let repair_plan_path = out_dir.join("repair_plan_uncovered.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdict"],
        "measured_zero"
    );
    let global = saga_row(&packet, "saga.global-coherence");
    assert_eq!(global["verdict"], "unmeasured");
    assert_eq!(
        global["verdictData"]["methodStatus"],
        "residual_not_covered"
    );
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentCovered"],
        false
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_saga_summary_has_no_class_vocabulary(&summary);
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    );
}

#[test]
fn cli_analyze_saga_descent_ignores_alias_outside_residual_component() {
    let out_dir = temp_dir("ag-saga-descent-outside-alias");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["primitives"][0]["resL"] = json!(["src:inventory"]);
    repair_plan["primitives"][0]["resR"] = json!([]);
    repair_plan["primitives"][0]["support"]["variables"] = json!(["src:inventory"]);
    repair_plan["primitives"][1]["resL"] = json!([]);
    repair_plan["primitives"][1]["resR"] = json!([]);
    repair_plan["primitives"][1]["support"]["variables"] = json!([]);
    repair_plan["primitives"][2]["resL"] = json!(["src:inventory"]);
    repair_plan["primitives"][2]["resR"] = json!([]);
    repair_plan["primitives"][2]["support"]["variables"] = json!(["src:inventory"]);
    repair_plan["semanticProjection"]["lambda"] = json!([
        "atom:order",
        "atom:inventory",
        "atom:order-inventory-restriction"
    ]);
    repair_plan["semanticProjection"]["pi"] = json!([
        {"atomRef": "atom:order", "subject": "src:order"},
        {"atomRef": "atom:inventory", "subject": "src:inventory"},
        {"atomRef": "atom:order-inventory-restriction", "subject": "src:order"}
    ]);
    let repair_plan_path = out_dir.join("repair_plan_outside_alias.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdict"],
        "measured_zero"
    );
    let global = saga_row(&packet, "saga.global-coherence");
    assert_eq!(global["verdict"], "measured_zero");
    assert_eq!(
        global["verdictData"]["methodStatus"],
        "complete_support_global_coherent"
    );
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentCovered"],
        true
    );
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentFaithful"],
        true
    );
    assert!(
        closure["closureDiagnostics"]["aliasWitnesses"]
            .as_array()
            .expect("alias witnesses")
            .is_empty(),
        "alias witnesses are residual-component relative"
    );
}

#[test]
fn cli_analyze_saga_descent_mode_none_keeps_global_coherence_silent() {
    let out_dir = temp_dir("ag-saga-descent-mode-none");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["faithfulness"]["mode"] = json!("none");
    let repair_plan_path = out_dir.join("repair_plan_mode_none.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdict"],
        "measured_zero"
    );
    let global = saga_row(&packet, "saga.global-coherence");
    assert_eq!(global["verdict"], "unmeasured");
    assert_eq!(
        global["verdictData"]["methodStatus"],
        "complete_support_not_declared"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .expect("boundary statements")
            .iter()
            .any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "complete_support_not_declared"
            })
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_saga_summary_has_no_class_vocabulary(&summary);
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    );
}

#[test]
fn cli_analyze_saga_descent_mode_none_with_nonboundary_residual_stays_silent() {
    let root = ag_measurement_root();
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["faithfulness"]["mode"] = json!("none");
    repair_plan["complex"]["tripleOverlaps"] = json!([]);
    for primitive in repair_plan["primitives"].as_array_mut().unwrap() {
        primitive["resL"] = json!(["repair:cycle"]);
        primitive["resR"] = json!([]);
        primitive["support"]["variables"] = json!(["repair:cycle"]);
    }
    let out_dir = run_saga_fixture_lock("ag-saga-descent-mode-none-nonboundary", repair_plan);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdictData"]["methodStatus"],
        "residual_not_in_b1"
    );
    assert_eq!(
        saga_row(&packet, "saga.global-coherence")["verdict"],
        "unmeasured"
    );
    assert_eq!(
        saga_row(&packet, "saga.global-coherence")["verdictData"]["methodStatus"],
        "complete_support_not_declared"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_saga_summary_has_no_class_vocabulary(&summary);
}

#[test]
fn cli_gate_allows_saga_silence_by_design_with_boundary_override() {
    let out_dir = temp_dir("ag-saga-descent-gate-boundary-override");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["faithfulness"]["mode"] = json!("none");
    let repair_plan_path = out_dir.join("repair_plan_mode_none.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let comparison = invariant_by_id(&packet, "saga-comparison:h1-transfer");
    assert_eq!(comparison["status"], "silence_by_design");
    assert_eq!(comparison["reason"], "comparison_data_not_supplied");
    assert!(comparison["whatNext"].as_str().is_some_and(|text| {
        text.contains("incidence bridge") && text.contains("H1 comparison contract")
    }));

    let report_path = out_dir.join("archsig-gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        out_dir
            .join("archsig-measurement-packet.json")
            .to_str()
            .expect("path is utf-8"),
        "--policy",
        root.join("gate_policy_conservative.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        report_path.to_str().expect("path is utf-8"),
    ]);
    let report = read_json(&report_path);
    assert_eq!(report["decision"], "PASS_WITHIN_GATE_POLICY");
    let saga_mapping = report["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("applied mappings")
        .iter()
        .find(|mapping| {
            mapping["rowRef"]
                .as_str()
                .is_some_and(|row_ref| row_ref.contains("saga-global-coherence"))
        })
        .expect("saga global coherence mapping exists");
    assert_eq!(saga_mapping["action"], "pass_with_boundary");
    assert_eq!(saga_mapping["boundaryOverrideApplied"], true);
    let comparison_mapping = report["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("applied mappings")
        .iter()
        .find(|mapping| mapping["rowRef"] == "saga-comparison:h1-transfer")
        .expect("comparison silence mapping exists");
    assert_eq!(comparison_mapping["action"], "pass_with_boundary");
    assert_eq!(comparison_mapping["boundaryOverrideApplied"], true);
}

#[test]
fn cli_gate_allows_diagnostic_ceiling_silence_with_boundary_override() {
    let out_dir = temp_dir("ag-diagnostic-ceiling-gate-boundary-override");
    let root = ag_measurement_root();
    let (mut policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "law:saga-grounded",
        "evaluator": "ag.saga-grounded",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    profile["diagnosticCeiling"] = json!("descent");
    profile["witnessFamily"] = json!([{
        "law": "ag.saga-grounded",
        "variable": "atom:order"
    }]);
    let policy_path = out_dir.join("law_policy_saga_grounded.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json").to_str().unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(&policy_path)
            .to_str()
            .unwrap(),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .unwrap(),
        "--out-dir",
        out_dir.to_str().unwrap(),
    ]);

    let packet_path = out_dir.join("archsig-measurement-packet.json");
    let packet = read_json(&packet_path);
    let ceiling_row = packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-grounded")
        .expect("diagnostic ceiling row");
    assert_eq!(ceiling_row["verdict"], "not_computed");
    assert_eq!(
        ceiling_row["verdictData"]["methodStatus"],
        "diagnostic_ceiling_not_reached"
    );
    let ceiling_ref = ceiling_row["verdictRef"].as_str().unwrap();
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["scopeRefs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|scope_ref| scope_ref == ceiling_ref)
            })
    );

    let gate_report_path = out_dir.join("gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        packet_path.to_str().unwrap(),
        "--policy",
        root.join("gate_policy_conservative.json").to_str().unwrap(),
        "--out",
        gate_report_path.to_str().unwrap(),
    ]);
    let gate_report = read_json(&gate_report_path);
    assert_eq!(gate_report["decision"], "PASS_WITHIN_GATE_POLICY");
    let mapping = gate_report["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .unwrap()
        .iter()
        .find(|mapping| mapping["rowRef"] == ceiling_ref)
        .expect("diagnostic ceiling row reaches gate mapping");
    assert_eq!(mapping["action"], "pass_with_boundary");
    assert_eq!(mapping["boundaryOverrideApplied"], true);
}

#[test]
fn cli_analyze_saga_descent_nonboundary_residual_is_unconditional_negative() {
    let out_dir = temp_dir("ag-saga-descent-nonboundary");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["complex"]["tripleOverlaps"] = json!([]);
    for primitive in repair_plan["primitives"].as_array_mut().unwrap() {
        primitive["resL"] = json!(["repair:cycle"]);
        primitive["resR"] = json!([]);
        primitive["support"]["variables"] = json!(["repair:cycle"]);
    }
    let repair_plan_path = out_dir.join("repair_plan_nonboundary.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let membership = saga_row(&packet, "saga.residual-boundary-membership");
    assert_eq!(membership["verdict"], "measured_nonzero");
    assert_eq!(
        membership["verdictData"]["methodStatus"],
        "residual_not_in_b1"
    );
    let invariant = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:boundary-membership")
        .expect("boundary membership invariant");
    assert_eq!(invariant["boundaryMembership"]["inB1"], false);
    assert!(json_contains_substring(
        &invariant["boundaryMembership"]["residualSupport"],
        "overlap:order-shared"
    ));
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_saga_summary_has_no_class_vocabulary(&summary);
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL
    );
}

#[test]
fn cli_analyze_saga_descent_alias_witness_blocks_global_coherence() {
    let out_dir = temp_dir("ag-saga-descent-alias");
    let root = ag_measurement_root();
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut repair_plan = read_json(&root.join("repair_plan_complete_support.json"));
    repair_plan["primitives"][0]["resL"] = json!(["src:order"]);
    repair_plan["primitives"][0]["resR"] = json!([]);
    repair_plan["primitives"][0]["support"]["variables"] = json!(["src:order"]);
    repair_plan["primitives"][1]["resL"] = json!([]);
    repair_plan["primitives"][1]["resR"] = json!([]);
    repair_plan["primitives"][1]["support"]["variables"] = json!([]);
    repair_plan["primitives"][2]["resL"] = json!(["src:order"]);
    repair_plan["primitives"][2]["resR"] = json!([]);
    repair_plan["primitives"][2]["support"]["variables"] = json!(["src:order"]);
    repair_plan["semanticProjection"]["lambda"] =
        json!(["atom:order", "atom:order-inventory-restriction"]);
    repair_plan["semanticProjection"]["k"] = json!(["src:order"]);
    repair_plan["semanticProjection"]["pi"] = json!([
        {"atomRef": "atom:order", "subject": "src:order"},
        {"atomRef": "atom:order-inventory-restriction", "subject": "src:order"}
    ]);
    let repair_plan_path = out_dir.join("repair_plan_alias.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&packet, "saga.residual-boundary-membership")["verdict"],
        "measured_zero"
    );
    let global = saga_row(&packet, "saga.global-coherence");
    assert_eq!(global["verdict"], "measured_nonzero");
    assert_eq!(global["verdictData"]["methodStatus"], "alias_not_faithful");
    let closure = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:closure-diagnostics")
        .expect("closure diagnostics invariant");
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentCovered"],
        true
    );
    assert_eq!(
        closure["closureDiagnostics"]["residualComponentFaithful"],
        false
    );
    assert!(
        !closure["closureDiagnostics"]["aliasWitnesses"]
            .as_array()
            .expect("alias witnesses")
            .is_empty()
    );
}

#[test]
fn cli_analyze_contract_fixture_locks_are_byte_deterministic() {
    let root = ag_measurement_root();

    let saga_positive_a = run_saga_fixture_lock(
        "saga-contract-boundary-positive-a",
        read_json(&root.join("repair_plan_complete_support.json")),
    );
    let saga_positive_b = run_saga_fixture_lock(
        "saga-contract-boundary-positive-b",
        read_json(&root.join("repair_plan_complete_support.json")),
    );
    assert_byte_identical_analysis_artifacts(&saga_positive_a, &saga_positive_b);
    let positive_packet = read_json(&saga_positive_a.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&positive_packet, "saga.residual-boundary-membership")["verdict"],
        "measured_zero"
    );
    assert_eq!(
        saga_row(&positive_packet, "saga.global-coherence")["verdict"],
        "measured_zero"
    );
    let positive_summary = read_json(&saga_positive_a.join("archsig-analysis-summary.json"));
    assert_eq!(
        positive_summary["translationRule"]["theoremRef"],
        "part10/3.5"
    );
    assert_eq!(
        positive_summary["translationRule"]["concreteSupportRefs"],
        json!([])
    );

    let mut nonboundary_repair = read_json(&root.join("repair_plan_complete_support.json"));
    nonboundary_repair["complex"]["tripleOverlaps"] = json!([]);
    for primitive in nonboundary_repair["primitives"].as_array_mut().unwrap() {
        primitive["resL"] = json!(["repair:cycle"]);
        primitive["resR"] = json!([]);
        primitive["support"]["variables"] = json!(["repair:cycle"]);
    }
    let saga_negative_a = run_saga_fixture_lock(
        "saga-contract-boundary-negative-a",
        nonboundary_repair.clone(),
    );
    let saga_negative_b =
        run_saga_fixture_lock("saga-contract-boundary-negative-b", nonboundary_repair);
    assert_byte_identical_analysis_artifacts(&saga_negative_a, &saga_negative_b);
    let negative_packet = read_json(&saga_negative_a.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&negative_packet, "saga.residual-boundary-membership")["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        saga_row(&negative_packet, "saga.residual-boundary-membership")["verdictData"]["methodStatus"],
        "residual_not_in_b1"
    );
    assert_eq!(
        invariant_by_id(&negative_packet, "saga-descent:boundary-membership")["boundaryMembership"]
            ["inB1"],
        false
    );
    let negative_summary = read_json(&saga_negative_a.join("archsig-analysis-summary.json"));
    assert_eq!(
        negative_summary["translationRule"]["theoremRef"],
        "part10/3.4"
    );
    assert!(
        negative_summary["translationRule"]["concreteSupportRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty()),
        "nonboundary residual must name concrete support refs"
    );

    let mut alias_repair = read_json(&root.join("repair_plan_complete_support.json"));
    alias_repair["primitives"][0]["resL"] = json!(["src:order"]);
    alias_repair["primitives"][0]["resR"] = json!([]);
    alias_repair["primitives"][0]["support"]["variables"] = json!(["src:order"]);
    alias_repair["primitives"][1]["resL"] = json!([]);
    alias_repair["primitives"][1]["resR"] = json!([]);
    alias_repair["primitives"][1]["support"]["variables"] = json!([]);
    alias_repair["primitives"][2]["resL"] = json!(["src:order"]);
    alias_repair["primitives"][2]["resR"] = json!([]);
    alias_repair["primitives"][2]["support"]["variables"] = json!(["src:order"]);
    alias_repair["semanticProjection"]["lambda"] =
        json!(["atom:order", "atom:order-inventory-restriction"]);
    alias_repair["semanticProjection"]["k"] = json!(["src:order"]);
    alias_repair["semanticProjection"]["pi"] = json!([
        {"atomRef": "atom:order", "subject": "src:order"},
        {"atomRef": "atom:order-inventory-restriction", "subject": "src:order"}
    ]);
    let alias_a = run_saga_fixture_lock("saga-contract-alias-negative-a", alias_repair.clone());
    let alias_b = run_saga_fixture_lock("saga-contract-alias-negative-b", alias_repair);
    assert_byte_identical_analysis_artifacts(&alias_a, &alias_b);
    let alias_packet = read_json(&alias_a.join("archsig-measurement-packet.json"));
    assert_eq!(
        saga_row(&alias_packet, "saga.global-coherence")["verdict"],
        "measured_nonzero"
    );
    let alias_closure = invariant_by_id(&alias_packet, "saga-descent:closure-diagnostics");
    assert_eq!(
        alias_closure["closureDiagnostics"]["residualComponentCovered"],
        true
    );
    assert_eq!(
        alias_closure["closureDiagnostics"]["residualComponentFaithful"],
        false
    );
    assert!(
        alias_closure["closureDiagnostics"]["aliasWitnesses"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    );

    let cech_a = run_analyze_fixture_lock(
        "saga-contract-cech-b8-a",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
        None,
    );
    let cech_b = run_analyze_fixture_lock(
        "saga-contract-cech-b8-b",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
        None,
    );
    assert_byte_identical_analysis_artifacts(&cech_a, &cech_b);
    let cech_packet = read_json(&cech_a.join("archsig-measurement-packet.json"));
    let cech = invariant_by_id(&cech_packet, "cech-cohomology:profile:ag-default@1");
    let cech_summary = read_json(&cech_a.join("archsig-analysis-summary.json"));
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"],
        json!(["atom:b8-cocycle-P"])
    );
    assert_eq!(
        cech["observedCocycle"]["representative"],
        json!([{
            "edge": "ctx:W_dep->ctx:W_state",
            "sourceContext": "ctx:W_dep",
            "targetContext": "ctx:W_state",
            "value": 1,
            "supportAtomRefs": ["atom:b8-cocycle-P"]
        }])
    );
    assert_eq!(cech["dimensions"]["H1"], Value::from(1));
    assert_eq!(cech["observedCocycle"]["classNonzero"], true);
    assert_eq!(cech_summary["translationRule"]["theoremRef"], "part4/12.3");
    assert_eq!(
        cech_summary["translationRule"]["concreteSupportRefs"],
        json!(["atom:b8-cocycle-P"])
    );

    let repair_a = run_analyze_fixture_lock(
        "saga-contract-square-free-a",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
        None,
    );
    let repair_b = run_analyze_fixture_lock(
        "saga-contract-square-free-b",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
        None,
    );
    assert_byte_identical_analysis_artifacts(&repair_a, &repair_b);
    let repair_packet = read_json(&repair_a.join("archsig-measurement-packet.json"));
    let repair_reading = repair_packet["analyticReadings"]
        .as_array()
        .expect("analytic readings")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "repair-lower-bound-inspection@1")
        .expect("repair lower-bound reading exists");
    assert_eq!(
        repair_reading["value"]["minimalHittingSets"],
        json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    let repair_summary = read_json(&repair_a.join("archsig-analysis-summary.json"));
    assert_eq!(
        repair_summary["conclusion"],
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED
    );
    assert_eq!(repair_summary["translationRule"]["theoremRef"], "part8/5.2");
    assert_eq!(
        repair_summary["translationRule"]["concreteSupportRefs"],
        json!(["x_inventory", "x_checkout+x_payment"])
    );
}

#[test]
fn cli_measurement_profile_finite_bounds_cap_and_effective_lowering() {
    let out_dir = temp_dir("ag-profile-finite-bounds");
    let root = ag_measurement_root();

    let mut cap_exceeded = read_json(&root.join("measurement_profile_ag.json"));
    cap_exceeded["finiteBounds"]["maxSquareFreeWitnessVariables"] = json!(13);
    let cap_path = out_dir.join("measurement_profile_cap_exceeded.json");
    fs::write(
        &cap_path,
        serde_json::to_vec_pretty(&cap_exceeded).expect("profile serializes"),
    )
    .expect("cap profile writes");
    let cap_report = out_dir.join("cap-report.json");
    run_sig0_expect_code(
        &[
            "measurement-profile",
            "--measurement-profile",
            cap_path.to_str().expect("path is utf-8"),
            "--out",
            cap_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let cap_json = read_json(&cap_report);
    assert_eq!(
        check_by_id(&cap_json, "measurement-profile-schema052-finite-bounds")["result"],
        "fail"
    );

    let mut reserved_profile = read_json(&root.join("measurement_profile_ag.json"));
    reserved_profile["diagnosticCeiling"] = json!({"reserved": true});
    let reserved_profile_path = out_dir.join("measurement_profile_reserved.json");
    fs::write(
        &reserved_profile_path,
        serde_json::to_vec_pretty(&reserved_profile).expect("reserved profile serializes"),
    )
    .expect("reserved profile writes");
    let reserved_profile_report = out_dir.join("reserved-profile-report.json");
    run_sig0_expect_code(
        &[
            "measurement-profile",
            "--measurement-profile",
            reserved_profile_path.to_str().expect("path is utf-8"),
            "--out",
            reserved_profile_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&reserved_profile_report),
            "measurement-profile-schema052-diagnostic-ceiling"
        )["result"],
        "fail"
    );

    let mut null_reserved_profile = read_json(&root.join("measurement_profile_ag.json"));
    null_reserved_profile["diagnosticCeiling"] = Value::Null;
    let null_reserved_profile_path = out_dir.join("measurement_profile_reserved_null.json");
    fs::write(
        &null_reserved_profile_path,
        serde_json::to_vec_pretty(&null_reserved_profile)
            .expect("null reserved profile serializes"),
    )
    .expect("null reserved profile writes");
    let null_reserved_profile_report = out_dir.join("reserved-profile-null-report.json");
    run_sig0_expect_code(
        &[
            "measurement-profile",
            "--measurement-profile",
            null_reserved_profile_path.to_str().expect("path is utf-8"),
            "--out",
            null_reserved_profile_report
                .to_str()
                .expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        check_by_id(
            &read_json(&null_reserved_profile_report),
            "measurement-profile-schema052-diagnostic-ceiling"
        )["result"],
        "fail"
    );

    let mut selected_ceiling_profile = read_json(&root.join("measurement_profile_ag.json"));
    selected_ceiling_profile["diagnosticCeiling"] = json!("descent");
    let selected_ceiling_path = out_dir.join("measurement_profile_ceiling.json");
    fs::write(
        &selected_ceiling_path,
        serde_json::to_vec_pretty(&selected_ceiling_profile)
            .expect("selected ceiling profile serializes"),
    )
    .expect("selected ceiling profile writes");
    let selected_ceiling_report = out_dir.join("selected-ceiling-report.json");
    run_sig0(&[
        "measurement-profile",
        "--measurement-profile",
        selected_ceiling_path.to_str().expect("path is utf-8"),
        "--out",
        selected_ceiling_report.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(
        read_json(&selected_ceiling_report)["summary"]["result"],
        "pass"
    );

    let (lowered_policy, mut lowered_profile) =
        read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    lowered_profile["finiteBounds"]["maxSquareFreeWitnessVariables"] = json!(1);
    let policy_path = out_dir.join("law_policy_lowered_square_free.json");
    write_test_policy_and_profile(&policy_path, lowered_policy, lowered_profile);
    let lowered_output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(lowered_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&lowered_output.stderr)
            .contains("finiteBounds.maxSquareFreeWitnessVariables=1"),
        "lowered finiteBounds must become the effective evaluator bound\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&lowered_output.stdout),
        String::from_utf8_lossy(&lowered_output.stderr)
    );
}

#[test]
fn cli_analyze_rejects_measurement_profile_witness_family() {
    let out_dir = temp_dir("ag-measurement-profile-witness-family-rejected");
    let root = ag_measurement_root();
    let policy_path = out_dir.join("law_policy.json");
    let profile_path = out_dir.join("measurement_profile.json");
    let mut profile = read_json(&root.join("measurement_profile_ag.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.cech-obstruction", "variable": "e_order_shared"}
    ]);
    fs::write(
        &policy_path,
        fs::read(root.join("law_policy_ag.json")).expect("policy fixture reads"),
    )
    .expect("policy fixture writes");
    fs::write(
        &profile_path,
        serde_json::to_vec_pretty(&profile).expect("profile serializes"),
    )
    .expect("profile writes");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("unknown field `witnessFamily`"));
    assert!(!out_dir.join("archsig-measurement-packet.json").exists());
}

#[test]
fn cli_analyze_v2_writes_measurement_packet_foundation() {
    let out_dir = temp_dir("ag-measurement-analyze");
    let root = ag_measurement_root();
    let profile_path = out_dir.join("measurement_profile_ceiling.json");
    let mut profile = read_json(&root.join("measurement_profile_ag.json"));
    profile["diagnosticCeiling"] = json!("descent");
    fs::write(
        &profile_path,
        serde_json::to_vec_pretty(&profile).expect("ceiling profile serializes"),
    )
    .expect("ceiling profile writes");
    let law_surface_path = out_dir.join("law_surface_stage3.json");
    let mut law_surface = read_json(&root.join("law_surface_ag_v052.json"));
    law_surface["skeleton"] = json!([{
        "simplex": "vertex:order",
        "supportAtomRef": "atom:order",
        "requiredLawId": "law:checkout"
    }]);
    law_surface["defectSources"] = json!([{
        "lawId": "law:checkout",
        "coverRef": "cover:order-inventory",
        "chartDefects": [{
            "chart": "ctx:order",
            "defectObservable": { "axis": "cech", "predicate": "sectionValue" }
        }],
        "holdsCriterion": {
            "kind": "defect-raw-value-zero",
            "zeroSense": "empty-witness-set"
        }
    }]);
    law_surface["quotientSheafCondition"] = json!({"mode": "assumed"});
    fs::write(
        &law_surface_path,
        serde_json::to_vec_pretty(&law_surface).expect("stage3 law surface serializes"),
    )
    .expect("stage3 law surface writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        law_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["schema"], "normalized-archmap/v0.5.4");
    assert_eq!(
        normalized["summary"]["doctrineFingerprint"],
        "sha256:aat-canonical-doctrine-schema052"
    );

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["schema"], "archsig-measurement-packet/v0.5.4");
    assert!(packet["profile"].is_object());
    assert!(packet["structuralVerdict"].is_array());
    assert!(packet["computedInvariants"].is_array());
    assert!(packet["analyticReadings"].is_array());
    assert!(packet["assumptions"].is_array());
    assert!(packet["boundaryStatements"].is_array());
    assert!(packet["nonConclusions"].is_array());
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|text| {
                text.as_str().is_some_and(|text| {
                    text.contains("silence_by_design: diagnostic ceiling descent")
                })
            })
    );
    let boundary_texts = packet["boundaryStatements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|statement| statement["text"].as_str().expect("boundary text"))
        .collect::<BTreeSet<_>>();
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|text| { boundary_texts.contains(text.as_str().expect("nonConclusion text")) }),
        "compat nonConclusions must be reproduced as boundaryStatements text"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| statement["kind"] == "not_applicable"
                && statement["scopeRefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|scope_ref| scope_ref == "candidate-regime:stability-placeholder")),
        "analytic-only theorem candidate must be represented as a not_applicable boundary"
    );
    let boundary_kinds = packet["boundaryStatements"]
        .as_array()
        .unwrap()
        .iter()
        .map(|statement| statement["kind"].as_str().expect("boundary kind"))
        .collect::<BTreeSet<_>>();
    assert!(
        boundary_kinds.is_subset(&BTreeSet::from([
            "silence_by_design",
            "out_of_selected_vocabulary",
            "unmeasured_support",
            "violated_assumption",
            "blocked_method",
            "not_applicable",
        ])),
        "M8 must reuse existing BoundaryStatementV1 kinds"
    );
    for (id, kind, reason_text, scope_text) in [
        (
            "boundary:m8:higher-hn-silence",
            "silence_by_design",
            "higher_hn_n_ge_3_part_iv_scope_boundary",
            "Cohomological readings in degrees n>=3",
        ),
        (
            "boundary:m8:non-abelian-stack-gerbe-vocabulary",
            "out_of_selected_vocabulary",
            "non_abelian_stack_gerbe_outside_abelian_f2_vocabulary",
            "Non-abelian stack/gerbe degree-2 descent data",
        ),
        (
            "boundary:m8:higher-tor-unmeasured-support",
            "unmeasured_support",
            "higher_tor_i_ge_2_unmeasured_support",
            "Higher Tor_i for i>=2",
        ),
    ] {
        assert!(
            packet["boundaryStatements"].as_array().unwrap().iter().any(
                |statement| statement["id"] == id
                    && statement["kind"] == kind
                    && statement["reason"] == reason_text
                    && statement["scopeRefs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|scope_ref| scope_ref == packet["packetId"].as_str().unwrap())
                    && statement["text"]
                        .as_str()
                        .is_some_and(|text| text.contains(scope_text))
            ),
            "M8 typed boundary {id} must keep its own kind and scope"
        );
    }
    assert!(
        packet["nonConclusions"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(Value::as_str)
            .all(|text| {
                !text.contains("Cohomological readings in degrees n>=3")
                    && !text.contains("Non-abelian stack/gerbe degree-2 descent data")
                    && !text.contains("Higher Tor_i")
            }),
        "M8 silence must be a typed boundary, not a nonConclusions headline"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .len(),
        1,
        "M8 typed boundary must not generate a structural verdict"
    );
    assert!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .iter()
            .all(|row| row["verdictData"]["methodStatus"] != "depends_on_violated_assumption"),
        "M8 typed boundary must not trigger assumption dependency propagation"
    );
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(0));
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(
        cech["selectedH2"]["status"],
        "not_measured_for_triple_overlap_faces"
    );
    assert_eq!(packet["analyticReadings"][0]["regime"], "theorem-candidate");

    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(validation["summary"]["result"], "pass");

    let viewer = read_json(&out_dir.join("archsig-atom-viewer-data.json"));
    assert_eq!(viewer["schema"], "archsig-atom-viewer-data/v0.5.4");
    assert_eq!(
        viewer["sourceArtifactRefs"]["measurementPacket"],
        "archsig-measurement-packet.json"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_representative_json_artifacts_omit_absolute_sheaf_cohomology_notation() {
    let base_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-base",
        "archmap_v2.json",
        "law_policy_ag.json",
        "law_surface_ag_v052.json",
        None,
    );
    let head_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-head",
        "archmap_v2.json",
        "law_policy_ag.json",
        "law_surface_ag_v052.json",
        None,
    );

    let comparison_dir = temp_dir("full-sheaf-output-lint-comparison");
    run_sig0(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base run path is utf-8"),
        "--head-run",
        head_run.to_str().expect("head run path is utf-8"),
        "--out-dir",
        comparison_dir
            .to_str()
            .expect("comparison output path is utf-8"),
    ]);

    let gate_report_path = temp_dir("full-sheaf-output-lint-gate").join("archsig-gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        head_run
            .join("archsig-measurement-packet.json")
            .to_str()
            .expect("packet path is utf-8"),
        "--policy",
        ag_measurement_root()
            .join("gate_policy_conservative.json")
            .to_str()
            .expect("gate policy path is utf-8"),
        "--out",
        gate_report_path
            .to_str()
            .expect("gate report path is utf-8"),
    ]);

    let output_surfaces = [
        (
            "measurement packet",
            head_run.join("archsig-measurement-packet.json"),
        ),
        (
            "analysis summary",
            head_run.join("archsig-analysis-summary.json"),
        ),
        (
            "comparison report",
            comparison_dir.join("archsig-comparison-report.json"),
        ),
        ("gate report", gate_report_path),
    ];
    for (surface, path) in output_surfaces {
        let content = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "{surface} output must be readable at {}: {error}",
                path.display()
            )
        });
        assert!(
            !has_absolute_sheaf_cohomology_notation(&content),
            "{surface} must not emit absolute H^n(X, ...) sheaf notation"
        );
    }

    let period_run = run_analyze_fixture_lock(
        "full-sheaf-output-lint-period",
        "archmap_v2_period_stokes.json",
        "law_policy_period.json",
        "law_surface_ag_v052.json",
        None,
    );
    let period_packet = read_json(&period_run.join("archsig-measurement-packet.json"));
    assert_eq!(period_packet["profile"]["coefficient"], "R");
    let period_m8 = period_packet["boundaryStatements"]
        .as_array()
        .expect("period boundaryStatements is array")
        .iter()
        .filter(|statement| {
            statement["id"]
                .as_str()
                .is_some_and(|id| id.starts_with("boundary:m8:"))
        })
        .collect::<Vec<_>>();
    assert_eq!(period_m8.len(), 2);
    for (id, kind, reason) in [
        (
            "boundary:m8:higher-hn-silence",
            "silence_by_design",
            "higher_hn_n_ge_3_part_iv_scope_boundary",
        ),
        (
            "boundary:m8:higher-tor-unmeasured-support",
            "unmeasured_support",
            "higher_tor_i_ge_2_unmeasured_support",
        ),
    ] {
        let statement = period_m8
            .iter()
            .find(|statement| statement["id"] == id)
            .unwrap_or_else(|| panic!("period M8 boundary {id} is missing"));
        assert_eq!(statement["kind"], kind);
        assert_eq!(statement["reason"], reason);
        assert_eq!(
            statement["scopeRefs"],
            json!([period_packet["packetId"]
                .as_str()
                .expect("packet id is string")])
        );
    }
    assert!(
        period_m8
            .iter()
            .any(|statement| { statement["id"] == "boundary:m8:higher-hn-silence" })
    );
    assert!(
        period_m8
            .iter()
            .any(|statement| { statement["id"] == "boundary:m8:higher-tor-unmeasured-support" })
    );
    assert!(
        !period_m8.iter().any(|statement| {
            statement["id"] == "boundary:m8:non-abelian-stack-gerbe-vocabulary"
        })
    );
    assert!(period_m8.iter().all(|statement| {
        statement["reason"]
            .as_str()
            .is_some_and(|reason| !reason.contains("F2"))
            && statement["text"]
                .as_str()
                .is_some_and(|text| !text.contains("F2"))
    }));

    assert!(has_absolute_sheaf_cohomology_notation("H^1(X, Ob_U)"));
    assert!(has_absolute_sheaf_cohomology_notation("H^n(X, Ob_U)"));
    assert!(!has_absolute_sheaf_cohomology_notation(
        "selected cover H^1"
    ));
    assert!(!has_absolute_sheaf_cohomology_notation("coverRelativeH1"));
}

#[test]
fn cli_r13_two_vertex_circle_nerve_fixture_locks_body_worked_example() {
    let fixture = read_json(&ag_measurement_root().join("circle_nerve_two_vertex_body_v052.json"));
    assert_eq!(fixture["schema"], "ag-circle-nerve-fixture/v0.5.4");
    assert_eq!(
        fixture["provenance"]["reference"],
        "part10/9.2 + appendix/B.9"
    );
    assert_eq!(
        fixture["provenance"]["leanWitness"],
        "circleSimplex/circleNext is the separate 3-edge Lean witness"
    );
    assert!(
        fixture["provenance"]["note"]
            .as_str()
            .is_some_and(|note| note.contains("not a Lean-proved witness"))
    );
    assert_eq!(fixture["coefficient"]["ring"], "Z");
    assert_eq!(fixture["coefficient"]["quotient"], "F2");
    assert_eq!(fixture["coefficient"]["ideal"], "(2)");
    assert_eq!(fixture["coefficient"]["oneIsNonzero"], true);
    assert_eq!(fixture["vertices"], json!(["v_minus", "v_plus"]));
    let edges = fixture["edges"].as_array().expect("circle edges");
    assert_eq!(edges.len(), 2);
    assert_eq!(edges[0]["source"], "v_minus");
    assert_eq!(edges[0]["target"], "v_plus");
    assert_eq!(edges[0]["id"], "e_plus");
    assert_eq!(edges[0]["value"], 1);
    assert_eq!(edges[1]["source"], "v_plus");
    assert_eq!(edges[1]["target"], "v_minus");
    assert_eq!(edges[1]["id"], "e_minus");
    assert_eq!(edges[1]["value"], 0);
    assert_eq!(
        edges
            .iter()
            .map(|edge| edge["value"].as_u64().expect("F2 edge value") as u8)
            .fold(0, |sum, value| sum ^ value),
        1,
        "the residual has nonzero reverse-edge parity in F2"
    );
    assert_eq!(fixture["higherSimplices"], json!([]));
    assert_eq!(fixture["expected"]["cocycle"], true);
    assert_eq!(fixture["expected"]["classNonzero"], true);
}

#[test]
fn cli_r9_numeric_locks_preserve_ag_measurement_values_and_verdicts() {
    let pseudo_circle = run_analyze_fixture_lock_with_surface(
        "r9-pseudo-circle-h1",
        "archmap_v2_cech_h1_visible.json",
        "law_policy_cech_h1.json",
        "law_surface_cech_h1_v052.json",
        None,
    );
    let pseudo_circle_packet = read_json(&pseudo_circle.join("archsig-measurement-packet.json"));
    assert_eq!(
        pseudo_circle_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let pseudo_circle_invariant = invariant_by_id(
        &pseudo_circle_packet,
        "cech-cohomology:profile:ag-default@1",
    );
    assert_eq!(pseudo_circle_invariant["dimensions"]["H1"], 1);
    assert_eq!(pseudo_circle_invariant["coefficient"], "F2");

    let circle_nerve_a = run_analyze_fixture_lock_with_surface(
        "r9-circle-nerve-a",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
        None,
    );
    let circle_nerve_b = run_analyze_fixture_lock_with_surface(
        "r9-circle-nerve-b",
        "archmap_v2_cech_b8_toy.json",
        "law_policy_cech_b8.json",
        "law_surface_cech_b8_v052.json",
        None,
    );
    assert_byte_identical_analysis_artifacts(&circle_nerve_a, &circle_nerve_b);
    let circle_nerve_packet = read_json(&circle_nerve_a.join("archsig-measurement-packet.json"));
    assert_eq!(
        circle_nerve_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let circle_nerve =
        invariant_by_id(&circle_nerve_packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(circle_nerve["dimensions"]["H1"], 1);
    assert_eq!(circle_nerve["observedCocycle"]["classNonzero"], true);
    assert_eq!(
        circle_nerve["observedCocycle"]["mismatchSupportRefs"],
        json!(["atom:b8-cocycle-P"])
    );

    let square_free = run_analyze_fixture_lock_with_surface(
        "r9-square-free-hitting-sets",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
        None,
    );
    let square_free_packet = read_json(&square_free.join("archsig-measurement-packet.json"));
    let square_free_invariant = invariant_by_id(
        &square_free_packet,
        "square-free-repair:profile:ag-square-free@1",
    );
    assert_eq!(
        square_free_invariant["alexanderDualRepair"]["minimalHittingSets"],
        json!([["x_inventory"], ["x_checkout", "x_payment"]]),
    );
    assert_eq!(
        square_free_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );

    let tor = run_analyze_fixture_lock_with_surface(
        "r9-tor-one",
        "archmap_v2_law_conflict_tor.json",
        "law_policy_tor.json",
        "law_surface_ag_v052.json",
        None,
    );
    let tor_packet = read_json(&tor.join("archsig-measurement-packet.json"));
    assert_eq!(
        tor_packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let tor_invariant = invariant_by_id(
        &tor_packet,
        "law-conflict-tor:profile:ag-law-conflict-tor@1",
    );
    assert_eq!(
        tor_invariant["torByDegree"],
        json!([{
            "degree": 1,
            "classCount": 1,
            "coefficient": "F2",
            "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
        }])
    );
    assert_eq!(tor_invariant["lawConflicts"][0]["degree"], 1);
    assert_eq!(tor_invariant["proxyComparison"]["taylorClassCount"], 1);
}

#[test]
fn cli_analyze_v2_cech_h1_visible_fixture_measures_nonzero() {
    let out_dir = temp_dir("ag-measurement-cech-h1-visible");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.cech-obstruction"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["nonZero"],
        true
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(
        cech["claimScope"],
        "selected-cover 1-skeleton Cech cochain calculation"
    );
    assert_eq!(cech["observedCocycle"]["classNonzero"], true);
    assert_eq!(
        cech["observedCocycle"]["representative"]
            .as_array()
            .expect("representative is array")
            .len(),
        3,
        "fully observed square with three mismatched edges (odd cycle sum) carries the class"
    );
    assert_eq!(cech["observedEdgeCount"], 4);
    assert_eq!(
        cech["unobservedEdgeRefs"].as_array().map(Vec::len),
        Some(0)
    );
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"],
        json!([
            "atom:bottom-cech-section-value",
            "atom:left-cech-section-value",
            "atom:right-cech-section-value",
            "atom:top-cech-section-value"
        ])
    );
    assert_eq!(
        cech["classSupport"]["edgeRefs"],
        json!([
            "ctx:left->ctx:bottom",
            "ctx:right->ctx:bottom",
            "ctx:top->ctx:right"
        ])
    );
    assert_eq!(
        cech["classSupport"]["supportAtomRefs"],
        json!([
            "atom:bottom-cech-section-value",
            "atom:left-cech-section-value",
            "atom:right-cech-section-value",
            "atom:top-cech-section-value"
        ])
    );
    assert_eq!(cech["nerveShape"]["b1"], Value::from(1));
    assert_eq!(cech["nerveShape"]["oneSkeletonB1"], Value::from(1));
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"],
        "not_discharged"
    );
    assert!(
        cech["coverNerveProjection"]["faces"]
            .as_array()
            .is_some_and(Vec::is_empty),
        "Cech H1 visible fixture has restriction chains but no measured triple-overlap 2-simplex"
    );
    assert_eq!(
        cech["selectedH2"]["status"],
        "computed_for_selected_1_skeleton"
    );
    let mut stable_cech_row = packet["structuralVerdict"][0].clone();
    stable_cech_row
        .as_object_mut()
        .expect("structural row is object")
        .remove("dependsOnAssumptions");
    assert_eq!(
        stable_cech_row,
        json!({
            "verdictRef": "structuralVerdict/ag-cech-obstruction/surface-cech-surface-v052/finite-f2-cech-computed",
            "evaluator": "ag.cech-obstruction",
            "law": "surface:cech-surface-v052",
            "target": {
                "kind": "cover-relative-cech-h1-class",
                "coverRef": "cover:order-inventory",
                "coefficient": "F2",
                "scopeSize": {
                    "contexts": 1,
                    "edges": 1,
                    "triangles": 0
                },
                "classRef": "computedInvariants/cech-cohomology:profile:ag-default@1"
            },
            "verdict": "measured_nonzero",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": true,
                "methodStatus": "finite_f2_cech_computed",
                "certRef": "computedInvariants/cech-cohomology:profile:ag-default@1"
            },
            "evidence": {
                "computedInvariantRefs": ["cech-cohomology:profile:ag-default@1"],
                "sourceRefs": []
            },
            "reason": "finite F2 Cech 1-cocycle is not a coboundary on the selected cover"
        }),
        "ledger transparency must keep the Cech structural verdict payload stable apart from the v0.5.4 target/evidence additions"
    );
    let cech_fixture_path = "input:archmap_v2_cech_h1_visible.json";
    let computed_without_capacity = Value::Array(
        packet["computedInvariants"]
            .as_array()
            .expect("computedInvariants is array")
            .iter()
            .filter(|row| row["invariantId"] != "topological-debt-capacity:profile:ag-default@1")
            .map(|row| {
                let mut row = row.clone();
                let object = row.as_object_mut().expect("computed invariant is object");
                assert!(
                    object.contains_key("kind")
                        && object.contains_key("value")
                        && object.contains_key("representation"),
                    "computed invariant must expose measurement packet typed invariant fields"
                );
                object.remove("kind");
                object.remove("value");
                object.remove("representation");
                row
            })
            .collect(),
    );
    assert_eq!(
        computed_without_capacity,
        json!([
            {
                "archmapRef": cech_fixture_path,
                "atomCount": 8,
                "contextCount": 4,
                "coverCount": 1,
                "doctrineFingerprint": "sha256:aat-canonical-doctrine-schema052",
                "invariantId": "finite-poset-site-shape",
                "evaluator": "ag.foundation"
            },
            {
                "claimScope": "selected-cover 1-skeleton Cech cochain calculation",
                "coefficient": "F2",
                "contextCount": 4,
                "coverNerveProjection": {
                    "coverRef": "cover:order-inventory",
                    "edges": [
                        {
                            "edgeId": "ctx:left->ctx:bottom",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:left",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:left-cech-section-value"],
                            "targetContextRef": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edgeId": "ctx:right->ctx:bottom",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:right",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:right-cech-section-value"],
                            "targetContextRef": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edgeId": "ctx:top->ctx:left",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:top",
                            "supportAtomRefs": [],
                            "targetContextRef": "ctx:left",
                            "value": 0
                        },
                        {
                            "edgeId": "ctx:top->ctx:right",
                            "objectKind": "nerveEdge",
                            "sectionObservation": "observed",
                            "source": "selected cover restriction edge",
                            "sourceContextRef": "ctx:top",
                            "supportAtomRefs": ["atom:right-cech-section-value", "atom:top-cech-section-value"],
                            "targetContextRef": "ctx:right",
                            "value": 1
                        }
                    ],
                    "faceSource": "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer",
                    "faces": [],
                    "h2CoherenceVisualized": false,
                    "vertices": [
                        {
                            "atomRefs": ["atom:bottom", "atom:bottom-cech-section-value"],
                            "contextRef": "ctx:bottom",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:left", "atom:left-cech-section-value"],
                            "contextRef": "ctx:left",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:right", "atom:right-cech-section-value"],
                            "contextRef": "ctx:right",
                            "objectKind": "nerveVertex"
                        },
                        {
                            "atomRefs": ["atom:top", "atom:top-cech-section-value"],
                            "contextRef": "ctx:top",
                            "objectKind": "nerveVertex"
                        }
                    ]
                },
                "dimensions": {
                    "H0": 1,
                    "H1": 1
                },
                "evaluator": "ag.cech-obstruction",
                "invariantId": "cech-cohomology:profile:ag-default@1",
                "method": "finite-f2-incidence-graph-cochain@1",
                "methodStatus": "finite_f2_cech_computed",
                "observedEdgeCount": 4,
                "unobservedEdgeRefs": [],
                "observedCocycle": {
                    "classNonzero": true,
                    "mismatchSupportRefs": [
                        "atom:bottom-cech-section-value",
                        "atom:left-cech-section-value",
                        "atom:right-cech-section-value",
                        "atom:top-cech-section-value"
                    ],
                    "representative": [
                        {
                            "edge": "ctx:left->ctx:bottom",
                            "sourceContext": "ctx:left",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:left-cech-section-value"],
                            "targetContext": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edge": "ctx:right->ctx:bottom",
                            "sourceContext": "ctx:right",
                            "supportAtomRefs": ["atom:bottom-cech-section-value", "atom:right-cech-section-value"],
                            "targetContext": "ctx:bottom",
                            "value": 1
                        },
                        {
                            "edge": "ctx:top->ctx:right",
                            "sourceContext": "ctx:top",
                            "supportAtomRefs": ["atom:right-cech-section-value", "atom:top-cech-section-value"],
                            "targetContext": "ctx:right",
                            "value": 1
                        }
                    ]
                },
                "classSupport": {
                    "kind": "selected-cover-edge-support",
                    "edgeRefs": [
                        "ctx:left->ctx:bottom",
                        "ctx:right->ctx:bottom",
                        "ctx:top->ctx:right"
                    ],
                    "supportAtomRefs": [
                        "atom:bottom-cech-section-value",
                        "atom:left-cech-section-value",
                        "atom:right-cech-section-value",
                        "atom:top-cech-section-value"
                    ]
                },
                "nerveShape": {
                    "b1": 1,
                    "oneSkeletonB1": 1,
                    "capacityLowerBound": 0,
                    "isForest": false,
                    "eulerCharacteristic": 0
                },
                "theorem12_4Discharge": {
                    "theoremRef": "part4/12.4",
                    "isForest": {
                        "holds": false,
                        "status": "not_discharged",
                        "checkedBy": Value::Null
                    },
                    "tripleOverlapsEmpty": {
                        "holds": true,
                        "status": "discharged_by_check",
                        "checkedBy": "selected cover has no projected triple-overlap faces"
                    },
                    "restrictionMapsSurjective": {
                        "holds": false,
                        "status": "not_discharged",
                        "checkedBy": Value::Null
                    },
                    "restrictionSurjectivityWitnesses": [],
                    "coverShapeExcludesGluingObstruction": false,
                    "conclusionCode": Value::Null
                },
                "boundaryNote": "COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION is relative to the selected abelian coefficient sheaf; non-abelian torsor, stacky descent, and gerbe obstructions are not excluded.",
                "rankD0": 3,
                "reason": "selected cover has a non-empty Cech 1-skeleton for ag.cech-obstruction",
                "restrictionEdgeCount": 4,
                "selectedCoverRef": "cover:order-inventory",
                "selectedH2": {
                    "dimension": 0,
                    "reason": "no selected 2-simplices are present in the finite incidence graph complex",
                    "status": "computed_for_selected_1_skeleton"
                },
                "status": "computed"
            }
        ]),
        "ledger transparency must not change computed invariants for the same Cech input"
    );
    assert_eq!(
        packet["suppliedData"],
        json!([
            {
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap_v2_cech_h1_visible.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law_policy_cech_h1.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement_profile_ag.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            },
            {
                "suppliedId": "supplied:law-surface",
                "kind": "law-equation-surface",
                "sourceArtifactRef": "input:law_surface_cech_h1_v052.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-equation-surface/v0.5.4-validation",
                    "boundary": "validated CLI input artifact; semantic content beyond the selected contract remains outside the packet claim"
                }
            }
        ]),
        "measurement packet must carry non-empty suppliedData ledger for all supplied input artifacts"
    );
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(capacity["evaluator"], "ag.cech-obstruction");
    assert_eq!(capacity["status"], "computed");
    assert_eq!(capacity["structuralVerdictRef"], Value::Null);
    assert_eq!(capacity["dimensions"]["dimC0"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC1"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC2"], Value::from(0));
    assert_eq!(capacity["capacityLowerBound"], Value::from(0));
    assert_eq!(capacity["eulerCharacteristic"], Value::from(0));
    assert_eq!(capacity["b1NerveReading"]["oneSkeletonB1"], Value::from(1));
    assert_eq!(capacity["b1NerveReading"]["nerveComplexB1"], Value::from(1));
    assert_eq!(
        capacity["measuredCechVerdictEcho"]["h1ClassNonzero"],
        Value::Bool(true)
    );
    assert!(
        capacity["b1NerveReading"]["nonClaim"]
            .as_str()
            .is_some_and(|text| text.contains("not concrete H1 class existence claims")),
        "capacity reading must not claim concrete H1 class existence"
    );
    assert!(
        capacity["boundaryNote"]
            .as_str()
            .is_some_and(|text| text.contains("Part IV principle 11.3")),
        "cohomological non-claim boundary must be scoped to Part IV"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.3"
                    && entry["assumption"] == "constant coefficient nerve b1 comparison"
                    && entry["status"] == "checked"
            }),
        "b1 nerve reading must be relative to a checked constant coefficient assumption"
    );
    assert_eq!(
        packet["analyticReadings"],
        json!([
            {
                "readingId": "candidate-regime:stability-placeholder",
                "evaluator": "ag.foundation",
                "claimStatus": "candidate",
                "fidelity": "proxy",
                "value": {
                    "reason": "theorem-candidate readings are analytic-only until a follow-up evaluator computes them",
                    "state": "not_evaluated"
                },
                "regime": "theorem-candidate",
                "structuralVerdictRef": Value::Null
            }
        ]),
        "ledger transparency must not change analytic readings for the same Cech input"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"]
                        == "selected Cech nerve is a forest with no triple-overlap faces"
                    && entry["status"] == "assumed"
            }),
        "cycle/no-triple Cech nerve must not check the theorem 12.4 forest premise"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"] == "restriction maps are surjective"
                    && entry["status"] == "assumed"
            }),
        "surjective restriction must remain assumed even when other structural premises are visible"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
}

fn run_cech_h1_analyze(case_id: &str, archmap: Value) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let archmap_path = out_dir.join("archmap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("cech archmap serializes"),
    )
    .expect("cech archmap writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    out_dir
}

fn strip_cech_section_atoms(archmap: &mut Value, subjects: &[&str]) {
    let removed = archmap["atoms"]
        .as_array()
        .expect("atoms are array")
        .iter()
        .filter(|atom| {
            atom["predicate"] == "sectionValue"
                && atom["subject"]
                    .as_str()
                    .is_some_and(|subject| subjects.contains(&subject))
        })
        .map(|atom| atom["id"].as_str().expect("atom id").to_string())
        .collect::<BTreeSet<_>>();
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms are array")
        .retain(|atom| {
            !atom["id"]
                .as_str()
                .is_some_and(|id| removed.contains(id))
        });
    for context in archmap["contexts"].as_array_mut().expect("contexts") {
        context["atoms"]
            .as_array_mut()
            .expect("context atoms")
            .retain(|atom| {
                !atom.as_str().is_some_and(|id| removed.contains(id))
            });
    }
}

#[test]
fn cli_analyze_v2_cech_all_sections_unobserved_is_silence_not_measured_zero() {
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    strip_cech_section_atoms(
        &mut archmap,
        &["ctx:top", "ctx:left", "ctx:right", "ctx:bottom"],
    );
    let out_dir = run_cech_h1_analyze("ag-cech-all-sections-unobserved", archmap);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let row = &packet["structuralVerdict"][0];
    assert_eq!(row["evaluator"], "ag.cech-obstruction");
    assert_eq!(row["verdict"], "not_computed");
    assert_eq!(row["verdictData"]["methodStatus"], "sections_not_observed");
    assert_eq!(row["verdictData"]["zero"], false);
    assert_eq!(
        row["target"]["scopeSize"],
        json!({"contexts": 0, "edges": 0, "triangles": 0}),
        "unmeasured cech row must not claim a positive measured scope"
    );
    let invariant = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["observedEdgeCount"], 0);
    assert_eq!(
        invariant["unobservedEdgeRefs"].as_array().map(Vec::len),
        Some(4)
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .is_some_and(|rows| rows.iter().any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "sections_not_observed"
                    && statement["text"]
                        .as_str()
                        .is_some_and(|text| text.contains("supply section observations"))
            })),
        "all-unobserved cech run must carry a silence_by_design boundary with whatNext"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"], "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE",
        "no NO_MEASURED_H1 conclusion may be drawn from unobserved sections"
    );
}

#[test]
fn cli_analyze_v2_cech_partially_observed_edges_measure_observed_and_stay_silent_elsewhere() {
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    strip_cech_section_atoms(&mut archmap, &["ctx:top", "ctx:right"]);
    let out_dir = run_cech_h1_analyze("ag-cech-partially-observed", archmap);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let row = &packet["structuralVerdict"][0];
    assert_eq!(row["evaluator"], "ag.cech-obstruction");
    assert_eq!(
        row["verdict"], "measured_zero",
        "a single observed mismatch edge extends to a coboundary; the old nonzero relied on unobserved zeros"
    );
    let invariant = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(invariant["observedEdgeCount"], 1);
    let unobserved = invariant["unobservedEdgeRefs"]
        .as_array()
        .expect("unobserved edge refs");
    assert_eq!(unobserved.len(), 3);
    let silence = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements")
        .iter()
        .find(|statement| {
            statement["reason"] == "sections_not_observed_on_selected_edges"
        })
        .expect("partial observation must emit an unobserved-edges silence statement");
    assert_eq!(silence["kind"], "silence_by_design");
    for edge in unobserved {
        let edge = edge.as_str().expect("edge id");
        assert!(
            silence["text"].as_str().is_some_and(|text| text.contains(edge)),
            "silence text must list unobserved edge {edge}"
        );
    }
    assert!(
        silence["scopeRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().any(|scope| scope == &row["verdictRef"])),
        "measured_zero row must be qualified by the unobserved-edges silence"
    );
}

#[test]
fn cli_analyze_v2_cech_effectivity_ledger_checks_forest_no_triple_only() {
    let out_dir = temp_dir("ag-measurement-cech-effectivity-ledger");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let right_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:right")
        .expect("right context exists");
    right_context["restrictsTo"] = json!([]);
    let bottom_section_value = archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .iter_mut()
        .find(|atom| atom["id"] == "atom:bottom-cech-section-value")
        .expect("bottom section value atom exists");
    bottom_section_value["object"] = json!("section=left-local");
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            json!({
                "id": "atom:surj-top-left",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-top-right",
                "kind": "semantic",
                "subject": "ctx:top->ctx:right",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-left-bottom",
                "kind": "semantic",
                "subject": "ctx:left->ctx:bottom",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
        ]);
    let archmap_path = out_dir.join("archmap_v2_cech_forest_no_triple.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_forest.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_forest_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech_row = &packet["structuralVerdict"][0];
    assert_eq!(cech_row["evaluator"], "ag.cech-obstruction");
    assert_eq!(
        cech_row["verdict"], "measured_zero",
        "ledger transparency must not change the Cech verdict calculation"
    );
    assert_eq!(cech_row["verdictData"]["zero"], true);
    assert_eq!(
        cech_row["verdictData"]["methodStatus"],
        "finite_f2_cech_computed"
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(0));
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    assert!(
        cech["coverNerveProjection"]["faces"]
            .as_array()
            .is_some_and(Vec::is_empty),
        "forest/no-triple fixture must have no projected triple-overlap face"
    );

    let assumptions = packet["assumptions"].as_array().unwrap();
    for assumption in [
        "local lawful sections form an effective Ob_U-torsor",
        "local adjustment action is fixed and effective",
        "coefficient object satisfies descent",
    ] {
        assert!(
            assumptions.iter().any(|entry| {
                entry["theoremRef"] == "part4/11.1"
                    && entry["assumption"] == assumption
                    && entry["status"] == "assumed"
            }),
            "theorem 11.1 premise must be visible in the CBI ledger: {assumption}"
        );
    }
    assert!(
        assumptions.iter().any(|entry| {
            entry["theoremRef"] == "part4/12.4"
                && entry["assumption"] == "restriction maps are surjective"
                && entry["status"] == "checked"
        }),
        "surjective restriction must be discharged by the finite selected restriction check"
    );
    assert!(
        assumptions.iter().any(|entry| {
            entry["theoremRef"] == "part4/12.4"
                && entry["assumption"]
                    == "selected Cech nerve is a forest with no triple-overlap faces"
                && entry["status"] == "checked"
        }),
        "forest/no-triple structural premise must be checked from the selected cover nerve"
    );
    assert_eq!(cech["nerveShape"]["isForest"], true);
    assert_eq!(cech["nerveShape"]["b1"], Value::from(0));
    assert_eq!(
        cech["theorem12_4Discharge"]["isForest"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"],
        "discharged_by_check"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionSurjectivityWitnesses"]
            .as_array()
            .expect("restriction witnesses are array")
            .len(),
        3
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        true
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["conclusionCode"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
    assert!(
        cech["boundaryNote"].as_str().is_some_and(|text| {
            text.contains("non-abelian torsor")
                && text.contains("stacky descent")
                && text.contains("gerbe obstructions")
        }),
        "cover-shape exclusion must keep the non-abelian boundary visible"
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
    assert!(
        summary["readThisFirst"]["whatItMeans"]
            .as_str()
            .is_some_and(|text| text.contains("restriction-surjectivity witnesses"))
    );
    assert!(
        summary["readThisFirst"]["boundary"]
            .as_str()
            .is_some_and(|text| text.contains("Non-abelian torsor"))
    );
}

#[test]
fn cli_analyze_v2_cech_surjectivity_witness_requires_edge_coverage() {
    let out_dir = temp_dir("ag-measurement-cech-surjectivity-coverage");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let right_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:right")
        .expect("right context exists");
    right_context["restrictsTo"] = json!([]);
    let bottom_section_value = archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .iter_mut()
        .find(|atom| atom["id"] == "atom:bottom-cech-section-value")
        .expect("bottom section value atom exists");
    bottom_section_value["object"] = json!("section=left-local");
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            json!({
                "id": "atom:surj-top-left",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-top-left-duplicate",
                "kind": "semantic",
                "subject": "ctx:top->ctx:left",
                "object": "finite-preimage-witness-duplicate",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
            json!({
                "id": "atom:surj-left-bottom",
                "kind": "semantic",
                "subject": "ctx:left->ctx:bottom",
                "object": "finite-preimage-witness",
                "axis": "cech",
                "predicate": "restrictionSurjectivityWitness",
                "refs": ["src:cover"]
            }),
        ]);
    let archmap_path = out_dir.join("archmap_v2_cech_duplicate_surj_witness.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_forest.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_forest_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionSurjectivityWitnesses"]
            .as_array()
            .expect("restriction witnesses are array")
            .len(),
        3,
        "duplicate witnesses are retained for audit"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["restrictionMapsSurjective"]["status"], "not_discharged",
        "witness count alone must not discharge missing selected edge coverage"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
}

#[test]
fn cli_analyze_v2_cover_nerve_faces_require_packet_triple_overlap_support() {
    let out_dir = temp_dir("ag-measurement-cech-triple-overlap");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:triple-overlap",
            "kind": "component",
            "subject": "src:triple-overlap",
            "axis": "static",
            "predicate": "tripleOverlapWitness",
            "refs": ["src:triple-overlap"]
        }));
    archmap["sources"]["src:triple-overlap"] = json!({
        "kind": "policy",
            "path": "docs/tool/ag_measurement_evidence_contract.md",
            "section": "B.8.2"
    });
    for context_id in ["ctx:top", "ctx:left", "ctx:bottom"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:triple-overlap".to_string()));
    }
    let incomplete_dir = out_dir.join("incomplete-boundary-face");
    fs::create_dir_all(&incomplete_dir).expect("incomplete face dir exists");
    let incomplete_archmap_path = incomplete_dir.join("archmap_v2_cech_triple_overlap.json");
    fs::write(
        &incomplete_archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("incomplete face archmap fixture can be written");
    run_sig0(&[
        "analyze",
        "--archmap",
        incomplete_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        incomplete_dir.to_str().expect("path is utf-8"),
    ]);
    let incomplete_packet = read_json(&incomplete_dir.join("archsig-measurement-packet.json"));
    let incomplete_capacity = invariant_by_id(
        &incomplete_packet,
        "topological-debt-capacity:profile:ag-default@1",
    );
    assert_eq!(incomplete_capacity["dimensions"]["dimC1"], Value::from(4));
    assert_eq!(incomplete_capacity["dimensions"]["dimC2"], Value::from(1));
    assert_eq!(
        incomplete_capacity["b1NerveReading"]["oneSkeletonB1"],
        Value::from(1)
    );
    assert_eq!(
        incomplete_capacity["b1NerveReading"]["nerveComplexB1"],
        Value::from(1),
        "incomplete projected face boundary must not silently add missing selected C1 edges"
    );
    let top_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:top")
        .expect("ctx:top exists");
    top_context["restrictsTo"]
        .as_array_mut()
        .expect("ctx:top restrictsTo is array")
        .push(Value::String("ctx:bottom".to_string()));
    let archmap_path = out_dir.join("archmap_v2_cech_triple_overlap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_positive_capacity.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_positive_capacity_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structuralVerdict is array")
            .iter()
            .filter(|row| row["evaluator"] == "ag.cech-obstruction")
            .count(),
        1,
        "Topological Debt Capacity must not add a structural verdict row"
    );
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    let faces = cech["coverNerveProjection"]["faces"]
        .as_array()
        .expect("cover nerve faces are array");
    assert_eq!(
        cech["theorem12_4Discharge"]["tripleOverlapsEmpty"]["status"],
        "not_discharged"
    );
    assert_eq!(
        cech["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"],
        false
    );
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_ne!(
        summary["conclusion"],
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    );
    assert!(
        faces.iter().any(|face| {
            let contexts = face["contextRefs"]
                .as_array()
                .expect("contextRefs is array")
                .iter()
                .filter_map(Value::as_str)
                .collect::<BTreeSet<_>>();
            contexts == BTreeSet::from(["ctx:bottom", "ctx:left", "ctx:top"])
                && face["sharedAtomRefs"]
                    .as_array()
                    .expect("sharedAtomRefs is array")
                    .iter()
                    .any(|atom| atom == "atom:triple-overlap")
                && face["coherenceClaim"] == "not_visualized"
        }),
        "cover nerve faces must be sourced from selected triple-overlap sharedAtomRefs"
    );
    assert_eq!(
        cech["coverNerveProjection"]["faceSource"],
        "selected cover triple-overlap sharedAtomRefs recorded in archsig-measurement-packet/v0.5.4; not inferred by the viewer"
    );
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(
        capacity["structuralVerdictRef"],
        Value::Null,
        "Topological Debt Capacity must remain a computedInvariant reading"
    );
    assert_eq!(capacity["dimensions"]["dimC0"], Value::from(4));
    assert_eq!(capacity["dimensions"]["dimC1"], Value::from(5));
    assert_eq!(capacity["dimensions"]["dimC2"], Value::from(1));
    assert_eq!(capacity["capacityLowerBound"], Value::from(0));
    assert_eq!(capacity["eulerCharacteristic"], Value::from(0));
    assert_eq!(
        capacity["b1NerveReading"]["oneSkeletonB1"],
        Value::from(2),
        "extra top-bottom edge creates an additional graph cycle before the selected 2-face is quotiented"
    );
    assert_eq!(
        capacity["b1NerveReading"]["nerveComplexB1"],
        Value::from(1),
        "selected triple-overlap face must fill one graph cycle in the nerve complex reading"
    );
    assert!(
        capacity["b1NerveReading"]["distinction"]
            .as_str()
            .is_some_and(|text| text.contains("oneSkeletonB1 counts graph cycles")),
        "b1 reading must label the graph-vs-complex distinction"
    );
    assert_eq!(cech["coverNerveProjection"]["h2CoherenceVisualized"], false);
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(
        cech["selectedH2"]["status"],
        "not_measured_for_triple_overlap_faces"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"]
                        == "selected Cech nerve is a forest with no triple-overlap faces"
                    && entry["status"] == "assumed"
            }),
        "triple-overlap faces keep theorem 12.4 forest/no-triple premise assumed"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part4/12.4"
                    && entry["assumption"] == "restriction maps are surjective"
                    && entry["status"] == "assumed"
            }),
        "surjective restriction must remain assumed even when triple-overlap faces are present"
    );

}

#[test]
fn cli_analyze_v2_restriction_compatibility_measures_support_inclusion() {
    let root_out = temp_dir("ag-measurement-restriction-compatibility");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("compatible")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(&zero_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = restriction_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_support_inclusion_computed"
    );
    let zero_invariant = invariant_by_id(
        &zero_packet,
        "restriction-compatibility:profile:ag-restriction@1",
    );
    assert_eq!(zero_invariant["method"], "finite-support-inclusion@1");
    assert_eq!(zero_invariant["edgeChecks"][0]["status"], "compatible");

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("violated")).expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(&nonzero_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = restriction_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "restriction-compatibility:profile:ag-restriction@1",
    );
    assert_eq!(nonzero_invariant["edgeChecks"][0]["status"], "violated");
    assert_eq!(
        nonzero_invariant["edgeChecks"][0]["violations"][0]["generatorRef"],
        "atom:gen-source-x"
    );
    assert!(
        nonzero_invariant["edgeChecks"][0]["violations"][0]["sourceRefs"]
            .as_array()
            .unwrap()
            .iter()
            .any(|source_ref| source_ref == "src:source-generator"),
        "violated edge must carry source refs"
    );
    assert!(
        nonzero_invariant["boundaryNote"].as_str().is_some_and(
            |note| note.contains("sheaf image 再定義で消えうる、理論対象の defect ではない")
        ),
        "presentation-relative boundary must be explicit"
    );
    assert!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "restriction evaluator must reuse the existing five verdict values"
    );

    let missing_dir = root_out.join("missing");
    fs::create_dir_all(&missing_dir).expect("missing dir exists");
    let missing_archmap = missing_dir.join("archmap.json");
    let missing_policy = missing_dir.join("law_policy.json");
    fs::write(
        &missing_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("missing-target"))
            .expect("archmap serializes"),
    )
    .expect("missing archmap is written");
    write_test_policy_and_profile(&missing_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        missing_archmap.to_str().unwrap(),
        "--law-policy",
        missing_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(missing_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        missing_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        missing_dir.to_str().unwrap(),
    ]);
    let missing_packet = read_json(&missing_dir.join("archsig-measurement-packet.json"));
    let missing_row = restriction_row(&missing_packet);
    assert_eq!(missing_row["verdict"], "not_computed");
    assert_eq!(
        missing_row["verdictData"]["methodStatus"],
        "restriction_generator_missing"
    );

    let empty_dir = root_out.join("empty");
    fs::create_dir_all(&empty_dir).expect("empty dir exists");
    let empty_archmap = empty_dir.join("archmap.json");
    let empty_policy = empty_dir.join("law_policy.json");
    fs::write(
        &empty_archmap,
        serde_json::to_vec_pretty(&restriction_archmap("empty-edges")).expect("archmap serializes"),
    )
    .expect("empty archmap is written");
    write_test_policy_and_profile(&empty_policy, restriction_policy(), restriction_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        empty_archmap.to_str().unwrap(),
        "--law-policy",
        empty_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(empty_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        empty_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        empty_dir.to_str().unwrap(),
    ]);
    let empty_packet = read_json(&empty_dir.join("archsig-measurement-packet.json"));
    let empty_row = restriction_row(&empty_packet);
    assert_eq!(empty_row["verdict"], "not_computed");
    assert_eq!(
        empty_row["verdictData"]["methodStatus"],
        "empty_selected_restriction_edges"
    );

    let bad_profile_dir = root_out.join("bad-profile");
    fs::create_dir_all(&bad_profile_dir).expect("bad profile dir exists");
    let bad_policy = bad_profile_dir.join("law_policy.json");
    let mut profile = restriction_profile();
    profile["effCoeff"] = Value::String("finite-linear-algebra@1".to_string());
    write_test_policy_and_profile(&bad_policy, restriction_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            bad_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_profile_dir.to_str().unwrap(),
        ],
        2,
    );

    let missing_witness_family_dir = root_out.join("missing-witness-family");
    fs::create_dir_all(&missing_witness_family_dir).expect("missing witness family dir exists");
    let missing_witness_family_policy = missing_witness_family_dir.join("law_policy.json");
    let profile = section_profile();
    write_test_policy_and_profile(&missing_witness_family_policy, section_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            missing_witness_family_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                missing_witness_family_policy.to_str().unwrap(),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            missing_witness_family_dir.to_str().unwrap(),
        ],
        2,
    );

    for (case, assignment) in [
        ("missing-equals", "x"),
        ("unknown-variable", "z=1"),
        ("non-boolean", "x=maybe"),
        ("duplicate-variable", "x=1,x=0"),
        ("empty-assignment", ""),
    ] {
        let malformed_dir = root_out.join(format!("malformed-{case}"));
        fs::create_dir_all(&malformed_dir).expect("malformed dir exists");
        let malformed_archmap = malformed_dir.join("archmap.json");
        let malformed_policy = malformed_dir.join("law_policy.json");
        let mut archmap = section_archmap("lawful");
        archmap["atoms"][2]["object"] = Value::String(assignment.to_string());
        fs::write(
            &malformed_archmap,
            serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
        )
        .expect("malformed archmap is written");
        write_test_policy_and_profile(&malformed_policy, section_policy(), section_profile());
        run_sig0_expect_code(
            &[
                "analyze",
                "--archmap",
                malformed_archmap.to_str().unwrap(),
                "--law-policy",
                malformed_policy.to_str().unwrap(),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(malformed_policy.to_str().unwrap()))
                    .to_str()
                    .expect("path is utf-8"),
                "--out-dir",
                malformed_dir.to_str().unwrap(),
            ],
            2,
        );
    }
}

#[test]
fn cli_analyze_v2_boundary_residue_measures_mayer_vietoris_d0() {
    let root_out = temp_dir("ag-measurement-boundary-residue");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("zero")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(
        &zero_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = boundary_residue_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_computed"
    );
    let zero_invariant = invariant_by_id(
        &zero_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(zero_invariant["method"], "finite-mayer-vietoris-d0@1");
    assert_eq!(zero_invariant["imageMembership"], true);
    assert_eq!(zero_invariant["restrictionMatrix"]["rank"], Value::from(1));
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-coefficient" && row["status"] == "checked"),
        "F2 coefficient must be checked in the ledger"
    );
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-z-zero" && row["status"] == "assumed"),
        "Z-zero lifting must stay assumed"
    );

    let sum_dir = root_out.join("sum-zero");
    fs::create_dir_all(&sum_dir).expect("sum-zero dir exists");
    let sum_archmap = sum_dir.join("archmap.json");
    let sum_policy = sum_dir.join("law_policy.json");
    fs::write(
        &sum_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("sum-zero"))
            .expect("archmap serializes"),
    )
    .expect("sum-zero archmap is written");
    write_test_policy_and_profile(
        &sum_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        sum_archmap.to_str().unwrap(),
        "--law-policy",
        sum_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(sum_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        sum_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        sum_dir.to_str().unwrap(),
    ]);
    let sum_packet = read_json(&sum_dir.join("archsig-measurement-packet.json"));
    let sum_row = boundary_residue_row(&sum_packet);
    assert_eq!(sum_row["verdict"], "measured_zero");
    let sum_invariant = invariant_by_id(
        &sum_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(sum_invariant["imageMembership"], true);
    assert_eq!(sum_invariant["restrictionMatrix"]["rank"], Value::from(2));

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&boundary_residue_archmap("nonzero"))
            .expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(
        &nonzero_policy,
        boundary_residue_policy(),
        boundary_residue_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = boundary_residue_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "boundary-residue:profile:ag-boundary-residue@1",
    );
    assert_eq!(nonzero_invariant["imageMembership"], false);
    assert!(
        nonzero_invariant["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("no pi1 or monodromy verdict")),
        "boundary note must not revive pi1 / monodromy verdicts"
    );
    assert!(
        nonzero_packet["analyticReadings"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["evaluator"] != "ag.boundary-residue"),
        "boundary-residue must be structural only and not a period/modelRelative analytic reading"
    );
    assert_eq!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["evaluator"] == "ag.boundary-residue")
            .count(),
        1,
        "M6 must generate exactly one structural verdict row"
    );

    for (case, expected_status) in [
        ("missing-classification", "boundary_classification_absent"),
        ("missing-mismatch", "boundary_mismatch_section_absent"),
        ("missing-matrix", "boundary_restriction_matrix_absent"),
        ("duplicate-role", "boundary_classification_absent"),
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("case dir exists");
        let archmap_path = out_dir.join("archmap.json");
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&boundary_residue_archmap(case)).expect("archmap serializes"),
        )
        .expect("case archmap is written");
        write_test_policy_and_profile(
            &policy_path,
            boundary_residue_policy(),
            boundary_residue_profile(),
        );
        run_sig0(&[
            "analyze",
            "--archmap",
            archmap_path.to_str().unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            policy_path
                .with_file_name("law_surface.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().unwrap(),
        ]);
        let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
        let row = boundary_residue_row(&packet);
        assert_eq!(row["verdict"], "not_computed");
        assert_eq!(row["verdictData"]["methodStatus"], expected_status);
        if case == "missing-classification" {
            assert!(
                packet["assumptions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|row| row["theoremRef"] == "part8/P1-2-d0" && row["status"] == "violated"),
                "d0 assumption must not be checked when classification is absent"
            );
        }
    }

    for case in [
        "invalid-boundary-column",
        "invalid-core-mismatch",
        "unknown-variable",
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("invalid case dir exists");
        let archmap_path = out_dir.join("archmap.json");
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&boundary_residue_archmap(case)).expect("archmap serializes"),
        )
        .expect("invalid case archmap is written");
        write_test_policy_and_profile(
            &policy_path,
            boundary_residue_policy(),
            boundary_residue_profile(),
        );
        run_sig0_expect_code(
            &[
                "analyze",
                "--archmap",
                archmap_path.to_str().unwrap(),
                "--law-policy",
                policy_path.to_str().unwrap(),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(policy_path.to_str().unwrap()))
                    .to_str()
                    .expect("path is utf-8"),
                "--out-dir",
                out_dir.to_str().unwrap(),
            ],
            2,
        );
    }

    let z_zero_dir = root_out.join("z-zero");
    fs::create_dir_all(&z_zero_dir).expect("z-zero dir exists");
    let z_zero_policy = z_zero_dir.join("law_policy.json");
    let mut profile = boundary_residue_profile();
    profile["coefficient"] = Value::String("Z".to_string());
    write_test_policy_and_profile(&z_zero_policy, boundary_residue_policy(), profile);
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        z_zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(z_zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        z_zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        z_zero_dir.to_str().unwrap(),
    ]);
    let z_zero_packet = read_json(&z_zero_dir.join("archsig-measurement-packet.json"));
    let z_zero_row = boundary_residue_row(&z_zero_packet);
    assert_eq!(z_zero_row["verdict"], "unknown");
    assert_eq!(
        z_zero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_obstruction_only"
    );
    assert!(
        z_zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P1-2-coefficient" && row["status"] == "assumed"),
        "non-F2 coefficient mode must record the F2 parity projection as assumed"
    );

    let z_nonzero_dir = root_out.join("z-nonzero");
    fs::create_dir_all(&z_nonzero_dir).expect("z-nonzero dir exists");
    let z_nonzero_policy = z_nonzero_dir.join("law_policy.json");
    let mut profile = boundary_residue_profile();
    profile["coefficient"] = Value::String("Z".to_string());
    write_test_policy_and_profile(&z_nonzero_policy, boundary_residue_policy(), profile);
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        z_nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(z_nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        z_nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        z_nonzero_dir.to_str().unwrap(),
    ]);
    let z_nonzero_packet = read_json(&z_nonzero_dir.join("archsig-measurement-packet.json"));
    let z_nonzero_row = boundary_residue_row(&z_nonzero_packet);
    assert_eq!(z_nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(
        z_nonzero_row["verdictData"]["methodStatus"],
        "finite_mayer_vietoris_d0_obstruction_only"
    );
}

#[test]
fn cli_analyze_v2_section_factorization_checks_selected_section() {
    let root_out = temp_dir("ag-measurement-section-factorization");
    let root = ag_measurement_root();

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&section_archmap("lawful")).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(&zero_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = section_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    assert_eq!(
        zero_row["verdictData"]["methodStatus"],
        "finite_section_pullback_computed"
    );
    let zero_invariant =
        invariant_by_id(&zero_packet, "section-factorization:profile:ag-section@1");
    assert_eq!(
        zero_invariant["sectionAssignment"]["assignmentStatus"],
        "total"
    );
    assert_eq!(
        zero_invariant["sectionAssignment"]["activeSupport"],
        json!(["x"])
    );
    assert!(
        zero_invariant["minimalForbiddenSupports"][0]["supportRef"]
            .as_str()
            .is_some_and(|reference| reference.starts_with("law-surface:"))
    );
    assert_eq!(zero_invariant["violatedForbiddenSupports"], json!([]));
    assert!(
        zero_invariant["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("section-relative lawful only")
                && note.contains("exactness without No-Cancellation")),
        "section-relative boundary must be explicit"
    );
    assert!(
        zero_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| {
                row["theoremRef"] == "part8/P0-3"
                    && row["checkedBy"]
                        .as_str()
                        .is_some_and(|checked_by| checked_by.contains("law-surface:"))
            }),
        "I_Ob^U presentation ledger must be checked by selected raw support atoms"
    );

    let nonzero_dir = root_out.join("nonzero");
    fs::create_dir_all(&nonzero_dir).expect("nonzero dir exists");
    let nonzero_archmap = nonzero_dir.join("archmap.json");
    let nonzero_policy = nonzero_dir.join("law_policy.json");
    fs::write(
        &nonzero_archmap,
        serde_json::to_vec_pretty(&section_archmap("unlawful")).expect("archmap serializes"),
    )
    .expect("nonzero archmap is written");
    write_test_policy_and_profile(&nonzero_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        nonzero_archmap.to_str().unwrap(),
        "--law-policy",
        nonzero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(nonzero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        nonzero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        nonzero_dir.to_str().unwrap(),
    ]);
    let nonzero_packet = read_json(&nonzero_dir.join("archsig-measurement-packet.json"));
    let nonzero_row = section_row(&nonzero_packet);
    assert_eq!(nonzero_row["verdict"], "measured_nonzero");
    assert_eq!(nonzero_row["verdictData"]["nonZero"], true);
    let nonzero_invariant = invariant_by_id(
        &nonzero_packet,
        "section-factorization:profile:ag-section@1",
    );
    assert_eq!(
        nonzero_invariant["violatedForbiddenSupports"][0]["support"],
        json!(["x", "y"])
    );
    assert!(
        nonzero_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "section evaluator must reuse the existing five verdict values"
    );

    let partial_dir = root_out.join("partial");
    fs::create_dir_all(&partial_dir).expect("partial dir exists");
    let partial_archmap = partial_dir.join("archmap.json");
    let partial_policy = partial_dir.join("law_policy.json");
    fs::write(
        &partial_archmap,
        serde_json::to_vec_pretty(&section_archmap("partial")).expect("archmap serializes"),
    )
    .expect("partial archmap is written");
    write_test_policy_and_profile(&partial_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        partial_archmap.to_str().unwrap(),
        "--law-policy",
        partial_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(partial_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        partial_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        partial_dir.to_str().unwrap(),
    ]);
    let partial_packet = read_json(&partial_dir.join("archsig-measurement-packet.json"));
    let partial_row = section_row(&partial_packet);
    assert_eq!(partial_row["verdict"], "unknown");
    assert_eq!(
        partial_row["verdictData"]["methodStatus"],
        "section_assignment_partial_undecidable"
    );

    let absent_dir = root_out.join("absent");
    fs::create_dir_all(&absent_dir).expect("absent dir exists");
    let absent_archmap = absent_dir.join("archmap.json");
    let absent_policy = absent_dir.join("law_policy.json");
    fs::write(
        &absent_archmap,
        serde_json::to_vec_pretty(&section_archmap("absent")).expect("archmap serializes"),
    )
    .expect("absent archmap is written");
    write_test_policy_and_profile(&absent_policy, section_policy(), section_profile());
    run_sig0(&[
        "analyze",
        "--archmap",
        absent_archmap.to_str().unwrap(),
        "--law-policy",
        absent_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(absent_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        absent_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        absent_dir.to_str().unwrap(),
    ]);
    let absent_packet = read_json(&absent_dir.join("archsig-measurement-packet.json"));
    let absent_row = section_row(&absent_packet);
    assert_eq!(absent_row["verdict"], "not_computed");
    assert_eq!(
        absent_row["verdictData"]["methodStatus"],
        "section_assignment_absent"
    );
    assert!(
        absent_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| {
                row["theoremRef"] == "part8/P0-3-boundary" && row["status"] == "assumed"
            }),
        "No-Cancellation/exactness must stay in the assumption ledger"
    );

    let missing_generator_dir = root_out.join("missing-generator");
    fs::create_dir_all(&missing_generator_dir).expect("missing generator dir exists");
    let missing_generator_archmap = missing_generator_dir.join("archmap.json");
    let missing_generator_policy = missing_generator_dir.join("law_policy.json");
    fs::write(
        &missing_generator_archmap,
        serde_json::to_vec_pretty(&section_archmap("missing-generator"))
            .expect("archmap serializes"),
    )
    .expect("missing generator archmap is written");
    write_test_policy_and_profile(
        &missing_generator_policy,
        section_policy(),
        section_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        missing_generator_archmap.to_str().unwrap(),
        "--law-policy",
        missing_generator_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(missing_generator_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        missing_generator_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        missing_generator_dir.to_str().unwrap(),
    ]);
    let missing_generator_packet =
        read_json(&missing_generator_dir.join("archsig-measurement-packet.json"));
    let missing_generator_row = section_row(&missing_generator_packet);
    assert_eq!(missing_generator_row["verdict"], "not_computed");
    assert_eq!(
        missing_generator_row["verdictData"]["methodStatus"],
        "obstruction_generators_absent"
    );
    assert!(
        missing_generator_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/P0-3" && row["status"] == "violated"),
        "missing raw support evidence must not be treated as an empty ideal"
    );

    let bad_profile_dir = root_out.join("bad-profile");
    fs::create_dir_all(&bad_profile_dir).expect("bad profile dir exists");
    let bad_policy = bad_profile_dir.join("law_policy.json");
    let mut profile = section_profile();
    profile["zeroPredicate"] = Value::String("rank-zero@1".to_string());
    write_test_policy_and_profile(&bad_policy, section_policy(), profile);
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            zero_archmap.to_str().unwrap(),
            "--law-policy",
            bad_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_profile_dir.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_coherence_obstruction_measures_h2_nonzero_with_representative() {
    let out_dir = temp_dir("ag-measurement-coherence-h2-nonzero");
    let archmap_path = out_dir.join("archmap_coherence_h2_nonzero.json");
    let policy_path = out_dir.join("law_policy_coherence.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&coherence_boundary_archmap(true)).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    write_test_policy_and_profile(
        &policy_path,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let coherence = packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.coherence-obstruction")
        .expect("H2 coherence row is present");
    assert_eq!(coherence["verdict"], "measured_nonzero");
    assert_eq!(coherence["verdictData"]["nonZero"], true);
    assert_eq!(
        coherence["verdictData"]["methodStatus"],
        "finite_f2_h2_coherence_computed"
    );
    let invariant = invariant_by_id(&packet, "coherence-obstruction:profile:ag-coherence@1");
    assert_eq!(invariant["cohomologyQuotient"], "ker d^2/im d^1");
    assert!(
        !serde_json::to_string(invariant)
            .expect("invariant serializes")
            .contains("ker d^1/im d^0"),
        "H2 invariant prose must not use the H1 quotient"
    );
    assert_eq!(invariant["cocycleGate"]["passed"], true);
    assert_eq!(
        invariant["representative"]
            .as_array()
            .expect("representative is array")
            .len(),
        1,
        "tetrahedron-boundary fixture carries a concrete H2 representative"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["assumption"]
                == "banded abelian F2 coefficient object for selected H2 coherence"
                && entry["status"] == "checked"),
        "coefficient=F2 must be checked in the CBI ledger"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["assumption"]
                == "Leray / acyclicity comparison from selected Cech complex to sheaf cohomology"
                && entry["status"] == "assumed"),
        "Leray comparison must stay assumed"
    );

    let zero_cochain_dir = temp_dir("ag-measurement-coherence-h2-nonzero-zero-cochain");
    let zero_cochain_archmap_path = zero_cochain_dir.join("archmap_coherence_h2_zero_cochain.json");
    let zero_cochain_policy_path = zero_cochain_dir.join("law_policy_coherence.json");
    fs::write(
        &zero_cochain_archmap_path,
        serde_json::to_vec_pretty(&coherence_boundary_zero_cochain_archmap())
            .expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    write_test_policy_and_profile(
        &zero_cochain_policy_path,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_cochain_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        zero_cochain_policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            zero_cochain_policy_path.to_str().expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        zero_cochain_policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_cochain_dir.to_str().expect("path is utf-8"),
    ]);
    let zero_cochain_packet = read_json(&zero_cochain_dir.join("archsig-measurement-packet.json"));
    let zero_cochain_row = coherence_row(&zero_cochain_packet);
    assert_eq!(
        zero_cochain_row["verdict"], "measured_nonzero",
        "H2 quotient must be nonzero even when the supplied witness cochain is zero"
    );
    let zero_cochain_invariant = invariant_by_id(
        &zero_cochain_packet,
        "coherence-obstruction:profile:ag-coherence@1",
    );
    assert_eq!(zero_cochain_invariant["h2Dimension"], Value::from(1));
    assert!(
        !zero_cochain_invariant["representative"]
            .as_array()
            .expect("representative is array")
            .is_empty(),
        "nonzero H2 quotient must surface a representative independent of the zero witness cochain"
    );
}

#[test]
fn cli_analyze_v2_coherence_obstruction_distinguishes_zero_silence_and_banding_boundary() {
    let root_out = temp_dir("ag-measurement-coherence-statuses");

    let zero_dir = root_out.join("zero");
    fs::create_dir_all(&zero_dir).expect("zero dir exists");
    let zero_archmap = zero_dir.join("archmap.json");
    let zero_policy = zero_dir.join("law_policy.json");
    fs::write(
        &zero_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("zero archmap is written");
    write_test_policy_and_profile(
        &zero_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap.to_str().unwrap(),
        "--law-policy",
        zero_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(zero_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        zero_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_dir.to_str().unwrap(),
    ]);
    let zero_packet = read_json(&zero_dir.join("archsig-measurement-packet.json"));
    let zero_row = coherence_row(&zero_packet);
    assert_eq!(zero_row["verdict"], "measured_zero");
    assert_eq!(zero_row["verdictData"]["zero"], true);
    let zero_invariant =
        invariant_by_id(&zero_packet, "coherence-obstruction:profile:ag-coherence@1");
    assert_eq!(zero_invariant["cocycleGate"]["passed"], true);

    let unmeasured_dir = root_out.join("unmeasured");
    fs::create_dir_all(&unmeasured_dir).expect("unmeasured dir exists");
    let unmeasured_archmap = unmeasured_dir.join("archmap.json");
    let unmeasured_policy = unmeasured_dir.join("law_policy.json");
    fs::write(
        &unmeasured_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(false)).expect("archmap serializes"),
    )
    .expect("unmeasured archmap is written");
    write_test_policy_and_profile(
        &unmeasured_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        unmeasured_archmap.to_str().unwrap(),
        "--law-policy",
        unmeasured_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(unmeasured_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        unmeasured_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        unmeasured_dir.to_str().unwrap(),
    ]);
    let unmeasured_packet = read_json(&unmeasured_dir.join("archsig-measurement-packet.json"));
    let unmeasured_row = coherence_row(&unmeasured_packet);
    assert_eq!(unmeasured_row["verdict"], "unmeasured");
    assert_eq!(
        unmeasured_row["verdictData"]["methodStatus"],
        "coherence_witness_absent"
    );

    let empty_dir = root_out.join("empty");
    fs::create_dir_all(&empty_dir).expect("empty dir exists");
    let empty_archmap = empty_dir.join("archmap.json");
    let empty_policy = empty_dir.join("law_policy.json");
    fs::write(
        &empty_archmap,
        serde_json::to_vec_pretty(&coherence_empty_archmap()).expect("archmap serializes"),
    )
    .expect("empty archmap is written");
    write_test_policy_and_profile(
        &empty_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        empty_archmap.to_str().unwrap(),
        "--law-policy",
        empty_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(empty_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        empty_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        empty_dir.to_str().unwrap(),
    ]);
    let empty_packet = read_json(&empty_dir.join("archsig-measurement-packet.json"));
    let empty_row = coherence_row(&empty_packet);
    assert_eq!(empty_row["verdict"], "not_computed");
    assert_eq!(
        empty_row["verdictData"]["methodStatus"],
        "empty_selected_2_skeleton"
    );

    let banding_dir = root_out.join("banding");
    fs::create_dir_all(&banding_dir).expect("banding dir exists");
    let banding_archmap = banding_dir.join("archmap.json");
    let banding_policy = banding_dir.join("law_policy.json");
    fs::write(
        &banding_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("banding archmap is written");
    write_test_policy_and_profile(
        &banding_policy,
        coherence_policy("Aut(Dec_U)", false),
        coherence_profile("Aut(Dec_U)", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        banding_archmap.to_str().unwrap(),
        "--law-policy",
        banding_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(banding_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        banding_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        banding_dir.to_str().unwrap(),
    ]);
    let banding_packet = read_json(&banding_dir.join("archsig-measurement-packet.json"));
    let banding_row = coherence_row(&banding_packet);
    assert_eq!(banding_row["verdict"], "not_computed");
    assert_eq!(
        banding_row["verdictData"]["methodStatus"],
        "banding_violated"
    );
    assert!(
        banding_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| matches!(
                row["verdict"].as_str().unwrap(),
                "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
            )),
        "coherence evaluator must reuse the existing five verdict values"
    );

    let non_cocycle_dir = root_out.join("non-cocycle");
    fs::create_dir_all(&non_cocycle_dir).expect("non-cocycle dir exists");
    let non_cocycle_archmap = non_cocycle_dir.join("archmap.json");
    let non_cocycle_policy = non_cocycle_dir.join("law_policy.json");
    fs::write(
        &non_cocycle_archmap,
        serde_json::to_vec_pretty(&coherence_filled_tetrahedron_archmap())
            .expect("archmap serializes"),
    )
    .expect("non-cocycle archmap is written");
    write_test_policy_and_profile(
        &non_cocycle_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        non_cocycle_archmap.to_str().unwrap(),
        "--law-policy",
        non_cocycle_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(non_cocycle_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        non_cocycle_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        non_cocycle_dir.to_str().unwrap(),
    ]);
    let non_cocycle_packet = read_json(&non_cocycle_dir.join("archsig-measurement-packet.json"));
    let non_cocycle_row = coherence_row(&non_cocycle_packet);
    assert_eq!(non_cocycle_row["verdict"], "not_computed");
    assert_eq!(
        non_cocycle_row["verdictData"]["methodStatus"], "not_2_cocycle",
        "d2 h = 0 must gate im d1 membership before a nonzero verdict can be emitted"
    );
    let non_cocycle_invariant = invariant_by_id(
        &non_cocycle_packet,
        "coherence-obstruction:profile:ag-coherence@1",
    );
    assert_eq!(non_cocycle_invariant["cocycleGate"]["passed"], false);

    let incomplete_dir = root_out.join("incomplete");
    fs::create_dir_all(&incomplete_dir).expect("incomplete dir exists");
    let incomplete_archmap = incomplete_dir.join("archmap.json");
    let incomplete_policy = incomplete_dir.join("law_policy.json");
    fs::write(
        &incomplete_archmap,
        serde_json::to_vec_pretty(&coherence_incomplete_triangle_archmap())
            .expect("archmap serializes"),
    )
    .expect("incomplete archmap is written");
    write_test_policy_and_profile(
        &incomplete_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        incomplete_archmap.to_str().unwrap(),
        "--law-policy",
        incomplete_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(incomplete_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        incomplete_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        incomplete_dir.to_str().unwrap(),
    ]);
    let incomplete_packet = read_json(&incomplete_dir.join("archsig-measurement-packet.json"));
    let incomplete_row = coherence_row(&incomplete_packet);
    assert_eq!(incomplete_row["verdict"], "not_computed");
    assert_eq!(
        incomplete_row["verdictData"]["methodStatus"],
        "incomplete_selected_2_skeleton"
    );

    let oversized_dir = root_out.join("oversized");
    fs::create_dir_all(&oversized_dir).expect("oversized dir exists");
    let oversized_archmap = oversized_dir.join("archmap.json");
    let oversized_policy = oversized_dir.join("law_policy.json");
    fs::write(
        &oversized_archmap,
        serde_json::to_vec_pretty(&coherence_oversized_archmap()).expect("archmap serializes"),
    )
    .expect("oversized archmap is written");
    write_test_policy_and_profile(
        &oversized_policy,
        coherence_policy("F2", false),
        coherence_profile("F2", false),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        oversized_archmap.to_str().unwrap(),
        "--law-policy",
        oversized_policy.to_str().unwrap(),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(oversized_policy.to_str().unwrap()))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        oversized_policy
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        oversized_dir.to_str().unwrap(),
    ]);
    let oversized_packet = read_json(&oversized_dir.join("archsig-measurement-packet.json"));
    let oversized_row = coherence_row(&oversized_packet);
    assert_eq!(oversized_row["verdict"], "not_computed");
    assert_eq!(
        oversized_row["verdictData"]["methodStatus"],
        "selected_cover_too_large"
    );

    let missing_family_dir = root_out.join("missing-family");
    fs::create_dir_all(&missing_family_dir).expect("missing-family dir exists");
    let missing_family_archmap = missing_family_dir.join("archmap.json");
    let missing_family_policy = missing_family_dir.join("law_policy.json");
    let mut missing_family_profile = coherence_profile("F2", false);
    missing_family_profile["witnessFamily"] = Value::Array(vec![]);
    fs::write(
        &missing_family_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("missing-family archmap is written");
    write_test_policy_and_profile(
        &missing_family_policy,
        coherence_policy("F2", false),
        missing_family_profile,
    );
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            missing_family_archmap.to_str().unwrap(),
            "--law-policy",
            missing_family_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(missing_family_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            missing_family_dir.to_str().unwrap(),
        ],
        2,
    );

    let bad_selector_dir = root_out.join("bad-selector");
    fs::create_dir_all(&bad_selector_dir).expect("bad-selector dir exists");
    let bad_selector_archmap = bad_selector_dir.join("archmap.json");
    let bad_selector_policy = bad_selector_dir.join("law_policy.json");
    let mut bad_selector_profile = coherence_profile("F2", false);
    bad_selector_profile["resolutionSelector"] = Value::String("taylor@1".to_string());
    fs::write(
        &bad_selector_archmap,
        serde_json::to_vec_pretty(&coherence_triangle_archmap(true)).expect("archmap serializes"),
    )
    .expect("bad-selector archmap is written");
    write_test_policy_and_profile(
        &bad_selector_policy,
        coherence_policy("F2", false),
        bad_selector_profile,
    );
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            bad_selector_archmap.to_str().unwrap(),
            "--law-policy",
            bad_selector_policy.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(bad_selector_policy.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            bad_selector_dir.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_insight_artifacts_redact_local_source_refs() {
    let out_dir = temp_dir("ag-measurement-insight-source-redaction");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    let private_ref = "/workspace/local-only/internal.rs";
    archmap["sources"][private_ref] = json!({
        "kind": "rust",
        "path": private_ref,
        "symbol": "InternalOnly",
        "line": 1
    });
    let atoms = archmap["atoms"].as_array_mut().expect("atoms are array");
    let mismatch = atoms
        .iter_mut()
        .find(|atom| atom["id"] == "atom:left-cech-section-value")
        .expect("section value atom exists");
    mismatch["refs"]
        .as_array_mut()
        .expect("refs are array")
        .push(Value::String(private_ref.to_string()));
    let archmap_path = out_dir.join("archmap_v2_private_source_ref.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let report = fs::read_to_string(out_dir.join("archsig-insight-report.json"))
        .expect("insight report is generated");
    let brief = fs::read_to_string(out_dir.join("archsig-insight-brief.md"))
        .expect("insight brief is generated");
    let viewer = fs::read_to_string(out_dir.join("archsig-atom-viewer-data.json"))
        .expect("viewer data is generated");
    for artifact in [&report, &brief, &viewer] {
        assert!(
            !artifact.contains(private_ref),
            "insight artifacts must not leak local source refs"
        );
        assert!(
            artifact.contains("source-ref:redacted-local-path"),
            "insight artifacts must preserve a redacted source-ref marker"
        );
    }
}

#[test]
fn cli_analyze_v2_validation_failure_emits_blocking_insight_projection() {
    let out_dir = temp_dir("ag-measurement-insight-validation-failure");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["atoms"][0]["kind"] = Value::String("unknown-legacy-kind".to_string());
    let archmap_path = out_dir.join("archmap_v2_bad_atom_kind.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(!output.status.success());
    assert!(
        !out_dir.join("archsig-analysis-summary.json").exists(),
        "validation failure must not emit a success summary"
    );
    assert!(
        !out_dir.join("archsig-measurement-packet.json").exists(),
        "validation failure must not emit a measurement packet"
    );
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(report["insightCards"][0]["kind"], "validation_failure");
    assert_eq!(manifest["mode"], "validation-failure");
    assert_eq!(
        manifest["conclusionCode"],
        "VALIDATION_FAILED_BEFORE_MEASUREMENT"
    );
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:") && run_id.len() == 16)
    );
    assert!(manifest["inputDigests"]["archmap"]["sha256"].is_string());
    assert!(manifest["inputDigests"]["lawPolicy"]["sha256"].is_string());
}

#[test]
fn cli_analyze_v2_cech_rejects_unsupported_measurement_profile_selectors() {
    let out_dir = temp_dir("ag-measurement-cech-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    profile["coefficient"] = Value::String("Z".to_string());
    let policy_path = out_dir.join("law_policy_bad_cech_selector.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_cech_h1_visible.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_cech_requires_matching_witness_family() {
    let out_dir = temp_dir("ag-measurement-cech-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    let policy_path = out_dir.join("law_policy_missing_cech_witness.json");
    let mut policy = policy;
    policy["lawSurfaceRef"] = json!("law-surface:cech-h1-v052");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_cech_ignores_unanchored_mismatch_support() {
    let out_dir = temp_dir("ag-measurement-cech-unanchored-support");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    for atom in archmap["atoms"].as_array_mut().expect("atoms are array") {
        if atom["predicate"] == "sectionValue" {
            atom["object"] = Value::String("section=bottom-local".to_string());
        }
    }
    let archmap_path = out_dir.join("archmap_v2_unanchored_cech.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_h1_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["dimensions"]["H1"], Value::from(1));
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    assert_eq!(
        cech["observedCocycle"]["mismatchSupportRefs"]
            .as_array()
            .expect("mismatch support refs is array")
            .len(),
        0
    );
}

#[test]
fn cli_analyze_v2_topological_debt_capacity_does_not_claim_h1_class() {
    let out_dir = temp_dir("ag-measurement-cech-positive-capacity-no-class");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_cech_h1_visible.json"));
    for atom in archmap["atoms"].as_array_mut().expect("atoms are array") {
        if atom["predicate"] == "sectionValue" {
            atom["object"] = Value::String("section=bottom-local".to_string());
        }
    }
    let top_context = archmap["contexts"]
        .as_array_mut()
        .expect("contexts is array")
        .iter_mut()
        .find(|context| context["id"] == "ctx:top")
        .expect("ctx:top exists");
    top_context["restrictsTo"]
        .as_array_mut()
        .expect("ctx:top restrictsTo is array")
        .push(Value::String("ctx:bottom".to_string()));
    let archmap_path = out_dir.join("archmap_v2_positive_capacity_no_class.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_positive_capacity.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_cech_positive_capacity_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["observedCocycle"]["classNonzero"], false);
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(capacity["capacityLowerBound"], Value::from(1));
    assert_eq!(capacity["b1NerveReading"]["oneSkeletonB1"], Value::from(2));
    assert_eq!(capacity["b1NerveReading"]["nerveComplexB1"], Value::from(2));
    assert_eq!(
        capacity["measuredCechVerdictEcho"]["h1ClassNonzero"],
        Value::Bool(false)
    );
    assert!(
        capacity["b1NerveReading"]["nonClaim"]
            .as_str()
            .is_some_and(|text| text.contains("not concrete H1 class existence claims")),
        "positive capacity must remain a non-claim about concrete H1 class existence"
    );
}

#[test]
fn cli_analyze_v2_square_free_repair_outputs_hitting_sets_and_nsdepth() {
    let out_dir = temp_dir("ag-measurement-square-free-repair");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.square-free-repair"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "nsdepth_certificate_computed"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "repair inspection reading must not add a structural verdict row"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(repair["obstructionIdeal"]["id"], "I_Ob^U");
    assert_eq!(
        repair["minimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );
    assert!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .expect("declared generators are array")
            .iter()
            .all(|generator| {
                generator["supportAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
            }),
        "the observed square-free fixture must realize every declared generator"
    );
    assert_eq!(
        repair["alexanderDualRepair"]["minimalHittingSets"],
        serde_json::json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    assert_eq!(
        repair["deltaComplex"]["reducedHomology"]["betti"],
        serde_json::json!([
            {"degree": 0, "dimension": 1},
            {"degree": 1, "dimension": 0}
        ])
    );
    assert_eq!(repair["nsdepthCertificate"]["status"], "computed");
    assert_eq!(repair["nsdepthCertificate"]["nsdepth"], Value::from(2));
    assert_eq!(
        repair["nsdepthCertificate"]["verifiedMinimalForbiddenSupports"],
        serde_json::json!([["x_checkout", "x_inventory"], ["x_inventory", "x_payment"]])
    );
    assert_eq!(
        repair["nsdepthCertificate"]["certificateRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(
        repair["nsdepthCertificate"]["supportAtomRefs"],
        serde_json::json!([
            "atom:support-checkout-inventory",
            "atom:support-inventory-payment"
        ])
    );
    let nsdepth_assumption = packet["assumptions"]
        .as_array()
        .expect("assumptions are array")
        .iter()
        .find(|row| row["theoremRef"] == "part3/7.2B")
        .expect("NSdepth assumption ledger row exists");
    assert_eq!(nsdepth_assumption["status"], "checked");
    assert_eq!(
        nsdepth_assumption["checkedBy"],
        "ag.square-free-repair:computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert!(
        nsdepth_assumption["assumedBy"].is_null(),
        "ArchSig-computed NSdepth certificate must not be downgraded to an assumption"
    );
    let arrangement = invariant_by_id(&packet, "lawful-locus-arrangement:profile:ag-square-free@1");
    assert_eq!(
        arrangement["method"],
        "finite-delta-coordinate-arrangement@1"
    );
    assert_eq!(
        arrangement["facets"],
        serde_json::json!([["x_checkout", "x_payment"], ["x_inventory"]])
    );
    assert_eq!(arrangement["dimension"], Value::from(2));
    assert_eq!(arrangement["irreducibleComponentCount"], Value::from(2));
    assert_eq!(
        arrangement["components"],
        serde_json::json!([
            {
                "componentId": "lawful-locus-component:1",
                "facet": ["x_checkout", "x_payment"],
                "vanishingCoords": ["x_inventory"],
                "dimension": 2
            },
            {
                "componentId": "lawful-locus-component:2",
                "facet": ["x_inventory"],
                "vanishingCoords": ["x_checkout", "x_payment"],
                "dimension": 1
            }
        ])
    );
    assert!(
        arrangement["nonConclusions"]
            .as_array()
            .expect("arrangement nonConclusions is array")
            .iter()
            .any(|entry| entry
                .as_str()
                .is_some_and(|text| text.contains("does not evaluate section-specific"))),
        "lawful locus arrangement must not become a section-level verdict"
    );
    let facet_link = invariant_by_id(&packet, "delta-facet-link-reading:profile:ag-square-free@1");
    assert_eq!(
        facet_link["method"],
        "finite-delta-facet-link-neutral-reading@1"
    );
    assert_eq!(
        facet_link["facetDimensionReading"],
        serde_json::json!({
            "facets": [
                {
                    "facetId": "delta-facet:1",
                    "facet": ["x_checkout", "x_payment"],
                    "dimension": 2
                },
                {
                    "facetId": "delta-facet:2",
                    "facet": ["x_inventory"],
                    "dimension": 1
                }
            ],
            "minDimension": 1,
            "maxDimension": 2
        })
    );
    assert_eq!(facet_link["isPure"], Value::Bool(false));
    assert_eq!(
        facet_link["linkBoundaryReading"],
        serde_json::json!([
            {
                "vertex": "x_checkout",
                "linkFaces": [[], ["x_payment"]],
                "boundaryRanks": [],
                "componentCount": 1
            },
            {
                "vertex": "x_inventory",
                "linkFaces": [[]],
                "boundaryRanks": [],
                "componentCount": 0
            },
            {
                "vertex": "x_payment",
                "linkFaces": [[], ["x_checkout"]],
                "boundaryRanks": [],
                "componentCount": 1
            }
        ])
    );
    assert_eq!(
        facet_link["linkReducedBetti"],
        serde_json::json!([
            {
                "vertex": "x_checkout",
                "betti": [{"degree": 0, "dimension": 0}]
            },
            {
                "vertex": "x_inventory",
                "betti": [{"degree": 0, "dimension": 0}]
            },
            {
                "vertex": "x_payment",
                "betti": [{"degree": 0, "dimension": 0}]
            }
        ])
    );
    let facet_link_text =
        serde_json::to_string(&facet_link).expect("facet/link invariant serializes");
    let banned_terms = [
        "depth".to_string(),
        ["Reis", "ner"].concat(),
        ["Cohen", "-", "Macaulay"].concat(),
        "Krull".to_string(),
        ["sr", "Depth"].concat(),
    ];
    for banned in banned_terms {
        assert!(
            !facet_link_text.contains(&banned),
            "facet/link neutral reading must not contain banned term {banned}"
        );
    }
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "ag.nullstellensatz-depth-monotone"),
        "nsdepth monotone proxy is not authored in ArchMap input after R2"
    );
    let repair_reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "repair-lower-bound-inspection@1")
        .expect("repair lower-bound inspection reading exists");
    assert_eq!(repair_reading["regime"], "theorem-candidate");
    assert_eq!(repair_reading["structuralVerdictRef"], Value::Null);
    assert_eq!(
        repair_reading["value"]["minimalHittingSets"],
        serde_json::json!([["x_inventory"], ["x_checkout", "x_payment"]])
    );
    assert_eq!(
        repair_reading["value"]["nonClaim"],
        "not automatic repair; not operation semantics"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(summary["conclusion"], ARCHSIG_REPAIR_TARGETS_IDENTIFIED);
    assert_eq!(
        summary["readThisFirst"]["conclusion"],
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED
    );
    assert!(
        summary["readThisFirst"]["whatItMeans"]
            .as_str()
            .is_some_and(|text| text.contains("combinatorial repair target supports"))
    );
    assert!(
        summary["readThisFirst"]["boundary"]
            .as_str()
            .is_some_and(|text| {
                text.contains("Principle 5.3 boundary")
                    && text.contains("not automatic semantic repairs")
            })
    );
    let report = read_json(&out_dir.join("archsig-insight-report.json"));
    assert!(
        report["gluingGeometry"]["forbiddenCages"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "square-free obstruction fixture must project minimal forbidden support as cage geometry"
    );
    assert!(
        report["gluingGeometry"]["repairMorphs"]
            .as_array()
            .is_some_and(|items| {
                items.iter().any(|item| {
                    item["animationRole"] == "continuous_morph_lower_bound"
                        && item["nonClaim"] == "not automatic repair"
                        && item["fromCageRefs"]
                            .as_array()
                            .is_some_and(|refs| refs.len() >= 2)
                        && item["fromAtomRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
            }),
        "square-free repair fixture must project lower-bound repair candidate from related forbidden supports"
    );
}


#[test]
fn cli_analyze_v2_square_free_uses_law_surface_witnesses() {
    let out_dir = temp_dir("ag-measurement-square-free-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    let policy_path = out_dir.join("law_policy_square_free_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_square_free_ignores_undeclared_observed_variables() {
    let out_dir = temp_dir("ag-measurement-square-free-unknown-variable");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"][3]["subject"] = Value::String("x_unknown".to_string());
    let archmap_path = out_dir.join("archmap_v2_square_free_unknown_variable.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_square_free_uses_profile_only_for_runtime_caps() {
    let out_dir = temp_dir("ag-measurement-square-free-too-many-witnesses");
    let root = ag_measurement_root();
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    profile["witnessFamily"] = Value::Array(
        (0..13)
            .map(|index| {
                serde_json::json!({
                    "law": "ag.square-free-repair",
                    "variable": format!("x_{index}")
                })
            })
            .collect(),
    );
    let policy_path = out_dir.join("law_policy_square_free_too_many_witnesses.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_square_free_repair.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_square_free_observation_does_not_supply_generators() {
    let root = ag_measurement_root();
    let baseline_out = run_analyze_fixture_lock(
        "ag-measurement-square-free-law-surface-baseline",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
        None,
    );
    let extra_out = temp_dir("ag-measurement-square-free-observation-extra");
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:support-checkout-inventory-extra",
            "kind": "relation",
            "subject": "x_checkout",
            "object": "x_inventory",
            "axis": "square-free",
            "predicate": "support",
            "refs": ["src:checkout", "src:inventory"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(json!("atom:support-checkout-inventory-extra"));
    let archmap_path = extra_out.join("archmap-extra-support.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        extra_out.to_str().expect("path is utf-8"),
    ]);

    let baseline = read_json(&baseline_out.join("archsig-measurement-packet.json"));
    let extra = read_json(&extra_out.join("archsig-measurement-packet.json"));
    let baseline_repair = invariant_by_id(&baseline, "square-free-repair:profile:ag-square-free@1");
    let extra_repair = invariant_by_id(&extra, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        baseline_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .map(|generator| generator["support"].clone())
            .collect::<Vec<_>>(),
        extra_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .map(|generator| generator["support"].clone())
            .collect::<Vec<_>>(),
        "observed support atoms must not change the declared obstruction ideal"
    );
    assert_eq!(
        baseline_repair["minimalForbiddenSupports"],
        extra_repair["minimalForbiddenSupports"]
    );
    assert_eq!(
        baseline_repair["alexanderDualRepair"]["minimalHittingSets"],
        extra_repair["alexanderDualRepair"]["minimalHittingSets"]
    );
    assert!(
        extra_repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .any(|generator| generator["supportAtomRefs"]
                .as_array()
                .unwrap()
                .contains(&json!("atom:support-checkout-inventory-extra")))
    );
}

#[test]
fn cli_analyze_v2_square_free_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-square-free-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_square_free_law_surface_generator_change_is_observed() {
    let out_dir = temp_dir("ag-measurement-square-free-law-surface-change");
    let root = ag_measurement_root();
    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    surface["laws"][0]["forbiddenSupportGenerators"]
        .as_array_mut()
        .expect("forbidden support generators are array")
        .push(json!({"support": ["x_checkout", "x_payment"]}));
    let surface_path = out_dir.join("law_surface_changed.json");
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("law surface serializes"),
    )
    .expect("law surface fixture writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert!(manifest["inputDigests"]["lawSurface"]["sha256"].is_string());
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["minimalForbiddenSupports"].as_array().unwrap().len(),
        3
    );
    assert!(
        repair["minimalForbiddenSupports"]
            .as_array()
            .unwrap()
            .iter()
            .any(|support| support == &json!(["x_checkout", "x_payment"]))
    );
}

#[test]
fn cli_analyze_v2_tor_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-tor-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_cech_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-cech-missing-law-surface");
    let root = ag_measurement_root();
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_cech_h1.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_section_requires_explicit_law_surface() {
    let out_dir = temp_dir("ag-measurement-section-missing-law-surface");
    let archmap_path = out_dir.join("archmap.json");
    let policy_path = out_dir.join("law_policy.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&section_archmap("lawful")).expect("archmap serializes"),
    )
    .expect("archmap is written");
    write_test_policy_and_profile(&policy_path, section_policy(), section_profile());
    let output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires --law-surface"));
}

#[test]
fn cli_analyze_v2_square_free_without_observed_support_keeps_declared_generators() {
    let root = ag_measurement_root();
    let archmap_path = root.join("archmap_v2_square_free_repair_unobserved.json");
    let first_out = run_square_free_analysis("ag-measurement-square-free-zero-a", &archmap_path);
    let second_out = run_square_free_analysis("ag-measurement-square-free-zero-b", &archmap_path);
    assert_byte_identical_analysis_artifacts(&first_out, &second_out);

    let packet = read_json(&first_out.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "measured_zero");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "square_free_observation_empty"
    );
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    assert_eq!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert!(
        repair["obstructionIdeal"]["generators"]
            .as_array()
            .unwrap()
            .iter()
            .all(|generator| generator["supportAtomRefs"].as_array().unwrap().is_empty())
    );
    let unobserved_boundaries = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements are array")
        .iter()
        .filter(|statement| statement["reason"] == "declared_generator_unobserved")
        .collect::<Vec<_>>();
    assert_eq!(unobserved_boundaries.len(), 2);
    assert!(unobserved_boundaries.iter().all(|statement| {
        statement["kind"] == "silence_by_design"
            && statement["scopeRefs"].as_array().is_some_and(|refs| {
                refs.iter().any(|reference| {
                    reference
                        .as_str()
                        .is_some_and(|reference| reference.starts_with("structuralVerdict/"))
                })
            })
    }));
    let certificate = &repair["nsdepthCertificate"];
    assert_eq!(
        certificate["certificateRef"],
        "computedInvariants/square-free-repair:profile:ag-square-free@1"
    );
    assert_eq!(certificate["supportAtomRefs"], json!([]));
    let summary = read_json(&first_out.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    );
    assert!(summary["translationRule"]["theoremRef"].is_null());
    assert_eq!(
        summary["readThisFirst"]["whatItMeans"],
        "ArchSig produced a profile-relative foundation result for the selected measurement surface."
    );
    let report = read_json(&first_out.join("archsig-insight-report.json"));
    assert!(
        report["gluingGeometry"]["forbiddenCages"]
            .as_array()
            .is_some_and(Vec::is_empty)
    );
    assert!(
        report["gluingGeometry"]["repairMorphs"]
            .as_array()
            .is_some_and(Vec::is_empty)
    );
}

#[test]
fn cli_square_free_mixed_observation_keeps_nonzero_gate_blocking() {
    let root = ag_measurement_root();
    let out_dir = temp_dir("ag-measurement-square-free-mixed-observation");
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:support-inventory-payment")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:support-inventory-payment"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_square_free_mixed.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("mixed ArchMap serializes"),
    )
    .expect("mixed ArchMap writes");

    let run_dir = run_square_free_analysis("ag-square-free-mixed", &archmap_path);
    let packet = read_json(&run_dir.join("archsig-measurement-packet.json"));
    let repair = invariant_by_id(&packet, "square-free-repair:profile:ag-square-free@1");
    let generators = repair["obstructionIdeal"]["generators"]
        .as_array()
        .expect("square-free generators are array");
    assert_eq!(generators.len(), 2);
    assert!(generators.iter().any(|generator| {
        generator["supportAtomRefs"]
            .as_array()
            .is_some_and(|refs| refs.is_empty())
    }));
    assert!(generators.iter().any(|generator| {
        generator["supportAtomRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
    }));
    let unobserved_boundaries = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements are array")
        .iter()
        .filter(|statement| statement["reason"] == "declared_generator_unobserved")
        .collect::<Vec<_>>();
    assert_eq!(unobserved_boundaries.len(), 1);
    assert!(
        unobserved_boundaries[0]["scopeRefs"]
            .as_array()
            .is_some_and(|refs| refs.iter().all(|reference| {
                !reference
                    .as_str()
                    .is_some_and(|reference| reference.starts_with("structuralVerdict/"))
            }))
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );

    let report = run_square_free_gate(&run_dir, 1);
    let mapping = report["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("absolute gate mappings")
        .iter()
        .find(|mapping| {
            mapping["rowRef"]
                .as_str()
                .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
        })
        .expect("mixed square-free gate mapping");
    assert_eq!(mapping["verdict"], "measured_nonzero");
    assert_eq!(mapping["action"], "block");
    assert_eq!(mapping["boundaryOverrideApplied"], false);

    assert_eq!(
        report["decision"], "BLOCKED_BY_GATE_POLICY",
        "mixed observation must remain blocking even with one silence_by_design statement"
    );
    let geometry =
        read_json(&run_dir.join("archsig-insight-report.json"))["gluingGeometry"].clone();
    assert_eq!(geometry["forbiddenCages"].as_array().map(Vec::len), Some(1));
    assert!(
        geometry["forbiddenCages"][0]["atomRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
    );
}

#[test]
fn cli_square_free_observation_drives_conservative_gate_sequence() {
    let root = ag_measurement_root();
    let sequence_dir = temp_dir("ag-measurement-square-free-gate-sequence");
    let mut clean_archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    clean_archmap["atoms"] = Value::Array(
        clean_archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "support")
            .cloned()
            .collect(),
    );
    clean_archmap["contexts"][0]["atoms"] = Value::Array(
        clean_archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| {
                !matches!(
                    atom.as_str(),
                    Some("atom:support-checkout-inventory" | "atom:support-inventory-payment")
                )
            })
            .cloned()
            .collect(),
    );
    let clean_archmap_path = sequence_dir.join("archmap_square_free_clean.json");
    fs::write(
        &clean_archmap_path,
        serde_json::to_vec_pretty(&clean_archmap).expect("clean ArchMap serializes"),
    )
    .expect("clean ArchMap writes");

    let clean_run = run_square_free_analysis("ag-square-free-gate-clean", &clean_archmap_path);
    let blocked_run = run_analyze_fixture_lock_with_surface(
        "ag-square-free-gate-blocked",
        "archmap_v2_square_free_repair.json",
        "law_policy_square_free.json",
        "law_surface_ag_v052.json",
        None,
    );
    let repaired_archmap_path = sequence_dir.join("archmap_square_free_repaired.json");
    let repaired_archmap = read_json(&root.join("archmap_v2_square_free_repair_unobserved.json"));
    fs::write(
        &repaired_archmap_path,
        serde_json::to_vec_pretty(&repaired_archmap).expect("repaired ArchMap serializes"),
    )
    .expect("repaired ArchMap writes");
    assert_ne!(clean_archmap_path, repaired_archmap_path);
    let repaired_run =
        run_square_free_analysis("ag-square-free-gate-repaired", &repaired_archmap_path);

    let clean_gate = run_square_free_gate(&clean_run, 0);
    let blocked_gate = run_square_free_gate(&blocked_run, 1);
    let repaired_gate = run_square_free_gate(&repaired_run, 0);

    assert_eq!(clean_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    assert_eq!(blocked_gate["decision"], "BLOCKED_BY_GATE_POLICY");
    assert_eq!(repaired_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    for report in [&clean_gate, &repaired_gate] {
        let mapping = report["ruleOutcomes"][0]["appliedMapping"]
            .as_array()
            .expect("absolute gate mappings")
            .iter()
            .find(|mapping| {
                mapping["rowRef"]
                    .as_str()
                    .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
            })
            .expect("square-free gate mapping");
        assert_eq!(mapping["verdict"], "measured_zero");
        assert_eq!(mapping["action"], "pass_with_boundary");
        assert_eq!(mapping["boundaryOverrideApplied"], true);
    }
    let blocked_mapping = blocked_gate["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .expect("blocked absolute gate mappings")
        .iter()
        .find(|mapping| {
            mapping["rowRef"]
                .as_str()
                .is_some_and(|row_ref| row_ref.contains("ag-square-free-repair"))
        })
        .expect("blocked square-free gate mapping");
    assert_eq!(blocked_mapping["verdict"], "measured_nonzero");
    assert_eq!(blocked_mapping["action"], "block");
}

#[test]
fn cli_analyze_v2_law_conflict_tor_outputs_conflict_classes() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let validation = read_json(&out_dir.join("law-policy-validation.json"));
    let expanded = &validation["expandedPolicies"][0];
    assert!(
        !expanded
            .as_object()
            .expect("expanded policy is an object")
            .contains_key("law")
    );
    assert_eq!(
        expanded["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
    assert_eq!(
        expanded["sourceSelector"],
        "lawPair:law:checkout,law:inventory"
    );

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.law-conflict-tor"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_monomial_tor_taylor_computed"
    );
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["certRef"],
        "computedInvariants/law-conflict-tor:profile:ag-law-conflict-tor@1"
    );
    assert!(
        packet["structuralVerdict"][0]["dependsOnAssumptions"]
            .as_array()
            .expect("dependsOnAssumptions is array")
            .iter()
            .any(|assumption_id| assumption_id.as_str().is_some_and(
                |id| id.starts_with("assumption:part8-9-1-coefficient-compatibility:")
            )),
        "Tor verdict must depend on the common ambient coefficient compatibility ledger row"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "Hilbert interference reading must not add a structural verdict row"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert!(
        summary["translationRule"]["concreteSupportRefs"]
            .as_array()
            .is_some_and(|refs| {
                refs.iter().any(|reference| reference == "src:ambient")
                    && refs
                        .iter()
                        .any(|reference| reference == "src:checkout-policy")
                    && refs
                        .iter()
                        .any(|reference| reference == "ctx:tor-common-ambient")
            })
    );
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(
        tor["claimScope"],
        "degree-1 square-free monomial Tor over the selected common ambient pair"
    );
    assert_eq!(tor["resolutionSelectorEffective"], true);
    assert_eq!(
        tor["commonAmbient"]["ambientRef"],
        "ambient:checkout-inventory"
    );
    let tor_object = tor.as_object().expect("Tor invariant is object");
    assert!(
        !tor_object.contains_key("coefficientRef")
            && !tor_object.contains_key("comparisonMorphismRef"),
        "M15 must expose coefficient compatibility through the assumption ledger, not new Tor schema fields"
    );
    assert_eq!(
        tor["lawConflicts"],
        serde_json::json!([{
            "conflictId": "LawConflict_1:1",
            "degree": 1,
            "support": ["x_checkout", "x_inventory", "x_payment"],
            "multidegree": ["x_checkout", "x_inventory", "x_payment"],
            "sharedSupport": ["x_inventory"],
            "leftLaw": "law:checkout",
            "leftGeneratorRef": "law-surface:law:checkout:1",
            "rightLaw": "law:inventory",
            "rightGeneratorRef": "law-surface:law:inventory:1",
            "contextRefs": ["ctx:tor-common-ambient"],
            "sourceRefs": ["src:checkout-policy", "src:inventory-policy"]
        }])
    );
    assert_eq!(
        tor["torByDegree"],
        serde_json::json!([{
            "degree": 1,
            "classCount": 1,
            "coefficient": "F2",
            "scope": "H_1 of Taylor(I_left) tensor R/I_right by square-free multidegree"
        }])
    );
    assert_eq!(tor["proxyComparison"]["proxyClassCount"], Value::from(1));
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::from(1));
    assert!(
        tor["boundaryNote"]
            .as_str()
            .is_some_and(|note| note.contains("higher Tor_i") && note.contains("F2")),
        "Tor boundary note must keep higher Tor and field-coefficient boundaries visible"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|row| row["theoremRef"] == "part8/9.1-coefficient-compatibility"
                && row["assumption"]
                    == "common ambient coefficient compatibility under the selected single F2 coefficient model"
                && row["status"] == "checked"
                && row["checkedBy"]
                    == "measurement-profile:profile:ag-law-conflict-tor@1.coefficient:F2"),
        "Tor assumption ledger must record checked coefficient compatibility for the selected common ambient"
    );
    let hilbert = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "hilbert-interference-series@1")
        .expect("Hilbert interference audit reading exists");
    assert_eq!(hilbert["regime"], "analytic-measurement");
    assert_eq!(hilbert["structuralVerdictRef"], Value::Null);
    assert_eq!(
        hilbert["value"]["regimeBoundary"],
        "audit-only in the selected graded square-free monomial Taylor regime"
    );
    assert_eq!(
        hilbert["value"]["series"],
        serde_json::json!([{"degree": 1, "coefficient": 1}])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_disjoint_supports_are_not_computed() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-disjoint");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout".to_string());
    archmap["atoms"][2]["object"] = Value::String("x_payment".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_disjoint.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(
        tor["lawConflicts"]
            .as_array()
            .expect("conflicts is array")
            .len(),
        0
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_undeclared_nested_support_is_unmeasured() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-nested");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout,x_inventory,x_inventory".to_string());
    archmap["atoms"][2]["object"] = Value::String("x_inventory,x_payment".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_nested.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unmeasured");
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert!(tor["lawConflicts"].as_array().unwrap().is_empty());
}

#[test]
fn cli_analyze_v2_law_conflict_tor_taylor_reduces_proxy_overcount() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-taylor-overcount");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][2]["object"] = Value::String("x_checkout,x_inventory,x_payment".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(json!({
            "id": "atom:checkout-law-generator-2",
            "kind": "relation",
            "subject": "law:checkout",
            "object": "x_inventory,x_payment",
            "axis": "tor",
            "predicate": "lawIdealGenerator",
            "refs": ["src:checkout-policy"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:checkout-law-generator-2".to_string()));
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_taylor_overcount.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["verdict"],
        "measured_nonzero"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(tor["proxyComparison"]["proxyClassCount"], Value::from(1));
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::from(1));
    assert_eq!(
        tor["lawConflicts"][0]["multidegree"],
        serde_json::json!(["x_checkout", "x_inventory", "x_payment"])
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_preserves_common_ambient_law_pair_order() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-reversed-law-pair");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][0]["object"] = Value::String("law:inventory,law:checkout".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_reversed_law_pair.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(
        tor["commonAmbient"]["lawPair"],
        serde_json::json!(["law:inventory", "law:checkout"])
    );
    assert_eq!(tor["lawConflicts"][0]["leftLaw"], "law:inventory");
    assert_eq!(tor["lawConflicts"][0]["rightLaw"], "law:checkout");
    assert_eq!(
        tor["lawConflicts"][0]["leftGeneratorRef"],
        "law-surface:law:inventory:1"
    );
    assert_eq!(
        tor["lawConflicts"][0]["rightGeneratorRef"],
        "law-surface:law:checkout:1"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_non_square_free_is_unmeasured() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-non-square-free");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_checkout,x_inventory,x_inventory".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_non_square_free.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unmeasured");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "non_square_free_monomial"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["method"], "finite-monomial-tor-taylor@1");
    assert_eq!(tor["torByDegree"][0]["status"], "unmeasured");
    assert_eq!(tor["torByDegree"][0]["classCount"], Value::Null);
    assert_eq!(tor["proxyComparison"]["taylorClassCount"], Value::Null);
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "hilbert-interference-series@1"),
        "Hilbert interference reading must stay absent outside the square-free monomial regime"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|row| row["theoremRef"] == "part5/5.5"
                && row["assumption"]
                    == "finite square-free monomial law ideals selected for degree-1 Taylor Tor"
                && row["status"] == "violated"),
        "non-square-free generators must violate the square-free Taylor premise"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_generators_outside_ambient_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-ambient-mismatch");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][2]["subject"] = Value::String("law:shipping".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_ambient_mismatch.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_tor.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_without_common_ambient_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-no-ambient");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "commonAmbient")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:tor-common-ambient"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_no_ambient.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "no_common_ambient"
    );
    assert!(
        packet["structuralVerdict"][0]["dependsOnAssumptions"]
            .as_array()
            .expect("dependsOnAssumptions is array")
            .iter()
            .any(|assumption_id| assumption_id.as_str().is_some_and(
                |id| id.starts_with("assumption:part8-9-1-coefficient-compatibility:")
            )),
        "not-computed Tor verdict still records the coefficient compatibility dependency"
    );
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert_eq!(tor["status"], "not_computed");
    assert_eq!(tor["reason"], "no_common_ambient");
    assert_ne!(
        packet["structuralVerdict"][0]["verdict"], "measured_zero",
        "violated common ambient / coefficient compatibility must not degrade to measured_zero"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(
                |row| row["theoremRef"] == "part8/9.1-coefficient-compatibility"
                    && row["status"] == "violated"
                    && row["assumedBy"] == "measurement-profile:profile:ag-law-conflict-tor@1"
            ),
        "missing common ambient must mark coefficient compatibility violated in the assumption ledger"
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_uses_law_surface_witnesses() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-witness-family");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    let policy_path = out_dir.join("law_policy_tor_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_law_conflict_tor_selects_only_declared_law_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-explicit-law-pair");
    let root = ag_measurement_root();
    let (policy, profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    let policy_path = out_dir.join("law_policy_tor.json");
    let surface_path = out_dir.join("law_surface_with_unselected_law.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    surface["laws"].as_array_mut().unwrap().push(json!({
        "lawId": "law:shipping",
        "conditionType": "closed-equational",
        "witnessVariables": [{
            "variable": "x_shipping",
            "binding": {
                "archmapVariable": "x_shipping",
                "axis": "square-free",
                "predicate": "support"
            }
        }],
        "forbiddenSupportGenerators": [{"support": ["x_shipping"]}]
    }));
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("law surface serializes"),
    )
    .expect("law surface is written");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let tor = invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1");
    assert!(
        tor["witnessVariables"]
            .as_array()
            .expect("Tor witness variables are an array")
            .iter()
            .all(|variable| variable != "x_shipping"),
        "an unselected law declared with a law: prefix must not enter the Tor witness family"
    );
    assert_eq!(
        tor["witnessVariables"],
        json!(["x_checkout", "x_inventory", "x_payment"])
    );
    assert_eq!(
        tor["lawIdeals"]
            .as_array()
            .expect("Tor law ideals are an array")
            .iter()
            .map(|ideal| ideal["law"].clone())
            .collect::<Vec<_>>(),
        vec![json!("law:checkout"), json!("law:inventory")]
    );
}

#[test]
fn cli_law_policy_rejects_malformed_tor_law_pairs() {
    let root = ag_measurement_root();
    for (name, pair, evaluator, expected_evidence) in [
        (
            "missing",
            None,
            Some("ag.law-conflict-tor"),
            "ag.law-conflict-tor requires an explicit lawPair declaration",
        ),
        (
            "one",
            Some(vec!["law:checkout"]),
            Some("ag.law-conflict-tor"),
            "lawPair must contain exactly two distinct non-empty law ids",
        ),
        (
            "duplicate",
            Some(vec!["law:checkout", "law:checkout"]),
            Some("ag.law-conflict-tor"),
            "lawPair must contain exactly two distinct non-empty law ids",
        ),
        (
            "wrong-evaluator",
            Some(vec!["law:checkout", "law:inventory"]),
            Some("ag.square-free-repair"),
            "lawPair is reserved for the ag.law-conflict-tor evaluator",
        ),
    ] {
        let out_dir = temp_dir(&format!("ag-law-policy-tor-pair-{name}"));
        let mut policy = read_json(&root.join("law_policy_tor.json"));
        let entry = policy["policies"][0]
            .as_object_mut()
            .expect("Tor policy entry is an object");
        if let Some(pair) = pair {
            entry.insert("lawPair".to_string(), json!(pair));
        } else {
            entry.remove("lawPair");
        }
        entry.insert("evaluator".to_string(), json!(evaluator));
        let policy_path = out_dir.join("law_policy.json");
        fs::write(
            &policy_path,
            serde_json::to_vec_pretty(&policy).expect("policy serializes"),
        )
        .expect("policy writes");
        fs::write(
            out_dir.join("measurement_profile.json"),
            fs::read(root.join("measurement_profile_tor.json")).expect("profile reads"),
        )
        .expect("profile writes");
        let report_path = out_dir.join("law-policy-validation.json");

        run_sig0_expect_code(
            &[
                "law-policy",
                "--law-policy",
                policy_path.to_str().expect("policy path is utf-8"),
                "--measurement-profile",
                test_measurement_profile_path(Path::new(
                    policy_path.to_str().expect("policy path is utf-8"),
                ))
                .to_str()
                .expect("profile path is utf-8"),
                "--law-surface",
                root.join("law_surface_ag_v052.json")
                    .to_str()
                    .expect("surface path is utf-8"),
                "--out",
                report_path.to_str().expect("report path is utf-8"),
            ],
            1,
        );
        let report = read_json(&report_path);
        assert_eq!(report["summary"]["result"], "fail");
        assert!(report["checks"].as_array().is_some_and(|checks| {
            checks.iter().any(|check| {
                check["id"] == "law-policy-schema052-entry-shape"
                    && check["examples"].as_array().is_some_and(|examples| {
                        examples
                            .iter()
                            .any(|example| example["evidence"] == expected_evidence)
                    })
            })
        }));
    }
}

#[test]
fn cli_law_policy_rejects_non_closed_tor_law_surface() {
    let out_dir = temp_dir("ag-law-policy-tor-non-closed");
    let root = ag_measurement_root();
    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    for law_id in ["law:checkout", "law:inventory"] {
        surface["laws"]
            .as_array_mut()
            .expect("law surface laws are an array")
            .iter_mut()
            .find(|law| law["lawId"] == law_id)
            .expect("Tor law exists")
            .as_object_mut()
            .expect("Tor law is an object")
            .insert("conditionType".to_string(), json!("constructible"));
    }
    let surface_path = out_dir.join("law_surface_non_closed.json");
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("surface serializes"),
    )
    .expect("surface writes");
    let report_path = out_dir.join("law-policy-validation.json");

    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("policy path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_tor.json")
                .to_str()
                .expect("profile path is utf-8"),
            "--law-surface",
            surface_path.to_str().expect("surface path is utf-8"),
            "--out",
            report_path.to_str().expect("report path is utf-8"),
        ],
        1,
    );
    let report = read_json(&report_path);
    assert!(report["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-schema052-law-surface-resolution"
                && check["result"] == "fail"
        })
    }));
}

#[test]
fn cli_analyze_v2_square_free_requires_explicit_law() {
    let out_dir = temp_dir("ag-measurement-square-free-missing-law");
    let root = ag_measurement_root();
    let (mut policy, profile) =
        read_fixture_policy_profile(&root.join("law_policy_square_free.json"));
    policy["policies"][0]
        .as_object_mut()
        .expect("policy entry is an object")
        .remove("law");
    let policy_path = out_dir.join("law_policy_square_free_missing_law.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    let report_path = out_dir.join("law-policy-validation.json");
    run_sig0_expect_code(
        &[
            "law-policy",
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            root.join("measurement_profile_square_free.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        1,
    );
    let report = read_json(&report_path);
    assert!(report["checks"].as_array().is_some_and(|checks| {
        checks.iter().any(|check| {
            check["id"] == "law-policy-schema052-entry-shape"
                && check["examples"].as_array().is_some_and(|examples| {
                    examples.iter().any(|example| {
                        example["evidence"]
                            == "ag.square-free-repair requires an explicit law selector"
                    })
                })
        })
    }));
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_unsupported_resolution_selector() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-bad-resolution");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_tor.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_tor_bad_resolution.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_law_conflict_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_rejects_malformed_common_ambient_pair() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-bad-ambient");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][0]["object"] = Value::String("law:checkout".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_bad_ambient.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_tor.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_law_conflict_tor_ignores_undeclared_observed_variables() {
    let out_dir = temp_dir("ag-measurement-law-conflict-tor-unknown-variable");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_law_conflict_tor.json"));
    archmap["atoms"][1]["object"] = Value::String("x_unknown,x_inventory".to_string());
    let archmap_path = out_dir.join("archmap_v2_law_conflict_tor_unknown_variable.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_tor.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_tor.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_outputs_analytic_hodge_reading() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"][0]["evaluator"],
        "ag.sheaf-laplacian"
    );
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "finite_laplacian_analytic_reading_computed"
    );
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "curvature hotspot reading must not add a structural verdict row"
    );
    let invariant = invariant_by_id(&packet, "sheaf-laplacian:profile:ag-sheaf-laplacian@1");
    assert_eq!(
        invariant["claimScope"],
        "graph Laplacian analytic proxy; not a full sheaf chain-complex Hodge theorem"
    );
    assert_eq!(
        invariant["laplacianMatrix"],
        serde_json::json!([[1.0, -1.0], [-1.0, 1.0]])
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.sheaf-laplacian")
        .expect("laplacian analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["claimStatus"], "certified");
    assert_eq!(reading["fidelity"], "proxy");
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(
        reading["value"]["readingKind"],
        "graph-laplacian-hodge-proxy@1"
    );
    assert_eq!(
        reading["value"]["modelScope"],
        "finite graph Laplacian over selected cochain cells and boundary edges"
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["harmonic"],
        serde_json::json!([0.5, 0.5])
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["exact"],
        serde_json::json!([0.0, 0.0])
    );
    assert_eq!(
        reading["value"]["hodgeDecomposition"]["coexact"],
        serde_json::json!([0.5, -0.5])
    );
    assert_eq!(reading["value"]["harmonicMass"], Value::from(0.5));
    assert_eq!(reading["value"]["distanceToFlatness"], Value::from(0.5));
    assert_eq!(reading["value"]["spectralGap"], Value::from(2.0));
    assert_eq!(
        reading["value"]["curvatureTransferSpectrum"],
        serde_json::json!([
            {"cell": "cell:left", "curvature": 1.0},
            {"cell": "cell:right", "curvature": -1.0}
        ])
    );
    assert_eq!(reading["value"]["essentialRepairLowerBound"], Value::Null);
    assert_eq!(
        reading["value"]["nonConclusion"],
        "near-flat analytic values are not structural lawfulness verdicts"
    );
    let candidate = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| {
            reading["readingId"]
                .as_str()
                .is_some_and(|id| id.starts_with("theorem-candidate:harmonic-debt:"))
        })
        .expect("harmonic debt theorem-candidate reading exists");
    assert_eq!(candidate["regime"], "theorem-candidate");
    assert_eq!(
        candidate["value"]["essentialRepairLowerBound"],
        Value::from(0.707107)
    );
    let hotspot = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "curvature-transfer-perron-hotspot@1")
        .expect("curvature hotspot theorem-candidate reading exists");
    assert_eq!(hotspot["regime"], "theorem-candidate");
    assert_eq!(hotspot["structuralVerdictRef"], Value::Null);
    assert_eq!(
        hotspot["value"]["sourceProxyReadingKind"],
        "graph-laplacian-hodge-proxy@1"
    );
    assert_eq!(
        hotspot["value"]["hotspots"],
        serde_json::json!([
            {"cell": "cell:left", "hotspotWeight": 0.707107},
            {"cell": "cell:right", "hotspotWeight": 0.707107}
        ])
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_harmonic_debt_requires_cost_model_for_lower_bound() {
    let root = ag_measurement_root();
    let out_dir = temp_dir("ag-measurement-harmonic-debt");
    let mut policy = read_json(&root.join("law_policy_laplacian.json"));
    policy["measurementProfileRef"] = json!("profile:ag-harmonic-debt@1");
    policy["policies"][0]["evaluator"] = json!("ag.harmonic-debt");
    let policy_path = out_dir.join("law_policy_harmonic_debt.json");
    let profile_path = out_dir.join("measurement_profile_harmonic_debt.json");
    let surface_path = root.join("law_surface_ag_v052.json");
    fs::write(&policy_path, serde_json::to_vec_pretty(&policy).unwrap()).unwrap();
    fs::copy(
        root.join("measurement_profile_harmonic_debt.json"),
        &profile_path,
    )
    .unwrap();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--measurement-profile",
        profile_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--out-dir",
        out_dir.to_str().unwrap(),
    ]);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert!(
        packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["evaluator"] != "ag.harmonic-debt"),
        "harmonic debt must stay out of structural verdicts"
    );
    let invariant = invariant_by_id(&packet, "harmonic-debt:profile:ag-harmonic-debt@1");
    assert_eq!(invariant["harmonicDebtNorm"], json!(0.707107));
    assert_eq!(invariant["essentialRepairLowerBound"], json!(0.353553));
    assert_eq!(invariant["lowerBoundStatus"], "cost_model_supplied");
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/8.7")
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.harmonic-debt")
        .unwrap();
    assert_eq!(reading["claimStatus"], "certified");
    assert_eq!(reading["fidelity"], "faithful");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);

    let no_cost_out = temp_dir("ag-measurement-harmonic-debt-no-cost");
    let no_cost_profile = read_json(&profile_path);
    let mut no_cost_profile = no_cost_profile;
    no_cost_profile["analytic"]
        .as_object_mut()
        .unwrap()
        .remove("costModel");
    let no_cost_profile_path = no_cost_out.join("measurement_profile_harmonic_debt.json");
    fs::write(
        &no_cost_profile_path,
        serde_json::to_vec_pretty(&no_cost_profile).unwrap(),
    )
    .unwrap();
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--measurement-profile",
        no_cost_profile_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--out-dir",
        no_cost_out.to_str().unwrap(),
    ]);
    let no_cost_packet = read_json(&no_cost_out.join("archsig-measurement-packet.json"));
    let no_cost_invariant =
        invariant_by_id(&no_cost_packet, "harmonic-debt:profile:ag-harmonic-debt@1");
    assert_eq!(
        no_cost_invariant["lowerBoundStatus"],
        "cost_model_not_supplied"
    );
    assert_eq!(no_cost_invariant["status"], "silence_by_design");
    assert_eq!(
        no_cost_invariant["whatNext"],
        "supply analytic.costModel with a positive Lipschitz constant and harmonic resolution before evaluating essentialRepairLowerBound"
    );
    assert!(no_cost_invariant.get("essentialRepairLowerBound").is_none());
    let no_cost_reading = no_cost_packet["analyticReadings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.harmonic-debt")
        .unwrap();
    assert!(
        no_cost_reading["value"]
            .get("essentialRepairLowerBound")
            .is_none()
    );
    assert_eq!(
        no_cost_reading["value"]["whatNext"],
        no_cost_invariant["whatNext"]
    );
    assert!(
        !no_cost_packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["theoremRef"] == "part8/8.7")
    );
    assert!(
        no_cost_packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| {
                statement["kind"] == "silence_by_design"
                    && statement["reason"] == "cost_model_not_supplied"
                    && statement["text"].as_str().is_some_and(|text| {
                        text.contains("analytic.costModel")
                            && text.contains("essentialRepairLowerBound")
                    })
            }),
        "missing cost model must remain a typed silence_by_design boundary"
    );
    let no_cost_gate_report = no_cost_out.join("gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        no_cost_out
            .join("archsig-measurement-packet.json")
            .to_str()
            .unwrap(),
        "--policy",
        root.join("gate_policy_conservative.json").to_str().unwrap(),
        "--out",
        no_cost_gate_report.to_str().unwrap(),
    ]);
    let no_cost_gate = read_json(&no_cost_gate_report);
    assert_eq!(no_cost_gate["decision"], "PASS_WITHIN_GATE_POLICY");
    let no_cost_mapping = no_cost_gate["ruleOutcomes"][0]["appliedMapping"]
        .as_array()
        .unwrap()
        .iter()
        .find(|mapping| mapping["rowRef"] == "analytic:harmonic-debt:profile:ag-harmonic-debt@1")
        .expect("analytic cost-model silence reaches gate mapping");
    assert_eq!(no_cost_mapping["action"], "pass_with_boundary");
    assert_eq!(no_cost_mapping["boundaryOverrideApplied"], true);

    let invalid_out = temp_dir("ag-measurement-harmonic-debt-invalid-cost");
    let mut invalid_profile = read_json(&profile_path);
    invalid_profile["analytic"]["costModel"]["kind"] = json!("unbounded-cost");
    let invalid_profile_path = invalid_out.join("measurement_profile_harmonic_debt.json");
    fs::write(
        &invalid_profile_path,
        serde_json::to_vec_pretty(&invalid_profile).unwrap(),
    )
    .unwrap();
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_sheaf_laplacian.json")
                .to_str()
                .unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--measurement-profile",
            invalid_profile_path.to_str().unwrap(),
            "--law-surface",
            surface_path.to_str().unwrap(),
            "--out-dir",
            invalid_out.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_duplicate_cochain_cells() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-duplicate-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    let mut duplicate = archmap["atoms"][0].clone();
    duplicate["id"] = Value::String("atom:laplacian-left-cochain-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:laplacian-left-cochain-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_duplicate_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_non_finite_cochain_values() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["object"] = Value::String("NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_laplacian.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_laplacian_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_sheaf_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_missing_witness_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-missing-witness");
    let root = ag_measurement_root();
    let (policy, mut profile) =
        read_fixture_policy_profile(&root.join("law_policy_laplacian.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.sheaf-laplacian", "variable": "cell:left"},
        {"law": "ag.sheaf-laplacian", "variable": "cell:right"},
        {"law": "ag.sheaf-laplacian", "variable": "cell:extra"}
    ]);
    let policy_path = out_dir.join("law_policy_laplacian_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_sheaf_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    let invariant = invariant_by_id(&packet, "sheaf-laplacian:profile:ag-sheaf-laplacian@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "cellular_model_missing:cell:extra");
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_near_flat_is_not_measured_zero() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-near-flat");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["object"] = Value::String("0.001".to_string());
    archmap["atoms"][1]["object"] = Value::String("0".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_near_flat.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "unknown");
    assert_eq!(packet["structuralVerdict"][0]["verdictData"]["zero"], false);

    let zero_out_dir = temp_dir("ag-measurement-sheaf-laplacian-exact-zero-color");
    let mut zero_archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    zero_archmap["atoms"][0]["object"] = Value::String("0".to_string());
    zero_archmap["atoms"][1]["object"] = Value::String("0".to_string());
    let zero_archmap_path = zero_out_dir.join("archmap_v2_sheaf_laplacian_exact_zero.json");
    fs::write(
        &zero_archmap_path,
        serde_json::to_vec_pretty(&zero_archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    run_sig0(&[
        "analyze",
        "--archmap",
        zero_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        zero_out_dir.to_str().expect("path is utf-8"),
    ]);
    let zero_report = read_json(&zero_out_dir.join("archsig-insight-report.json"));
    assert!(
        zero_report["gluingGeometry"]["locusField"]["fieldRows"]
            .as_array()
            .expect("fieldRows is array")
            .iter()
            .filter(|row| row["status"] == "analytic_reading")
            .all(|row| row["colorRole"] == "analytic_reading"),
        "exact-zero analytic curvature rows must stay in the analytic lane, not measured_zero"
    );
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_without_boundary_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-no-boundary");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["predicate"] != "cellularBoundary")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:laplacian-boundary"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_no_boundary.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_laplacian.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(packet["structuralVerdict"][0]["verdict"], "not_computed");
    assert_eq!(
        packet["structuralVerdict"][0]["verdictData"]["methodStatus"],
        "cellular_model_missing"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_outputs_pairing_and_audit_reading() {
    let out_dir = temp_dir("ag-measurement-period-stokes");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_period_stokes.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "period readings are analytic-only and must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(
        invariant["periodPairingMatrix"],
        serde_json::json!([[2.0, -1.0]])
    );
    assert_eq!(invariant["stokesAudit"]["status"], "checked");
    assert_eq!(
        invariant["stokesAudit"]["maxAbsoluteResidual"],
        Value::from(0.0)
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.period-stokes")
        .expect("period analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(reading["value"]["modelRelative"], true);
    assert_eq!(
        reading["value"]["cycleBasis"],
        serde_json::json!(["cycle:alpha", "cycle:beta"])
    );
    assert_eq!(
        reading["value"]["periodPairingMatrix"],
        serde_json::json!([[2.0, -1.0]])
    );
    assert_eq!(
        reading["value"]["nonConclusion"],
        "period pairing is a model-relative analytic reading and is not a structural lawfulness verdict"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|entry| {
                entry["assumption"] == "period_comparison" && entry["status"] == "assumed"
            })
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_audit_mismatch_is_analytic_residual() {
    let out_dir = temp_dir("ag-measurement-period-stokes-audit-mismatch");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][3]["object"] = Value::String("chain:sigma=4".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_audit_mismatch.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "legacy analytic period-stokes residual must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(
        invariant["stokesAudit"]["status"], "residual_nonzero",
        "legacy analytic period-stokes must report nonzero residual without crashing"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_audit_outputs_structural_verdicts() {
    let root_out = temp_dir("ag-measurement-period-stokes-audit");
    let root = ag_measurement_root();

    for (case, coefficient, boundary_value, expected_verdict, expected_status) in [
        (
            "zero",
            "Q",
            "chain:sigma=3",
            "measured_zero",
            "fixed_coefficient_stokes_audit_computed",
        ),
        (
            "nonzero",
            "Q",
            "chain:sigma=4",
            "measured_nonzero",
            "fixed_coefficient_stokes_audit_computed",
        ),
        (
            "float-only",
            "R",
            "chain:sigma=3",
            "unknown",
            "strict_coefficient_unresolved",
        ),
    ] {
        let out_dir = root_out.join(case);
        fs::create_dir_all(&out_dir).expect("case dir exists");
        let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
        archmap["atoms"][3]["object"] = Value::String(boundary_value.to_string());
        let archmap_path = out_dir.join("archmap.json");
        fs::write(
            &archmap_path,
            serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
        )
        .expect("archmap fixture can be written");
        let (mut policy, mut profile) =
            read_fixture_policy_profile(&root.join("law_policy_period.json"));
        profile["coefficient"] = Value::String(coefficient.to_string());
        profile["effCoeff"] = Value::String("fixed-coefficient-stokes-audit@1".to_string());
        profile["resolutionSelector"] =
            Value::String("finite-poset-period-stokes-audit@1".to_string());
        profile["zeroPredicate"] = Value::String("stokes-residual-zero@1".to_string());
        profile["nonZeroPredicate"] = Value::String("stokes-residual-nonzero@1".to_string());
        profile["certSelector"] = Value::String("finite-certificate@1".to_string());
        profile["witnessFamily"] = json!([
            {"law": "ag.period-stokes-audit", "variable": "cycle:alpha"},
            {"law": "ag.period-stokes-audit", "variable": "cycle:beta"}
        ]);
        policy["policies"][0]["law"] = Value::String("ag.period-stokes-audit".to_string());
        policy["policies"][0]["evaluator"] = Value::String("ag.period-stokes-audit".to_string());
        let policy_path = out_dir.join("law_policy.json");
        write_test_policy_and_profile(&policy_path, policy, profile);

        run_sig0(&[
            "analyze",
            "--archmap",
            archmap_path.to_str().unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().unwrap()))
                .to_str()
                .expect("path is utf-8"),
            "--law-surface",
            policy_path
                .with_file_name("law_surface.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().unwrap(),
        ]);

        let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
        let structural = packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array");
        assert_eq!(
            structural.len(),
            1,
            "period-stokes-audit must add exactly one structural verdict row"
        );
        assert_eq!(structural[0]["evaluator"], "ag.period-stokes-audit");
        assert_eq!(structural[0]["verdict"], expected_verdict);
        assert_eq!(
            structural[0]["verdictData"]["methodStatus"],
            expected_status
        );
        let invariant = invariant_by_id(&packet, "period-stokes-audit:profile:ag-period-stokes@1");
        assert_eq!(invariant["evaluator"], "ag.period-stokes-audit");
        assert_eq!(invariant["stokesAudit"]["coefficient"], coefficient);
        assert!(
            packet["analyticReadings"]
                .as_array()
                .expect("analytic readings is array")
                .iter()
                .any(|reading| reading["evaluator"] == "ag.period-stokes"
                    && reading["structuralVerdictRef"] == Value::Null
                    && reading["value"]["readingKind"] == "strict-period-pairing@1"),
            "strict-period-pairing must remain an analytic reading separate from the structural verdict"
        );
    }
}

#[test]
fn cli_analyze_v2_common_structural_verdict_discipline_locks_measurement_evaluators() {
    let root_out = temp_dir("ag-measurement-common-structural-verdict-discipline");
    let mut observed_new_structural_evaluators = BTreeSet::new();

    for (case, evaluator, archmap, policy, profile) in [
        (
            "restriction",
            "ag.restriction-compatibility",
            restriction_archmap("compatible"),
            restriction_policy(),
            restriction_profile(),
        ),
        (
            "section",
            "ag.section-factorization",
            section_archmap("lawful"),
            section_policy(),
            section_profile(),
        ),
        (
            "coherence",
            "ag.coherence-obstruction",
            coherence_triangle_archmap(true),
            coherence_policy("F2", false),
            coherence_profile("F2", false),
        ),
        (
            "boundary-residue",
            "ag.boundary-residue",
            boundary_residue_archmap("zero"),
            boundary_residue_policy(),
            boundary_residue_profile(),
        ),
    ] {
        let packet = run_generated_ag_measurement_case(&root_out, case, archmap, policy, profile);
        assert_common_structural_verdict_discipline(&packet, evaluator);
        observed_new_structural_evaluators.insert(evaluator.to_string());
    }

    let root = ag_measurement_root();
    let mut period_archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    period_archmap["atoms"][3]["object"] = Value::String("chain:sigma=3".to_string());
    let (mut period_policy, mut period_profile) =
        read_fixture_policy_profile(&root.join("law_policy_period.json"));
    period_profile["coefficient"] = Value::String("Q".to_string());
    period_profile["effCoeff"] = Value::String("fixed-coefficient-stokes-audit@1".to_string());
    period_profile["resolutionSelector"] =
        Value::String("finite-poset-period-stokes-audit@1".to_string());
    period_profile["zeroPredicate"] = Value::String("stokes-residual-zero@1".to_string());
    period_profile["nonZeroPredicate"] = Value::String("stokes-residual-nonzero@1".to_string());
    period_profile["certSelector"] = Value::String("finite-certificate@1".to_string());
    period_profile["witnessFamily"] = json!([
        {"law": "ag.period-stokes-audit", "variable": "cycle:alpha"},
        {"law": "ag.period-stokes-audit", "variable": "cycle:beta"}
    ]);
    period_policy["policies"][0]["law"] = Value::String("ag.period-stokes-audit".to_string());
    period_policy["policies"][0]["evaluator"] = Value::String("ag.period-stokes-audit".to_string());
    let period_packet = run_generated_ag_measurement_case(
        &root_out,
        "period-stokes-audit",
        period_archmap,
        period_policy,
        period_profile,
    );
    assert_common_structural_verdict_discipline(&period_packet, "ag.period-stokes-audit");
    observed_new_structural_evaluators.insert("ag.period-stokes-audit".to_string());

    assert_eq!(
        observed_new_structural_evaluators,
        BTreeSet::from([
            "ag.restriction-compatibility".to_string(),
            "ag.section-factorization".to_string(),
            "ag.coherence-obstruction".to_string(),
            "ag.boundary-residue".to_string(),
            "ag.period-stokes-audit".to_string(),
        ]),
        "PRD M common must limit new structural verdict evaluators to M2/M3/M5/M6/M9"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_without_audit_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-no-audit");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| {
                atom["predicate"] != "dOmegaIntegral" && atom["predicate"] != "boundaryPeriod"
            })
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| {
                !matches!(
                    atom.as_str(),
                    Some("atom:stokes-domega-sigma" | "atom:stokes-boundary-sigma")
                )
            })
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_period_stokes_no_audit.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0
    );
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "period_model_missing");
}

#[test]
fn cli_analyze_v2_period_stokes_missing_pairing_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-missing-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:period-eta-alpha",
            "kind": "semantic",
            "subject": "omega:secondary",
            "object": "cycle:alpha=5",
            "axis": "period",
            "predicate": "periodIntegral",
            "refs": ["src:period-alpha"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:period-eta-alpha".to_string()));
    let archmap_path = out_dir.join("archmap_v2_period_stokes_missing_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_period.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "period_model_missing:omega:secondary/cycle:beta"
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["evaluator"] != "ag.period-stokes"),
        "missing period pairing cells must not synthesize zero analytic readings"
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_unknown_cycle() {
    let out_dir = temp_dir("ag-measurement-period-stokes-unknown-cycle");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][0]["object"] = Value::String("cycle:missing=2".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_unknown_cycle.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_duplicate_pairings() {
    let out_dir = temp_dir("ag-measurement-period-stokes-duplicate");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    let mut duplicate = archmap["atoms"][0].clone();
    duplicate["id"] = Value::String("atom:period-omega-alpha-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:period-omega-alpha-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_period_stokes_duplicate.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_non_finite_values() {
    let out_dir = temp_dir("ag-measurement-period-stokes-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_period_stokes.json"));
    archmap["atoms"][0]["object"] = Value::String("cycle:alpha=NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_period_stokes_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_period.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_period.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-period-stokes-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_period.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_period_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_period_stokes.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_period_stokes_missing_witness_cycle_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-period-stokes-missing-witness");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_period.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.period-stokes", "variable": "cycle:alpha"},
        {"law": "ag.period-stokes", "variable": "cycle:beta"},
        {"law": "ag.period-stokes", "variable": "cycle:extra"}
    ]);
    let policy_path = out_dir.join("law_policy_period_missing_witness.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_period_stokes.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        policy_path
            .with_file_name("law_surface.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "period-stokes:profile:ag-period-stokes@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "period_model_missing:cycle:extra");
}

#[test]
fn cli_analyze_v2_support_transfer_outputs_residue_and_wasserstein_cost() {
    let out_dir = temp_dir("ag-measurement-support-transfer");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_support_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        0,
        "transfer readings are analytic-only and must not generate structural verdict rows"
    );
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(
        invariant["transferMeasurementPairing"],
        serde_json::json!([[0.25, 0.75]])
    );
    assert_eq!(invariant["transferResidue"], Value::from(0.790569));
    assert_eq!(invariant["wassersteinTransferCost"], Value::from(3.5));
    assert_eq!(
        invariant["supportLocalizedPremise"]["matrixCompletion"],
        "only supplied repairPath x target support pairings are admitted; any missing pairing blocks computation"
    );
    assert_eq!(
        invariant["supportLocalizedPremise"]["requiredPairingCount"],
        Value::from(2)
    );
    assert_eq!(
        invariant["supportLocalizedPremise"]["repairPathSupports"],
        serde_json::json!([{
            "repairPath": "repair:path:core",
            "supportTargets": ["support:api", "support:data"],
            "atomRef": "atom:transfer-repair-path-core"
        }])
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["evaluator"] == "ag.support-transfer")
        .expect("transfer analytic reading exists");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(reading["regime"], "analytic-measurement");
    assert_eq!(
        reading["value"]["transferMeasurementPairing"],
        serde_json::json!([[0.25, 0.75]])
    );
    assert_eq!(reading["value"]["transferResidue"], Value::from(0.790569));
    assert_eq!(
        reading["value"]["wassersteinTransferCost"],
        Value::from(3.5)
    );
    assert_eq!(
        reading["value"]["supportLocalizedPremise"]["nonConclusion"],
        "no unconditional transfer matrix is inferred for support-disjoint or unobserved paths"
    );
    assert_eq!(
        reading["value"]["nonConclusion"],
        "transfer readings do not prove absence of side effects or global repair safety"
    );
    let candidate = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| {
            reading["readingId"]
                .as_str()
                .is_some_and(|id| id.starts_with("theorem-candidate:transfer-lower-bound:"))
        })
        .expect("transfer lower bound theorem-candidate reading exists");
    assert_eq!(candidate["regime"], "theorem-candidate");
    assert_eq!(candidate["value"]["transferLowerBound"], Value::from(3.5));
    assert!(
        packet["assumptions"]
            .as_array()
            .expect("assumptions is array")
            .iter()
            .any(|entry| {
                entry["assumption"] == "transfer_lower_bound" && entry["status"] == "assumed"
            })
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(
        summary["conclusion"],
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_blocks_support_disjoint_pairing() {
    let out_dir = temp_dir("ag-measurement-support-transfer-support-disjoint");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][0]["object"] = Value::String("support:api".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_support_disjoint.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert!(
        invariant["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("support_localized_premise_violated"))
    );
    assert_eq!(invariant["supportLocalizedPremise"]["status"], "violated");
    assert_eq!(
        invariant["supportLocalizedPremise"]["blockedPairings"],
        serde_json::json!(["repair:path:core/support:data"])
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "support-localized-transfer@1"),
        "support-disjoint pairings must not fill a transfer matrix"
    );
}

#[test]
fn cli_analyze_v2_refactor_transport_reading_requires_functoriality_witness() {
    let out_dir = temp_dir("ag-measurement-refactor-transport");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_square_free_repair.json"));
    archmap["sources"]["src:refactor"] = serde_json::json!({
        "kind": "policy",
        "path": "docs/tool/ag_measurement_evidence_contract.md",
        "section": "AC-M10"
    });
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:refactor-transport",
            "kind": "semantic",
            "subject": "refactor:extract-square-free-repair-module",
            "object": "ag.square-free-repair",
            "axis": "refactor",
            "predicate": "functorialityWitness",
            "refs": ["src:refactor"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:refactor-transport".to_string()));
    let archmap_path = out_dir.join("archmap_v2_refactor_transport.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--refactor-morphism",
        root.join("refactor_morphism.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        packet["structuralVerdict"]
            .as_array()
            .expect("structural verdict is array")
            .len(),
        1,
        "refactor transport witness must not add a verdict row"
    );
    let reading = packet["analyticReadings"]
        .as_array()
        .expect("analytic readings is array")
        .iter()
        .find(|reading| reading["value"]["readingKind"] == "refactor-verdict-transport@1")
        .expect("refactor transport reading exists when functoriality witness is supplied");
    assert_eq!(reading["evaluator"], "ag.foundation");
    assert_eq!(reading["structuralVerdictRef"], Value::Null);
    assert_eq!(
        reading["value"]["witnessAtomRef"],
        "atom:refactor-transport"
    );
    assert_eq!(
        reading["value"]["transportedEvaluator"],
        "ag.square-free-repair"
    );
    assert_eq!(reading["value"]["schema"], "refactor-morphism/v0.5.4");
    assert!(
        reading["value"]["nonConclusion"]
            .as_str()
            .is_some_and(|text| text.contains("creates no new verdict"))
    );
}

#[test]
fn cli_refactor_and_refinement_artifacts_are_validated_fail_closed() {
    let root = ag_measurement_root();
    let morphism = read_json(&root.join("refactor_morphism.json"));
    assert!(validate_refactor_morphism_v1(&morphism).is_ok());
    let mut invalid_morphism = morphism.clone();
    invalid_morphism["siteMorphism"]["direction"] = json!("fine-to-coarse");
    assert!(validate_refactor_morphism_v1(&invalid_morphism).is_err());
    let mut unknown_morphism = morphism.clone();
    unknown_morphism["conclusion"] = json!("forged");
    assert!(validate_refactor_morphism_v1(&unknown_morphism).is_err());

    let refinement = read_json(&root.join("refinement_comparison.json"));
    assert!(validate_refinement_comparison_v1(&refinement).is_ok());
    let mut invalid_refinement = refinement.clone();
    invalid_refinement["direction"] = json!("fine-to-coarse");
    assert!(validate_refinement_comparison_v1(&invalid_refinement).is_err());
}

#[test]
fn cli_analyze_v2_refactor_transport_absent_without_functoriality_witness() {
    let out_dir = temp_dir("ag-measurement-refactor-transport-absent");
    let root = ag_measurement_root();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_square_free_repair.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_square_free.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["value"]["readingKind"] != "refactor-invariant-transport@1"),
        "refactor transport reading must be absent without supplied functoriality witness data"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_pairing_cell_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-repair-path-secondary",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "support:api,support:data",
            "axis": "transfer",
            "predicate": "repairPath",
            "refs": ["src:repair-path"]
        }));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-secondary-api",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "support:api=0.5",
            "axis": "transfer",
            "predicate": "transferPairing",
            "refs": ["src:transfer-api"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-repair-path-secondary".to_string(),
        ));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String("atom:transfer-secondary-api".to_string()));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "transfer_model_missing:repair:path:secondary/support:data"
    );
    assert!(
        packet["analyticReadings"]
            .as_array()
            .expect("analytic readings is array")
            .iter()
            .all(|reading| reading["evaluator"] != "ag.support-transfer"),
        "missing transfer pairing cells must not synthesize zero analytic readings"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_repair_path_row_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-row");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(serde_json::json!({
            "id": "atom:transfer-repair-path-secondary",
            "kind": "semantic",
            "subject": "repair:path:secondary",
            "object": "support:api,support:data",
            "axis": "transfer",
            "predicate": "repairPath",
            "refs": ["src:repair-path"]
        }));
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-repair-path-secondary".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_row.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(
        invariant["reason"],
        "transfer_model_missing:repair:path:secondary/support:api,repair:path:secondary/support:data"
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_unknown_target() {
    let out_dir = temp_dir("ag-measurement-support-transfer-unknown-target");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][1]["object"] = Value::String("support:missing=0.25".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_unknown_target.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_duplicate_pairings() {
    let out_dir = temp_dir("ag-measurement-support-transfer-duplicate");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    let mut duplicate = archmap["atoms"][1].clone();
    duplicate["id"] = Value::String("atom:transfer-path-api-duplicate".to_string());
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(duplicate);
    archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .expect("context atoms is array")
        .push(Value::String(
            "atom:transfer-path-api-duplicate".to_string(),
        ));
    let archmap_path = out_dir.join("archmap_v2_support_transfer_duplicate.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_non_finite_values() {
    let out_dir = temp_dir("ag-measurement-support-transfer-nan");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"][1]["object"] = Value::String("support:api=NaN".to_string());
    let archmap_path = out_dir.join("archmap_v2_support_transfer_nan.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_transfer.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_rejects_malformed_profile_selector() {
    let out_dir = temp_dir("ag-measurement-support-transfer-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_transfer.json"));
    profile["resolutionSelector"] = Value::String("unsupported@1".to_string());
    let policy_path = out_dir.join("law_policy_transfer_bad_profile.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2_support_transfer.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_support_transfer_missing_ground_cost_is_not_computed() {
    let out_dir = temp_dir("ag-measurement-support-transfer-missing-cost");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_support_transfer.json"));
    archmap["atoms"] = Value::Array(
        archmap["atoms"]
            .as_array()
            .expect("atoms is array")
            .iter()
            .filter(|atom| atom["id"] != "atom:transfer-ground-data")
            .cloned()
            .collect(),
    );
    archmap["contexts"][0]["atoms"] = Value::Array(
        archmap["contexts"][0]["atoms"]
            .as_array()
            .expect("context atoms is array")
            .iter()
            .filter(|atom| atom.as_str() != Some("atom:transfer-ground-data"))
            .cloned()
            .collect(),
    );
    let archmap_path = out_dir.join("archmap_v2_support_transfer_missing_cost.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_transfer.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_transfer.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = invariant_by_id(&packet, "support-transfer:profile:ag-support-transfer@1");
    assert_eq!(invariant["status"], "not_computed");
    assert_eq!(invariant["reason"], "missing_ground_costs:support:data");
}

#[test]
fn cli_analyze_v2_sheaf_laplacian_rejects_unknown_cell() {
    let out_dir = temp_dir("ag-measurement-sheaf-laplacian-unknown-cell");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2_sheaf_laplacian.json"));
    archmap["atoms"][0]["subject"] = Value::String("cell:missing".to_string());
    let archmap_path = out_dir.join("archmap_v2_sheaf_laplacian_unknown_cell.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_laplacian.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_laplacian.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_rejects_unresolved_measurement_profile_refs() {
    let out_dir = temp_dir("ag-measurement-bad-profile");
    let root = ag_measurement_root();
    let (policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    profile["coverRef"] = Value::String("cover:missing".to_string());
    let policy_path = out_dir.join("law_policy_bad_cover.json");
    write_test_policy_and_profile(&policy_path, policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_selects_multiple_measurement_profiles_at_runtime() {
    let out_dir = temp_dir("ag-measurement-multiple-profiles");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    let primary_profile = read_json(&root.join("measurement_profile_ag.json"));
    let mut secondary_profile = primary_profile.clone();
    secondary_profile["profileId"] = json!("profile:ag-secondary@1");
    policy["policies"][0]["profileRef"] = json!("profile:ag-secondary@1");
    let policy_path = out_dir.join("law_policy_multiple_profiles.json");
    let primary_path = out_dir.join("measurement_profile_primary.json");
    let secondary_path = out_dir.join("measurement_profile_secondary.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("policy writes");
    fs::write(
        &primary_path,
        serde_json::to_vec_pretty(&primary_profile).expect("primary profile serializes"),
    )
    .expect("primary profile writes");
    fs::write(
        &secondary_path,
        serde_json::to_vec_pretty(&secondary_profile).expect("secondary profile serializes"),
    )
    .expect("secondary profile writes");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        primary_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        secondary_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let profile_ids = packet["profiles"]
        .as_array()
        .expect("multi-profile packet carries profiles")
        .iter()
        .filter_map(|profile| profile["profileId"].as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        profile_ids,
        BTreeSet::from(["profile:ag-default@1", "profile:ag-secondary@1"])
    );
    assert!(invariant_by_id(&packet, "cech-cohomology:profile:ag-secondary@1").is_object());
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(
        manifest["measurementProfileInputPaths"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfiles"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );

    let mut incompatible_profile = secondary_profile;
    incompatible_profile["coverRef"] = json!("cover:missing");
    let incompatible_path = out_dir.join("measurement_profile_incompatible.json");
    fs::write(
        &incompatible_path,
        serde_json::to_vec_pretty(&incompatible_profile).expect("incompatible profile serializes"),
    )
    .expect("incompatible profile writes");
    let incompatible_out = temp_dir("ag-measurement-multiple-profiles-incompatible");
    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json").to_str().unwrap(),
            "--law-policy",
            policy_path.to_str().unwrap(),
            "--law-surface",
            root.join("law_surface_ag_v052.json").to_str().unwrap(),
            "--measurement-profile",
            primary_path.to_str().unwrap(),
            "--measurement-profile",
            incompatible_path.to_str().unwrap(),
            "--out-dir",
            incompatible_out.to_str().unwrap(),
        ],
        2,
    );
}

#[test]
fn cli_analyze_v2_saga_grounded_emits_split_packet_and_detector() {
    let out_dir = temp_dir("ag-measurement-saga-grounded");
    let root = ag_measurement_root();
    let mut policy = read_json(&root.join("law_policy_ag.json"));
    policy["id"] = json!("law-policy:grounded-test");
    policy["lawSurfaceRef"] = json!("law-surface:grounded-test");
    policy["policies"][0] = json!({
        "law": "law:grounded-test",
        "evaluator": "ag.saga-grounded",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    });
    let mut surface = read_json(&root.join("law_surface_ag_v052.json"));
    surface["id"] = json!("law-surface:grounded-test");
    surface["laws"].as_array_mut().unwrap().push(json!({
        "lawId": "law:grounded-test",
        "conditionType": "closed-equational",
        "witnessVariables": [
            {"variable": "atom:order", "binding": {"edge": ["ctx:order", "ctx:shared"], "axis": "cech", "predicate": "sectionValue"}},
            {"variable": "atom:inventory", "binding": {"edge": ["ctx:inventory", "ctx:shared"], "axis": "cech", "predicate": "sectionValue"}},
            {"variable": "atom:shared", "binding": {"edge": ["ctx:order", "ctx:inventory"], "axis": "cech", "predicate": "sectionValue"}}
        ],
        "forbiddenSupportGenerators": [
            {"support": ["atom:order", "atom:inventory"]},
            {"support": ["atom:inventory", "atom:shared"]}
        ]
    }));
    surface["skeleton"] = json!([{
        "simplex": "vertex:grounded",
        "supportAtomRef": "atom:order",
        "requiredLawId": "law:grounded-test"
    }]);
    surface["defectSources"] = json!([{
        "lawId": "law:grounded-test",
        "coverRef": "cover:order-inventory",
        "chartDefects": [
            {"chart": "ctx:order", "defectObservable": {"axis": "cech", "predicate": "sectionValue"}},
            {"chart": "ctx:inventory", "defectObservable": {"axis": "cech", "predicate": "sectionValue"}},
            {"chart": "ctx:shared", "defectObservable": {"axis": "cech", "predicate": "sectionValue"}}
        ],
        "holdsCriterion": {"kind": "defect-raw-value-zero", "zeroSense": "empty-witness-set"}
    }]);
    surface["quotientSheafCondition"] = json!({"mode": "assumed"});
    let policy_path = out_dir.join("law_policy_grounded.json");
    let surface_path = out_dir.join("law_surface_grounded.json");
    let plan_path = out_dir.join("repair_plan_grounded.json");
    fs::write(&policy_path, serde_json::to_vec_pretty(&policy).unwrap()).unwrap();
    fs::write(&surface_path, serde_json::to_vec_pretty(&surface).unwrap()).unwrap();
    let mut plan = read_json(&root.join("repair_plan_complete_support.json"));
    let supplied_faithfulness = read_json(&root.join("repair_plan_supplied_faithfulness.json"));
    let true_sheaf = read_json(&root.join("repair_plan_true_sheaf.json"));
    let gluing_data = read_json(&root.join("repair_plan_gluing_data.json"));
    let comparison = read_json(&root.join("repair_plan_comparison.json"));
    plan["faithfulness"] = supplied_faithfulness["faithfulness"].clone();
    plan["trueSheafCertificate"] = true_sheaf["trueSheafCertificate"].clone();
    plan["gluingData"] = gluing_data["gluingData"].clone();
    plan["comparison"] = comparison["comparison"].clone();
    plan["grounding"] = json!({
        "kind": "saga-grounding",
        "surfaceRef": "law-surface:grounded-test",
        "profileRef": "profile:ag-default@1"
    });
    fs::write(&plan_path, serde_json::to_vec_pretty(&plan).unwrap()).unwrap();

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json").to_str().unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--measurement-profile",
        root.join("measurement_profile_ag.json").to_str().unwrap(),
        "--repair-plan",
        plan_path.to_str().unwrap(),
        "--out-dir",
        out_dir.to_str().unwrap(),
    ]);
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let grounded = invariant_by_id(&packet, "saga-generated-end-to-end-packet");
    assert_eq!(grounded["kind"], "saga-grounded-conclusions");
    assert_eq!(grounded["schema"], "archsig-saga-conclusions/v0.5.4");
    assert_eq!(
        grounded["detectorCount"].as_u64(),
        grounded["detectorFindings"]
            .as_array()
            .map(|findings| findings.len() as u64)
    );
    assert_eq!(grounded["lawDependent"]["premise"]["status"], "holds");
    assert_eq!(
        grounded["lawDependent"]["conclusions"]
            .as_object()
            .unwrap()
            .len(),
        3
    );
    assert_eq!(
        grounded["lawIndependent"]["conclusions"]
            .as_object()
            .unwrap()
            .len(),
        7
    );
    assert_eq!(
        grounded["generatedQuotient"]["interpretation"]["class"],
        "zero"
    );
    assert_eq!(
        grounded["generatedQuotient"]["ambient"]["basis"],
        json!(["atom:inventory", "atom:order", "atom:shared"])
    );
    assert_eq!(
        grounded["generatedQuotient"]["obstructionIdeal"]["generators"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );
    assert_eq!(
        grounded["generatedQuotient"]["interpretation"]["map"]
            .as_array()
            .map(Vec::len),
        Some(3)
    );
    let mut malformed_packet = packet.clone();
    invariant_by_id_mut(&mut malformed_packet, "saga-generated-end-to-end-packet")["generatedQuotient"]
        ["interpretation"]["map"] = json!("forged");
    assert!(
        validate_measurement_packet_value_v1(&malformed_packet)
            .iter()
            .any(|check| check.result == "fail")
    );
    let mut mismatched_detector_count = packet.clone();
    invariant_by_id_mut(
        &mut mismatched_detector_count,
        "saga-generated-end-to-end-packet",
    )["detectorCount"] = json!(99);
    assert!(
        validate_measurement_packet_value_v1(&mismatched_detector_count)
            .iter()
            .any(|check| {
                check.result == "fail"
                    && check.examples.iter().any(|example| {
                        example
                            .source
                            .as_deref()
                            .is_some_and(|source| source.contains("detectorCount"))
                    })
            })
    );
    assert_eq!(
        grounded["lawIndependent"]["note"],
        "以下は law の充足を仮定せずに従う(定理8.2)。law 充足の証拠として読まない。"
    );
    let grounded_row = packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-grounded")
        .expect("saga-grounded structural verdict");
    assert_eq!(grounded_row["verdict"], "measured_zero");
    assert_eq!(
        grounded_row["reason"],
        "DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS"
    );

    let mut bad_archmap = read_json(&root.join("archmap_v2.json"));
    bad_archmap["contexts"][0]["atoms"]
        .as_array_mut()
        .unwrap()
        .push(json!("atom:grounded-defect"));
    bad_archmap["atoms"].as_array_mut().unwrap().push(json!({
        "id": "atom:grounded-defect",
        "kind": "semantic",
        "subject": "ctx:order",
        "object": "section=bad",
        "axis": "cech",
        "predicate": "sectionValue",
        "refs": ["src:order"]
    }));
    let bad_archmap_path = out_dir.join("archmap_grounded_defect.json");
    let bad_out_dir = temp_dir("ag-measurement-saga-grounded-defect");
    fs::write(
        &bad_archmap_path,
        serde_json::to_vec_pretty(&bad_archmap).unwrap(),
    )
    .unwrap();
    run_sig0(&[
        "analyze",
        "--archmap",
        bad_archmap_path.to_str().unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--measurement-profile",
        root.join("measurement_profile_ag.json").to_str().unwrap(),
        "--repair-plan",
        plan_path.to_str().unwrap(),
        "--out-dir",
        bad_out_dir.to_str().unwrap(),
    ]);
    let bad_packet = read_json(&bad_out_dir.join("archsig-measurement-packet.json"));
    let bad_grounded = invariant_by_id(&bad_packet, "saga-generated-end-to-end-packet");
    assert_eq!(bad_grounded["lawDependent"]["premise"]["status"], "fails");
    assert_eq!(
        bad_grounded["detectorFindings"].as_array().map(Vec::len),
        Some(1)
    );
    let bad_grounded_row = bad_packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-grounded")
        .expect("bad saga-grounded structural verdict");
    assert_eq!(bad_grounded_row["verdict"], "measured_nonzero");
    assert_eq!(bad_grounded_row["reason"], "MEASURED_LAW_DEFECT_AT_CHART");
    assert_eq!(
        bad_grounded["generatedQuotient"]["interpretation"]["class"],
        "nonzero"
    );

    let incomplete_out_dir = temp_dir("ag-measurement-saga-grounded-layer-d-missing");
    let incomplete_plan_path = incomplete_out_dir.join("repair_plan_incomplete.json");
    let mut incomplete_plan = read_json(&root.join("repair_plan_complete_support.json"));
    incomplete_plan["grounding"] = plan["grounding"].clone();
    fs::write(
        &incomplete_plan_path,
        serde_json::to_vec_pretty(&incomplete_plan).unwrap(),
    )
    .unwrap();
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json").to_str().unwrap(),
        "--law-policy",
        policy_path.to_str().unwrap(),
        "--law-surface",
        surface_path.to_str().unwrap(),
        "--measurement-profile",
        root.join("measurement_profile_ag.json").to_str().unwrap(),
        "--repair-plan",
        incomplete_plan_path.to_str().unwrap(),
        "--out-dir",
        incomplete_out_dir.to_str().unwrap(),
    ]);
    let incomplete_packet = read_json(&incomplete_out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        incomplete_packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["evaluator"] == "ag.saga-grounded")
            .unwrap()["verdict"],
        "not_computed"
    );
}


#[test]
fn cli_rejects_archmap_v2_context_restriction_cycle() {
    let out_dir = temp_dir("ag-measurement-context-cycle");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["contexts"][2]["restrictsTo"] =
        Value::Array(vec![Value::String("ctx:order".to_string())]);
    let archmap_path = out_dir.join("archmap_v2_cycle.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");
    let report = out_dir.join("archmap-validation.json");

    run_sig0_expect_code(
        &[
            "archmap",
            "--input",
            archmap_path.to_str().expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ],
        1,
    );

    let json = read_json(&report);
    assert!(
        json["checks"].as_array().unwrap().iter().any(|check| {
            check["id"] == "archmap-schema052-context-poset-refs" && check["result"] == "fail"
        }),
        "context restriction cycle must fail finite-poset validation"
    );
}

#[test]
fn archmap_v2_normalize_is_byte_deterministic() {
    let out_dir_a = temp_dir("ag-normalize-a");
    let out_dir_b = temp_dir("ag-normalize-b");
    let root = ag_measurement_root();

    for out_dir in [&out_dir_a, &out_dir_b] {
        run_sig0(&[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ]);
    }

    let first = fs::read(out_dir_a.join("normalized-archmap.json")).expect("first output exists");
    let second = fs::read(out_dir_b.join("normalized-archmap.json")).expect("second output exists");
    assert_eq!(
        first, second,
        "same ArchMap v2 input must normalize to byte-identical output"
    );
}

#[test]
fn archmap_v2_cross_doctrine_comparison_degenerates_to_comparable() {
    let root = ag_measurement_root();
    let left_value = read_json(&root.join("archmap_v2.json"));
    let right_value = left_value.clone();
    let left: ArchMapDocumentV2 = serde_json::from_value(left_value).expect("left archmap parses");
    let right: ArchMapDocumentV2 =
        serde_json::from_value(right_value).expect("right archmap parses");

    let result = compare_archmap_v2_doctrine(&left, &right);
    assert_eq!(result["status"], "comparable");
    assert_eq!(result["reason"], "fixed_tool_doctrine");
}

#[test]
fn archmap_v2_cross_doctrine_comparison_rejects_noncanonical_input() {
    let root = ag_measurement_root();
    let left_value = read_json(&root.join("archmap_v2.json"));
    let mut right_value = left_value.clone();
    right_value["extractionDoctrineRef"] = json!({
        "doctrineId": "doctrine:custom@1",
        "fingerprint": "sha256:other-doctrine",
        "components": ["custom"]
    });
    let left: ArchMapDocumentV2 = serde_json::from_value(left_value).expect("left archmap parses");
    let right: ArchMapDocumentV2 =
        serde_json::from_value(right_value).expect("right archmap parses");

    let result = compare_archmap_v2_doctrine(&left, &right);
    assert_eq!(result["status"], "not_comparable");
    assert_eq!(result["reason"], "invalid_fixed_doctrine");
    assert_eq!(result["leftCanonical"], true);
    assert_eq!(result["rightCanonical"], false);
}

#[test]
fn practical_rust_service_example_runs_current_analyze() {
    let out_dir = temp_dir("practical-rust-service-current-analyze");
    let root = practical_rust_service_root();

    // Mirror the demo script's base act: same LawPolicy, base law surface.
    let mut policy = read_json(&root.join("law_policy/law_policy.json"));
    policy["lawSurfaceRef"] = json!("law-surface:practical-rust-base-v052");
    let policy_path = out_dir.join("law_policy_base.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&policy).expect("base policy serializes"),
    )
    .expect("base policy writes");

    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap/archmap.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_policy/law_surface_base.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    assert!(
        output.status.success(),
        "current practical sample analyze must pass\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let archmap_validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(archmap_validation["summary"]["atomCount"], 70);
    assert_eq!(archmap_validation["summary"]["contextCount"], 7);
    assert_eq!(archmap_validation["summary"]["coverCount"], 1);
    assert_eq!(archmap_validation["summary"]["result"], "pass");

    let normalized = read_json(&out_dir.join("normalized-archmap.json"));
    assert_eq!(normalized["schema"], "normalized-archmap/v0.5.4");
    assert_eq!(normalized["summary"]["normalizedAtomCount"], 70);
    assert_eq!(normalized["summary"]["contextCount"], 7);
    assert_eq!(normalized["summary"]["coverCount"], 1);

    let measurement_packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        measurement_packet["schema"],
        "archsig-measurement-packet/v0.5.4"
    );
    assert_eq!(
        measurement_packet["packetId"],
        "measurement:practical-rust-commerce-fulfillment/v0.5.4"
    );
    let verdict_rows = measurement_packet["structuralVerdict"]
        .as_array()
        .expect("structural verdict rows");
    assert_eq!(
        verdict_rows.len(),
        3,
        "base act carries the cech row plus the two silent SAGA rows"
    );
    assert!(
        verdict_rows.iter().any(|row| {
            row["evaluator"] == "ag.cech-obstruction" && row["verdict"] == "measured_zero"
        }),
        "practical sample must expose the selected AG structural verdict"
    );
    assert!(
        verdict_rows.iter().all(|row| {
            row["evaluator"] == "ag.cech-obstruction"
                || (row["verdict"] == "not_computed"
                    && row["verdictData"]["methodStatus"] == "repair_plan_not_supplied")
        }),
        "without a RepairPlan the SAGA rows must stay typed silence"
    );
    assert!(
        measurement_packet["computedInvariants"]
            .as_array()
            .is_some_and(|rows| rows.iter().any(|row| row["atomCount"] == 70
                && row["contextCount"] == 7
                && row["coverCount"] == 1)),
        "measurement packet must preserve the finite-poset-site shape counts"
    );

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert_eq!(summary["schema"], "archsig-analysis-summary/v0.5.4");
    assert_eq!(
        summary["conclusion"],
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    );
    assert_eq!(summary["structuralVerdictSummary"]["rowCount"], 3);
    assert_eq!(summary["structuralVerdictSummary"]["nonTerminalCount"], 2);

    assert_eq!(manifest["schema"], "archsig-run-manifest/v0.5.4");
    assert_eq!(manifest["mode"], "measurement");
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:") && run_id.len() == 16)
    );
    assert!(manifest["inputDigests"]["profileFingerprint"]["sha256"].is_string());
    assert!(
        manifest["generatedArtifacts"]
            .as_array()
            .is_some_and(|artifacts| [
                "archsig-measurement-packet.json",
                "archsig-analysis-summary.json",
                "archsig-insight-report.json",
                "archsig-atom-viewer-data.json",
            ]
            .into_iter()
            .all(|name| artifacts.iter().any(|artifact| artifact == name))),
        "manifest must list the current practical demo artifacts"
    );
}

#[test]
fn cli_analyze_current_run_removes_stale_retired_artifacts() {
    let out_dir = temp_dir("current-analyze-removes-stale-retired-artifacts");
    let root = ag_measurement_root();
    let retired_artifacts = [
        ["typed", "evaluator", "results.json"].join("-"),
        ["architecture", "distance.json"].join("-"),
        ["archsig", "analysis", "packet.json"].join("-"),
        ["archsig", "analysis", "detail", "index.json"].join("-"),
        ["llm", "interpretation", "packet.json"].join("-"),
    ];
    for artifact in &retired_artifacts {
        fs::write(out_dir.join(artifact), "{}").expect("stale artifact fixture writes");
    }

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);

    for artifact in &retired_artifacts {
        assert!(
            !out_dir.join(artifact).exists(),
            "current analyze must remove stale retired artifact {artifact}"
        );
    }
    assert!(out_dir.join("archsig-measurement-packet.json").exists());
    assert!(out_dir.join("archsig-run-manifest.json").exists());

    let malformed_profile = out_dir.join("malformed-profile.json");
    fs::write(&malformed_profile, "{\n").expect("malformed profile writes");
    let output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        malformed_profile.to_str().expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(out_dir.join("archsig-measurement-packet.json").exists());
    assert!(out_dir.join("archsig-run-manifest.json").exists());
}

#[test]
fn cli_analyze_practical_service_outputs_are_byte_deterministic_with_known_digests() {
    let first_out = temp_dir("practical-rust-service-determinism-a");
    let second_out = temp_dir("practical-rust-service-determinism-b");
    let root = practical_rust_service_root();
    let args = |out_dir: &Path| {
        vec![
            "analyze".to_string(),
            "--archmap".to_string(),
            root.join("archmap/archmap_head.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-policy".to_string(),
            root.join("law_policy/law_policy.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            root.join("law_policy/measurement_profile.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            root.join("law_policy/measurement_profile_drift.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-surface".to_string(),
            root.join("law_policy/law_surface.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--repair-plan".to_string(),
            root.join("saga/repair_plan_head.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--out-dir".to_string(),
            out_dir.to_str().expect("path is utf-8").to_string(),
        ]
    };
    let first_args = args(&first_out);
    let second_args = args(&second_out);
    let first_arg_refs = first_args.iter().map(String::as_str).collect::<Vec<_>>();
    let second_arg_refs = second_args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&first_arg_refs);
    run_sig0(&second_arg_refs);

    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
    ] {
        assert_eq!(
            fs::read(first_out.join(artifact)).expect("first artifact is readable"),
            fs::read(second_out.join(artifact)).expect("second artifact is readable"),
            "{artifact} must be byte-identical across repeated analyze runs"
        );
    }

    let manifest = read_json(&first_out.join("archsig-run-manifest.json"));
    assert_eq!(manifest["toolVersion"], "0.5.4");
    assert_eq!(manifest["runId"], "run:492434adf066");
    assert_eq!(
        manifest["inputDigests"]["archmap"]["sha256"],
        "653037e1812bad367d211b926b976065d69842ec6d26cb5d4f82bdb9ac5f46e3"
    );
    assert_eq!(
        manifest["inputDigests"]["lawPolicy"]["sha256"],
        "840659c0ea8b483d77acb970bbce259ee30c5bd996aa9e6dd8e74e103292dbe9"
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfile"]["sha256"],
        "c20e6fa2f3f7bd33b8685bafef5d89f62fa4f419c6f67cabf179e80176a32539"
    );
    assert_eq!(
        manifest["inputDigests"]["measurementProfiles"]
            .as_array()
            .map(Vec::len),
        Some(2)
    );
    assert_eq!(
        manifest["inputDigests"]["profileFingerprint"]["sha256"],
        "724f89f73c2bf9e2aa72effeb6df4eece0332a3d1a0b5f625349fd298d83adb3"
    );
    assert_eq!(
        manifest["inputDigests"]["siteCoverDigest"]["sha256"],
        "e3ae81e46a9aa93d0d990d4aaa9b02d86c150ff51aa24c8c5914f63e7e9bd35b"
    );
    assert_eq!(
        manifest["inputDigests"]["siteCoverDigest"]["basis"],
        "normalized contexts + covers + derived finite cover nerve"
    );
    assert_eq!(
        manifest["inputDigests"]["repairPlan"]["sha256"],
        "705954f81878a1d164734aebd24ba7fa10fa2f7b605e835f6ec2a1726865435e"
    );
}

#[test]
fn cli_analyze_outputs_do_not_embed_local_absolute_input_paths() {
    let input_dir = temp_dir("practical-rust-service-absolute-inputs");
    let first_out = temp_dir("practical-rust-service-absolute-output-a");
    let second_out = temp_dir("practical-rust-service-absolute-output-b");
    let root = practical_rust_service_root();
    let archmap_path = input_dir.join("archmap.json");
    let law_policy_path = input_dir.join("law_policy.json");
    let measurement_profile_path = input_dir.join("measurement_profile.json");
    fs::copy(root.join("archmap/archmap_head.json"), &archmap_path)
        .expect("archmap fixture copies to absolute temp path");
    fs::copy(root.join("law_policy/law_policy.json"), &law_policy_path)
        .expect("law policy fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/measurement_profile.json"),
        &measurement_profile_path,
    )
    .expect("measurement profile fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/measurement_profile_drift.json"),
        input_dir.join("measurement_profile_drift.json"),
    )
    .expect("drift profile fixture copies to absolute temp path");
    fs::copy(
        root.join("law_policy/law_surface.json"),
        input_dir.join("law_surface.json"),
    )
    .expect("law surface fixture copies to absolute temp path");
    fs::copy(
        root.join("saga/repair_plan_head.json"),
        input_dir.join("repair_plan.json"),
    )
    .expect("repair plan fixture copies to absolute temp path");

    let args = |out_dir: &Path| {
        vec![
            "analyze".to_string(),
            "--archmap".to_string(),
            archmap_path.to_str().expect("path is utf-8").to_string(),
            "--law-policy".to_string(),
            law_policy_path.to_str().expect("path is utf-8").to_string(),
            "--measurement-profile".to_string(),
            measurement_profile_path
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--measurement-profile".to_string(),
            input_dir
                .join("measurement_profile_drift.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--law-surface".to_string(),
            input_dir
                .join("law_surface.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--repair-plan".to_string(),
            input_dir
                .join("repair_plan.json")
                .to_str()
                .expect("path is utf-8")
                .to_string(),
            "--out-dir".to_string(),
            out_dir.to_str().expect("path is utf-8").to_string(),
        ]
    };
    let first_args = args(&first_out);
    let second_args = args(&second_out);
    let first_arg_refs = first_args.iter().map(String::as_str).collect::<Vec<_>>();
    let second_arg_refs = second_args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&first_arg_refs);
    run_sig0(&second_arg_refs);

    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
    ] {
        let first = fs::read(first_out.join(artifact)).expect("first artifact is readable");
        let second = fs::read(second_out.join(artifact)).expect("second artifact is readable");
        assert_eq!(
            first, second,
            "{artifact} must be byte-identical across repeated absolute-path analyze runs"
        );
        let text = String::from_utf8_lossy(&first);
        let forbidden_markers = [
            format!("{}/", ["", "Users"].join("/")),
            format!("{}/", ["", "private"].join("/")),
            [".", "codex"].join(""),
            ["Hello", "Lean"].join(""),
            ["Algebraic", "Architecture", "TheoryV2"].join(""),
        ];
        for forbidden in forbidden_markers {
            assert!(
                !text.contains(&forbidden),
                "{artifact} must not expose local workspace marker {forbidden}"
            );
        }
    }

    let manifest = read_json(&first_out.join("archsig-run-manifest.json"));
    let _: ArchSigRunManifestV1 =
        serde_json::from_value(manifest.clone()).expect("v2 manifest matches schema struct");
    assert_eq!(manifest["archmapInputPath"], "input:archmap.json");
    assert_eq!(manifest["lawPolicyInputPath"], "input:law_policy.json");
    assert_eq!(
        manifest["inputDigests"]["archmap"]["path"],
        "input:archmap.json"
    );
    assert_eq!(
        manifest["inputDigests"]["lawPolicy"]["path"],
        "input:law_policy.json"
    );
    assert_eq!(
        manifest["validationResultSummary"]["analysis"]["result"],
        "pass"
    );
}

#[test]
fn cli_analyze_stamp_appends_opt_in_run_id_suffix() {
    let out_dir = temp_dir("practical-rust-service-stamp");
    let root = practical_rust_service_root();
    let args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join("archmap/archmap_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join("law_policy/law_surface.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--repair-plan".to_string(),
        root.join("saga/repair_plan_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--out-dir".to_string(),
        out_dir.to_str().expect("path is utf-8").to_string(),
        "--stamp".to_string(),
    ];
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);

    let manifest = read_json(&out_dir.join("archsig-run-manifest.json"));
    assert!(
        manifest["runId"]
            .as_str()
            .is_some_and(|run_id| run_id.starts_with("run:492434adf066-stamp:")),
        "stamp opt-in should append a wall-clock suffix to the deterministic input-derived prefix"
    );
}

#[test]
fn cli_help_exposes_only_llm_atom_archmap_surface() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("Part IV"),
        "current v1 CLI help must describe architecture distance without Part IV public wording\n{stdout}"
    );

    for command in ["archmap", "law-policy", "analyze", "schema-catalog"] {
        assert!(
            stdout.contains(command),
            "ArchSig help must expose retained command {command}\n{stdout}"
        );
    }

    for removed in [
        "archmap-generate",
        "interpretation-profile",
        "archsig-analysis",
        "aat-analysis",
        "analysis-summary",
        "summary",
        "codebase-inspection",
        "llm-native-workflow",
        "north-star-workflow",
    ] {
        assert!(
            !stdout.contains(removed),
            "ArchSig help must not expose removed v0 runtime surface {removed}\n{stdout}"
        );
    }

    for removed in removed_commands() {
        assert!(
            !help_command_names(&stdout).contains(removed),
            "ArchSig help still exposes removed command {removed}\n{stdout}"
        );
    }
}

#[test]
fn cli_rejects_implicit_scan_default() {
    let output = run_sig0_output(&[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ArchMap/LawPolicy/measurement-packet primary")
            && stderr.contains("archsig analyze"),
        "implicit scan should be rejected with the analyze boundary\n{stderr}"
    );
}

#[test]
fn removed_legacy_commands_are_not_accepted() {
    for command in removed_commands().iter().copied().chain(["pr-review"]) {
        let output = run_sig0_output(&[command, "--help"]);
        assert!(
            !output.status.success(),
            "removed command {command} should not be accepted"
        );
    }
}

#[test]
fn removed_legacy_analyze_flags_are_not_accepted() {
    let root = ag_measurement_root();
    for flag in [
        ["--strict", "distance"].join("-"),
        ["--emit", "raw", "artifacts"].join("-"),
    ] {
        let out_dir = temp_dir(&format!("removed-analyze-flag-{flag}"));
        let output = run_sig0_output(&[
            "analyze",
            "--archmap",
            root.join("archmap_v2.json")
                .to_str()
                .expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
            flag.as_str(),
        ]);
        assert!(
            !output.status.success(),
            "removed analyze flag {flag} should not be accepted"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("unexpected argument") || stderr.contains("unrecognized option"),
            "removed analyze flag {flag} should fail as an unknown flag\n{stderr}"
        );
    }
}

#[test]
fn cli_rejects_legacy_archmap_fields() {
    let out_dir = temp_dir("legacy-archmap-fields");
    let mut archmap = read_json(&ag_measurement_root().join("archmap_v2.json"));
    archmap[["map", "Items"].concat()] = serde_json::json!([]);
    archmap[["homo", "morphism"].concat()] =
        serde_json::json!({"reading": "old compatibility input"});
    archmap[["obstruction", "CircuitCandidates"].concat()] = serde_json::json!([]);
    let input = out_dir.join("legacy-archmap.json");
    fs::write(
        &input,
        serde_json::to_vec_pretty(&archmap).expect("json serializes"),
    )
    .expect("legacy fixture can be written");
    let output = run_sig0_output(&[
        "archmap",
        "--input",
        input.to_str().expect("legacy input path is utf-8"),
        "--out",
        out_dir
            .join("validation.json")
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "legacy ArchMap fields must be rejected instead of accepted as compatibility input"
    );
}

#[test]
fn cli_schema_catalog_is_primary_archsig_surface_only() {
    let out_dir = temp_dir("schema-catalog");
    let catalog = out_dir.join("schema-version-catalog.json");
    run_sig0(&[
        "schema-catalog",
        "--out",
        catalog.to_str().expect("catalog path is utf-8"),
    ]);
    let json = read_json(&catalog);
    let artifacts = json["artifacts"].as_array().expect("artifacts are array");
    let ids = artifacts
        .iter()
        .map(|entry| entry["artifactId"].as_str().expect("artifact id"))
        .collect::<Vec<_>>();
    let unique_ids = ids.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_ids.len(),
        ids.len(),
        "schema catalog artifact IDs must be unique"
    );
    let schema_names = artifacts
        .iter()
        .map(|entry| entry["schemaName"].as_str().expect("schema name"))
        .collect::<Vec<_>>();
    let unique_schema_names = schema_names.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_schema_names.len(),
        schema_names.len(),
        "schema catalog schema names must be unique"
    );
    assert_eq!(
        ids,
        vec![
            "archmap-current",
            "aat-atom-vocabulary/v0.5.4",
            "archmap-scope-manifest/v0.5.4",
            "archmap-candidate-packet/v0.5.4",
            "archmap-extraction-consistency/v0.5.4",
            "archmap-coverage-ledger/v0.5.4",
            "aat-atom-vocabulary-binding/v0.5.4",
            "law-equation-surface/v0.5.4",
            "law-policy/v0.5.4",
            "archsig-policy-bundle/v0.5.4",
            "measurement-profile/v0.5.4",
            "archsig-repair-plan/v0.5.4",
            "h1-comparison-data/v0.5.4",
            "law-evaluator-registry/v0.5.4",
            "normalized-archmap-current",
            "archsig-measurement-packet/v0.5.4",
            "archsig-saga-conclusions/v0.5.4",
            "archsig-boundary-statement/v0.5.4",
            "refactor-morphism/v0.5.4",
            "refinement-comparison/v0.5.4",
            "archsig-gate-policy/v0.5.4",
            "archsig-gate-report/v0.5.4",
            "archmap-diff/v0.5.4",
            "archsig-comparison-report/v0.5.4",
            "archsig-run-manifest/v0.5.4",
            "archsig-atom-viewer-data/v0.5.4",
            "archsig-measurement-view-model/v0.5.4",
        ]
    );
    for entry in artifacts {
        let artifact_id = entry["artifactId"].as_str().expect("artifact id");
        let expected_role = match artifact_id {
            "archmap-scope-manifest/v0.5.4"
            | "archmap-candidate-packet/v0.5.4"
            | "archmap-extraction-consistency/v0.5.4"
            | "archmap-coverage-ledger/v0.5.4"
            | "aat-atom-vocabulary-binding/v0.5.4" => "authoring",
            _ => "primary",
        };
        assert_eq!(entry["artifactRole"].as_str(), Some(expected_role));
    }
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "aat-atom-vocabulary/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("artifact-side projection")
                            && description.contains("allowed ArchMap atom kind tokens")
                            && description.contains("fixed AAT canonical doctrine")
                    })
                && entry["compatibilityBoundary"]["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| {
                        items.iter().any(|item| {
                            item.as_str()
                                .is_some_and(|text| text.contains("semantic correctness"))
                        })
                    })
        }),
        "schema catalog must describe the AAT atom vocabulary artifact boundary"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-boundary-statement/v0.5.4"
                && entry["schemaName"] == "archsig-boundary-statement/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description.contains("typed scoped qualifier contract")
                            && description.contains("nonConclusions as a compatibility view")
                    })
                && entry["compatibilityBoundary"]["nonConclusions"]
                    .as_array()
                    .is_some_and(|items| {
                        items.iter().any(|item| {
                            item.as_str()
                                .is_some_and(|text| text.contains("measured_zero"))
                        })
                    })
        }),
        "schema catalog must describe the BoundaryStatement v1 artifact boundary"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-measurement-packet/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_SAGA_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                            && [
                                "incidenceBridgeKind",
                                "h1ComparisonDataKind",
                                "normalizedComplexFingerprint",
                                "classPrerequisite",
                                "targetClassComputed",
                                "contractChecked",
                                "strings",
                                "booleans",
                            ]
                            .iter()
                            .all(|field| description.contains(field))
                    })
        }),
        "schema catalog must register SAGA conclusionCode values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-gate-policy/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        description
                            .contains("violated_assumption_dependency must map exactly to block")
                            && description.contains("cannot map to plain pass")
                    })
        }),
        "schema catalog must register the exact gate action for violated assumption dependency"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-gate-report/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_GATE_REPORT_DECISIONS
                            .iter()
                            .all(|decision| description.contains(decision))
                    })
        }),
        "schema catalog must register gate decision values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-comparison-report/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_COMPARISON_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                    })
        }),
        "schema catalog must register comparison conclusionCode values"
    );
    assert!(
        artifacts.iter().any(|entry| {
            entry["artifactId"] == "archsig-run-manifest/v0.5.4"
                && entry["compatibilityBoundary"]["fieldMappingPolicy"]
                    .as_str()
                    .is_some_and(|description| {
                        ARCHSIG_ANALYSIS_CONCLUSION_CODES
                            .iter()
                            .all(|code| description.contains(code))
                    })
        }),
        "schema catalog must register analyze conclusionCode values"
    );
}

#[test]
fn cli_policy_bundle_fingerprints_and_analyze_handoff_are_fail_closed() {
    let out_dir = temp_dir("policy-bundle");
    let root = ag_measurement_root();
    let law_policy = out_dir.join("law_policy_ag.json");
    let law_surface = out_dir.join("law_surface_ag_v052.json");
    let measurement_profile = out_dir.join("measurement_profile_ag.json");
    fs::copy(root.join("law_policy_ag.json"), &law_policy).expect("policy copies");
    fs::copy(root.join("law_surface_ag_v052.json"), &law_surface).expect("surface copies");
    fs::copy(
        root.join("measurement_profile_ag.json"),
        &measurement_profile,
    )
    .expect("profile copies");
    let bundle = out_dir.join("policy_bundle.json");
    run_sig0(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle path is utf-8"),
    ]);
    let bundle_json = read_json(&bundle);
    assert_eq!(bundle_json["schema"], "archsig-policy-bundle/v0.5.4");
    assert!(
        bundle_json["componentFingerprints"]["lawPolicy"]
            .as_str()
            .is_some_and(|value| value.starts_with("sha256:"))
    );

    let validation = out_dir.join("policy-bundle-validation.json");
    run_sig0(&[
        "policy-bundle",
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    assert_eq!(read_json(&validation)["summary"]["result"], "pass");
    let overwrite_validation = run_sig0_raw_output(&[
        "policy-bundle",
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle output path is utf-8"),
    ]);
    assert_eq!(overwrite_validation.status.code(), Some(2));

    let analyze_dir = out_dir.join("analyze");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out-dir",
        analyze_dir.to_str().expect("analyze path is utf-8"),
    ]);
    assert_eq!(
        read_json(&analyze_dir.join("archsig-measurement-packet.json"))["componentFingerprints"],
        bundle_json["componentFingerprints"]
    );
    assert_eq!(
        read_json(&analyze_dir.join("archsig-run-manifest.json"))["componentFingerprints"],
        bundle_json["componentFingerprints"]
    );

    let mut mismatched = bundle_json.clone();
    mismatched["componentFingerprints"]["lawPolicy"] = json!("sha256:wrong");
    let mismatched_path = out_dir.join("policy_bundle_mismatched.json");
    fs::write(
        &mismatched_path,
        serde_json::to_vec_pretty(&mismatched).expect("mismatched bundle serializes"),
    )
    .expect("mismatched bundle writes");
    let mismatched_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--policy-bundle",
        mismatched_path.to_str().expect("mismatched path is utf-8"),
        "--out",
        out_dir
            .join("mismatched-validation.json")
            .to_str()
            .expect("mismatched validation path is utf-8"),
    ]);
    assert_eq!(mismatched_output.status.code(), Some(1));

    let analyze_mismatched_dir = out_dir.join("analyze-mismatched-bundle");
    let analyze_mismatched_output = run_sig0_raw_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        mismatched_path
            .to_str()
            .expect("mismatched bundle path is utf-8"),
        "--out-dir",
        analyze_mismatched_dir
            .to_str()
            .expect("mismatched analyze path is utf-8"),
    ]);
    assert_eq!(analyze_mismatched_output.status.code(), Some(2));
    assert!(
        !analyze_mismatched_dir
            .join("archsig-measurement-packet.json")
            .exists(),
        "analyze must not emit a measurement packet for a mismatched policy bundle"
    );

    let mut unknown_policy = read_json(&law_policy);
    unknown_policy["unexpected"] = json!(true);
    let unknown_policy_path = out_dir.join("law_policy_unknown.json");
    fs::write(
        &unknown_policy_path,
        serde_json::to_vec_pretty(&unknown_policy).expect("unknown policy serializes"),
    )
    .expect("unknown policy writes");
    let unknown_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        unknown_policy_path
            .to_str()
            .expect("unknown policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        out_dir
            .join("unknown-policy-bundle.json")
            .to_str()
            .expect("unknown bundle path is utf-8"),
    ]);
    assert_eq!(unknown_output.status.code(), Some(2));

    let overwrite_output = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        law_policy.to_str().expect("policy output path is utf-8"),
    ]);
    assert_eq!(overwrite_output.status.code(), Some(2));

    let stdout_creation = run_sig0_raw_output(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
    ]);
    assert_eq!(stdout_creation.status.code(), Some(2));
}

#[test]
fn cli_tor_policy_bundle_preserves_explicit_law_pair() {
    let out_dir = temp_dir("policy-bundle-tor");
    let root = ag_measurement_root();
    let law_policy = out_dir.join("law_policy_tor.json");
    let law_surface = out_dir.join("law_surface_ag_v052.json");
    let measurement_profile = out_dir.join("measurement_profile_tor.json");
    fs::copy(root.join("law_policy_tor.json"), &law_policy).expect("policy copies");
    fs::copy(root.join("law_surface_ag_v052.json"), &law_surface).expect("surface copies");
    fs::copy(
        root.join("measurement_profile_tor.json"),
        &measurement_profile,
    )
    .expect("profile copies");
    let bundle = out_dir.join("policy_bundle_tor.json");

    run_sig0(&[
        "policy-bundle",
        "--law-policy",
        law_policy.to_str().expect("policy path is utf-8"),
        "--law-surface",
        law_surface.to_str().expect("surface path is utf-8"),
        "--measurement-profile",
        measurement_profile.to_str().expect("profile path is utf-8"),
        "--out",
        bundle.to_str().expect("bundle path is utf-8"),
    ]);

    let analyze_dir = out_dir.join("analyze");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_law_conflict_tor.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--policy-bundle",
        bundle.to_str().expect("bundle path is utf-8"),
        "--out-dir",
        analyze_dir.to_str().expect("analyze path is utf-8"),
    ]);

    let validation = read_json(&analyze_dir.join("law-policy-validation.json"));
    assert_eq!(validation["summary"]["result"], "pass");
    assert_eq!(
        validation["expandedPolicies"][0]["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
    assert!(
        !validation["expandedPolicies"][0]
            .as_object()
            .expect("expanded policy is an object")
            .contains_key("law")
    );

    let packet = read_json(&analyze_dir.join("archsig-measurement-packet.json"));
    assert_eq!(
        invariant_by_id(&packet, "law-conflict-tor:profile:ag-law-conflict-tor@1")["commonAmbient"]
            ["lawPair"],
        json!(["law:checkout", "law:inventory"])
    );
}

#[test]
fn cli_analyze_v2_cech_execution_plan_follows_declared_edge_binding() {
    let root = ag_measurement_root();
    let root_out = temp_dir("ag-measurement-cech-execution-plan");
    let surface_path = root.join("law_surface_cech_section_v052.json");
    let (mut law_policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    law_policy["lawSurfaceRef"] = json!("law-surface:cech-section-v052");
    law_policy["policies"][0]["law"] = json!("surface:cech-surface-v052");
    let policy_path = root_out.join("law_policy_cech_execution_plan.json");
    write_test_policy_and_profile(&policy_path, law_policy, profile);

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        root_out.join("top-left").to_str().expect("path is utf-8"),
    ]);

    let top_left_packet = read_json(
        &root_out
            .join("top-left")
            .join("archsig-measurement-packet.json"),
    );
    assert_eq!(
        top_left_packet["structuralVerdict"][0]["law"],
        "surface:cech-surface-v052"
    );
    let top_left_manifest = read_json(&root_out.join("top-left/archsig-run-manifest.json"));
    assert_eq!(
        top_left_manifest["validationReports"]["lawSurface"],
        "law-surface-validation.json"
    );
    assert_eq!(
        top_left_manifest["validationResultSummary"]["lawSurface"]["result"],
        "pass"
    );
    let top_left_invariant =
        invariant_by_id(&top_left_packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(top_left_invariant["restrictionEdgeCount"], json!(1));
    assert_eq!(top_left_invariant["rankD0"], json!(1));
    assert_eq!(top_left_invariant["dimensions"], json!({"H0": 3, "H1": 0}));
    assert_eq!(
        top_left_invariant["coverNerveProjection"]["edges"][0]["edgeId"],
        json!("ctx:top->ctx:left")
    );

    let mut changed_surface = read_json(&surface_path);
    changed_surface["laws"][0]["witnessVariables"][0]["binding"]["edge"] =
        json!(["ctx:top", "ctx:right"]);
    let changed_surface_path = root_out.join("law_surface_cech_execution_plan_changed.json");
    fs::write(
        &changed_surface_path,
        serde_json::to_string_pretty(&changed_surface).expect("surface serializes"),
    )
    .expect("changed surface is written");

    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        changed_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        root_out.join("top-right").to_str().expect("path is utf-8"),
    ]);
    let top_right_packet = read_json(
        &root_out
            .join("top-right")
            .join("archsig-measurement-packet.json"),
    );
    let top_right_invariant =
        invariant_by_id(&top_right_packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(top_right_invariant["restrictionEdgeCount"], json!(1));
    assert_eq!(top_right_invariant["rankD0"], json!(1));
    assert_eq!(top_right_invariant["dimensions"], json!({"H0": 3, "H1": 0}));
    assert_eq!(
        top_right_invariant["coverNerveProjection"]["edges"][0]["edgeId"],
        json!("ctx:top->ctx:right")
    );

    let section_out = root_out.join("section");
    let section_archmap_path = section_out.join("archmap.json");
    fs::create_dir_all(&section_out).expect("section output directory exists");
    fs::write(
        &section_archmap_path,
        serde_json::to_string_pretty(&section_archmap("lawful"))
            .expect("section archmap serializes"),
    )
    .expect("section archmap is written");
    let section_policy_path = section_out.join("law_policy.json");
    let mut section_policy_value = section_policy();
    section_policy_value["lawSurfaceRef"] = json!("law-surface:cech-section-v052");
    write_test_policy_and_profile(
        &section_policy_path,
        section_policy_value,
        section_profile(),
    );
    run_sig0(&[
        "analyze",
        "--archmap",
        section_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        section_policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            section_policy_path.to_str().expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        section_out.to_str().expect("path is utf-8"),
    ]);
    let section_packet = read_json(&section_out.join("archsig-measurement-packet.json"));
    assert_eq!(
        section_row(&section_packet)["verdict"],
        json!("measured_zero")
    );
    let section_invariant = invariant_by_id(
        &section_packet,
        "section-factorization:profile:ag-section@1",
    );
    assert_eq!(section_invariant["witnessVariables"], json!(["x", "y"]));
    assert!(
        section_invariant["minimalForbiddenSupports"][0]["supportRef"]
            .as_str()
            .is_some_and(|reference| reference.starts_with("law-surface:"))
    );

    let mut invalid_surface = changed_surface.clone();
    invalid_surface["laws"][0]["witnessVariables"][0]["binding"]["edge"] =
        json!(["ctx:top", "ctx:missing"]);
    let invalid_surface_path = root_out.join("law_surface_cech_execution_plan_invalid.json");
    fs::write(
        &invalid_surface_path,
        serde_json::to_string_pretty(&invalid_surface).expect("surface serializes"),
    )
    .expect("invalid surface is written");
    let invalid_out_dir = root_out.join("invalid");
    let invalid_output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        invalid_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        invalid_out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(invalid_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&invalid_output.stderr)
            .contains("is not in the selected restriction 1-skeleton")
    );
    assert!(
        !invalid_out_dir
            .join("archsig-measurement-packet.json")
            .exists()
    );
    assert!(!invalid_out_dir.join("normalized-archmap.json").exists());

    let mut known_disconnected_surface = changed_surface;
    known_disconnected_surface["laws"][0]["witnessVariables"][0]["binding"]["edge"] =
        json!(["ctx:top", "ctx:bottom"]);
    let known_disconnected_surface_path =
        root_out.join("law_surface_cech_execution_plan_known_disconnected.json");
    fs::write(
        &known_disconnected_surface_path,
        serde_json::to_string_pretty(&known_disconnected_surface)
            .expect("known disconnected surface serializes"),
    )
    .expect("known disconnected surface is written");
    let known_disconnected_out_dir = root_out.join("known-disconnected");
    let known_disconnected_output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        known_disconnected_surface_path
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        known_disconnected_out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(known_disconnected_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&known_disconnected_output.stderr)
            .contains("is not in the selected restriction 1-skeleton")
    );
    assert!(
        !known_disconnected_out_dir
            .join("archsig-measurement-packet.json")
            .exists()
    );
    let known_disconnected_analysis =
        read_json(&known_disconnected_out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(known_disconnected_analysis["summary"]["result"], "fail");
    assert_eq!(
        read_json(&known_disconnected_out_dir.join("archsig-run-manifest.json"))["mode"],
        "analysis-failure"
    );

    let mismatch_out_dir = root_out.join("mismatched-law");
    let mut mismatched_policy = read_json(&policy_path);
    mismatched_policy["policies"][0]["law"] = json!("law:undeclared");
    let mismatched_policy_path = root_out.join("law_policy_cech_mismatched.json");
    fs::write(
        &mismatched_policy_path,
        serde_json::to_string_pretty(&mismatched_policy).expect("policy serializes"),
    )
    .expect("mismatched policy is written");
    let mismatch_output = run_sig0_output(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2_cech_h1_visible.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        mismatched_policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        mismatch_out_dir.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(mismatch_output.status.code(), Some(2));
    let mismatch_validation = read_json(&mismatch_out_dir.join("law-policy-validation.json"));
    assert!(json_contains_substring(
        &mismatch_validation,
        "policies[].law must resolve exactly to a lawId declared by the supplied law surface"
    ));
}

#[test]
fn cli_analyze_v2_cech_empty_selected_scope_rejects_unresolved_edge() {
    let out_dir = temp_dir("ag-measurement-cech-empty-selected-scope");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    for context in archmap["contexts"]
        .as_array_mut()
        .expect("contexts are an array")
    {
        context["restrictsTo"] = json!([]);
    }
    let archmap_path = out_dir.join("archmap_v2_empty_cech_skeleton.json");
    fs::write(
        &archmap_path,
        serde_json::to_string_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("write archmap fixture");
    let (law_policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    profile["witnessFamily"] = json!([
        {"law": "ag.cech-obstruction", "variable": "e_order_shared"}
    ]);
    let law_policy_path = out_dir.join("law_policy_ag_with_independent_square_free.json");
    write_test_policy_and_profile(&law_policy_path, law_policy, profile);

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            law_policy_path.to_str().expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                law_policy_path.to_str().expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--law-surface",
            root.join("law_surface_ag_v052.json")
                .to_str()
                .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert!(!out_dir.join("archsig-measurement-packet.json").exists());
    assert!(!out_dir.join("normalized-archmap.json").exists());
    assert_eq!(
        read_json(&out_dir.join("archsig-run-manifest.json"))["mode"],
        "analysis-failure"
    );
    if !out_dir.join("archsig-measurement-packet.json").exists() {
        return;
    }

    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let cech_row = &packet["structuralVerdict"][0];
    assert_eq!(cech_row["evaluator"], "ag.cech-obstruction");
    assert_eq!(cech_row["verdict"], "not_computed");
    assert_eq!(cech_row["verdictData"]["zero"], false);
    assert_eq!(cech_row["verdictData"]["nonZero"], false);
    assert_eq!(
        cech_row["verdictData"]["methodStatus"],
        "empty_selected_scope"
    );
    assert!(
        cech_row["dependsOnAssumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|assumption_id| assumption_id
                .as_str()
                .is_some_and(|id| id.starts_with("assumption:part8-B-8-2-empty-selected-scope:"))),
        "Cech verdict must depend on its empty-scope precondition"
    );
    assert_eq!(cech_row["verdictData"].get("certRef"), None);
    let reason = cech_row["reason"].as_str().expect("reason is present");
    assert!(reason.contains("empty_selected_scope"));
    assert!(!reason.contains("should"));
    assert!(!reason.contains("author"));
    assert!(!reason.contains("intent"));
    assert!(
        packet["assumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| {
                entry["theoremRef"] == "part8/B.8.2-empty-selected-scope"
                    && entry["status"] == "violated"
                    && entry["assumption"] == "U-adequate cover selects a non-empty Cech 1-skeleton"
            }),
        "empty selected Cech skeleton must be recorded as a violated evaluator precondition"
    );
    let square_free_row = packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["evaluator"] == "ag.square-free-repair")
        .expect("independent square-free row exists");
    assert_eq!(
        square_free_row["verdict"], "measured_nonzero",
        "independent measured_zero row must not be downgraded by unrelated violated Cech precondition"
    );
    assert_eq!(square_free_row["verdictData"]["zero"], false);
    assert!(
        !square_free_row["dependsOnAssumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|theorem_ref| theorem_ref == "part8/B.8.2-empty-selected-scope"),
        "independent square-free row must not depend on the Cech empty-scope precondition"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| statement["kind"] == "blocked_method"
                && statement["reason"] == "empty_selected_scope"
                && statement["scopeRefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|scope_ref| scope_ref
                        .as_str()
                        .is_some_and(|value| value.starts_with("structuralVerdict/")))),
        "empty selected Cech scope must be represented as a blocked_method boundary scoped to the not_computed verdict"
    );
    assert!(
        packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| statement["kind"] == "violated_assumption"
                && statement["scopeRefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|scope_ref| scope_ref.as_str().is_some_and(|value| {
                        value.starts_with("assumption:part8-B-8-2-empty-selected-scope:")
                    }))
                && statement["scopeRefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|scope_ref| scope_ref
                        .as_str()
                        .is_some_and(|value| value.starts_with("structuralVerdict/")))),
        "violated assumption boundary must scope to the affected not_computed verdict"
    );
    assert!(
        !packet["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|statement| statement["kind"] == "violated_assumption")
            .flat_map(|statement| statement["scopeRefs"].as_array().unwrap())
            .filter_map(|scope_ref| scope_ref.as_str())
            .any(|scope_ref| scope_ref.contains("square-free-repair")),
        "violated Cech precondition boundary must not scope to independent square-free measured_zero"
    );

    let cech = invariant_by_id(&packet, "cech-cohomology:profile:ag-default@1");
    assert_eq!(cech["status"], "not_computed");
    assert_eq!(cech["methodStatus"], "empty_selected_scope");
    assert_eq!(cech["restrictionEdgeCount"], Value::from(0));
    assert_eq!(cech["selectedH2"]["dimension"], Value::Null);
    assert_eq!(cech["selectedH2"]["status"], "not_computed");
    assert_eq!(
        cech["selectedH2"]["reason"],
        "empty_selected_scope: selected cover has no non-empty Cech 1-skeleton for ag.cech-obstruction"
    );
    let capacity = invariant_by_id(&packet, "topological-debt-capacity:profile:ag-default@1");
    assert_eq!(capacity["status"], "not_computed");
    assert_eq!(capacity["methodStatus"], "empty_selected_scope");
    assert_eq!(capacity["capacityLowerBound"], Value::Null);
    assert_eq!(capacity["eulerCharacteristic"], Value::Null);
    assert_eq!(capacity["b1NerveReading"]["oneSkeletonB1"], Value::Null);
    assert_eq!(capacity["b1NerveReading"]["nerveComplexB1"], Value::Null);

    let validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(validation["summary"]["result"], "pass");

    let summary = read_json(&out_dir.join("archsig-analysis-summary.json"));
    assert_eq!(summary["conclusion"], "REPAIR_TARGETS_IDENTIFIED");
    assert_eq!(
        summary["structuralVerdictSummary"]["nonTerminalCount"],
        Value::from(1)
    );
    assert_eq!(
        summary["assumptionSummary"]["violatedCount"],
        Value::from(1)
    );

    let insight = read_json(&out_dir.join("archsig-insight-report.json"));
    assert_eq!(
        insight["boundaryDigest"]["blockingCount"],
        Value::from(2),
        "violated precondition plus not_computed Cech row are blockers"
    );
    assert!(
        insight["boundaryDigest"]["blocking"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["reasonCode"] == "empty_selected_scope"),
        "report boundary digest must expose empty scope as a blocker"
    );
}

#[test]
fn cli_gate_rejects_supplied_vacuous_measured_zero_packet() {
    let out_dir = temp_dir("archsig-gate-vacuous-measured-zero");
    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "measured_zero");
    let mut packet = read_json(&packet_path);
    packet["structuralVerdict"][0]["target"]["scopeSize"] =
        json!({"contexts": 0, "edges": 0, "triangles": 0});
    packet["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] = json!([]);
    fs::write(
        &packet_path,
        serde_json::to_vec_pretty(&packet).expect("packet serializes"),
    )
    .expect("packet writes");
    let report_path = out_dir.join("gate-report.json");

    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            ag_measurement_root()
                .join("gate_policy_conservative.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let report = read_json(&report_path);
    assert_eq!(report["decision"], "NOT_EVALUABLE");
    assert!(
        report["packetValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| {
                check["id"] == "measurement-packet-schema052-structural-verdict-new-shape"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_gate_rejects_silence_scope_on_measured_nonzero() {
    let out_dir = temp_dir("archsig-gate-silence-on-measured-nonzero");
    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "measured_nonzero");
    let mut packet = read_json(&packet_path);
    let structural_ref = packet["structuralVerdict"][0]["verdictRef"]
        .as_str()
        .expect("structural verdict ref")
        .to_string();
    packet["boundaryStatements"][0]["scopeRefs"] = json!([structural_ref]);
    fs::write(
        &packet_path,
        serde_json::to_vec_pretty(&packet).expect("packet serializes"),
    )
    .expect("packet writes");
    let report_path = out_dir.join("gate-report.json");

    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            ag_measurement_root()
                .join("gate_policy_conservative.json")
                .to_str()
                .expect("policy path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let report = read_json(&report_path);
    assert_eq!(report["decision"], "NOT_EVALUABLE");
    assert!(
        report["packetValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| {
                check["id"] == "measurement-packet-schema052-boundary-statements"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_gate_rejects_plain_pass_for_non_terminal_and_missing_mapping() {
    let out_dir = temp_dir("archsig-gate-invalid-policy");
    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "unmeasured");
    let policy_path = out_dir.join("bad-policy.json");
    fs::write(
        &policy_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-gate-policy/v0.5.4",
            "policyId": "gate-policy:bad@1",
            "rules": [{
                "ruleId": "absolute-bad",
                "scope": "absolute",
                "verdictMapping": {
                    "measured_zero": "pass",
                    "measured_nonzero": "block",
                    "unmeasured": "pass",
                    "unknown": "pass_with_boundary",
                    "not_computed": "pass_with_boundary"
                }
            }]
        }))
        .expect("policy serializes"),
    )
    .expect("policy fixture can be written");
    let report_path = out_dir.join("gate-report.json");

    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let report = read_json(&report_path);
    assert_eq!(report["decision"], "NOT_EVALUABLE");
    assert!(
        report["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-verdictMapping-unmeasured-no-plain-pass"
                && check["result"] == "fail")
    );
    assert!(
        report["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-verdictMapping-violated_assumption_dependency-must-block"
                && check["result"] == "fail")
    );
    assert!(
        report["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-verdictMapping-violated_assumption_dependency-present"
                && check["result"] == "fail")
    );

    let introduced_policy_path = out_dir.join("bad-introduced-policy.json");
    fs::write(
        &introduced_policy_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-gate-policy/v0.5.4",
            "policyId": "gate-policy:bad-introduced@1",
            "rules": [{
                "ruleId": "introduced-bad",
                "scope": "introduced-by-change",
                "introducedByChangeMapping": {
                    "new": "block",
                    "cleared": "pass",
                    "preexisting": "pass_with_boundary",
                    "removed": "pass",
                    "other": "pass_with_boundary"
                }
            }]
        }))
        .expect("policy serializes"),
    )
    .expect("policy fixture can be written");
    let introduced_report_path = out_dir.join("introduced-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            introduced_policy_path.to_str().expect("path is utf-8"),
            "--out",
            introduced_report_path.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let introduced_report = read_json(&introduced_report_path);
    assert!(
        introduced_report["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-introducedByChangeMapping-removed-no-plain-pass"
                && check["result"] == "fail")
    );
}

#[test]
fn cli_gate_rejects_unknown_packet_verdict_and_policy_mapping_keys() {
    let out_dir = temp_dir("archsig-gate-unknown-vocabulary");
    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "alien_verdict");
    let policy_path = ag_measurement_root().join("gate_policy_conservative.json");
    let report_path = out_dir.join("unknown-verdict-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            report_path.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let report = read_json(&report_path);
    assert_eq!(report["decision"], "NOT_EVALUABLE");
    assert!(
        report["packetValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(
                |check| check["id"] == "gate-packet-structural-verdict-0-verdict-vocabulary"
                    && check["result"] == "fail"
            )
    );

    let valid_packet_path = out_dir.join("valid-packet.json");
    write_gate_packet(&valid_packet_path, "measured_zero");
    let bad_policy_path = out_dir.join("bad-policy-key.json");
    let mut bad_policy = read_json(&policy_path);
    bad_policy["rules"][0]["verdictMapping"]["alien_verdict"] = json!("block");
    fs::write(
        &bad_policy_path,
        serde_json::to_vec_pretty(&bad_policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");
    let bad_policy_report = out_dir.join("bad-policy-key-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            valid_packet_path.to_str().expect("path is utf-8"),
            "--policy",
            bad_policy_path.to_str().expect("path is utf-8"),
            "--out",
            bad_policy_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let bad_policy_json = read_json(&bad_policy_report);
    assert!(
        bad_policy_json["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-verdictMapping-alien_verdict-known-key"
                && check["result"] == "fail")
    );

    let bad_override_policy_path = out_dir.join("bad-boundary-override-key.json");
    let mut bad_override_policy = read_json(&policy_path);
    bad_override_policy["rules"][0]["boundaryKindOverrides"]["alien_boundary"] =
        json!("pass_with_boundary");
    fs::write(
        &bad_override_policy_path,
        serde_json::to_vec_pretty(&bad_override_policy).expect("policy serializes"),
    )
    .expect("policy fixture can be written");
    let bad_override_report = out_dir.join("bad-boundary-override-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            valid_packet_path.to_str().expect("path is utf-8"),
            "--policy",
            bad_override_policy_path.to_str().expect("path is utf-8"),
            "--out",
            bad_override_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let bad_override_json = read_json(&bad_override_report);
    assert!(
        bad_override_json["policyValidation"]
            .as_array()
            .unwrap()
            .iter()
            .any(|check| check["id"]
                == "gate-policy-rule-0-boundary-override-alien_boundary-known-key"
                && check["result"] == "fail")
    );
}

#[test]
fn cli_gate_not_evaluable_for_malformed_packet_or_unsupported_comparison() {
    let out_dir = temp_dir("archsig-gate-not-evaluable");
    let policy_path = ag_measurement_root().join("gate_policy_conservative.json");
    let malformed_packet = out_dir.join("malformed-packet.json");
    fs::write(
        &malformed_packet,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:malformed",
            "structuralVerdict": []
        }))
        .expect("packet serializes"),
    )
    .expect("packet fixture can be written");
    let malformed_report = out_dir.join("malformed-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            malformed_packet.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            malformed_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert_eq!(read_json(&malformed_report)["decision"], "NOT_EVALUABLE");

    let bad_minimal_packet = out_dir.join("bad-minimal-packet.json");
    fs::write(
        &bad_minimal_packet,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:bad-minimal",
            "profile": {},
            "structuralVerdict": [{
                "verdict": "measured_zero",
                "verdictData": {}
            }],
            "nonConclusions": []
        }))
        .expect("packet serializes"),
    )
    .expect("packet fixture can be written");
    let bad_minimal_report = out_dir.join("bad-minimal-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            bad_minimal_packet.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            bad_minimal_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert_eq!(read_json(&bad_minimal_report)["decision"], "NOT_EVALUABLE");

    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "measured_zero");

    let comparison_only_packet = out_dir.join("comparison-only-packet.json");
    let mut comparison_only = read_json(&packet_path);
    comparison_only["structuralVerdict"] = json!([]);
    comparison_only["computedInvariants"] = json!([{
        "invariantId": "saga-comparison:h1-transfer",
        "kind": "h1-comparison-transfer",
        "evaluator": "ag.saga-comparison",
        "status": "silence_by_design",
        "whatNext": "supply the missing comparison input",
        "value": {"status": "silence_by_design"},
        "representation": {"basis": "typed-silence"},
        "contract": {
            "incidenceBridgeKind": "unknown",
            "h1ComparisonDataKind": "unknown",
            "normalizedComplexFingerprint": "unknown",
            "classPrerequisite": false,
            "targetClassComputed": false,
            "contractChecked": false
        }
    }]);
    comparison_only["boundaryStatements"] = json!([{
        "id": "boundary:saga-comparison",
        "kind": "silence_by_design",
        "scopeRefs": ["saga-comparison:h1-transfer"],
        "reason": "comparison_data_not_supplied",
        "text": "supply the missing comparison input"
    }]);
    comparison_only["nonConclusions"] = json!(["supply the missing comparison input"]);
    fs::write(
        &comparison_only_packet,
        serde_json::to_vec_pretty(&comparison_only).expect("comparison-only packet serializes"),
    )
    .expect("comparison-only packet writes");
    let comparison_only_report = out_dir.join("comparison-only-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            comparison_only_packet.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            comparison_only_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert_eq!(
        read_json(&comparison_only_report)["decision"],
        "NOT_EVALUABLE"
    );

    let comparison_path = out_dir.join("comparison.json");
    fs::write(
        &comparison_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-pr-review-report/v0.5.4"
        }))
        .expect("comparison serializes"),
    )
    .expect("comparison fixture can be written");
    let comparison_report = out_dir.join("comparison-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            comparison_path.to_str().expect("path is utf-8"),
            "--out",
            comparison_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let comparison_gate = read_json(&comparison_report);
    assert_eq!(comparison_gate["decision"], "NOT_EVALUABLE");
    assert_eq!(
        comparison_gate["reason"],
        "comparison report schema validation failed"
    );

    let empty_comparison_path = out_dir.join("empty-comparison.json");
    fs::write(
        &empty_comparison_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-comparison-report/v0.5.4",
            "conclusionCode": "NO_NEW_MEASURED_OBSTRUCTION_RECORDED",
            "comparability": { "level": "identical" },
            "verdictTransitions": []
        }))
        .expect("comparison serializes"),
    )
    .expect("comparison fixture can be written");
    let empty_comparison_report = out_dir.join("empty-comparison-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            empty_comparison_path.to_str().expect("path is utf-8"),
            "--out",
            empty_comparison_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert_eq!(
        read_json(&empty_comparison_report)["decision"],
        "NOT_EVALUABLE"
    );

    let unknown_category_comparison_path = out_dir.join("unknown-category-comparison.json");
    fs::write(
        &unknown_category_comparison_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-comparison-report/v0.5.4",
            "conclusionCode": "NO_NEW_MEASURED_OBSTRUCTION_RECORDED",
            "comparability": { "level": "identical" },
            "verdictTransitions": [{
                "rowKey": "ag.cech-obstruction|ag.cech-obstruction|finite_f2_cech_computed",
                "baseRowRef": "structuralVerdict/ag.cech-obstruction/ag.cech-obstruction/finite_f2_cech_computed",
                "headRowRef": "structuralVerdict/ag.cech-obstruction/ag.cech-obstruction/finite_f2_cech_computed",
                "transition": "preexisting_recorded_row",
                "introducedByChangeCategory": "alien",
                "deltaRefs": []
            }]
        }))
        .expect("comparison serializes"),
    )
    .expect("comparison fixture can be written");
    let unknown_category_report = out_dir.join("unknown-category-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            unknown_category_comparison_path
                .to_str()
                .expect("path is utf-8"),
            "--out",
            unknown_category_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert_eq!(
        read_json(&unknown_category_report)["decision"],
        "NOT_EVALUABLE"
    );
}

#[test]
fn cli_gate_records_applied_mapping_and_exit_codes_without_fail_vocab() {
    let out_dir = temp_dir("archsig-gate-report");
    let policy_path = ag_measurement_root().join("gate_policy_conservative.json");
    let pass_packet = out_dir.join("pass-packet.json");
    write_gate_packet(&pass_packet, "measured_zero");
    let pass_report = out_dir.join("pass-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        pass_packet.to_str().expect("path is utf-8"),
        "--policy",
        policy_path.to_str().expect("path is utf-8"),
        "--out",
        pass_report.to_str().expect("path is utf-8"),
    ]);
    let pass_json = read_json(&pass_report);
    assert_eq!(pass_json["schema"], "archsig-gate-report/v0.5.4");
    assert_eq!(pass_json["decision"], "PASS_WITHIN_GATE_POLICY");
    assert_eq!(
        pass_json["ruleOutcomes"][0]["appliedMapping"][0]["verdict"],
        "measured_zero"
    );
    assert_eq!(
        pass_json["ruleOutcomes"][0]["appliedMapping"][0]["action"],
        "pass"
    );
    assert!(
        !json_contains_exact_string(&pass_json, "fail"),
        "gate output must not use fail as a mapping or output vocabulary"
    );
    assert_eq!(
        pass_json["ruleOutcomes"][1]["status"], "not_applicable",
        "introduced-by-change rules without --comparison must be skipped, not silently passed"
    );

    let block_packet = out_dir.join("block-packet.json");
    write_gate_packet(&block_packet, "measured_nonzero");
    let block_report = out_dir.join("block-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            block_packet.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            block_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&block_report)["decision"],
        "BLOCKED_BY_GATE_POLICY"
    );

    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            pass_packet.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            out_dir.to_str().expect("directory path is utf-8"),
        ],
        3,
    );
}

#[test]
fn cli_gate_report_is_byte_deterministic() {
    let out_dir = temp_dir("archsig-gate-determinism");
    let policy_path = ag_measurement_root().join("gate_policy_conservative.json");
    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "unknown");
    let first = out_dir.join("gate-report-a.json");
    let second = out_dir.join("gate-report-b.json");
    for report in [&first, &second] {
        run_sig0(&[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--out",
            report.to_str().expect("path is utf-8"),
        ]);
    }
    assert_eq!(
        fs::read(&first).expect("first report exists"),
        fs::read(&second).expect("second report exists")
    );
}

#[test]
fn cli_gate_rejects_duplicate_json_and_input_output_aliases() {
    let out_dir = temp_dir("archsig-gate-input-safety");
    let policy_path = ag_measurement_root().join("gate_policy_conservative.json");
    let duplicate_packet = out_dir.join("duplicate-packet.json");
    fs::write(
        &duplicate_packet,
        r#"{"schema":"archsig-measurement-packet/v0.5.4","schema":"duplicate"}"#,
    )
    .expect("duplicate packet writes");
    let duplicate_output = run_sig0_output(&[
        "gate",
        "--packet",
        duplicate_packet.to_str().expect("path is utf-8"),
        "--policy",
        policy_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(duplicate_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&duplicate_output.stderr).contains("duplicate JSON object key")
    );

    let packet_path = out_dir.join("packet.json");
    write_gate_packet(&packet_path, "measured_zero");
    let overwrite_output = run_sig0_output(&[
        "gate",
        "--packet",
        packet_path.to_str().expect("path is utf-8"),
        "--policy",
        policy_path.to_str().expect("path is utf-8"),
        "--out",
        packet_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(overwrite_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&overwrite_output.stderr).contains("output path must differ"));
}

#[test]
fn cli_compare_asserts_identical_and_verdict_row_transitions() {
    let out_dir = temp_dir("archsig-compare-positive-transitions");
    let root = ag_measurement_root();
    let source_run = out_dir.join("source-run");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        source_run.to_str().expect("path is utf-8"),
    ]);

    let clone_run = |name: &str| {
        let target = out_dir.join(name);
        fs::create_dir_all(&target).expect("comparison run directory can be created");
        for entry in fs::read_dir(&source_run).expect("source run can be read") {
            let entry = entry.expect("source run entry can be read");
            let file_type = entry
                .file_type()
                .expect("source run entry type can be read");
            if file_type.is_file() {
                fs::copy(entry.path(), target.join(entry.file_name()))
                    .expect("comparison artifact can be copied");
            }
        }
        target
    };

    let identical_base = clone_run("identical-base");
    let identical_head = clone_run("identical-head");
    let identical_out = out_dir.join("identical-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        identical_base.to_str().expect("path is utf-8"),
        "--head-run",
        identical_head.to_str().expect("path is utf-8"),
        "--out-dir",
        identical_out.to_str().expect("path is utf-8"),
    ]);
    let identical = read_json(&identical_out.join("archsig-comparison-report.json"));
    assert_eq!(identical["comparability"]["level"], "identical");
    assert_eq!(
        identical["conclusionCode"],
        ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED
    );
    assert!(
        identical["verdictTransitions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|transition| transition["transition"] == "preexisting_recorded_row")
    );

    let mut verdict_row_archmap = read_json(&root.join("archmap_v2.json"));
    verdict_row_archmap["atoms"][0]["object"] = json!("changed-object-for-verdict-row");
    let verdict_row_archmap_path = out_dir.join("verdict-row-archmap.json");
    fs::write(
        &verdict_row_archmap_path,
        serde_json::to_vec_pretty(&verdict_row_archmap).expect("verdict-row ArchMap serializes"),
    )
    .expect("verdict-row ArchMap writes");
    let verdict_row_head = out_dir.join("verdict-row-head");
    run_sig0(&[
        "analyze",
        "--archmap",
        verdict_row_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        verdict_row_head.to_str().expect("path is utf-8"),
    ]);
    let verdict_row_out = out_dir.join("verdict-row-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        source_run.to_str().expect("path is utf-8"),
        "--head-run",
        verdict_row_head.to_str().expect("path is utf-8"),
        "--out-dir",
        verdict_row_out.to_str().expect("path is utf-8"),
    ]);
    let verdict_row_report = read_json(&verdict_row_out.join("archsig-comparison-report.json"));
    assert_eq!(verdict_row_report["comparability"]["level"], "verdict-row");

    let source_packet = read_json(&source_run.join("archsig-measurement-packet.json"));
    let zero_index = source_packet["structuralVerdict"]
        .as_array()
        .unwrap()
        .iter()
        .position(|row| row["verdict"] == "measured_zero")
        .expect("AG fixture has a measured_zero row");
    let row_evaluator = source_packet["structuralVerdict"][zero_index]["evaluator"]
        .as_str()
        .expect("AG fixture row has evaluator");
    let invariant_id = source_packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|invariant| invariant["evaluator"] == row_evaluator)
        .and_then(|invariant| invariant["invariantId"].as_str())
        .expect("AG fixture has a computed invariant for the selected evaluator")
        .to_string();

    let set_row_identity = |run: &Path| {
        let packet_path = run.join("archsig-measurement-packet.json");
        let mut packet = read_json(&packet_path);
        packet["structuralVerdict"][zero_index]["target"]["classRef"] =
            json!(format!("computedInvariants/{invariant_id}"));
        packet["structuralVerdict"][zero_index]["evidence"]["computedInvariantRefs"] =
            json!([invariant_id]);
        fs::write(
            packet_path,
            serde_json::to_vec_pretty(&packet).expect("transition packet serializes"),
        )
        .expect("transition packet writes");
        refresh_run_measurement_packet_digest(run);
    };
    let set_measured_nonzero = |run: &Path| {
        let packet_path = run.join("archsig-measurement-packet.json");
        let mut packet = read_json(&packet_path);
        packet["structuralVerdict"][zero_index]["verdict"] = json!("measured_nonzero");
        packet["structuralVerdict"][zero_index]["verdictData"]["zero"] = json!(false);
        packet["structuralVerdict"][zero_index]["verdictData"]["nonZero"] = json!(true);
        packet["structuralVerdict"][zero_index]["target"]["classRef"] =
            json!(format!("computedInvariants/{invariant_id}"));
        packet["structuralVerdict"][zero_index]["evidence"]["computedInvariantRefs"] =
            json!([invariant_id]);
        fs::write(
            packet_path,
            serde_json::to_vec_pretty(&packet).expect("transition packet serializes"),
        )
        .expect("transition packet writes");
        refresh_run_measurement_packet_digest(run);
    };

    let new_base = clone_run("new-base");
    let new_head = clone_run("new-head");
    set_row_identity(&new_base);
    set_row_identity(&new_head);
    set_measured_nonzero(&new_head);
    let new_out = out_dir.join("new-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        new_base.to_str().expect("path is utf-8"),
        "--head-run",
        new_head.to_str().expect("path is utf-8"),
        "--out-dir",
        new_out.to_str().expect("path is utf-8"),
    ]);
    let new_report = read_json(&new_out.join("archsig-comparison-report.json"));
    assert_eq!(
        new_report["conclusionCode"],
        ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE
    );
    assert!(
        new_report["verdictTransitions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|transition| transition["transition"]
                == "measured_obstruction_recorded_after_change")
    );

    let cleared_base = clone_run("cleared-base");
    let cleared_head = clone_run("cleared-head");
    set_row_identity(&cleared_base);
    set_row_identity(&cleared_head);
    set_measured_nonzero(&cleared_base);
    let cleared_out = out_dir.join("cleared-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        cleared_base.to_str().expect("path is utf-8"),
        "--head-run",
        cleared_head.to_str().expect("path is utf-8"),
        "--out-dir",
        cleared_out.to_str().expect("path is utf-8"),
    ]);
    let cleared_report = read_json(&cleared_out.join("archsig-comparison-report.json"));
    assert_eq!(
        cleared_report["conclusionCode"],
        ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE
    );
    assert!(cleared_report["verdictTransitions"]
        .as_array()
        .unwrap()
        .iter()
        .any(|transition| transition["transition"] == "measured_obstruction_no_longer_recorded"));
}

#[test]
fn cli_compare_records_cover_change_without_transport_and_feeds_gate_other_transition() {
    let out_dir = temp_dir("archsig-compare-cover-change");
    let root = ag_measurement_root();
    let base_run = out_dir.join("base-run");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        base_run.to_str().expect("path is utf-8"),
    ]);

    let mut head_archmap = read_json(&root.join("archmap_v2.json"));
    head_archmap["contexts"]
        .as_array_mut()
        .expect("contexts are array")
        .push(json!({
            "id": "ctx:audit",
            "atoms": ["atom:order"],
            "restrictsTo": [],
            "refs": ["src:cover"]
        }));
    head_archmap["covers"][0]["contexts"] =
        json!(["ctx:order", "ctx:inventory", "ctx:shared", "ctx:audit"]);
    let head_archmap_path = out_dir.join("archmap_v2_cover_changed.json");
    fs::write(
        &head_archmap_path,
        serde_json::to_vec_pretty(&head_archmap).expect("archmap serializes"),
    )
    .expect("head archmap can be written");
    let head_run = out_dir.join("head-run");
    run_sig0(&[
        "analyze",
        "--archmap",
        head_archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        head_run.to_str().expect("path is utf-8"),
    ]);

    let compare_a = out_dir.join("compare-a");
    let compare_b = out_dir.join("compare-b");
    for compare_out in [&compare_a, &compare_b] {
        run_sig0(&[
            "compare",
            "--base-run",
            base_run.to_str().expect("path is utf-8"),
            "--head-run",
            head_run.to_str().expect("path is utf-8"),
            "--out-dir",
            compare_out.to_str().expect("path is utf-8"),
        ]);
    }
    assert_eq!(
        fs::read(compare_a.join("archsig-comparison-report.json")).expect("first report exists"),
        fs::read(compare_b.join("archsig-comparison-report.json")).expect("second report exists"),
        "comparison report must be byte deterministic"
    );
    assert_eq!(
        fs::read(compare_a.join("archmap-diff.json")).expect("first diff exists"),
        fs::read(compare_b.join("archmap-diff.json")).expect("second diff exists"),
        "archmap diff must be byte deterministic"
    );

    let comparison = read_json(&compare_a.join("archsig-comparison-report.json"));
    let allowed_record_codes = BTreeSet::from([
        ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED,
        ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
        ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
        ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA,
    ]);
    assert_eq!(comparison["schema"], "archsig-comparison-report/v0.5.4");
    assert_eq!(
        comparison["discipline"],
        "Comparison is a record-level juxtaposition of two ArchSig runs. It does not claim causal repair, semantic equivalence, or preserved obstruction identity; a class-zero reading is available only under a checked coarse-to-fine refinement contract."
    );
    assert!(
        comparison["inputDigests"]["headRun"]["measurementPacket"]["sha256"]
            .as_str()
            .is_some_and(|digest| !digest.is_empty()),
        "comparison report must lock the head measurement-packet digest for gate handoff"
    );
    assert!(
        allowed_record_codes.contains(
            comparison["conclusionCode"]
                .as_str()
                .expect("comparison conclusionCode is a string")
        ),
        "comparison conclusionCode must come from the registered record-level const vocabulary"
    );
    assert_eq!(
        comparison["conclusionCode"],
        ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA
    );
    assert_eq!(comparison["comparability"]["level"], "not-comparable");
    assert!(
        comparison["boundaryStatements"]
            .as_array()
            .unwrap()
            .iter()
            .any(|boundary| boundary["kind"] == "cover_changed_between_runs")
    );
    assert!(
        comparison["verdictTransitions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|transition| transition["transition"] == "other_transition"
                && transition["introducedByChangeCategory"] == "other")
    );
    assert!(
        !json_contains_substring(&comparison, "TRANSPORT")
            && !json_contains_substring(&comparison, "INTRODUCED_BY_CHANGE")
            && !json_contains_substring(&comparison, "CLEARED_BY_CHANGE")
            && !json_contains_substring(&comparison, "ZERO_PRESERVED"),
        "comparison report must not expose transport or causal conclusion names"
    );

    let diff = read_json(&compare_a.join("archmap-diff.json"));
    assert_eq!(diff["schema"], "archmap-diff/v0.5.4");
    assert!(
        diff["contexts"]["added"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["id"] == "ctx:audit")
    );
    assert!(
        diff["covers"]["modified"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["id"] == "cover:order-inventory")
    );

    let gate_policy_path = out_dir.join("introduced-policy.json");
    fs::write(
        &gate_policy_path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-gate-policy/v0.5.4",
            "policyId": "gate-policy:introduced@1",
            "rules": [{
                "ruleId": "introduced-change",
                "scope": "introduced-by-change",
                "introducedByChangeMapping": {
                    "new": "block",
                    "cleared": "pass",
                    "preexisting": "pass",
                    "removed": "pass_with_boundary",
                    "other": "pass_with_boundary"
                }
            }]
        }))
        .expect("policy serializes"),
    )
    .expect("policy can be written");
    let gate_report_path = out_dir.join("gate-report.json");
    run_sig0(&[
        "gate",
        "--packet",
        head_run
            .join("archsig-measurement-packet.json")
            .to_str()
            .expect("path is utf-8"),
        "--policy",
        gate_policy_path.to_str().expect("path is utf-8"),
        "--comparison",
        compare_a
            .join("archsig-comparison-report.json")
            .to_str()
            .expect("path is utf-8"),
        "--out",
        gate_report_path.to_str().expect("path is utf-8"),
    ]);
    let gate_report = read_json(&gate_report_path);
    assert_eq!(gate_report["decision"], "PASS_WITHIN_GATE_POLICY");
    assert!(
        gate_report["ruleOutcomes"][0]["appliedMapping"]
            .as_array()
            .unwrap()
            .iter()
            .any(|mapping| mapping["transition"] == "other_transition"
                && mapping["mappingKey"] == "other"
                && mapping["action"] == "pass_with_boundary")
    );

    let unrelated_packet = out_dir.join("unrelated-gate-packet.json");
    write_gate_packet(&unrelated_packet, "measured_zero");
    let digest_mismatch_report = out_dir.join("gate-digest-mismatch-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            unrelated_packet.to_str().expect("path is utf-8"),
            "--policy",
            gate_policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            compare_a
                .join("archsig-comparison-report.json")
                .to_str()
                .expect("path is utf-8"),
            "--out",
            digest_mismatch_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let mismatch = read_json(&digest_mismatch_report);
    assert_eq!(mismatch["decision"], "NOT_EVALUABLE");
    assert_eq!(
        mismatch["reason"],
        "comparison report headRun measurement packet digest does not match --packet"
    );
}

#[test]
fn cli_compare_refinement_binds_fingerprints_and_transports_only_zero() {
    let out_dir = temp_dir("archsig-compare-refinement-zero-transport");
    let root = ag_measurement_root();
    let zero_plan = zero_plan_for_refinement_test(&root);

    let base_archmap = read_json(&root.join("archmap_v2.json"));
    let base_run = run_saga_compare_fixture(
        "refinement-coarse-zero",
        base_archmap.clone(),
        zero_plan.clone(),
    );
    let fine_archmap = refinement_fine_archmap_for_test(&root);
    let fine_run = run_saga_compare_fixture(
        "refinement-fine-zero",
        fine_archmap.clone(),
        zero_plan.clone(),
    );

    let refinement_path = out_dir.join("refinement.json");
    let refinement_for = |coarse: &Path, fine: &Path| {
        let coarse_manifest = read_json(&coarse.join("archsig-run-manifest.json"));
        let fine_manifest = read_json(&fine.join("archsig-run-manifest.json"));
        json!({
            "schema": "refinement-comparison/v0.5.4",
            "id": "refinement-comparison:e2e",
            "direction": "coarse-to-fine",
            "coarse": {
                "siteRef": "archmap:/contexts",
                "coverRef": "cover:order-inventory",
                "complexFingerprint": coarse_manifest["inputDigests"]["siteCoverDigest"]["sha256"]
            },
            "fine": {
                "siteRef": "archmap:/contexts",
                "coverRef": "cover:order-inventory",
                "complexFingerprint": fine_manifest["inputDigests"]["siteCoverDigest"]["sha256"]
            },
            "zeroTransport": {
                "kind": "class-zero-preservation",
                "checked": true,
                "map": "coarse-to-fine-supplied"
            }
        })
    };
    fs::write(
        &refinement_path,
        serde_json::to_vec_pretty(&refinement_for(&base_run, &fine_run))
            .expect("refinement serializes"),
    )
    .expect("refinement writes");

    let positive_out = out_dir.join("positive-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base path is utf-8"),
        "--head-run",
        fine_run.to_str().expect("fine path is utf-8"),
        "--refinement",
        refinement_path.to_str().expect("refinement path is utf-8"),
        "--out-dir",
        positive_out.to_str().expect("output path is utf-8"),
    ]);
    let positive = read_json(&positive_out.join("archsig-comparison-report.json"));
    assert_eq!(positive["comparability"]["level"], "not-comparable");
    assert_eq!(positive["comparability"]["sameSiteCoverDigest"], false);
    assert_eq!(positive["classTransport"]["status"], "established");
    assert_eq!(
        positive["classTransport"]["conclusionCode"],
        ARCHSIG_CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT
    );
    assert_eq!(
        positive["classTransport"]["recordComparability"],
        "not-comparable"
    );
    assert_eq!(
        positive["classTransport"]["runBinding"]["coarse"]["complexFingerprint"],
        read_json(&base_run.join("archsig-run-manifest.json"))["inputDigests"]["siteCoverDigest"]["sha256"]
    );
    assert_eq!(
        positive["classTransport"]["runBinding"]["fine"]["complexFingerprint"],
        read_json(&fine_run.join("archsig-run-manifest.json"))["inputDigests"]["siteCoverDigest"]["sha256"]
    );
    assert_eq!(positive["classTransport"]["boundaryStatement"], Value::Null);

    let mut nonzero_plan = zero_plan_for_refinement_test(&root);
    nonzero_plan["complex"]["overlaps"]
        .as_array_mut()
        .expect("nonzero overlaps are array")
        .push(json!({
            "id": "overlap:order-inventory-alt",
            "left": "ctx:order",
            "right": "ctx:inventory"
        }));
    nonzero_plan["primitives"]
        .as_array_mut()
        .expect("nonzero primitives are array")
        .push(json!({
            "id": "primitive:order-inventory-alt",
            "overlapRef": "overlap:order-inventory-alt",
            "resL": ["repair:cycle"],
            "resR": [],
            "support": {"kind": "supplied", "variables": ["repair:cycle"]}
        }));
    for primitive in nonzero_plan["primitives"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .take(3)
    {
        primitive["resL"] = json!([]);
        primitive["resR"] = json!([]);
        primitive["support"]["variables"] = json!([]);
    }
    nonzero_plan["faithfulness"] = json!({
        "mode": "supplied",
        "supplied": {
            "zeroPrimitiveRef": "primitive:inventory-shared",
            "residualSupportPredicate": {
                "kind": "finite-support",
                "supportVariables": ["repair:cycle"],
                "zeroOnZeroPrimitive": true
            },
            "faithfulnessLaw": "Q is faithful on the supplied residual support"
        }
    });
    nonzero_plan["gluingData"]["overlapRefs"]
        .as_array_mut()
        .expect("nonzero gluing overlap refs are array")
        .push(json!("overlap:order-inventory-alt"));
    nonzero_plan["gluingData"]["sectionRefs"]
        .as_array_mut()
        .expect("nonzero gluing section refs are array")
        .push(json!({
            "overlapRef": "overlap:order-inventory-alt",
            "sectionRef": "section:order-inventory-alt"
        }));
    let nonzero_base = run_saga_compare_fixture(
        "refinement-coarse-nonzero",
        read_json(&root.join("archmap_v2.json")),
        nonzero_plan.clone(),
    );
    let nonzero_head = run_saga_compare_fixture(
        "refinement-fine-nonzero",
        read_json(&root.join("archmap_v2.json")),
        nonzero_plan.clone(),
    );
    let nonzero_refinement_path = out_dir.join("nonzero-refinement.json");
    fs::write(
        &nonzero_refinement_path,
        serde_json::to_vec_pretty(&refinement_for(&nonzero_base, &nonzero_head))
            .expect("nonzero refinement serializes"),
    )
    .expect("nonzero refinement writes");
    let nonzero_out = out_dir.join("nonzero-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        nonzero_base.to_str().expect("nonzero base path is utf-8"),
        "--head-run",
        nonzero_head.to_str().expect("nonzero head path is utf-8"),
        "--refinement",
        nonzero_refinement_path
            .to_str()
            .expect("nonzero refinement path is utf-8"),
        "--out-dir",
        nonzero_out.to_str().expect("nonzero output path is utf-8"),
    ]);
    let nonzero = read_json(&nonzero_out.join("archsig-comparison-report.json"));
    assert_eq!(nonzero["classTransport"]["sourceClassNonZero"], true);
    assert_eq!(nonzero["classTransport"]["targetClassNonZero"], true);
    assert_eq!(nonzero["classTransport"]["zeroPreserved"], false);
    assert_eq!(nonzero["classTransport"]["status"], "not_computed");
    assert_eq!(nonzero["classTransport"]["conclusionCode"], Value::Null);
    assert_eq!(
        nonzero["classTransport"]["boundaryStatement"]["kind"],
        "class_zero_transport_not_established"
    );

    let mixed_base = run_saga_compare_fixture(
        "refinement-coarse-nonzero-to-zero",
        base_archmap,
        nonzero_plan,
    );
    let mixed_head = run_saga_compare_fixture(
        "refinement-fine-nonzero-to-zero",
        fine_archmap,
        zero_plan_for_refinement_test(&root),
    );
    let mixed_refinement_path = out_dir.join("mixed-refinement.json");
    fs::write(
        &mixed_refinement_path,
        serde_json::to_vec_pretty(&refinement_for(&mixed_base, &mixed_head))
            .expect("mixed refinement serializes"),
    )
    .expect("mixed refinement writes");
    let mixed_out = out_dir.join("mixed-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        mixed_base.to_str().expect("mixed base path is utf-8"),
        "--head-run",
        mixed_head.to_str().expect("mixed head path is utf-8"),
        "--refinement",
        mixed_refinement_path
            .to_str()
            .expect("mixed refinement path is utf-8"),
        "--out-dir",
        mixed_out.to_str().expect("mixed output path is utf-8"),
    ]);
    let mixed = read_json(&mixed_out.join("archsig-comparison-report.json"));
    assert_eq!(mixed["classTransport"]["sourceClassNonZero"], true);
    assert_eq!(mixed["classTransport"]["targetClassNonZero"], false);
    assert_eq!(mixed["classTransport"]["zeroPreserved"], false);
    assert_eq!(mixed["classTransport"]["status"], "not_computed");
    assert_eq!(mixed["classTransport"]["conclusionCode"], Value::Null);
    assert_eq!(
        mixed["classTransport"]["boundaryStatement"]["kind"],
        "class_zero_transport_not_established"
    );

    let mut mismatched_refinement = refinement_for(&base_run, &fine_run);
    mismatched_refinement["fine"]["complexFingerprint"] = json!("sha256:mismatch");
    let mismatched_path = out_dir.join("mismatched-refinement.json");
    fs::write(
        &mismatched_path,
        serde_json::to_vec_pretty(&mismatched_refinement)
            .expect("mismatched refinement serializes"),
    )
    .expect("mismatched refinement writes");
    let mismatch_output = run_sig0_output(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base path is utf-8"),
        "--head-run",
        fine_run.to_str().expect("fine path is utf-8"),
        "--refinement",
        mismatched_path.to_str().expect("mismatched path is utf-8"),
        "--out-dir",
        out_dir
            .join("mismatched-compare")
            .to_str()
            .expect("mismatch output is utf-8"),
    ]);
    assert_eq!(mismatch_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&mismatch_output.stderr)
            .contains("COMPARISON_DATA_CONTRACT_VIOLATION")
    );

    let separate_out = out_dir.join("separate-compare");
    run_sig0(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base path is utf-8"),
        "--head-run",
        fine_run.to_str().expect("fine path is utf-8"),
        "--out-dir",
        separate_out.to_str().expect("separate output is utf-8"),
    ]);
    let separate = read_json(&separate_out.join("archsig-comparison-report.json"));
    assert_eq!(
        separate["profileConclusionCode"],
        "TWO_PROFILES_REPORTED_SEPARATELY"
    );
    assert_eq!(separate["classTransport"]["status"], "silence_by_design");

    let mut reverse = refinement_for(&base_run, &fine_run);
    reverse["direction"] = json!("fine-to-coarse");
    let reverse_path = out_dir.join("reverse-refinement.json");
    fs::write(
        &reverse_path,
        serde_json::to_vec_pretty(&reverse).expect("reverse refinement serializes"),
    )
    .expect("reverse refinement writes");
    let reverse_output = run_sig0_output(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("base path is utf-8"),
        "--head-run",
        fine_run.to_str().expect("fine path is utf-8"),
        "--refinement",
        reverse_path.to_str().expect("reverse path is utf-8"),
        "--out-dir",
        out_dir
            .join("reverse-compare")
            .to_str()
            .expect("reverse output is utf-8"),
    ]);
    assert_eq!(reverse_output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&reverse_output.stderr)
            .contains("direction must be coarse-to-fine")
    );
}

#[test]
fn cli_refinement_fixture_binds_to_generated_run_fingerprints() {
    let root = ag_measurement_root();
    let coarse = run_saga_compare_fixture(
        "refinement-static-fixture-coarse",
        read_json(&root.join("archmap_v2.json")),
        zero_plan_for_refinement_test(&root),
    );
    let fine = run_saga_compare_fixture(
        "refinement-static-fixture-fine",
        refinement_fine_archmap_for_test(&root),
        zero_plan_for_refinement_test(&root),
    );
    let fixture = read_json(&root.join("refinement_comparison.json"));
    let coarse_manifest = read_json(&coarse.join("archsig-run-manifest.json"));
    let fine_manifest = read_json(&fine.join("archsig-run-manifest.json"));
    assert_eq!(fixture["direction"], "coarse-to-fine");
    assert_eq!(
        fixture["coarse"]["complexFingerprint"],
        coarse_manifest["inputDigests"]["siteCoverDigest"]["sha256"]
    );
    assert_eq!(
        fixture["fine"]["complexFingerprint"],
        fine_manifest["inputDigests"]["siteCoverDigest"]["sha256"]
    );
}

#[test]
fn cli_compare_rejects_malformed_measurement_packet_runs() {
    let out_dir = temp_dir("archsig-compare-malformed-packet");
    let root = ag_measurement_root();
    let base_run = out_dir.join("base-run");
    run_sig0(&[
        "analyze",
        "--archmap",
        root.join("archmap_v2.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_ag.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
        ))
        .to_str()
        .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        base_run.to_str().expect("path is utf-8"),
    ]);
    let head_run = out_dir.join("head-run");
    fs::create_dir_all(&head_run).expect("head run can be created");
    for artifact in ["archsig-run-manifest.json", "normalized-archmap.json"] {
        fs::copy(base_run.join(artifact), head_run.join(artifact)).expect("copy run artifact");
    }
    fs::write(
        head_run.join("archsig-measurement-packet.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:malformed",
            "structuralVerdict": []
        }))
        .expect("packet serializes"),
    )
    .expect("malformed packet can be written");

    let output = run_sig0_output(&[
        "compare",
        "--base-run",
        base_run.to_str().expect("path is utf-8"),
        "--head-run",
        head_run.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.join("compare").to_str().expect("path is utf-8"),
    ]);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("head measurement packet"),
        "compare must identify the malformed packet side"
    );
    assert!(
        !out_dir
            .join("compare")
            .join("archsig-comparison-report.json")
            .exists(),
        "malformed compare input must not emit success-looking report"
    );
}

#[test]
fn cli_analyze_v2_validation_failure_uses_exit_code_2() {
    let out_dir = temp_dir("archsig-analyze-validation-exit-code");
    let root = ag_measurement_root();
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    archmap["atoms"][0]["kind"] = json!("externalForecast");
    let archmap_path = out_dir.join("archmap-vocabulary-error.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("archmap fixture can be written");

    run_sig0_expect_code(
        &[
            "analyze",
            "--archmap",
            archmap_path.to_str().expect("path is utf-8"),
            "--law-policy",
            root.join("law_policy_ag.json")
                .to_str()
                .expect("path is utf-8"),
            "--measurement-profile",
            test_measurement_profile_path(Path::new(
                root.join("law_policy_ag.json")
                    .to_str()
                    .expect("path is utf-8"),
            ))
            .to_str()
            .expect("path is utf-8"),
            "--out-dir",
            out_dir.to_str().expect("path is utf-8"),
        ],
        2,
    );
    assert!(!out_dir.join("archsig-measurement-packet.json").exists());
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("archsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temporary directory can be created");
    dir
}

fn write_gate_packet(path: &Path, verdict: &str) {
    fs::write(
        path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:gate-test",
            "profile": {
                "schema": "measurement-profile/v0.5.4",
                "profileId": "profile:gate-test@1",
                "siteRef": "site:gate-test",
                "coverRef": "cover:gate-test",
                "coefficient": "constant:Z",
                "effCoeff": "constant",
                "resolutionSelector": "gate-test",
                "domain": "gate-test",
                "zeroPredicate": "gate-test-zero",
                "nonZeroPredicate": "gate-test-nonzero",
                "certSelector": "gate-test-cert",
                "verdictDiscipline": "five-valued",
                "finiteBounds": {
                    "maxSquareFreeWitnessVariables": 12,
                    "maxCoherenceContexts": 12,
                    "maxTorWitnessVariables": 12,
                    "maxBoundaryResidueVariables": 16,
                    "maxLaplacianCells": 16,
                    "maxPeriodCycles": 16,
                    "maxTransferTargets": 16
                }
            },
            "structuralVerdict": [{
                "verdictRef": "structuralVerdict/ag-cech-obstruction/ag-cech-h1/computed",
                "evaluator": "ag.cech-obstruction",
                "law": "ag.cech-h1",
                "target": {
                    "kind": "cover-relative-cech-h1-class",
                    "coverRef": "cover:gate-test",
                    "coefficient": "constant:Z",
                    "scopeSize": {
                        "contexts": 1,
                        "edges": 1,
                        "triangles": 0
                    },
                    "classRef": "computedInvariants/gate-test:computed"
                },
                "verdict": verdict,
                "verdictData": {
                    "inScope": true,
                    "zero": verdict == "measured_zero",
                    "nonZero": verdict == "measured_nonzero",
                    "methodStatus": "computed",
                    "certRef": "computedInvariants/gate-test:computed"
                },
                "dependsOnAssumptions": [],
                "evidence": {
                    "computedInvariantRefs": ["gate-test:computed"],
                    "sourceRefs": []
                }
            }],
            "computedInvariants": [{
                "invariantId": "gate-test:computed",
                "kind": "cech-h1-rank",
                "evaluator": "ag.cech-obstruction",
                "value": 0,
                "representation": {
                    "coefficient": "constant:Z"
                }
            }],
            "analyticReadings": [],
            "assumptions": [],
            "suppliedData": [{
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law-policy.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement-profile.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation"
                }
            }],
            "boundaryStatements": [{
                "id": "boundary:gate-test",
                "kind": "silence_by_design",
                "scopeRefs": [
                    "measurement:gate-test"
                ],
                "reason": "gate_test_fixture",
                "text": "gate test packet is a minimal measurement packet fixture"
            }],
            "nonConclusions": [
                "gate test packet is a minimal measurement packet fixture"
            ]
        }))
        .expect("packet serializes"),
    )
    .expect("packet fixture can be written");
}

fn json_contains_exact_string(value: &Value, needle: &str) -> bool {
    match value {
        Value::String(text) => text == needle,
        Value::Array(items) => items
            .iter()
            .any(|item| json_contains_exact_string(item, needle)),
        Value::Object(object) => object
            .values()
            .any(|item| json_contains_exact_string(item, needle)),
        _ => false,
    }
}

fn has_absolute_sheaf_cohomology_notation(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    while index + 1 < bytes.len() {
        if bytes[index] == b'H' && bytes[index + 1] == b'^' {
            let mut degree_end = index + 2;
            if degree_end < bytes.len() && bytes[degree_end] == b'n' {
                degree_end += 1;
            } else if degree_end < bytes.len() && bytes[degree_end].is_ascii_digit() {
                while degree_end < bytes.len() && bytes[degree_end].is_ascii_digit() {
                    degree_end += 1;
                }
            } else {
                index += 1;
                continue;
            }
            if bytes.get(degree_end) == Some(&b'(') {
                return true;
            }
        }
        index += 1;
    }
    false
}

fn json_contains_substring(value: &Value, needle: &str) -> bool {
    match value {
        Value::String(text) => text.contains(needle),
        Value::Array(items) => items
            .iter()
            .any(|item| json_contains_substring(item, needle)),
        Value::Object(object) => object
            .values()
            .any(|item| json_contains_substring(item, needle)),
        _ => false,
    }
}

fn run_sig0(args: &[&str]) {
    let output = run_sig0_output(args);
    assert!(
        output.status.success(),
        "archsig {:?} failed\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_sig0_expect_code(args: &[&str], expected_code: i32) {
    let output = run_sig0_output(args);
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "archsig {:?} exit code mismatch\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_sig0_output(args: &[&str]) -> std::process::Output {
    run_sig0_raw_output(args)
}
fn run_sig0_raw_output(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn help_command_names(help: &str) -> BTreeSet<&str> {
    help.lines()
        .filter_map(|line| {
            let trimmed = line.trim_start();
            line.starts_with("  ")
                .then(|| trimmed.split_whitespace().next())
                .flatten()
        })
        .collect()
}

fn removed_commands() -> &'static [&'static str] {
    &[
        "adapter-scan",
        "validate",
        "relation-complexity",
        "snapshot",
        "signature-diff",
        "diff",
        "air",
        "air-from-archmap",
        "validate-air",
        "feature-report",
        "theorem-check",
        "repair-registry",
        "synthesis-constraints",
        "no-solution-certificate",
        "organization-policy",
        "architecture-policy",
        "law-violation-report",
        "law-policy-templates",
        "custom-rule-plugins",
        "measurement-units",
        "pr-quality-analysis",
        "aat-observable-bundle",
        "archmap-workflow",
        "reported-axes-catalog",
        "policy-decision",
        "report-artifacts",
        "pr-comment",
        "baseline-suppression",
        "schema-compatibility",
    ]
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}

fn refresh_run_measurement_packet_digest(run: &Path) {
    let packet_path = run.join("archsig-measurement-packet.json");
    let packet = read_json(&packet_path);
    let digest = format!(
        "{:x}",
        Sha256::digest(serde_json::to_vec(&packet).expect("measurement packet canonicalizes")),
    );
    let manifest_path = run.join("archsig-run-manifest.json");
    let mut manifest = read_json(&manifest_path);
    manifest["artifactDigests"]["measurementPacket"] = json!({
        "path": "archsig-measurement-packet.json",
        "sha256": digest,
    });
    fs::write(
        manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("manifest serializes"),
    )
    .expect("manifest writes");
}

fn sidecar_measurement_profile_path(policy_path: &Path) -> PathBuf {
    if policy_path.file_name().and_then(|name| name.to_str()) == Some("law_policy.json") {
        policy_path.with_file_name("measurement_profile.json")
    } else if let Some(file_name) = policy_path.file_name().and_then(|name| name.to_str()) {
        if let Some(suffix) = file_name.strip_prefix("law_policy_") {
            policy_path.with_file_name(format!("measurement_profile_{suffix}"))
        } else {
            policy_path.with_file_name("measurement_profile.json")
        }
    } else {
        policy_path.with_file_name("measurement_profile.json")
    }
}

fn read_fixture_policy_profile(policy_path: &Path) -> (Value, Value) {
    (
        read_json(policy_path),
        read_json(&sidecar_measurement_profile_path(policy_path)),
    )
}

fn test_measurement_profile_path(policy_path: &Path) -> PathBuf {
    let profile_path = sidecar_measurement_profile_path(policy_path);
    assert!(
        profile_path.exists(),
        "test must create measurement profile sidecar before invoking analyze"
    );
    profile_path
}

fn write_test_policy_and_profile(policy_path: &Path, mut policy: Value, profile: Value) {
    policy["schema"] = json!("law-policy/v0.5.4");
    if policy.get("lawSurfaceRef").is_none() {
        policy["lawSurfaceRef"] = json!("law-surface:ag-measurement-v052");
    }
    if policy.get("basisLedger").is_none() {
        policy["basisLedger"] = json!([{
            "basisId": "policy-basis:layering",
            "kind": "repo-document",
            "path": "docs/tool/ag_measurement_evidence_contract.md",
            "revision": "ag-measurement-current"
        }]);
    }
    let mut surface_laws = Vec::new();
    let witness_family = profile
        .get("witnessFamily")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    if let Some(entries) = policy["policies"].as_array_mut() {
        for (entry_index, entry) in entries.iter_mut().enumerate() {
            let evaluator = entry["evaluator"].as_str().unwrap_or_default().to_string();
            if evaluator == "ag.cech-obstruction" {
                continue;
            }
            let use_generated_law = !witness_family.is_empty()
                && evaluator != "ag.cech-obstruction"
                && evaluator != "ag.section-factorization";
            let law_id = if !use_generated_law {
                entry["law"].as_str().unwrap_or(&evaluator).to_string()
            } else {
                format!("law:generated:{entry_index}")
            };
            if use_generated_law {
                entry["law"] = json!(law_id);
            }
            let variables = witness_family
                .iter()
                .filter(|witness| witness["law"].as_str() == Some(evaluator.as_str()))
                .filter_map(|witness| witness["variable"].as_str().map(str::to_string))
                .collect::<Vec<_>>();
            if variables.is_empty() {
                let condition_type = match evaluator.as_str() {
                    "ag.saga-descent"
                    | "ag.cech-obstruction"
                    | "ag.coherence-obstruction"
                    | "ag.restriction-compatibility"
                    | "ag.boundary-residue" => "descent",
                    "ag.period-stokes" | "ag.period-stokes-audit" => "temporal",
                    _ => "constructible",
                };
                surface_laws.push(json!({
                    "lawId": law_id,
                    "conditionType": condition_type,
                    "evaluatorRef": evaluator
                }));
            } else {
                let axis = match evaluator.as_str() {
                    "ag.cech-obstruction" => "cech",
                    "ag.section-factorization" => "section-factorization",
                    "ag.sheaf-laplacian" => "laplacian",
                    "ag.period-stokes" | "ag.period-stokes-audit" => "period",
                    "ag.support-transfer" => "transfer",
                    _ => "square-free",
                };
                let predicate = match axis {
                    "laplacian" => "cellularCochain",
                    "period" => "periodIntegral",
                    "transfer" => "transferPairing",
                    "cech" => "sectionValue",
                    _ => "support",
                };
                surface_laws.push(json!({
                    "lawId": law_id,
                    "conditionType": "closed-equational",
                    "witnessVariables": variables.iter().map(|variable| json!({
                        "variable": variable,
                        "binding": {"axis": axis, "predicate": predicate}
                    })).collect::<Vec<_>>(),
                    "forbiddenSupportGenerators": [json!({"support": variables})]
                }));
            }
        }
    }
    if !surface_laws.is_empty() {
        let surface_path = policy_path.with_file_name("law_surface.json");
        fs::write(
            &surface_path,
            serde_json::to_vec_pretty(&json!({
                "schema": "law-equation-surface/v0.5.4",
                "id": "law-surface:ag-measurement-v052",
                "laws": surface_laws
            }))
            .expect("generated law surface serializes"),
        )
        .expect("generated law surface writes");
    }
    fs::write(
        policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("test law policy can be written");
    let mut profile = profile;
    profile["schema"] = json!("measurement-profile/v0.5.4");
    profile
        .as_object_mut()
        .map(|object| object.remove("witnessFamily"));
    if profile.get("finiteBounds").is_none() {
        profile["finiteBounds"] = json!({
            "maxSquareFreeWitnessVariables": 12,
            "maxCoherenceContexts": 12,
            "maxTorWitnessVariables": 12,
            "maxBoundaryResidueVariables": 16,
            "maxLaplacianCells": 16,
            "maxPeriodCycles": 16,
            "maxTransferTargets": 16
        });
    }
    fs::write(
        sidecar_measurement_profile_path(policy_path),
        serde_json::to_vec_pretty(&profile).expect("profile serializes"),
    )
    .expect("test measurement profile can be written");
}

fn check_by_id<'a>(report: &'a Value, check_id: &str) -> &'a Value {
    report["checks"]
        .as_array()
        .expect("checks is array")
        .iter()
        .find(|check| check["id"] == check_id)
        .unwrap_or_else(|| panic!("missing validation check {check_id}"))
}

fn saga_row<'a>(packet: &'a Value, law: &str) -> &'a Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structural verdict array")
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-descent" && row["law"] == law)
        .unwrap_or_else(|| panic!("missing saga row {law}"))
}

fn assert_saga_summary_has_no_class_vocabulary(summary: &Value) {
    assert!(
        !json_contains_substring(summary, "class"),
        "SAGA summary must not introduce layer C class vocabulary"
    );
}

fn zero_plan_for_refinement_test(root: &Path) -> Value {
    let mut plan = read_json(&root.join("repair_plan_complete_support.json"));
    plan["trueSheafCertificate"] =
        read_json(&root.join("repair_plan_true_sheaf.json"))["trueSheafCertificate"].clone();
    plan["gluingData"] =
        read_json(&root.join("repair_plan_gluing_data.json"))["gluingData"].clone();
    plan
}

fn refinement_fine_archmap_for_test(root: &Path) -> Value {
    let mut fine_archmap = read_json(&root.join("archmap_v2.json"));
    fine_archmap["contexts"][2]["atoms"]
        .as_array_mut()
        .expect("fine context atoms are array")
        .push(json!("atom:order"));
    fine_archmap
}

fn run_saga_compare_fixture(case_id: &str, archmap: Value, repair_plan: Value) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let archmap_path = out_dir.join("archmap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("compare ArchMap serializes"),
    )
    .expect("compare ArchMap writes");
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let repair_plan_path = out_dir.join("repair_plan.json");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("compare RepairPlan serializes"),
    )
    .expect("compare RepairPlan writes");
    let measurement_profile_path = test_measurement_profile_path(&policy_path);
    let law_surface_path = policy_path.with_file_name("law_surface.json");
    let analyze_args = [
        "analyze",
        "--archmap",
        archmap_path
            .to_str()
            .expect("compare ArchMap path is utf-8"),
        "--law-policy",
        policy_path
            .to_str()
            .expect("compare LawPolicy path is utf-8"),
        "--measurement-profile",
        measurement_profile_path
            .to_str()
            .expect("compare MeasurementProfile path is utf-8"),
        "--law-surface",
        law_surface_path
            .to_str()
            .expect("compare law surface path is utf-8"),
        "--repair-plan",
        repair_plan_path
            .to_str()
            .expect("compare RepairPlan path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("compare output path is utf-8"),
    ];
    let output = run_sig0_output(&analyze_args);
    assert!(
        output.status.success(),
        "compare fixture analyze failed\nstdout:\n{}\nstderr:\n{}\nvalidation:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        ["archmap-validation.json", "repair-plan-validation.json"]
            .iter()
            .filter_map(|name| fs::read_to_string(out_dir.join(name)).ok())
            .collect::<Vec<_>>()
            .join("\n")
    );
    out_dir
}

fn run_saga_fixture_lock(case_id: &str, repair_plan: Value) -> PathBuf {
    let root = ag_measurement_root();
    run_saga_fixture_lock_with_archmap(
        case_id,
        repair_plan,
        read_json(&root.join("archmap_v2.json")),
    )
}

fn run_saga_fixture_lock_with_archmap(
    case_id: &str,
    repair_plan: Value,
    archmap: Value,
) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let (mut policy, profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let law_surface_path = out_dir.join("law_surface.json");
    let repair_plan_path = out_dir.join("repair_plan.json");
    let archmap_path = out_dir.join("archmap.json");
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("ArchMap serializes"),
    )
    .expect("ArchMap writes");
    fs::write(
        &repair_plan_path,
        serde_json::to_vec_pretty(&repair_plan).expect("repair plan serializes"),
    )
    .expect("repair plan writes");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(policy_path.to_str().expect("path is utf-8")))
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        law_surface_path.to_str().expect("path is utf-8"),
        "--repair-plan",
        repair_plan_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    out_dir
}

fn run_analyze_fixture_lock(
    case_id: &str,
    archmap: &str,
    law_policy: &str,
    law_surface: &str,
    repair_plan: Option<&Path>,
) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let law_policy_path = root.join(law_policy);
    let measurement_profile_path = if matches!(
        law_policy,
        "law_policy_cech_h1.json" | "law_policy_cech_b8.json"
    ) {
        root.join("measurement_profile_ag.json")
    } else {
        test_measurement_profile_path(&law_policy_path)
    };
    let mut args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join(archmap)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        law_policy_path.to_str().expect("path is utf-8").to_string(),
        "--measurement-profile".to_string(),
        measurement_profile_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join(law_surface)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
    ];
    if let Some(repair_plan) = repair_plan {
        args.push("--repair-plan".to_string());
        args.push(repair_plan.to_str().expect("path is utf-8").to_string());
    }
    args.push("--out-dir".to_string());
    args.push(out_dir.to_str().expect("path is utf-8").to_string());
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

fn run_analyze_fixture_lock_with_surface(
    case_id: &str,
    archmap: &str,
    law_policy: &str,
    law_surface: &str,
    repair_plan: Option<&Path>,
) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let source_law_policy_path = root.join(law_policy);
    let measurement_profile_path = if matches!(
        law_policy,
        "law_policy_cech_h1.json" | "law_policy_cech_b8.json"
    ) {
        root.join("measurement_profile_ag.json")
    } else {
        test_measurement_profile_path(&source_law_policy_path)
    };
    let law_surface_path = root.join(law_surface);
    let policy = read_json(&source_law_policy_path);
    let surface = read_json(&law_surface_path);
    assert_eq!(
        policy["lawSurfaceRef"], surface["id"],
        "R9 fixture policy must explicitly resolve to its supplied law surface"
    );
    let law_policy_path = source_law_policy_path;
    let mut args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join(archmap)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        law_policy_path.to_str().expect("path is utf-8").to_string(),
        "--measurement-profile".to_string(),
        measurement_profile_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        law_surface_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
    ];
    if let Some(repair_plan) = repair_plan {
        args.push("--repair-plan".to_string());
        args.push(repair_plan.to_str().expect("path is utf-8").to_string());
    }
    args.push("--out-dir".to_string());
    args.push(out_dir.to_str().expect("path is utf-8").to_string());
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

fn run_square_free_analysis(case_id: &str, archmap_path: &Path) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    out_dir
}

fn run_square_free_gate(run_dir: &Path, expected_exit_code: i32) -> Value {
    let root = ag_measurement_root();
    let packet_path = run_dir.join("archsig-measurement-packet.json");
    let policy_path = root.join("gate_policy_conservative.json");
    let report_path = run_dir.join("archsig-gate-report.json");
    let args = [
        "gate",
        "--packet",
        packet_path.to_str().expect("packet path is utf-8"),
        "--policy",
        policy_path.to_str().expect("policy path is utf-8"),
        "--out",
        report_path.to_str().expect("report path is utf-8"),
    ];
    run_sig0_expect_code(&args, expected_exit_code);
    read_json(&report_path)
}

fn assert_byte_identical_analysis_artifacts(first_out: &Path, second_out: &Path) {
    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
    ] {
        if !first_out.join(artifact).exists() && !second_out.join(artifact).exists() {
            continue;
        }
        assert_eq!(
            fs::read(first_out.join(artifact)).expect("first artifact is readable"),
            fs::read(second_out.join(artifact)).expect("second artifact is readable"),
            "{artifact} must be byte-identical across repeated SAGA fixture runs"
        );
    }
}

fn invariant_by_id<'a>(packet: &'a Value, invariant_id: &str) -> &'a Value {
    packet["computedInvariants"]
        .as_array()
        .expect("computedInvariants is array")
        .iter()
        .find(|invariant| invariant["invariantId"] == invariant_id)
        .unwrap_or_else(|| panic!("missing computed invariant {invariant_id}"))
}

fn invariant_by_id_mut<'a>(packet: &'a mut Value, invariant_id: &str) -> &'a mut Value {
    packet["computedInvariants"]
        .as_array_mut()
        .expect("computedInvariants is array")
        .iter_mut()
        .find(|invariant| invariant["invariantId"] == invariant_id)
        .unwrap_or_else(|| panic!("missing computed invariant {invariant_id}"))
}

fn coherence_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.coherence-obstruction")
        .expect("coherence row exists")
}

fn restriction_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.restriction-compatibility")
        .expect("restriction compatibility row exists")
}

fn section_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.section-factorization")
        .expect("section factorization row exists")
}

fn boundary_residue_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.boundary-residue")
        .expect("boundary residue row exists")
}

fn run_generated_ag_measurement_case(
    root_out: &Path,
    case: &str,
    archmap: Value,
    policy: Value,
    profile: Value,
) -> Value {
    let out_dir = root_out.join(case);
    fs::create_dir_all(&out_dir).expect("case dir exists");
    let archmap_path = out_dir.join("archmap.json");
    let policy_path = out_dir.join("law_policy.json");
    let profile_path = sidecar_measurement_profile_path(&policy_path);
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("case archmap is written");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let law_surface_path = policy_path.with_file_name("law_surface.json");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        law_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    read_json(&out_dir.join("archsig-measurement-packet.json"))
}

fn assert_common_structural_verdict_discipline(packet: &Value, evaluator: &str) {
    let allowed_verdicts = BTreeSet::from([
        "measured_zero",
        "measured_nonzero",
        "unmeasured",
        "unknown",
        "not_computed",
    ]);
    let structural = packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array");
    assert_eq!(
        structural
            .iter()
            .filter(|row| row["evaluator"] == evaluator)
            .count(),
        1,
        "{evaluator} must emit exactly one structural verdict row"
    );

    let violated = packet["assumptions"]
        .as_array()
        .expect("assumptions is array")
        .iter()
        .filter(|row| row["status"] == "violated")
        .filter_map(|row| row["theoremRef"].as_str())
        .collect::<BTreeSet<_>>();

    for row in structural {
        let verdict = row["verdict"].as_str().expect("verdict is string");
        assert!(
            allowed_verdicts.contains(verdict),
            "structural verdict must stay in the five-value vocabulary"
        );
        if verdict == "measured_zero" {
            assert_eq!(row["verdictData"]["inScope"], true);
            assert_eq!(row["verdictData"]["zero"], true);
            assert_eq!(row["verdictData"]["nonZero"], false);
            assert!(
                row["verdictData"]["certRef"]
                    .as_str()
                    .is_some_and(|cert_ref| !cert_ref.is_empty()),
                "measured_zero must carry a certificate reference in PRD M common fixtures"
            );
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") {
            let depends_on = row["dependsOnAssumptions"]
                .as_array()
                .map(|dependencies| {
                    dependencies
                        .iter()
                        .filter_map(|dependency| dependency.as_str())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            assert!(
                depends_on
                    .iter()
                    .all(|dependency| !violated.contains(dependency)),
                "measured structural verdicts must not depend on violated assumptions"
            );
        }
    }
}

fn restriction_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-restriction-policy",
        "measurementProfileRef": "profile:ag-restriction@1",
        "policies": [{
            "law": "ag.restriction-compatibility",
            "evaluator": "ag.restriction-compatibility",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn restriction_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-restriction@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:restriction",
        "coefficient": "F2",
        "effCoeff": "finite-support-inclusion@1",
        "witnessFamily": [
            {"law": "ag.restriction-compatibility", "variable": "x"},
            {"law": "ag.restriction-compatibility", "variable": "y"}
        ],
        "resolutionSelector": "support-inclusion@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "all-inclusions-hold@1",
        "nonZeroPredicate": "some-inclusion-fails@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn boundary_residue_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-boundary-residue-policy",
        "measurementProfileRef": "profile:ag-boundary-residue@1",
        "policies": [{
            "law": "ag.boundary-residue",
            "evaluator": "ag.boundary-residue",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn boundary_residue_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-boundary-residue@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:boundary-residue",
        "coefficient": "F2",
        "effCoeff": "finite-mayer-vietoris-d0@1",
        "witnessFamily": [
            {"law": "ag.boundary-residue", "variable": "b0"},
            {"law": "ag.boundary-residue", "variable": "b1"}
        ],
        "resolutionSelector": "mayer-vietoris-d0@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "boundary-residue-zero@1",
        "nonZeroPredicate": "boundary-residue-nonzero@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn section_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-section-policy",
        "measurementProfileRef": "profile:ag-section@1",
        "policies": [{
            "law": "ag.section-factorization",
            "evaluator": "ag.section-factorization",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn section_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-section@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:section",
        "coefficient": "F2",
        "effCoeff": "finite-section-evaluation@1",
        "witnessFamily": [
            {"law": "ag.section-factorization", "variable": "x"},
            {"law": "ag.section-factorization", "variable": "y"}
        ],
        "resolutionSelector": "section-factorization@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "pullback-zero@1",
        "nonZeroPredicate": "pullback-nonzero@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn restriction_archmap(case: &str) -> Value {
    let source_generator = match case {
        "compatible" => Some(("atom:gen-source-xy", "x,y", "src:source-generator")),
        "violated" | "missing-target" => Some(("atom:gen-source-x", "x", "src:source-generator")),
        "empty-edges" => Some(("atom:gen-source-x", "x", "src:source-generator")),
        _ => panic!("unknown restriction fixture case: {case}"),
    };
    let target_generator = match case {
        "compatible" => Some(("atom:gen-target-x", "x", "src:target-generator")),
        "violated" => Some(("atom:gen-target-xy", "x,y", "src:target-generator")),
        "empty-edges" => Some(("atom:gen-target-x", "x", "src:target-generator")),
        "missing-target" => None,
        _ => panic!("unknown restriction fixture case: {case}"),
    };
    let mut atoms = vec![
        atom_json(
            "atom:source",
            "component",
            "src:source",
            "static",
            "component",
            None,
            vec!["src:source"],
        ),
        atom_json(
            "atom:target",
            "component",
            "src:target",
            "static",
            "component",
            None,
            vec!["src:target"],
        ),
    ];
    if let Some((atom_id, support, source_ref)) = source_generator {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "ctx:source",
            "restriction-compatibility",
            "restrictionIdealGenerator",
            Some(support),
            vec!["ctx:source", source_ref],
        ));
    }
    if let Some((atom_id, support, source_ref)) = target_generator {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "ctx:target",
            "restriction-compatibility",
            "restrictionIdealGenerator",
            Some(support),
            vec!["ctx:target", source_ref],
        ));
    }
    let mut source_atoms = vec!["atom:source"];
    if let Some((atom_id, _, _)) = source_generator {
        source_atoms.push(atom_id);
    }
    let mut target_atoms = vec!["atom:target"];
    if let Some((atom_id, _, _)) = target_generator {
        target_atoms.push(atom_id);
    }
    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-restriction-fixture-{case}"),
        "sources": {
            "src:source": {"kind": "rust", "path": "src/source.rs", "symbol": "Source", "line": 1},
            "src:target": {"kind": "rust", "path": "src/target.rs", "symbol": "Target", "line": 1},
            "src:source-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M2 source generator"},
            "src:target-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M2 target generator"},
            "ctx:source": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M2"},
            "ctx:target": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M2"}
        },
        "atoms": atoms,
        "contexts": [
            {
                "id": "ctx:source",
                "atoms": source_atoms,
                "restrictsTo": if case == "empty-edges" { json!([]) } else { json!(["ctx:target"]) },
                "refs": ["ctx:source"]
            },
            {
                "id": "ctx:target",
                "atoms": target_atoms,
                "refs": ["ctx:target"]
            }
        ],
        "covers": [{
            "id": "cover:restriction",
            "contexts": ["ctx:source", "ctx:target"],
            "refs": ["ctx:source", "ctx:target"]
        }]
    })
}

fn boundary_residue_archmap(case: &str) -> Value {
    let include_roles = case != "missing-classification";
    let include_mismatch = case != "missing-mismatch";
    let include_columns = case != "missing-matrix";
    let mismatch_support = match case {
        "zero"
        | "missing-classification"
        | "missing-mismatch"
        | "missing-matrix"
        | "duplicate-role"
        | "invalid-boundary-column"
        | "invalid-core-mismatch" => "b0",
        "sum-zero" => "b0,b1",
        "nonzero" => "b1",
        "unknown-variable" => "b2",
        _ => panic!("unknown boundary residue fixture case: {case}"),
    };
    let mut atoms = vec![
        atom_json(
            "atom:core-component",
            "component",
            "ctx:core",
            "static",
            "component",
            None,
            vec!["ctx:core", "src:core"],
        ),
        atom_json(
            "atom:feature-component",
            "component",
            "ctx:feature",
            "static",
            "component",
            None,
            vec!["ctx:feature", "src:feature"],
        ),
        atom_json(
            "atom:boundary-component",
            "component",
            "ctx:boundary",
            "static",
            "component",
            None,
            vec!["ctx:boundary", "src:boundary"],
        ),
    ];
    if include_roles {
        atoms.extend([
            atom_json(
                "atom:role-core",
                "semantic",
                "ctx:core",
                "boundary-residue",
                "patchRole",
                Some("core"),
                vec!["ctx:core", "src:role"],
            ),
            atom_json(
                "atom:role-feature",
                "semantic",
                "ctx:feature",
                "boundary-residue",
                "patchRole",
                Some("feature"),
                vec!["ctx:feature", "src:role"],
            ),
            atom_json(
                "atom:role-boundary",
                "semantic",
                "ctx:boundary",
                "boundary-residue",
                "patchRole",
                Some("boundary"),
                vec!["ctx:boundary", "src:role"],
            ),
        ]);
        if case == "duplicate-role" {
            atoms.push(atom_json(
                "atom:role-core-duplicate",
                "semantic",
                "ctx:core",
                "boundary-residue",
                "patchRole",
                Some("feature"),
                vec!["ctx:core", "src:role"],
            ));
        }
    }
    if include_columns {
        atoms.push(atom_json(
            "atom:d0-core-b0",
            "relation",
            if case == "invalid-boundary-column" {
                "ctx:boundary"
            } else {
                "ctx:core"
            },
            "boundary-residue",
            "restrictionColumn",
            Some("b0"),
            if case == "invalid-boundary-column" {
                vec!["ctx:boundary", "src:d0-core"]
            } else {
                vec!["ctx:core", "ctx:boundary", "src:d0-core"]
            },
        ));
        if case == "sum-zero" {
            atoms.push(atom_json(
                "atom:d0-feature-b1",
                "relation",
                "ctx:feature",
                "boundary-residue",
                "restrictionColumn",
                Some("b1"),
                vec!["ctx:feature", "ctx:boundary", "src:d0-feature"],
            ));
        }
    }
    if include_mismatch {
        atoms.push(atom_json(
            "atom:boundary-section",
            "relation",
            "boundary:section",
            "boundary-residue",
            "boundarySection",
            Some(mismatch_support),
            if case == "invalid-core-mismatch" {
                vec!["ctx:core", "src:boundary-section"]
            } else {
                vec!["ctx:boundary", "src:boundary-section"]
            },
        ));
    }

    let core_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:core")
                .then_some(id)
        })
        .collect::<Vec<_>>();
    let feature_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:feature")
                .then_some(id)
        })
        .collect::<Vec<_>>();
    let boundary_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:boundary")
                .then_some(id)
        })
        .collect::<Vec<_>>();

    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-boundary-residue-fixture-{case}"),
        "sources": {
            "src:core": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 core patch"},
            "src:feature": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 feature patch"},
            "src:boundary": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 boundary patch"},
            "src:role": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 patch role"},
            "src:d0-core": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 Mayer-Vietoris d0"},
            "src:d0-feature": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 Mayer-Vietoris d0"},
            "src:boundary-section": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6 boundary section"},
            "ctx:core": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6"},
            "ctx:feature": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6"},
            "ctx:boundary": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M6"}
        },
        "atoms": atoms,
        "contexts": [
            {
                "id": "ctx:core",
                "atoms": core_atoms,
                "restrictsTo": ["ctx:boundary"],
                "refs": ["ctx:core"]
            },
            {
                "id": "ctx:feature",
                "atoms": feature_atoms,
                "restrictsTo": ["ctx:boundary"],
                "refs": ["ctx:feature"]
            },
            {
                "id": "ctx:boundary",
                "atoms": boundary_atoms,
                "refs": ["ctx:boundary"]
            }
        ],
        "covers": [{
            "id": "cover:boundary-residue",
            "contexts": ["ctx:core", "ctx:feature", "ctx:boundary"],
            "refs": ["ctx:core", "ctx:feature", "ctx:boundary"]
        }]
    })
}

fn section_archmap(case: &str) -> Value {
    let assignment = match case {
        "lawful" => Some((
            "atom:section-assignment-a",
            "x=1,y=0",
            "src:section-assignment-a",
        )),
        "unlawful" => Some((
            "atom:section-assignment-b",
            "x=1,y=1",
            "src:section-assignment-b",
        )),
        "partial" => Some(("atom:section-partial", "x=1", "src:section-partial")),
        "missing-generator" => Some((
            "atom:section-assignment-no-generator",
            "x=0,y=0",
            "src:section-assignment-no-generator",
        )),
        "absent" => None,
        _ => panic!("unknown section fixture case: {case}"),
    };
    let include_generator = case != "missing-generator";
    let mut atoms = vec![atom_json(
        "atom:section-carrier",
        "component",
        "section:selected",
        "section-factorization",
        "selectedSection",
        None,
        vec!["src:section-carrier"],
    )];
    if include_generator {
        atoms.push(atom_json(
            "atom:forbid-xy",
            "relation",
            "I_Ob^U",
            "section-factorization",
            "support",
            Some("x,y"),
            vec!["src:forbidden-support", "ctx:section"],
        ));
    }
    if let Some((atom_id, object, source_ref)) = assignment {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "section:selected",
            "section-factorization",
            "witnessAssignment",
            Some(object),
            vec![source_ref, "ctx:section"],
        ));
    }
    let mut context_atoms = vec!["atom:section-carrier"];
    if include_generator {
        context_atoms.push("atom:forbid-xy");
    }
    if let Some((atom_id, _, _)) = assignment {
        context_atoms.push(atom_id);
    }
    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-section-fixture-{case}"),
        "sources": {
            "src:section-carrier": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 section"},
            "src:forbidden-support": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 minimal forbidden support"},
            "src:section-assignment-a": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 total section assignment A"},
            "src:section-assignment-b": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 total section assignment B"},
            "src:section-partial": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 partial section"},
            "src:section-assignment-no-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3 assignment without raw support"},
            "ctx:section": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M3"}
        },
        "atoms": atoms,
        "contexts": [{
            "id": "ctx:section",
            "atoms": context_atoms,
            "refs": ["ctx:section"]
        }],
        "covers": [{
            "id": "cover:section",
            "contexts": ["ctx:section"],
            "refs": ["ctx:section"]
        }]
    })
}

fn coherence_policy(_coefficient: &str, include_cech: bool) -> Value {
    let mut policies = vec![json!({
        "law": "ag.coherence-obstruction",
        "evaluator": "ag.coherence-obstruction",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    })];
    if include_cech {
        policies.insert(
            0,
            json!({
                "law": "surface:cech-surface-v052",
                "evaluator": "ag.cech-obstruction",
                "basis": ["policy-basis:layering"],
                "scope": ["src/"],
                "severity": "high"
            }),
        );
    }
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-coherence-policy",
        "measurementProfileRef": "profile:ag-coherence@1",
        "policies": policies
    })
}

fn coherence_profile(coefficient: &str, include_cech: bool) -> Value {
    let mut witness_family = vec![json!({
        "law": "ag.coherence-obstruction",
        "variable": "h2"
    })];
    if include_cech {
        witness_family.push(json!({
            "law": "ag.cech-obstruction",
            "variable": "x_coherence"
        }));
    }
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-coherence@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:coherence",
        "coefficient": coefficient,
        "effCoeff": "finite-linear-algebra@1",
        "witnessFamily": witness_family,
        "resolutionSelector": "h2-coherence@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "rank-zero@1",
        "nonZeroPredicate": "rank-positive@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn coherence_triangle_archmap(include_witness: bool) -> Value {
    let mut atoms = vec![
        atom_json(
            "atom:a",
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ),
        atom_json(
            "atom:b",
            "component",
            "src:b",
            "static",
            "component",
            None,
            vec!["src:b"],
        ),
        atom_json(
            "atom:c",
            "component",
            "src:c",
            "static",
            "component",
            None,
            vec!["src:c"],
        ),
        atom_json(
            "atom:abc",
            "component",
            "src:abc",
            "static",
            "tripleOverlapWitness",
            None,
            vec!["src:abc"],
        ),
    ];
    if include_witness {
        atoms.push(atom_json(
            "atom:h2-abc",
            "relation",
            "ctx:a",
            "coherence",
            "tripleSection",
            Some("ctx:a,ctx:b,ctx:c"),
            vec!["ctx:a", "ctx:b", "ctx:c"],
        ));
    }
    let c_atoms = if include_witness {
        vec!["atom:c", "atom:abc", "atom:h2-abc"]
    } else {
        vec!["atom:c", "atom:abc"]
    };
    archmap_with_contexts(
        atoms,
        vec![
            context_json("ctx:a", vec!["atom:a", "atom:abc"], vec!["ctx:b", "ctx:c"]),
            context_json("ctx:b", vec!["atom:b", "atom:abc"], vec!["ctx:c"]),
            context_json("ctx:c", c_atoms, vec![]),
        ],
    )
}

fn coherence_boundary_archmap(include_witnesses: bool) -> Value {
    let face_specs = [
        ("abc", vec!["ctx:a", "ctx:b", "ctx:c"]),
        ("abd", vec!["ctx:a", "ctx:b", "ctx:d"]),
        ("acd", vec!["ctx:a", "ctx:c", "ctx:d"]),
        ("bcd", vec!["ctx:b", "ctx:c", "ctx:d"]),
    ];
    let mut atoms = vec![
        atom_json(
            "atom:a",
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ),
        atom_json(
            "atom:b",
            "component",
            "src:b",
            "static",
            "component",
            None,
            vec!["src:b"],
        ),
        atom_json(
            "atom:c",
            "component",
            "src:c",
            "static",
            "component",
            None,
            vec!["src:c"],
        ),
        atom_json(
            "atom:d",
            "component",
            "src:d",
            "static",
            "component",
            None,
            vec!["src:d"],
        ),
    ];
    for (name, contexts) in face_specs.iter() {
        atoms.push(atom_json(
            &format!("atom:face-{name}"),
            "component",
            &format!("src:face-{name}"),
            "static",
            "tripleOverlapWitness",
            None,
            vec![&format!("src:face-{name}")],
        ));
        if include_witnesses && *name == "abc" {
            atoms.push(atom_json(
                &format!("atom:h2-{name}"),
                "relation",
                contexts[0],
                "coherence",
                "tripleSection",
                Some(&contexts.join(",")),
                contexts.clone(),
            ));
        }
    }
    let contexts = if include_witnesses {
        vec![
            context_json(
                "ctx:a",
                vec![
                    "atom:a",
                    "atom:face-abc",
                    "atom:face-abd",
                    "atom:face-acd",
                    "atom:h2-abc",
                ],
                vec!["ctx:b", "ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:b",
                vec![
                    "atom:b",
                    "atom:face-abc",
                    "atom:face-abd",
                    "atom:face-bcd",
                    "atom:h2-abc",
                ],
                vec!["ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:c",
                vec![
                    "atom:c",
                    "atom:face-abc",
                    "atom:face-acd",
                    "atom:face-bcd",
                    "atom:h2-abc",
                ],
                vec!["ctx:d"],
            ),
            context_json(
                "ctx:d",
                vec!["atom:d", "atom:face-abd", "atom:face-acd", "atom:face-bcd"],
                vec![],
            ),
        ]
    } else {
        vec![
            context_json(
                "ctx:a",
                vec!["atom:a", "atom:face-abc", "atom:face-abd", "atom:face-acd"],
                vec!["ctx:b", "ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:b",
                vec!["atom:b", "atom:face-abc", "atom:face-abd", "atom:face-bcd"],
                vec!["ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:c",
                vec!["atom:c", "atom:face-abc", "atom:face-acd", "atom:face-bcd"],
                vec!["ctx:d"],
            ),
            context_json(
                "ctx:d",
                vec!["atom:d", "atom:face-abd", "atom:face-acd", "atom:face-bcd"],
                vec![],
            ),
        ]
    };
    archmap_with_contexts(atoms, contexts)
}

fn coherence_boundary_zero_cochain_archmap() -> Value {
    let mut archmap = coherence_boundary_archmap(true);
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(atom_json(
            "atom:h2-abc-duplicate",
            "relation",
            "ctx:a",
            "coherence",
            "tripleSection",
            Some("ctx:a,ctx:b,ctx:c"),
            vec!["ctx:a", "ctx:b", "ctx:c"],
        ));
    for context_id in ["ctx:a", "ctx:b", "ctx:c"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:h2-abc-duplicate".to_string()));
    }
    archmap
}

fn coherence_empty_archmap() -> Value {
    archmap_with_contexts(
        vec![
            atom_json(
                "atom:a",
                "component",
                "src:a",
                "static",
                "component",
                None,
                vec!["src:a"],
            ),
            atom_json(
                "atom:b",
                "component",
                "src:b",
                "static",
                "component",
                None,
                vec!["src:b"],
            ),
        ],
        vec![
            context_json("ctx:a", vec!["atom:a"], vec!["ctx:b"]),
            context_json("ctx:b", vec!["atom:b"], vec![]),
        ],
    )
}

fn coherence_incomplete_triangle_archmap() -> Value {
    archmap_with_contexts(
        vec![
            atom_json(
                "atom:a",
                "component",
                "src:a",
                "static",
                "component",
                None,
                vec!["src:a"],
            ),
            atom_json(
                "atom:b",
                "component",
                "src:b",
                "static",
                "component",
                None,
                vec!["src:b"],
            ),
            atom_json(
                "atom:c",
                "component",
                "src:c",
                "static",
                "component",
                None,
                vec!["src:c"],
            ),
            atom_json(
                "atom:abc",
                "component",
                "src:abc",
                "static",
                "tripleOverlapWitness",
                None,
                vec!["src:abc"],
            ),
            atom_json(
                "atom:h2-abc",
                "relation",
                "ctx:a",
                "coherence",
                "tripleSection",
                Some("ctx:a,ctx:b,ctx:c"),
                vec!["ctx:a", "ctx:b", "ctx:c"],
            ),
        ],
        vec![
            context_json(
                "ctx:a",
                vec!["atom:a", "atom:abc", "atom:h2-abc"],
                vec!["ctx:b"],
            ),
            context_json("ctx:b", vec!["atom:b", "atom:abc", "atom:h2-abc"], vec![]),
            context_json("ctx:c", vec!["atom:c", "atom:abc", "atom:h2-abc"], vec![]),
        ],
    )
}

fn coherence_oversized_archmap() -> Value {
    let mut atoms = Vec::new();
    let mut contexts = Vec::new();
    for index in 0..13 {
        let context_id = format!("ctx:n{index}");
        let atom_id = format!("atom:n{index}");
        atoms.push(atom_json(
            &atom_id,
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ));
        contexts.push(json!({
            "id": context_id,
            "atoms": [atom_id],
            "refs": ["src:a"]
        }));
    }
    let mut archmap = archmap_with_contexts(atoms, contexts);
    for index in 0..13 {
        archmap["sources"][format!("ctx:n{index}")] = json!({
            "kind": "policy",
            "path": "docs/tool/ag_measurement_evidence_contract.md",
            "section": "M5"
        });
    }
    archmap
}

fn coherence_filled_tetrahedron_archmap() -> Value {
    let mut archmap = coherence_boundary_archmap(false);
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            atom_json(
                "atom:abcd",
                "component",
                "src:abcd",
                "static",
                "quadrupleOverlapWitness",
                None,
                vec!["src:abc"],
            ),
            atom_json(
                "atom:h2-abc",
                "relation",
                "ctx:a",
                "coherence",
                "tripleSection",
                Some("ctx:a,ctx:b,ctx:c"),
                vec!["ctx:a", "ctx:b", "ctx:c"],
            ),
        ]);
    for context_id in ["ctx:a", "ctx:b", "ctx:c", "ctx:d"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:abcd".to_string()));
    }
    for context_id in ["ctx:a", "ctx:b", "ctx:c"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:h2-abc".to_string()));
    }
    archmap
}

fn archmap_with_contexts(atoms: Vec<Value>, contexts: Vec<Value>) -> Value {
    let cover_contexts = contexts
        .iter()
        .filter_map(|context| context["id"].as_str())
        .collect::<Vec<_>>();
    json!({
        "schema": "archmap/v0.5.4",
        "id": "ag-coherence-fixture",
        "sources": {
            "src:a": {"kind": "rust", "path": "src/a.rs", "symbol": "A", "line": 1},
            "src:b": {"kind": "rust", "path": "src/b.rs", "symbol": "B", "line": 1},
            "src:c": {"kind": "rust", "path": "src/c.rs", "symbol": "C", "line": 1},
            "src:d": {"kind": "rust", "path": "src/d.rs", "symbol": "D", "line": 1},
            "src:abc": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "src:face-abc": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "src:face-abd": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "src:face-acd": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "src:face-bcd": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "ctx:a": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "ctx:b": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "ctx:c": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"},
            "ctx:d": {"kind": "policy", "path": "docs/tool/ag_measurement_evidence_contract.md", "section": "M5"}
        },
        "atoms": atoms,
        "contexts": contexts,
        "covers": [{
            "id": "cover:coherence",
            "contexts": cover_contexts.clone(),
            "refs": cover_contexts
        }]
    })
}

fn atom_json(
    id: &str,
    kind: &str,
    subject: &str,
    axis: &str,
    predicate: &str,
    object: Option<&str>,
    refs: Vec<&str>,
) -> Value {
    let mut atom = json!({
        "id": id,
        "kind": kind,
        "subject": subject,
        "axis": axis,
        "predicate": predicate,
        "refs": refs
    });
    if let Some(object) = object {
        atom["object"] = Value::String(object.to_string());
    }
    atom
}

fn context_json(id: &str, atoms: Vec<&str>, restricts_to: Vec<&str>) -> Value {
    let mut context = json!({
        "id": id,
        "atoms": atoms,
        "refs": [id]
    });
    if !restricts_to.is_empty() {
        context["restrictsTo"] = json!(restricts_to);
    }
    context
}

fn run_practical_saga_head_analyze(test_name: &str) -> PathBuf {
    let out_dir = temp_dir(test_name);
    let root = practical_rust_service_root();
    let args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join("archmap/archmap_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join("law_policy/law_surface.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--repair-plan".to_string(),
        root.join("saga/repair_plan_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--out-dir".to_string(),
        out_dir.to_str().expect("path is utf-8").to_string(),
    ];
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

#[test]
fn cli_analyze_emits_measurement_view_model_typed_sections() {
    let out_dir = run_practical_saga_head_analyze("view-model-typed-sections");
    let view_model = read_json(&out_dir.join("archsig-measurement-view-model.json"));
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));

    assert_eq!(view_model["schema"], "archsig-measurement-view-model/v0.5.4");
    assert!(view_model["runId"].is_string());
    assert!(view_model["inputDigests"]["measurementPacket"]["sha256"].is_string());

    // complex mirrors the packet cover nerve projection (no viewer-side faces).
    let cech = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants")
        .iter()
        .find(|inv| {
            inv["invariantId"]
                .as_str()
                .is_some_and(|id| id.starts_with("cech-cohomology:"))
        })
        .expect("cech invariant");
    let projection = &cech["representation"]["coverNerveProjection"];
    let complex = &view_model["complex"];
    assert_eq!(
        complex["vertices"].as_array().map(Vec::len),
        projection["vertices"].as_array().map(Vec::len)
    );
    assert_eq!(
        complex["edges"].as_array().map(Vec::len),
        projection["edges"].as_array().map(Vec::len)
    );
    assert_eq!(
        complex["triples"].as_array().map(Vec::len),
        projection["faces"].as_array().map(Vec::len)
    );

    // edge witness rows are three-state and cover every complex edge.
    let mismatch_rows = view_model["edgeMismatch"].as_array().expect("edge rows");
    assert_eq!(
        mismatch_rows.len(),
        complex["edges"].as_array().expect("edges").len()
    );
    for row in mismatch_rows {
        let status = row["status"].as_str().expect("status");
        assert!(
            [
                "mismatch_observed",
                "agreement_observed",
                "witness_not_supplied"
            ]
            .contains(&status),
            "unexpected edge witness status {status}"
        );
    }

    // class support is undirected and carries no orientation channel.
    let class_support = &view_model["classSupport"];
    assert_eq!(class_support["undirected"], true);
    assert!(class_support["classNonzero"].is_boolean());
    assert!(class_support["representativeEdgeRefs"].is_array());
    for forbidden in ["direction", "rotation", "orientation", "magnitude"] {
        assert!(
            class_support.get(forbidden).is_none(),
            "class support must not carry {forbidden}"
        );
    }

    // coverage rows exist for every complex vertex and only reference them.
    let vertex_refs = complex["vertices"]
        .as_array()
        .expect("vertices")
        .iter()
        .map(|vertex| vertex["contextRef"].as_str().expect("contextRef"))
        .collect::<std::collections::BTreeSet<_>>();
    let coverage = view_model["observationCoverage"]
        .as_array()
        .expect("coverage rows");
    assert!(!coverage.is_empty());
    let mut covered_contexts = std::collections::BTreeSet::new();
    for row in coverage {
        let context_ref = row["contextRef"].as_str().expect("contextRef");
        assert!(
            vertex_refs.contains(context_ref),
            "coverage row references unknown context {context_ref}"
        );
        assert!(row["measurementAxis"].is_string());
        assert!(row["status"].is_string());
        covered_contexts.insert(context_ref);
    }
    assert_eq!(covered_contexts.len(), vertex_refs.len());

    // per-chart grounding rows project the saga-grounded premise.
    let local = &view_model["localObservations"];
    assert_eq!(local["evaluator"], "ag.saga-grounded");
    assert_eq!(local["verdict"], "measured_zero");
    assert_eq!(
        local["perChart"].as_array().map(Vec::len),
        Some(vertex_refs.len())
    );

    // boundary statements are projected verbatim.
    assert_eq!(view_model["boundaryStatements"], packet["boundaryStatements"]);

    // harmonic edge values are not recorded in current packets: absent, not zero.
    assert!(view_model["harmonicFlow"].is_null());

    // measured scalars carry packet provenance.
    for field in view_model["scalarFields"].as_array().expect("scalar fields") {
        assert!(field["sourceInvariantId"].is_string());
        assert_eq!(field["scope"], "cover");
    }
}

#[test]
fn cli_view_model_field_names_exclude_display_vocabulary() {
    let out_dir = run_practical_saga_head_analyze("view-model-vocabulary-lint");
    let view_model = read_json(&out_dir.join("archsig-measurement-view-model.json"));
    fn collect_keys(value: &serde_json::Value, keys: &mut Vec<String>) {
        match value {
            serde_json::Value::Object(map) => {
                for (key, child) in map {
                    keys.push(key.to_ascii_lowercase());
                    collect_keys(child, keys);
                }
            }
            serde_json::Value::Array(items) => {
                for child in items {
                    collect_keys(child, keys);
                }
            }
            _ => {}
        }
    }
    let mut keys = Vec::new();
    collect_keys(&view_model, &mut keys);
    for forbidden in [
        "weather", "front", "vortex", "cyclone", "fog", "storm", "wind", "cloud",
    ] {
        assert!(
            !keys.iter().any(|key| key.contains(forbidden)),
            "display vocabulary {forbidden} leaked into view model field names"
        );
    }
}
