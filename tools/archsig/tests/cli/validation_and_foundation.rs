use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use archsig::{
    ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION,
    ARCHSIG_COMPARISON_CLASS_TRANSPORT_CONCLUSION_CODES, ARCHSIG_COMPARISON_CONCLUSION_CODES,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE,
    ARCHSIG_COMPARISON_NO_NEW_MEASURED_OBSTRUCTION_RECORDED,
    ARCHSIG_COMPARISON_RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA, ARCHSIG_GATE_REPORT_DECISIONS,
    ARCHSIG_REPAIR_TARGETS_IDENTIFIED, ARCHSIG_SAGA_CONCLUSION_CODES,
    ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX, ArchMapDocumentV2, ArchSigRunManifestV1,
    compare_archmap_v2_doctrine,
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

    let mut removed_instance_fields = read_json(&input);
    removed_instance_fields["skeleton"] = json!([]);
    removed_instance_fields["defectSources"] = json!([]);
    let removed_instance_fields_path = out_dir.join("removed-instance-fields.json");
    fs::write(
        &removed_instance_fields_path,
        serde_json::to_vec_pretty(&removed_instance_fields)
            .expect("removed instance fields fixture serializes"),
    )
    .expect("removed instance fields fixture writes");
    let removed_instance_fields_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        removed_instance_fields_path
            .to_str()
            .expect("removed instance fields path is utf-8"),
    ]);
    assert_eq!(removed_instance_fields_output.status.code(), Some(2));
    let removed_instance_fields_stderr =
        String::from_utf8_lossy(&removed_instance_fields_output.stderr);
    assert!(removed_instance_fields_stderr.contains("unknown field"));
    assert!(
        removed_instance_fields_stderr.contains("skeleton")
            || removed_instance_fields_stderr.contains("defectSources")
    );

    let mut invalid_quotient = read_json(&input);
    invalid_quotient["quotientSheafCondition"] = json!({"mode": "invalid"});
    let invalid_quotient_path = out_dir.join("invalid-quotient.json");
    fs::write(
        &invalid_quotient_path,
        serde_json::to_vec_pretty(&invalid_quotient).expect("invalid quotient fixture serializes"),
    )
    .expect("invalid quotient fixture writes");
    let invalid_quotient_report = out_dir.join("invalid-quotient-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            invalid_quotient_path.to_str().expect("path is utf-8"),
            "--out",
            invalid_quotient_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(
        read_json(&invalid_quotient_report)["summary"]["result"],
        "fail"
    );

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

    let mut null_alias = read_json(&input);
    null_alias["laws"][0]["witnessVariables"][0]["binding"]["archmapVariable"] = Value::Null;
    null_alias["laws"][0]["witnessVariables"][0]["binding"]["axis"] = json!("cech");
    null_alias["laws"][0]["witnessVariables"][0]["binding"]["predicate"] = json!("sectionValue");
    let null_alias_path = out_dir.join("null-alias.json");
    fs::write(
        &null_alias_path,
        serde_json::to_vec_pretty(&null_alias).expect("null alias serializes"),
    )
    .expect("null alias writes");
    let null_alias_report = out_dir.join("null-alias-report.json");
    run_sig0_expect_code(
        &[
            "law-surface",
            "--law-surface",
            null_alias_path.to_str().expect("path is utf-8"),
            "--out",
            null_alias_report.to_str().expect("path is utf-8"),
        ],
        1,
    );
    assert_eq!(read_json(&null_alias_report)["summary"]["result"], "fail");

    let mut mismatched_binding = read_json(&input);
    let binding = mismatched_binding["laws"][0]["witnessVariables"][0]["binding"]
        .as_object_mut()
        .expect("binding is object");
    binding.insert("archmapVariable".to_string(), json!("p"));
    binding.insert("axis".to_string(), json!("cech"));
    binding.insert("predicate".to_string(), json!("sectionValue"));
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

    let mut instance_edge = read_json(&input);
    instance_edge["laws"][0]["witnessVariables"][0]["binding"]["edge"] = json!(["ctx:a", "ctx:b"]);
    let instance_edge_path = out_dir.join("instance-edge.json");
    fs::write(
        &instance_edge_path,
        serde_json::to_vec_pretty(&instance_edge).expect("instance edge serializes"),
    )
    .expect("instance edge writes");
    let instance_edge_output = run_sig0_output(&[
        "law-surface",
        "--law-surface",
        instance_edge_path.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(instance_edge_output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&instance_edge_output.stderr).contains("unknown field"));

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
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    ensure_restrictions(&mut archmap, &[("ctx:order", "ctx:inventory")]);
    let archmap_path = write_archmap_variant(&out_dir, archmap, "archmap_saga.json");

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
    let membership = saga_row(&packet, "saga.residual-boundary-membership");
    assert_eq!(membership["verdict"], "measured_zero");
    assert_eq!(membership["verdictData"]["methodStatus"], "residual_in_b1");
    assert!(
        packet["structuralVerdict"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["law"] != "saga.global-coherence"),
        "the retired saga.global-coherence row must stay silent as deleted vocabulary"
    );
    assert!(
        packet["computedInvariants"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["invariantId"] != "saga-comparison:h1-transfer"),
        "the retired saga comparison invariant must stay silent as deleted vocabulary"
    );
    let derivation = packet["computedInvariants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:residual-derivation")
        .expect("residual derivation invariant");
    assert_eq!(derivation["residualDerivation"]["derived"], true);
    assert!(
        derivation["residualDerivation"]["edges"]
            .as_array()
            .is_some_and(|edges| edges.iter().all(|edge| edge["value"] == 0
                && edge["witnessVariables"]
                    .as_array()
                    .is_some_and(Vec::is_empty))),
        "matching sections must derive a zero residual on every observed overlap"
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
    assert_eq!(summary["translationRule"]["theoremRef"], Value::Null);
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
                text.contains("derived SAGA residual") && text.contains("inside B1")
            }),
        "translation principal text must stay inside the selected profile"
    );
    assert!(
        summary["translationRule"]["boundary"].as_str().is_some_and(
            |text| text.contains("finite complex derived from the selected ArchMap cover")
        ),
        "translation boundary must stay relative to the selected complex"
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
            text.contains("ArchSig reports selected AG obstruction rows")
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

fn ensure_restrictions(archmap: &mut Value, edges: &[(&str, &str)]) {
    let contexts = archmap["contexts"]
        .as_array_mut()
        .expect("ArchMap contexts are an array");
    // restriction 関係は有限 poset(非巡回)なので、辞書順の向きで張る。
    for (left, right) in edges {
        let (left, right) = if left <= right {
            (left, right)
        } else {
            (right, left)
        };
        let context = contexts
            .iter_mut()
            .find(|context| context["id"] == *left)
            .expect("restriction source context exists");
        if !context["restrictsTo"].is_array() {
            context["restrictsTo"] = json!([]);
        }
        let restricts = context["restrictsTo"]
            .as_array_mut()
            .expect("restrictsTo is an array");
        if !restricts.iter().any(|target| target == right) {
            restricts.push(json!(right));
        }
    }
}

fn add_cech_witness_variables(policy_path: &Path, edges: &[(&str, &str, &str)]) {
    let surface_path = policy_path.with_file_name("law_surface.json");
    let mut surface = read_json(&surface_path);
    let laws = surface["laws"]
        .as_array_mut()
        .expect("law surface laws are an array");
    let variables = edges
        .iter()
        .map(|(variable, _, _)| (*variable).to_string())
        .collect::<Vec<_>>();
    laws.push(json!({
        "lawId": "law:test-cech-bindings",
        "conditionType": "closed-equational",
        "witnessVariables": edges.iter().map(|(variable, _, _)| json!({
            "variable": variable,
            "binding": {"axis": "cech", "predicate": "sectionValue"}
        })).collect::<Vec<_>>(),
        "forbiddenSupportGenerators": variables
            .iter()
            .map(|variable| json!({"support": [variable]}))
            .collect::<Vec<_>>()
    }));
    fs::write(
        &surface_path,
        serde_json::to_vec_pretty(&surface).expect("edited law surface serializes"),
    )
    .expect("edited law surface writes");
}

fn write_archmap_variant(out_dir: &Path, base: Value, file_name: &str) -> std::path::PathBuf {
    let path = out_dir.join(file_name);
    fs::write(
        &path,
        serde_json::to_vec_pretty(&base).expect("archmap variant serializes"),
    )
    .expect("archmap variant writes");
    path
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
