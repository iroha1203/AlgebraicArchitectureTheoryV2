#[test]
fn cli_analyze_v2_cech_empty_selected_scope_is_typed_silence() {
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

    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        law_policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        test_measurement_profile_path(Path::new(law_policy_path.to_str().expect("path is utf-8")))
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
    assert_eq!(
        summary["conclusion"],
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    );
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

    let retired_vocabulary_path = out_dir.join("retired-vocabulary-comparison.json");
    let retired_vocabulary = json!({
        "schema": "archsig-comparison-report/v0.5.7",
        "conclusionCode": "NO_NEW_MEASURED_OBSTRUCTION_RECORDED",
        "comparability": { "level": "identical" },
        "inputDigests": {
            "baseRun": {
                "runId": "run:base",
                "toolVersion": "0.5.4",
                "archmap": { "sha256": "base-archmap" },
                "lawPolicy": { "sha256": "base-policy" },
                "profileFingerprint": { "sha256": "base-profile" },
                "siteCoverDigest": { "sha256": "base-cover" },
                "measurementPacket": { "sha256": "base-packet" }
            },
            "headRun": {
                "runId": "run:head",
                "toolVersion": "0.5.4",
                "archmap": { "sha256": "head-archmap" },
                "lawPolicy": { "sha256": "head-policy" },
                "profileFingerprint": { "sha256": "head-profile" },
                "siteCoverDigest": { "sha256": "head-cover" },
                "measurementPacket": { "sha256": "head-packet" }
            }
        },
        "verdictTransitions": [{
            "rowKey": "ag.cech-obstruction|ag.cech-obstruction|finite_f2_cech_computed",
            "baseRowRef": "structuralVerdict/ag.cech-obstruction/ag.cech-obstruction/finite_f2_cech_computed",
            "headRowRef": "structuralVerdict/ag.cech-obstruction/ag.cech-obstruction/finite_f2_cech_computed",
            "transition": "preexisting_recorded_row",
            "introducedByChangeCategory": "preexisting",
            "deltaRefs": []
        }],
        "residualClassAgreement": {
            "status": "cohomologous",
            "theoremRef": "archsig-contract:retired-residual-class-agreement"
        },
        "residualDifferenceReading": {
            "status": "silence_by_design",
            "reason": "residual_derivation_not_recorded",
            "theoremRef": "archsig-contract:residual-difference-reading"
        }
    });
    fs::write(
        &retired_vocabulary_path,
        serde_json::to_vec_pretty(&retired_vocabulary)
            .expect("retired-vocabulary comparison serializes"),
    )
    .expect("retired-vocabulary comparison can be written");
    let retired_vocabulary_report = out_dir.join("retired-vocabulary-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            retired_vocabulary_path.to_str().expect("path is utf-8"),
            "--out",
            retired_vocabulary_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let retired_vocabulary_gate = read_json(&retired_vocabulary_report);
    assert_eq!(retired_vocabulary_gate["decision"], "NOT_EVALUABLE");
    assert_eq!(
        retired_vocabulary_gate["reason"],
        "comparison report schema validation failed"
    );

    let unknown_status_path = out_dir.join("unknown-residual-status-comparison.json");
    let mut unknown_status = retired_vocabulary.clone();
    unknown_status
        .as_object_mut()
        .expect("comparison fixture is an object")
        .remove("residualClassAgreement");
    unknown_status["residualDifferenceReading"] = json!({
        "status": "cohomologous",
        "theoremRef": "archsig-contract:residual-difference-reading"
    });
    fs::write(
        &unknown_status_path,
        serde_json::to_vec_pretty(&unknown_status).expect("unknown-status comparison serializes"),
    )
    .expect("unknown-status comparison can be written");
    let unknown_status_report = out_dir.join("unknown-residual-status-gate-report.json");
    run_sig0_expect_code(
        &[
            "gate",
            "--packet",
            packet_path.to_str().expect("path is utf-8"),
            "--policy",
            policy_path.to_str().expect("path is utf-8"),
            "--comparison",
            unknown_status_path.to_str().expect("path is utf-8"),
            "--out",
            unknown_status_report.to_str().expect("path is utf-8"),
        ],
        2,
    );
    let unknown_status_gate = read_json(&unknown_status_report);
    assert_eq!(unknown_status_gate["decision"], "NOT_EVALUABLE");
    assert_eq!(
        unknown_status_gate["reason"],
        "comparison report schema validation failed"
    );

    let empty_comparison_path = out_dir.join("empty-comparison.json");
    fs::write(
        &empty_comparison_path,
        serde_json::to_vec_pretty(&json!({
        "schema": "archsig-comparison-report/v0.5.7",
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
        "schema": "archsig-comparison-report/v0.5.7",
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
    let compare_overwrite = run_sig0_output(&[
        "compare",
        "--base-run",
        identical_base.to_str().expect("path is utf-8"),
        "--head-run",
        identical_head.to_str().expect("path is utf-8"),
        "--out-dir",
        identical_out.to_str().expect("path is utf-8"),
    ]);
    assert_eq!(compare_overwrite.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&compare_overwrite.stderr)
            .contains("compare output directory already contains current artifacts")
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        let symlink_parent = out_dir.join("compare-through-symlink");
        symlink(&identical_base, &symlink_parent).expect("comparison symlink can be created");
        let symlink_output = symlink_parent.join("nested-output");
        let symlink_result = run_sig0_output(&[
            "compare",
            "--base-run",
            identical_base.to_str().expect("path is utf-8"),
            "--head-run",
            identical_head.to_str().expect("path is utf-8"),
            "--out-dir",
            symlink_output.to_str().expect("path is utf-8"),
        ]);
        assert_eq!(symlink_result.status.code(), Some(2));
        assert!(
            String::from_utf8_lossy(&symlink_result.stderr)
                .contains("compare output directory must be outside both input run directories")
        );
        assert!(!identical_base.join("nested-output").exists());
    }

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
    assert_eq!(comparison["schema"], "archsig-comparison-report/v0.5.7");
    assert_eq!(
        comparison["discipline"],
        "Comparison is a record-level juxtaposition of two ArchSig runs. ArchSig derives a class-zero reading from the selected normalized ArchMap covers when each fine context has a unique observed coarse containment path."
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
