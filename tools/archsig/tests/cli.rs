use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

fn expressiveness_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/expressiveness")
}

fn validation_check_result<'a>(json: &'a Value, group: &str, id: &str) -> &'a str {
    json[group]
        .as_array()
        .expect("validation check group is array")
        .iter()
        .find(|check| check["id"] == id)
        .unwrap_or_else(|| panic!("validation check {id} exists in {group}"))["result"]
        .as_str()
        .expect("validation check result is string")
}

#[test]
fn cli_help_excludes_fieldsig_owned_commands() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("archmap-workflow"),
        "ArchSig help must expose the bounded ArchMap projection workflow\n{stdout}"
    );
    assert!(
        stdout.contains("adapter-scan"),
        "ArchSig help must expose bounded adapter scanning separately\n{stdout}"
    );
    for command in [
        "intent-map",
        "intent-forecast",
        "operation-support-estimate",
        "forecast-cone-skeleton",
        "consequence-envelope",
        "sft-forecast",
        "ai-proposal-governance",
        "dataset",
        "pr-history-dataset",
        "architecture-field-snapshot",
        "architecture-dynamics-metrics",
    ] {
        assert!(
            !stdout.contains(command),
            "ArchSig help still exposes FieldSig-owned command {command}\n{stdout}"
        );
    }
}

#[test]
fn cli_rejects_implicit_scan_default() {
    let output = run_sig0_output(&[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ArchSig is LLM-native"),
        "implicit scan should be rejected with an LLM-native boundary\n{stderr}"
    );
}

#[test]
fn cli_adapter_scan_emits_bounded_sig0_evidence() {
    let out_dir = temp_dir("sig0");
    let sig0 = out_dir.join("sig0.json");
    let validation = out_dir.join("validation.json");

    run_sig0(&[
        "adapter-scan",
        "--root",
        fixture_root().to_str().expect("fixture path is utf-8"),
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    let sig_json = read_json(&sig0);
    assert_eq!(sig_json["schemaVersion"], "archsig-sig0-v0");
    assert_eq!(
        sig_json["coverageBoundary"].as_str(),
        Some(
            "Lean import graph adapter covers explicit leading import declarations only; missing runtime, semantic, dynamic, generated, and framework evidence is retained as a boundary."
        )
    );
    assert!(
        sig_json["unsupportedConstructs"].is_array(),
        "adapter output must retain unsupportedConstructs even when empty"
    );
    assert!(
        sig_json["missingEvidence"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "adapter output must retain missing evidence boundaries"
    );
    assert!(
        sig_json["nonConclusions"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "adapter output must retain non-conclusions"
    );

    run_sig0(&[
        "validate",
        "--input",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
        "--universe-mode",
        "local-only",
    ]);
    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schemaVersion"],
        "component-universe-validation-report-v0"
    );
}

#[test]
fn cli_runs_archmap_primary_workflow() {
    let out_dir = temp_dir("archmap-workflow");
    let root = fixture_root();
    let archmap = root.join("archmap.json");

    run_sig0(&[
        "archmap-workflow",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);
    let validation_json = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(
        validation_json["schemaVersion"],
        "archmap-validation-report-v0"
    );
    assert_eq!(
        validation_json["homomorphismDiagnostics"]["reading"].as_str(),
        Some("derived bounded projection from source-grounded Atom observations")
    );
    assert!(
        matches!(
            validation_json["homomorphismDiagnostics"]["classification"].as_str(),
            Some("lossy" | "partial" | "nonHomomorphic")
        ),
        "ArchMap validation must classify the derived projection with explicit boundary state"
    );
    let family_names = validation_json["homomorphismDiagnostics"]["mapFamilySummaries"]
        .as_array()
        .expect("homomorphism family summaries are present")
        .iter()
        .map(|entry| entry["mapFamily"].as_str().expect("map family"))
        .collect::<Vec<_>>();
    for family in ["object", "relation", "law", "obstruction", "signatureAxis"] {
        assert!(
            family_names.contains(&family),
            "homomorphism diagnostics must retain {family} map family"
        );
    }
    assert!(
        matches!(
            validation_json["summary"]["result"].as_str(),
            Some("pass" | "warn")
        ),
        "ArchMap validation should complete without failing"
    );
    assert_eq!(
        validation_check_result(
            &validation_json,
            "legacySchemaChecks",
            "archmap-legacy-schema-fields"
        ),
        "pass",
        "primary ArchMap fixture must not require legacy fields"
    );
    assert_eq!(
        validation_check_result(
            &validation_json,
            "legacySchemaChecks",
            "archmap-legacy-obstruction-circuit-candidates"
        ),
        "pass",
        "primary ArchMap fixture must not expose obstruction candidates"
    );
    assert_eq!(
        validation_json["atomicObservationSummary"]["atomObservationCount"], 4,
        "ArchMap validation must surface observed atoms"
    );
    assert_eq!(
        validation_json["atomicObservationSummary"]["promotableAtomObservationCount"], 4,
        "ArchMap validation must count atom observations promotable to Lean-facing presentation"
    );
    assert_eq!(
        validation_json["atomicObservationSummary"]["leanPresentationCandidateCount"], 6,
        "ArchMap validation must retain atom, molecule, and semantic presentation observations"
    );
    assert!(
        validation_json["atomicObservationSummary"]["promotionBoundary"]
            .as_str()
            .expect("promotion boundary is present")
            .contains("does not certify universal ArchitectureAtom truth"),
        "promotion boundary must keep ArchMap candidates separate from certified atoms"
    );
    assert!(
        validation_json["atomicObservationChecks"]
            .as_array()
            .expect("atomic observation checks are array")
            .iter()
            .any(|check| check["id"] == "archmap-concern-hints-are-not-obstruction-circuits"),
        "validation must keep concern hints separate from obstruction circuits"
    );
    assert!(
        validation_json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|entry| entry == "atomic observation summary does not prove zero curvature")
    );

    let air_json = read_json(&out_dir.join("air.json"));
    assert_eq!(air_json["schemaVersion"], "aat-air-v0");
    let theorem_json = read_json(&out_dir.join("theorem-precondition-check.json"));
    assert_eq!(
        theorem_json["schemaVersion"],
        "theorem-precondition-check-report-v0"
    );
    let feature_json = read_json(&out_dir.join("feature-report.json"));
    assert_eq!(feature_json["schemaVersion"], "feature-extension-report-v0");
    assert!(
        matches!(
            feature_json["homomorphismSummary"]["classification"].as_str(),
            Some("partial" | "nonHomomorphic" | "lossy")
        ),
        "Feature report must summarize the ArchMap homomorphism boundary"
    );
    let feature_family_names = feature_json["homomorphismSummary"]["mapFamilies"]
        .as_array()
        .expect("feature homomorphism families are present")
        .iter()
        .map(|entry| entry["mapFamily"].as_str().expect("map family"))
        .collect::<Vec<_>>();
    for family in ["object", "relation", "law", "obstruction", "signatureAxis"] {
        assert!(
            feature_family_names.contains(&family),
            "Feature report must carry ArchMap {family} family forward"
        );
    }
    assert!(
        validation_json["responsibilityChecks"]
            .as_array()
            .expect("responsibility checks are array")
            .iter()
            .any(
                |check| check["id"] == "archmap-responsibility-non-conclusion-boundary"
                    && check["result"] == "pass"
            ),
        "ArchMap validation must keep lawfulness and obstruction non-conclusions explicit"
    );
    let bundle_json = read_json(&out_dir.join("aat-observable-bundle.json"));
    assert_eq!(bundle_json["schemaVersion"], "aat-observable-bundle-v0");
    assert_eq!(
        bundle_json["architectureId"], "archmap-fixture-repo",
        "workflow bundle must use the input ArchMap architecture id"
    );
    let bundle_text = serde_json::to_string(&bundle_json).expect("bundle json serializes");
    assert!(
        !bundle_text.contains("coupon-service"),
        "workflow bundle must not retain static fixture architecture id"
    );
    assert!(
        !bundle_text.contains("source:air:coupon"),
        "workflow bundle must not retain static fixture AIR source refs"
    );
    assert!(
        !bundle_text.contains("source:archmap:coupon"),
        "workflow bundle must not retain static fixture ArchMap source refs"
    );
    let source_ref_ids = bundle_json["sourceRefs"]
        .as_array()
        .expect("source refs are array")
        .iter()
        .map(|entry| entry["sourceRefId"].as_str().expect("source ref id"))
        .collect::<Vec<_>>();
    assert!(source_ref_ids.contains(&"source:archmap:primary"));
    assert!(source_ref_ids.contains(&"source:air:primary"));
    assert!(source_ref_ids.contains(&"source:theorem-check:primary"));
}

#[test]
fn cli_runs_llm_native_archmap_lawpolicy_archsig_workflow() {
    let out_dir = temp_dir("llm-native-workflow");
    let root = fixture_root();
    let archmap = root.join("archmap.json");
    let law_policy = root.join("law_policy.json");

    run_sig0(&[
        "llm-native-workflow",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        law_policy.to_str().expect("law policy path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("output directory path is utf-8"),
    ]);

    let archmap_validation = read_json(&out_dir.join("archmap-validation.json"));
    assert_eq!(
        archmap_validation["schemaVersion"],
        "archmap-validation-report-v0"
    );
    let law_policy_validation = read_json(&out_dir.join("law-policy-validation.json"));
    assert_eq!(
        law_policy_validation["schemaVersion"],
        "law-policy-validation-report-v0"
    );
    let analysis_packet = read_json(&out_dir.join("archsig-analysis-packet.json"));
    assert_eq!(
        analysis_packet["schemaVersion"],
        "archsig-analysis-packet-v0"
    );
    assert!(
        analysis_packet["obstructionCircuits"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "analysis packet must construct obstruction circuits"
    );
    assert!(
        analysis_packet["signatureAxes"]
            .as_array()
            .expect("signature axes are array")
            .iter()
            .any(
                |axis| axis["signatureAxisId"] == "sig-axis:semantic-inconsistency"
                    && axis["value"] == 1
            ),
        "analysis packet must value required signature axes"
    );
    let analysis_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(
        analysis_validation["summary"]["result"].as_str(),
        Some("pass")
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(llm_packet, analysis_packet);

    let air_json = read_json(&out_dir.join("air.json"));
    assert_eq!(air_json["schemaVersion"], "aat-air-v0");
    assert_eq!(
        air_json["feature"]["source"].as_str(),
        Some("manual"),
        "analysis-packet AIR remains a bounded manual review projection"
    );
    assert!(
        air_json["artifacts"]
            .as_array()
            .expect("AIR artifacts are array")
            .iter()
            .any(|artifact| artifact["kind"] == "archsig_analysis_packet"),
        "AIR must be projected from the ArchSig analysis packet"
    );
    assert!(
        !serde_json::to_string(&air_json)
            .expect("AIR serializes")
            .contains("archmap-v0-projection"),
        "LLM-native downstream AIR must not use the legacy ArchMap projection rule"
    );
    let air_validation = read_json(&out_dir.join("air-validation.json"));
    assert_eq!(air_validation["summary"]["result"].as_str(), Some("pass"));
    let theorem_check = read_json(&out_dir.join("theorem-precondition-check.json"));
    assert_eq!(
        theorem_check["schemaVersion"],
        "theorem-precondition-check-report-v0"
    );
    let feature_report = read_json(&out_dir.join("feature-report.json"));
    assert_eq!(
        feature_report["schemaVersion"],
        "feature-extension-report-v0"
    );
    assert_eq!(
        feature_report["homomorphismSummary"]["domain"].as_str(),
        Some("archmap-observation-map-v0"),
        "Feature Report must read the new ArchMap observation boundary"
    );
    assert_eq!(
        feature_report["homomorphismSummary"]["codomain"].as_str(),
        Some("archsig-analysis-packet-v0"),
        "Feature Report must carry ArchSig analysis packet state forward"
    );
    let bundle = read_json(&out_dir.join("aat-observable-bundle.json"));
    assert_eq!(bundle["schemaVersion"], "aat-observable-bundle-v0");
    let source_ref_ids = bundle["sourceRefs"]
        .as_array()
        .expect("source refs are array")
        .iter()
        .map(|entry| entry["sourceRefId"].as_str().expect("source ref id"))
        .collect::<Vec<_>>();
    assert!(source_ref_ids.contains(&"source:archsig-analysis-packet:primary"));
    assert!(source_ref_ids.contains(&"source:air:analysis-packet"));
    let bundle_validation = read_json(&out_dir.join("aat-observable-bundle-validation.json"));
    assert_eq!(
        bundle_validation["summary"]["result"].as_str(),
        Some("pass")
    );
}

#[test]
fn cli_archsig_analysis_step_outputs_packet_and_validation() {
    let out_dir = temp_dir("archsig-analysis-step");
    let root = fixture_root();
    let packet = out_dir.join("packet.json");
    let validation = out_dir.join("validation.json");
    let llm_packet = out_dir.join("llm-packet.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
        "--validation-out",
        validation.to_str().expect("validation path is utf-8"),
        "--llm-interpretation-out",
        llm_packet.to_str().expect("llm packet path is utf-8"),
    ]);
    let packet_json = read_json(&packet);
    let validation_json = read_json(&validation);
    assert_eq!(packet_json["schemaVersion"], "archsig-analysis-packet-v0");
    assert_eq!(
        validation_json["schemaVersion"],
        "archsig-analysis-packet-validation-report-v0"
    );
    assert_eq!(read_json(&llm_packet), packet_json);
}

#[test]
fn cli_negative_archmap_fixtures_preserve_guardrails() {
    let out_dir = temp_dir("negative-archmap-fixtures");
    let root = fixture_root();

    let concern_validation = out_dir.join("concern-validation.json");
    let concern_output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_invalid_concern_promoted.json")
            .to_str()
            .expect("invalid concern fixture path is utf-8"),
        "--out",
        concern_validation
            .to_str()
            .expect("concern validation path is utf-8"),
    ]);
    assert!(
        !concern_output.status.success(),
        "concern promotion fixture must fail validation"
    );
    let concern_json = read_json(&concern_validation);
    assert!(
        concern_json["atomicObservationChecks"]
            .as_array()
            .expect("atomic checks are array")
            .iter()
            .any(
                |check| check["id"] == "archmap-concern-hints-are-not-obstruction-circuits"
                    && check["result"] == "fail"
            ),
        "concernHints must not be accepted as obstruction circuits"
    );

    let gap_validation = out_dir.join("gap-validation.json");
    let gap_output = run_sig0_output(&[
        "archmap",
        "--input",
        root.join("archmap_invalid_gap_measured_zero.json")
            .to_str()
            .expect("invalid gap fixture path is utf-8"),
        "--out",
        gap_validation
            .to_str()
            .expect("gap validation path is utf-8"),
    ]);
    assert!(
        !gap_output.status.success(),
        "gap measured-zero fixture must fail validation"
    );
    let gap_json = read_json(&gap_validation);
    assert!(
        gap_json["atomicObservationChecks"]
            .as_array()
            .expect("atomic checks are array")
            .iter()
            .any(
                |check| check["id"] == "archmap-observation-gaps-not-measured-zero"
                    && check["result"] == "fail"
            ),
        "observation gaps must not be rounded to measured zero"
    );
}

#[test]
fn cli_regression_same_archmap_multiple_law_policies() {
    let root = fixture_root();
    let full_packet = read_json(&root.join("archsig_analysis_packet.json"));
    let layer_only_packet = read_json(&root.join("archsig_analysis_packet_layer_only.json"));
    assert_ne!(
        full_packet["selectedLawPolicyRef"]["artifactId"],
        layer_only_packet["selectedLawPolicyRef"]["artifactId"],
        "golden corpus must include multiple LawPolicy analyses"
    );
    assert!(
        full_packet["obstructionCircuits"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "full policy fixture should construct an obstruction"
    );
    assert_eq!(
        layer_only_packet["obstructionCircuits"]
            .as_array()
            .expect("layer-only obstructions are array")
            .len(),
        0,
        "layer-only policy should reanalyze the same ArchMap without semantic obstruction"
    );
}

#[test]
fn cli_locks_archmap_homomorphism_expressiveness_matrix() {
    let out_dir = temp_dir("archmap-homomorphism-expressiveness");
    let archmap = expressiveness_root().join("archmap_expressiveness_suite_v0.json");
    let validation = out_dir.join("archmap-validation.json");

    run_sig0(&[
        "archmap",
        "--input",
        archmap.to_str().expect("archmap path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);

    let json = read_json(&validation);
    assert_eq!(
        json["homomorphismDiagnostics"]["reading"].as_str(),
        Some("AAT concept coverage matrix for ArchMap bounded homomorphism expressiveness")
    );
    let family_names = json["homomorphismDiagnostics"]["mapFamilySummaries"]
        .as_array()
        .expect("homomorphism family summaries are array")
        .iter()
        .map(|entry| entry["mapFamily"].as_str().expect("map family"))
        .collect::<Vec<_>>();
    for family in ["object", "relation", "law", "obstruction", "signatureAxis"] {
        assert!(
            family_names.contains(&family),
            "expressiveness matrix must retain AAT {family} map family"
        );
    }
    assert!(
        json["homomorphismDiagnostics"]["unsupportedBoundaries"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "unsupported AAT concept coverage must remain explicit"
    );
    assert!(
        json["homomorphismDiagnostics"]["unmeasuredBoundaries"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "unmeasured AAT concept coverage must remain explicit"
    );
    assert_eq!(
        validation_check_result(&json, "legacySchemaChecks", "archmap-legacy-schema-fields"),
        "warn",
        "legacy expressiveness fixture should be accepted only as compatibility input"
    );
    assert_eq!(
        validation_check_result(
            &json,
            "legacySchemaChecks",
            "archmap-legacy-obstruction-circuit-candidates"
        ),
        "pass",
        "expressiveness fixture should not need legacy obstruction candidate input"
    );

    let legacy_obstruction_dir = temp_dir("archmap-legacy-obstruction-candidate");
    let legacy_archmap = legacy_obstruction_dir.join("archmap-with-legacy-obstruction.json");
    let legacy_validation = legacy_obstruction_dir.join("archmap-validation.json");
    let mut legacy_doc = read_json(&archmap);
    legacy_doc["obstructionCircuitCandidates"] = serde_json::from_str(
        r#"[{
          "circuitCandidateId": "legacy-circuit",
          "circuitKind": "FailedFilling",
          "lawRef": "law:legacy",
          "atomCandidateRefs": [],
          "moleculeCandidateRefs": [],
          "sourceRefs": [{"artifactId": "src-service-user", "kind": "file", "path": "src/services/user.ts"}],
          "observationStatus": "observed",
          "measurementBoundary": "measuredNonzero",
          "claimBoundary": "legacy compatibility fixture",
          "nonConclusions": ["legacy obstruction candidate is not primary ArchMap output"]
        }]"#,
    )
    .expect("legacy obstruction candidate fixture parses");
    fs::write(
        &legacy_archmap,
        serde_json::to_vec_pretty(&legacy_doc).expect("legacy archmap serializes"),
    )
    .expect("legacy archmap fixture can be written");
    run_sig0(&[
        "archmap",
        "--input",
        legacy_archmap
            .to_str()
            .expect("legacy archmap path is utf-8"),
        "--out",
        legacy_validation
            .to_str()
            .expect("legacy validation path is utf-8"),
    ]);
    let legacy_json = read_json(&legacy_validation);
    assert_eq!(
        validation_check_result(
            &legacy_json,
            "legacySchemaChecks",
            "archmap-legacy-obstruction-circuit-candidates"
        ),
        "warn",
        "legacy obstruction candidates should be called out as non-primary ArchMap output"
    );

    let workflow_dir = temp_dir("archmap-homomorphism-expressiveness-workflow");
    run_sig0(&[
        "archmap-workflow",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--out-dir",
        workflow_dir.to_str().expect("workflow dir path is utf-8"),
    ]);
    let feature = read_json(&workflow_dir.join("feature-report.json"));
    let feature_family_names = feature["homomorphismSummary"]["mapFamilies"]
        .as_array()
        .expect("feature homomorphism families are array")
        .iter()
        .map(|entry| entry["mapFamily"].as_str().expect("map family"))
        .collect::<Vec<_>>();
    for family in ["object", "relation", "law", "obstruction", "signatureAxis"] {
        assert!(
            feature_family_names.contains(&family),
            "workflow Feature Report must retain AAT {family} map family"
        );
    }
    let unsupported = feature["homomorphismSummary"]["unsupportedBoundaries"]
        .as_array()
        .expect("unsupported boundaries are array")
        .iter()
        .map(|item| item.as_str().expect("unsupported boundary"))
        .collect::<Vec<_>>();
    let unsupported_unique = unsupported.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unsupported.len(),
        unsupported_unique.len(),
        "unsupported boundaries must be deduplicated"
    );

    let bundle = read_json(&workflow_dir.join("aat-observable-bundle.json"));
    let concept_status = |concept_id: &str, field: &str| {
        bundle["conceptMappings"]
            .as_array()
            .expect("concept mappings are array")
            .iter()
            .find(|entry| entry["conceptId"] == concept_id)
            .and_then(|entry| entry[field].as_str())
            .expect("concept field is present")
            .to_string()
    };
    assert_eq!(
        concept_status("concept:semantic-diagram", "measurementStatus"),
        "measuredNonzero",
        "semantic diagram concept status must reflect supplied ArchMap evidence"
    );
    assert_eq!(
        concept_status("concept:theorem-boundary", "reviewStatus"),
        "blockedByFormalPromotionGuardrail",
        "theorem boundary must expose the formal promotion guardrail"
    );
    let theorem_boundary = &bundle["theoremBoundaries"][0];
    assert!(
        theorem_boundary["missingPreconditions"]
            .as_array()
            .is_some_and(|items| items.iter().any(|item| item
                .as_str()
                .is_some_and(|text| text.contains("validation and projection do not discharge")))),
        "Bundle theorem boundary must retain ArchMap preservation checklist blockers"
    );
}

#[test]
fn cli_schema_catalog_is_archsig_owned() {
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
    assert!(ids.contains(&"signature-artifact"));
    assert!(ids.contains(&"archmap"));
    assert_eq!(
        schema_catalog_artifact_role(artifacts, "archsig-analysis-packet"),
        "primary"
    );
    assert_eq!(
        schema_catalog_artifact_role(artifacts, "architecture-policy"),
        "adapter evidence"
    );
    assert_eq!(
        schema_catalog_artifact_role(artifacts, "law-violation-report"),
        "adapter evidence"
    );
    for bounded_surface in [
        "organization-policy",
        "policy-decision",
        "pr-comment-summary",
        "baseline-suppression",
        "pr-quality-analysis",
        "report-artifact-retention-manifest",
    ] {
        assert_eq!(
            schema_catalog_artifact_role(artifacts, bounded_surface),
            "bounded review projection",
            "{bounded_surface} must be classified as a bounded review projection"
        );
    }
    for fieldsig_id in [
        "intentmap",
        "operation-support-estimate",
        "forecast-cone-skeleton",
        "consequence-envelope-report",
        "ai-proposal-governance",
    ] {
        assert!(
            !ids.contains(&fieldsig_id),
            "ArchSig catalog still owns FieldSig artifact {fieldsig_id}"
        );
    }
}

fn schema_catalog_artifact_role<'a>(
    artifacts: &'a [serde_json::Value],
    artifact_id: &str,
) -> &'a str {
    artifacts
        .iter()
        .find(|entry| entry["artifactId"] == artifact_id)
        .unwrap_or_else(|| panic!("schema catalog artifact {artifact_id} exists"))["artifactRole"]
        .as_str()
        .expect("artifact role is string")
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

fn run_sig0_output(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}
