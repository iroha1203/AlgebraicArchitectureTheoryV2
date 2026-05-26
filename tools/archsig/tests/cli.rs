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

#[test]
fn cli_help_excludes_fieldsig_owned_commands() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("archmap-workflow"),
        "ArchSig help must expose the ArchMap-primary workflow\n{stdout}"
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
        stderr.contains("ArchSig is ArchMap-primary"),
        "implicit scan should be rejected with an ArchMap-primary boundary\n{stderr}"
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
        Some(
            "bounded AAT homomorphism from selected source architecture evidence to AAT observable signature, obstruction, and boundary space"
        )
    );
    assert!(
        matches!(
            validation_json["homomorphismDiagnostics"]["classification"].as_str(),
            Some("partial" | "nonHomomorphic")
        ),
        "ArchMap validation must classify the bounded homomorphism with explicit boundary state"
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
        validation_json["atomicObservationSummary"]["atomCandidateCount"], 4,
        "ArchMap validation must surface observed atom candidates"
    );
    assert!(
        validation_json["atomicObservationChecks"]
            .as_array()
            .expect("atomic observation checks are array")
            .iter()
            .any(|check| check["id"] == "archmap-obstruction-circuits-are-not-atoms"),
        "validation must keep obstruction circuits separate from primitive atoms"
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
        feature_json["homomorphismSummary"]["unmeasuredBoundaries"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "homomorphism summary must keep unmeasured boundaries"
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
