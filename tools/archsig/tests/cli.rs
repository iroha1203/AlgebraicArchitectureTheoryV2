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
