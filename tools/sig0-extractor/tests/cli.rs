use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

fn module_root_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/module_root")
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is after unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("sig0-extractor-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temp dir is created");
    dir
}

fn run_sig0(args: &[&str]) {
    let output = Command::new(env!("CARGO_BIN_EXE_sig0-extractor"))
        .args(args)
        .output()
        .expect("sig0-extractor command runs");
    assert!(
        output.status.success(),
        "command failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn read_json(path: &Path) -> Value {
    let contents = fs::read_to_string(path).expect("json output is readable");
    serde_json::from_str(&contents).expect("json output parses")
}

#[test]
fn cli_extracts_policy_runtime_fixture_contract() {
    let root = fixture_root();
    let out_dir = temp_dir("extract");
    let out = out_dir.join("sig0.json");

    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--policy",
        root.join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--runtime-edges",
        root.join("runtime_edges.json")
            .to_str()
            .expect("runtime path is utf-8"),
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schemaVersion"], "sig0-extractor-v0");
    assert_eq!(json["policies"]["policyId"], "minimal-measured-zero");
    assert_eq!(
        json["metricStatus"]["boundaryViolationCount"]["measured"],
        true
    );
    assert_eq!(json["metricStatus"]["runtimePropagation"]["measured"], true);
    assert_eq!(
        json["runtimeDependencyGraph"]["projectionRule"],
        "runtime-edge-projection-v0"
    );
    assert_eq!(
        json["runtimeEdgeEvidence"][0]["evidenceLocation"]["path"],
        "runtime/routes.json"
    );
}

#[test]
fn cli_dataset_fixture_keeps_unmeasured_deltas_null() {
    let root = fixture_root();
    let out_dir = temp_dir("dataset");
    let before = out_dir.join("before.json");
    let after = out_dir.join("after.json");
    let dataset = out_dir.join("dataset.json");

    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--out",
        before.to_str().expect("before path is utf-8"),
    ]);
    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--policy",
        root.join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--runtime-edges",
        root.join("runtime_edges.json")
            .to_str()
            .expect("runtime path is utf-8"),
        "--out",
        after.to_str().expect("after path is utf-8"),
    ]);
    run_sig0(&[
        "dataset",
        "--before",
        before.to_str().expect("before path is utf-8"),
        "--after",
        after.to_str().expect("after path is utf-8"),
        "--pr-metadata",
        root.join("pr_metadata.json")
            .to_str()
            .expect("metadata path is utf-8"),
        "--out",
        dataset.to_str().expect("dataset path is utf-8"),
    ]);

    let json = read_json(&dataset);
    assert_eq!(json["schemaVersion"], "empirical-signature-dataset-v0");
    assert_eq!(
        json["deltaSignatureSigned"]["boundaryViolationCount"],
        Value::Null
    );
    assert_eq!(
        json["deltaSignatureSigned"]["runtimePropagation"],
        Value::Null
    );
    assert_eq!(
        json["metricDeltaStatus"]["boundaryViolationCount"]["comparable"],
        false
    );
    assert_eq!(
        json["analysisMetadata"]["runtimeMetrics"]["runtimeGraphMeasured"],
        true
    );
}

#[test]
fn cli_relation_complexity_fixture_outputs_observation() {
    let root = fixture_root();
    let out_dir = temp_dir("relation");
    let out = out_dir.join("relation-complexity.json");

    run_sig0(&[
        "relation-complexity",
        "--input",
        root.join("relation_complexity_candidates.json")
            .to_str()
            .expect("relation path is utf-8"),
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schemaVersion"], "relation-complexity-observation/v0");
    assert_eq!(json["relationComplexity"], 3);
    assert_eq!(
        json["measurementUniverse"]["ruleSetVersion"],
        "relation-complexity-rules/v0"
    );
}

#[test]
fn cli_validation_warns_for_module_root_import_target() {
    let root = module_root_fixture_root();
    let out_dir = temp_dir("module-root");
    let sig0 = out_dir.join("sig0.json");
    let validation = out_dir.join("sig0-validation.json");

    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "validate",
        "--input",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
        "--universe-mode",
        "local-only",
    ]);

    let json = read_json(&validation);
    assert_eq!(json["summary"]["result"], "warn");
    assert_eq!(json["summary"]["failedCheckCount"], 0);
    assert_eq!(json["summary"]["externalEdgeCount"], 1);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "edge-endpoint-resolved" && check["result"] == "pass")
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "edge-closure-local" && check["result"] == "pass")
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "external-edge-targets"
                    && check["result"] == "warn"
                    && check["count"] == 1
            })
    );
}
