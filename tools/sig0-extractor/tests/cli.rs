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
fn cli_pr_metadata_generates_dataset_input_from_github_json() {
    let root = fixture_root();
    let out_dir = temp_dir("pr-metadata");
    let out = out_dir.join("pr_metadata.json");
    let out_without_reviews = out_dir.join("pr_metadata_without_reviews.json");

    run_sig0(&[
        "pr-metadata",
        "--pull-request",
        root.join("github_pr.json")
            .to_str()
            .expect("pull request path is utf-8"),
        "--files",
        root.join("github_files.json")
            .to_str()
            .expect("files path is utf-8"),
        "--reviews",
        root.join("github_reviews.json")
            .to_str()
            .expect("reviews path is utf-8"),
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["repository"]["owner"], "example");
    assert_eq!(json["pullRequest"]["number"], 42);
    assert_eq!(json["pullRequest"]["author"], "dependabot[bot]");
    assert_eq!(json["pullRequest"]["isBotGenerated"], true);
    assert_eq!(
        json["prMetrics"]["changedComponents"],
        serde_json::json!(["Formal", "Formal.Arch.A"])
    );
    assert_eq!(json["prMetrics"]["reviewRoundCount"], 1);
    assert_eq!(json["prMetrics"]["firstReviewLatencyHours"], 2.0);
    assert_eq!(json["prMetrics"]["approvalLatencyHours"], Value::Null);
    assert_eq!(json["prMetrics"]["mergeLatencyHours"], 36.0);

    run_sig0(&[
        "pr-metadata",
        "--pull-request",
        root.join("github_pr.json")
            .to_str()
            .expect("pull request path is utf-8"),
        "--files",
        root.join("github_files.json")
            .to_str()
            .expect("files path is utf-8"),
        "--out",
        out_without_reviews.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out_without_reviews);
    assert_eq!(json["prMetrics"]["reviewRoundCount"], 0);
    assert_eq!(json["prMetrics"]["firstReviewLatencyHours"], Value::Null);
    assert_eq!(json["prMetrics"]["approvalLatencyHours"], Value::Null);
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
fn cli_snapshot_diff_reports_axes_evidence_and_pr_attribution() {
    let fixture = fixture_root();
    let repo = temp_dir("snapshot-repo");
    fs::create_dir_all(repo.join("Formal/Arch")).expect("fixture directories are created");
    fs::write(
        repo.join("Formal.lean"),
        "import Formal.Arch.A\nimport Formal.Arch.B\n",
    )
    .expect("before root file is written");
    fs::write(
        repo.join("Formal/Arch/A.lean"),
        "namespace Formal.Arch\n\ndef fixtureA : Nat := 0\n\nend Formal.Arch\n",
    )
    .expect("A file is written");
    fs::write(
        repo.join("Formal/Arch/B.lean"),
        "import Formal.Arch.A\n\nnamespace Formal.Arch\n\ndef fixtureB : Nat := fixtureA + 1\n\nend Formal.Arch\n",
    )
    .expect("B file is written");

    let out_dir = temp_dir("snapshot-diff");
    let before_sig0 = out_dir.join("before-sig0.json");
    let before_validation = out_dir.join("before-validation.json");
    let before_snapshot = out_dir.join("before-snapshot.json");
    let after_sig0 = out_dir.join("after-sig0.json");
    let after_validation = out_dir.join("after-validation.json");
    let after_snapshot = out_dir.join("after-snapshot.json");
    let pr_metadata = out_dir.join("pr-metadata.json");
    let report = out_dir.join("signature-diff.json");

    run_sig0(&[
        "--root",
        repo.to_str().expect("repo path is utf-8"),
        "--policy",
        fixture
            .join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        before_sig0.to_str().expect("before sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "validate",
        "--input",
        before_sig0
            .to_str()
            .expect("before validation input path is utf-8"),
        "--out",
        before_validation
            .to_str()
            .expect("before validation path is utf-8"),
    ]);
    run_sig0(&[
        "snapshot",
        "--input",
        before_sig0.to_str().expect("before sig0 path is utf-8"),
        "--validation-report",
        before_validation
            .to_str()
            .expect("before validation path is utf-8"),
        "--repo-owner",
        "example",
        "--repo-name",
        "service",
        "--revision-sha",
        "before-sha",
        "--scanned-at",
        "2026-04-26T00:00:00Z",
        "--policy-path",
        fixture
            .join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        before_snapshot
            .to_str()
            .expect("before snapshot path is utf-8"),
    ]);

    fs::write(
        repo.join("Formal.lean"),
        "import Formal.Arch.A\nimport Formal.Arch.B\nimport Formal.Arch.C\n",
    )
    .expect("after root file is written");
    fs::write(
        repo.join("Formal/Arch/C.lean"),
        "import Formal.Arch.B\n\nnamespace Formal.Arch\n\ndef fixtureC : Nat := fixtureB + 1\n\nend Formal.Arch\n",
    )
    .expect("C file is written");
    run_sig0(&[
        "--root",
        repo.to_str().expect("repo path is utf-8"),
        "--policy",
        fixture
            .join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        after_sig0.to_str().expect("after sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "validate",
        "--input",
        after_sig0
            .to_str()
            .expect("after validation input path is utf-8"),
        "--out",
        after_validation
            .to_str()
            .expect("after validation path is utf-8"),
    ]);
    run_sig0(&[
        "snapshot",
        "--input",
        after_sig0.to_str().expect("after sig0 path is utf-8"),
        "--validation-report",
        after_validation
            .to_str()
            .expect("after validation path is utf-8"),
        "--repo-owner",
        "example",
        "--repo-name",
        "service",
        "--revision-sha",
        "after-sha",
        "--scanned-at",
        "2026-04-26T01:00:00Z",
        "--policy-path",
        fixture
            .join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        after_snapshot
            .to_str()
            .expect("after snapshot path is utf-8"),
    ]);

    fs::write(
        &pr_metadata,
        serde_json::json!({
            "repository": {
                "owner": "example",
                "name": "service",
                "defaultBranch": "main"
            },
            "pullRequest": {
                "number": 77,
                "author": "alice",
                "createdAt": "2026-04-25T00:00:00Z",
                "mergedAt": "2026-04-26T01:30:00Z",
                "baseCommit": "before-sha",
                "headCommit": "after-sha",
                "mergeCommit": null,
                "labels": [],
                "isBotGenerated": false
            },
            "prMetrics": {
                "changedFiles": 2,
                "changedLinesAdded": 4,
                "changedLinesDeleted": 0,
                "changedComponents": ["Formal", "Formal.Arch.C"],
                "reviewCommentCount": 0,
                "reviewThreadCount": 0,
                "reviewRoundCount": 0,
                "firstReviewLatencyHours": null,
                "approvalLatencyHours": null,
                "mergeLatencyHours": null
            }
        })
        .to_string(),
    )
    .expect("PR metadata is written");

    run_sig0(&[
        "signature-diff",
        "--before-snapshot",
        before_snapshot
            .to_str()
            .expect("before snapshot path is utf-8"),
        "--after-snapshot",
        after_snapshot
            .to_str()
            .expect("after snapshot path is utf-8"),
        "--before-sig0",
        before_sig0.to_str().expect("before sig0 path is utf-8"),
        "--after-sig0",
        after_sig0.to_str().expect("after sig0 path is utf-8"),
        "--pr-metadata",
        pr_metadata.to_str().expect("PR metadata path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "signature-diff-report-v0");
    assert_eq!(json["comparisonStatus"]["primaryDiffEligible"], true);
    assert!(
        json["worsenedAxes"]
            .as_array()
            .expect("worsenedAxes is array")
            .iter()
            .any(|axis| axis["delta"].as_i64().expect("delta is integer") > 0)
    );
    assert_eq!(
        json["evidenceDiff"]["componentDelta"]["added"],
        serde_json::json!(["Formal.Arch.C"])
    );
    assert_eq!(json["attribution"]["candidates"][0]["id"], "#77");
    assert!(
        json["attribution"]["candidates"][0]["confidence"]
            .as_f64()
            .expect("confidence is number")
            > 0.5
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
