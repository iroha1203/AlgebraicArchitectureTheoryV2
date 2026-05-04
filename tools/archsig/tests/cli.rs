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

fn air_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/air")
}

fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is after unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("archsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temp dir is created");
    dir
}

fn run_sig0(args: &[&str]) {
    let output = run_sig0_output(args);
    assert!(
        output.status.success(),
        "command failed\nstdout:\n{}\nstderr:\n{}",
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
    let contents = fs::read_to_string(path).expect("json output is readable");
    serde_json::from_str(&contents).expect("json output parses")
}

fn runtime_axis_mut(json: &mut Value) -> &mut Value {
    json["signature"]["axes"]
        .as_array_mut()
        .expect("signature axes are an array")
        .iter_mut()
        .find(|axis| axis["axis"] == "runtimePropagation")
        .expect("runtimePropagation axis exists")
}

fn runtime_layer_mut(json: &mut Value) -> &mut Value {
    json["coverage"]["layers"]
        .as_array_mut()
        .expect("coverage layers are an array")
        .iter_mut()
        .find(|layer| layer["layer"] == "runtime")
        .expect("runtime coverage layer exists")
}

fn runtime_claim_mut(json: &mut Value) -> &mut Value {
    json["claims"]
        .as_array_mut()
        .expect("claims are an array")
        .iter_mut()
        .find(|claim| claim["subjectRef"] == "signature.runtimePropagation")
        .expect("runtime claim exists")
}

fn set_measured_runtime_axis(json: &mut Value, runtime_propagation: i64) {
    let measurement_boundary = if runtime_propagation == 0 {
        "measuredZero"
    } else {
        "measuredNonzero"
    };
    let axis = runtime_axis_mut(json);
    axis["value"] = serde_json::json!(runtime_propagation);
    axis["measured"] = serde_json::json!(true);
    axis["measurementBoundary"] = serde_json::json!(measurement_boundary);
    axis["source"] = serde_json::json!("runtime-edge-projection-v0");
    axis["reason"] = Value::Null;

    let layer = runtime_layer_mut(json);
    layer["measurementBoundary"] = serde_json::json!(measurement_boundary);
    layer["universeRefs"] = serde_json::json!(["artifact-sig0"]);
    layer["measuredAxes"] = serde_json::json!(["runtimePropagation"]);
    layer["unmeasuredAxes"] = serde_json::json!([]);
    layer["projectionRule"] = serde_json::json!("runtime-edge-projection-v0");
    layer["extractionScope"] = serde_json::json!([
        "runtime edge evidence JSON",
        "0/1 runtime dependency graph over measured component pairs"
    ]);
    layer["exactnessAssumptions"] = serde_json::json!([
        "runtime-edge-projection-v0 maps each observed component pair to one runtime edge",
        "runtime evidence component ids resolve inside the AIR component universe"
    ]);
    layer["unsupportedConstructs"] = serde_json::json!([]);

    let claim = runtime_claim_mut(json);
    claim["claimId"] = serde_json::json!("claim-runtime-exposure-radius");
    claim["predicate"] =
        serde_json::json!("runtimePropagation is measured runtime exposure radius");
    claim["claimClassification"] = serde_json::json!("measured");
    claim["measurementBoundary"] = serde_json::json!(measurement_boundary);
    claim["evidenceRefs"] = serde_json::json!(["evidence-sig0"]);
    claim["coverageAssumptions"] = serde_json::json!(["runtime edge evidence coverage"]);
    claim["exactnessAssumptions"] = serde_json::json!(["runtime-edge-projection-v0 exactness"]);
    claim["missingPreconditions"] = serde_json::json!([]);
    claim["nonConclusions"] = serde_json::json!([
        "runtime blast radius is not concluded",
        "formal runtime zero bridge is not concluded"
    ]);
}

fn add_runtime_relation(json: &mut Value) {
    json["evidence"]
        .as_array_mut()
        .expect("evidence is an array")
        .push(serde_json::json!({
            "evidenceId": "evidence-runtime-coupon",
            "kind": "runtime_trace",
            "artifactRef": "artifact-sig0",
            "path": "runtime/routes.json",
            "symbol": "userCallsCoupon",
            "line": 17,
            "ruleId": "grpc",
            "confidence": "fixture"
        }));
    json["relations"]
        .as_array_mut()
        .expect("relations are an array")
        .push(serde_json::json!({
            "id": "relation-runtime-coupon",
            "layer": "runtime",
            "from": "UserService",
            "to": "CouponService",
            "kind": "grpc",
            "lifecycle": "added",
            "protectedBy": "unknown",
            "extractionRule": "runtime-edge-projection-v0",
            "evidenceRefs": ["evidence-runtime-coupon"]
        }));
    runtime_claim_mut(json)["evidenceRefs"] =
        serde_json::json!(["evidence-sig0", "evidence-runtime-coupon"]);
}

fn runtime_zero_bridge_claim_json(
    claim_id: &str,
    required_assumptions: Value,
    coverage_assumptions: Value,
    exactness_assumptions: Value,
    missing_preconditions: Value,
) -> Value {
    serde_json::json!({
        "claimId": claim_id,
        "subjectRef": "signature.runtimePropagation",
        "predicate": "runtimePropagation = some 0 discharges bounded runtime exposure obstruction",
        "claimLevel": "formal",
        "claimClassification": "proved",
        "measurementBoundary": "measuredZero",
        "theoremRefs": [
            "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction",
            "ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff",
            "runtimePropagationOfFinite_eq_zero_iff_noSemanticRuntimeExposureObstruction_under_universe"
        ],
        "evidenceRefs": [],
        "requiredAssumptions": required_assumptions,
        "coverageAssumptions": coverage_assumptions,
        "exactnessAssumptions": exactness_assumptions,
        "missingPreconditions": missing_preconditions,
        "nonConclusions": [
            "runtime blast radius is not concluded",
            "runtime telemetry completeness is not concluded"
        ]
    })
}

#[test]
fn cli_feature_report_classifies_good_static_fixture_as_split() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-good");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schemaVersion"], "feature-extension-report-v0");
    assert_eq!(json["architectureId"], "canonical-good-extension");
    assert_eq!(json["splitStatus"], "split");
    assert_eq!(json["reviewSummary"]["claimClassification"], "MEASURED");
    assert!(
        !json["preservedInvariants"]
            .as_array()
            .expect("preserved invariants are an array")
            .is_empty()
    );
    assert!(
        json["introducedObstructionWitnesses"]
            .as_array()
            .expect("witnesses are an array")
            .is_empty()
    );
    assert!(
        json["coverageGaps"]
            .as_array()
            .expect("coverage gaps are an array")
            .iter()
            .any(|gap| gap["layer"] == "runtime" && gap["measurementBoundary"] == "UNMEASURED")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion == "static split does not conclude runtime flatness")
    );
}

#[test]
fn cli_feature_report_surfaces_runtime_exposure_boundaries() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-runtime");

    let mut measured_zero_input = read_json(&root.join("good_extension.json"));
    set_measured_runtime_axis(&mut measured_zero_input, 0);
    let measured_zero_air = out_dir.join("runtime-measured-zero.air.json");
    let measured_zero_report = out_dir.join("runtime-measured-zero.report.json");
    fs::write(
        &measured_zero_air,
        serde_json::to_string_pretty(&measured_zero_input).expect("json serializes"),
    )
    .expect("measured zero AIR is written");
    run_sig0(&[
        "feature-report",
        "--air",
        measured_zero_air.to_str().expect("AIR path is utf-8"),
        "--out",
        measured_zero_report.to_str().expect("report path is utf-8"),
    ]);
    let measured_zero = read_json(&measured_zero_report);
    assert_eq!(measured_zero["runtimeSummary"]["runtimePropagation"], 0);
    assert_eq!(
        measured_zero["runtimeSummary"]["measurementBoundary"],
        "measuredZero"
    );
    assert_eq!(
        measured_zero["runtimeSummary"]["projectionRule"],
        "runtime-edge-projection-v0"
    );
    assert!(
        measured_zero["runtimeSummary"]["measuredAxes"]
            .as_array()
            .expect("runtime measured axes are an array")
            .iter()
            .any(|axis| axis == "runtimePropagation")
    );
    assert!(
        measured_zero["runtimeSummary"]["nonConclusions"]
            .as_array()
            .expect("runtime non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion
                == "runtimePropagation = 0 needs coverage, projection, exactness, and theorem preconditions before a formal claim")
    );

    let mut measured_nonzero_input = read_json(&root.join("good_extension.json"));
    set_measured_runtime_axis(&mut measured_nonzero_input, 2);
    add_runtime_relation(&mut measured_nonzero_input);
    let measured_nonzero_air = out_dir.join("runtime-measured-nonzero.air.json");
    let measured_nonzero_report = out_dir.join("runtime-measured-nonzero.report.json");
    fs::write(
        &measured_nonzero_air,
        serde_json::to_string_pretty(&measured_nonzero_input).expect("json serializes"),
    )
    .expect("measured nonzero AIR is written");
    run_sig0(&[
        "feature-report",
        "--air",
        measured_nonzero_air.to_str().expect("AIR path is utf-8"),
        "--out",
        measured_nonzero_report
            .to_str()
            .expect("report path is utf-8"),
    ]);
    let measured_nonzero = read_json(&measured_nonzero_report);
    assert_eq!(measured_nonzero["runtimeSummary"]["runtimePropagation"], 2);
    assert_eq!(measured_nonzero["runtimeSummary"]["relationCount"], 1);
    assert_eq!(
        measured_nonzero["reviewSummary"]["requiredAction"],
        "review measured runtime exposure radius separately from static split evidence"
    );
    assert!(
        measured_nonzero["runtimeSummary"]["nonConclusions"]
            .as_array()
            .expect("runtime non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion
                == "runtimePropagation is an exposure radius, not runtime blast radius")
    );

    let unmeasured_report = out_dir.join("runtime-unmeasured.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        unmeasured_report.to_str().expect("report path is utf-8"),
    ]);
    let unmeasured = read_json(&unmeasured_report);
    assert_eq!(
        unmeasured["runtimeSummary"]["runtimePropagation"],
        Value::Null
    );
    assert_eq!(
        unmeasured["runtimeSummary"]["measurementBoundary"],
        "unmeasured"
    );
    assert_eq!(
        unmeasured["reviewSummary"]["requiredAction"],
        "add runtime edge evidence before treating runtime risk as zero"
    );
    assert!(
        unmeasured["runtimeSummary"]["coverageGaps"]
            .as_array()
            .expect("runtime coverage gaps are an array")
            .iter()
            .any(|gap| gap == "runtime axis unmeasured: runtimePropagation")
    );
    assert!(
        unmeasured["runtimeSummary"]["nonConclusions"]
            .as_array()
            .expect("runtime non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion
                == "runtimePropagation null is UNMEASURED, not runtime risk zero")
    );
}

#[test]
fn cli_runtime_canonical_fixtures_lock_measurement_boundaries() {
    let root = air_fixture_root();
    let out_dir = temp_dir("runtime-canonical-fixtures");

    let measured_zero_report = out_dir.join("runtime-measured-zero.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("runtime_measured_zero.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        measured_zero_report.to_str().expect("report path is utf-8"),
    ]);
    let measured_zero = read_json(&measured_zero_report);
    assert_eq!(measured_zero["runtimeSummary"]["runtimePropagation"], 0);
    assert_eq!(
        measured_zero["runtimeSummary"]["measurementBoundary"],
        "measuredZero"
    );
    assert_eq!(
        measured_zero["runtimeSummary"]["projectionRule"],
        "runtime-edge-projection-v0"
    );
    assert!(
        measured_zero["theoremPreconditionChecks"]
            .as_array()
            .expect("theorem checks is array")
            .iter()
            .any(|check| check["claimId"] == "claim-runtime-exposure-radius"
                && check["resolvedClaimClassification"] == "MEASURED_WITNESS")
    );

    let measured_nonzero_report = out_dir.join("runtime-measured-nonzero.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("runtime_measured_nonzero.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        measured_nonzero_report
            .to_str()
            .expect("report path is utf-8"),
    ]);
    let measured_nonzero = read_json(&measured_nonzero_report);
    assert_eq!(measured_nonzero["runtimeSummary"]["runtimePropagation"], 2);
    assert_eq!(
        measured_nonzero["runtimeSummary"]["measurementBoundary"],
        "measuredNonzero"
    );
    assert_eq!(measured_nonzero["runtimeSummary"]["relationCount"], 1);
    assert_eq!(
        measured_nonzero["reviewSummary"]["requiredAction"],
        "review measured runtime exposure radius separately from static split evidence"
    );

    let unmeasured_report = out_dir.join("runtime-unmeasured.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("runtime_unmeasured.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        unmeasured_report.to_str().expect("report path is utf-8"),
    ]);
    let unmeasured = read_json(&unmeasured_report);
    assert_eq!(
        unmeasured["runtimeSummary"]["runtimePropagation"],
        Value::Null
    );
    assert_eq!(
        unmeasured["runtimeSummary"]["measurementBoundary"],
        "unmeasured"
    );
    assert!(
        unmeasured["runtimeSummary"]["coverageGaps"]
            .as_array()
            .expect("runtime coverage gaps are an array")
            .iter()
            .any(|gap| gap == "runtime axis unmeasured: runtimePropagation")
    );

    let blocked_report = out_dir.join("runtime-zero-bridge-blocked.check.json");
    run_sig0(&[
        "theorem-check",
        "--air",
        root.join("runtime_zero_bridge_blocked.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        blocked_report.to_str().expect("report path is utf-8"),
    ]);
    let blocked = read_json(&blocked_report);
    assert!(
        blocked["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-runtime-zero-bridge-blocked"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .iter()
                        .any(|precondition| precondition
                            == "runtime projection exactness assumptions are not recorded")
            )
    );
    assert_eq!(blocked["summary"]["formalProvedClaimCount"], 0);
    assert_eq!(blocked["summary"]["blockedClaimCount"], 1);
}

#[test]
fn cli_feature_report_surfaces_static_obstruction_witnesses() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-obstructions");

    for (fixture, expected_kind) in [
        ("hidden_interaction.json", "hidden_interaction"),
        ("policy_violation.json", "policy_violation"),
    ] {
        let report = out_dir.join(format!("{fixture}.report.json"));
        run_sig0(&[
            "feature-report",
            "--air",
            root.join(fixture).to_str().expect("fixture path is utf-8"),
            "--out",
            report.to_str().expect("report path is utf-8"),
        ]);

        let json = read_json(&report);
        assert_eq!(json["splitStatus"], "non_split");
        assert!(
            json["introducedObstructionWitnesses"]
                .as_array()
                .expect("witnesses are an array")
                .iter()
                .any(|witness| witness["kind"] == expected_kind)
        );
    }
}

#[test]
fn cli_feature_report_keeps_unmeasured_extension_unmeasured() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-unmeasured");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("unmeasured_runtime_semantic.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["splitStatus"], "unmeasured");
    assert_eq!(json["reviewSummary"]["claimClassification"], "UNMEASURED");
    assert!(
        json["coverageGaps"]
            .as_array()
            .expect("coverage gaps are an array")
            .iter()
            .any(|gap| gap["measurementBoundary"] == "UNMEASURED")
    );
    assert_eq!(
        json["semanticPathSummary"]["measurementBoundary"],
        "unmeasured"
    );
    assert!(
        json["semanticPathSummary"]["nonConclusions"]
            .as_array()
            .expect("semantic non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion == "unmeasured semantic layer is not measuredZero")
    );
}

#[test]
fn cli_feature_report_surfaces_semantic_nonfillability_witness() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-semantic");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("semantic_nonfillability.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["splitStatus"], "non_split");
    assert_eq!(
        json["semanticPathSummary"]["measurementBoundary"],
        "measuredNonzero"
    );
    assert_eq!(json["semanticPathSummary"]["pathCount"], 2);
    assert_eq!(json["semanticPathSummary"]["diagramCount"], 1);
    assert_eq!(json["semanticPathSummary"]["nonfillabilityWitnessCount"], 1);
    assert!(
        json["semanticPathSummary"]["representativePathIds"]
            .as_array()
            .expect("semantic representative path ids are an array")
            .iter()
            .any(|path_id| path_id == "path-discount-then-coupon")
    );
    assert!(
        json["semanticPathSummary"]["representativeDiagramIds"]
            .as_array()
            .expect("semantic representative diagram ids are an array")
            .iter()
            .any(|diagram_id| diagram_id == "diagram-coupon-discount-order")
    );
    assert!(
        json["semanticPathSummary"]["representativeNonfillabilityWitnessIds"]
            .as_array()
            .expect("semantic representative witness ids are an array")
            .iter()
            .any(|witness_id| witness_id == "witness-rounding-order-difference")
    );
    assert!(
        json["semanticPathSummary"]["evidenceKinds"]
            .as_array()
            .expect("semantic evidence kinds are an array")
            .iter()
            .any(|kind| kind == "observation_result")
    );
    assert!(
        json["semanticPathSummary"]["evidenceKinds"]
            .as_array()
            .expect("semantic evidence kinds are an array")
            .iter()
            .any(|kind| kind == "test")
    );
    assert!(
        json["semanticPathSummary"]["evidenceKinds"]
            .as_array()
            .expect("semantic evidence kinds are an array")
            .iter()
            .any(|kind| kind == "manual_annotation")
    );
    assert!(
        json["semanticPathSummary"]["extractionScope"]
            .as_array()
            .expect("semantic extraction scope is an array")
            .iter()
            .any(|scope| scope == "selected coupon / discount business-flow test")
    );
    assert!(
        json["semanticPathSummary"]["exactnessAssumptions"]
            .as_array()
            .expect("semantic exactness assumptions are an array")
            .iter()
            .any(|assumption| assumption == "fixture records both selected workflow observations")
    );
    assert!(
        json["semanticPathSummary"]["missingPreconditions"]
            .as_array()
            .expect("semantic missing preconditions are an array")
            .iter()
            .any(|precondition| precondition
                == "claim-coupon-discount-filler-blocked: formal filler contract has not been discharged")
    );
    assert!(
        json["semanticPathSummary"]["diagrams"]
            .as_array()
            .expect("semantic diagrams are an array")
            .iter()
            .any(
                |diagram| diagram["diagramId"] == "diagram-coupon-discount-order"
                    && diagram["lhsPathRef"] == "path-discount-then-coupon"
                    && diagram["rhsPathRef"] == "path-coupon-then-discount"
                    && diagram["claimRefs"]
                        .as_array()
                        .expect("semantic diagram claim refs are an array")
                        .iter()
                        .any(|claim_ref| claim_ref == "claim-rounding-order-nonfillability")
                    && diagram["evidence"]
                        .as_array()
                        .expect("semantic diagram evidence is an array")
                        .iter()
                        .any(|evidence| evidence["evidenceRef"] == "evidence-coupon-diagram")
            )
    );
    assert!(
        json["semanticPathSummary"]["nonfillabilityWitnesses"]
            .as_array()
            .expect("semantic nonfillability witnesses are an array")
            .iter()
            .any(|witness| {
                witness["witnessId"] == "witness-rounding-order-difference"
                    && witness["diagramRef"] == "diagram-coupon-discount-order"
                    && witness["measurementBoundary"] == "measuredNonzero"
                    && witness["theoremReference"]
                        .as_array()
                        .expect("semantic witness theorem refs are an array")
                        .iter()
                        .any(|theorem_ref| {
                            theorem_ref == "observationDifference_refutesDiagramFiller"
                        })
            })
    );
    assert!(
        json["introducedObstructionWitnesses"]
            .as_array()
            .expect("witnesses are an array")
            .iter()
            .any(|witness| witness["layer"] == "semantic"
                && witness["nonfillabilityWitnessRef"] == "witness-rounding-order-difference"
                && witness["measurementBoundary"] == "measuredNonzero"
                && witness["paths"]
                    .as_array()
                    .expect("semantic obstruction paths are an array")
                    .iter()
                    .any(|path_ref| path_ref == "path-coupon-then-discount"))
    );
}

#[test]
fn cli_feature_report_surfaces_semantic_measured_zero_boundary() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-semantic-zero");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("semantic_measured_zero.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(
        json["semanticPathSummary"]["measurementBoundary"],
        "measuredZero"
    );
    assert_eq!(json["semanticPathSummary"]["pathCount"], 2);
    assert_eq!(json["semanticPathSummary"]["diagramCount"], 1);
    assert_eq!(json["semanticPathSummary"]["nonfillabilityWitnessCount"], 0);
    assert!(
        json["semanticPathSummary"]["diagrams"]
            .as_array()
            .expect("semantic diagrams are an array")
            .iter()
            .any(
                |diagram| diagram["diagramId"] == "diagram-coupon-discount-commuting-order"
                    && diagram["fillerClaimRef"] == "claim-coupon-discount-commutes"
                    && diagram["nonfillabilityWitnessRefs"]
                        .as_array()
                        .expect("semantic witness refs are an array")
                        .is_empty()
            )
    );
    assert!(
        json["introducedObstructionWitnesses"]
            .as_array()
            .expect("obstruction witnesses are an array")
            .iter()
            .all(|witness| witness["layer"] != "semantic")
    );
}

#[test]
fn cli_feature_report_keeps_semantic_unmeasured_boundary_distinct_from_zero() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-semantic-unmeasured");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("semantic_unmeasured.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(
        json["semanticPathSummary"]["measurementBoundary"],
        "unmeasured"
    );
    assert!(
        json["semanticPathSummary"]["unmeasuredAxes"]
            .as_array()
            .expect("semantic unmeasured axes are an array")
            .iter()
            .any(|axis| axis == "projectionSoundnessViolation")
    );
    assert!(
        json["semanticPathSummary"]["nonConclusions"]
            .as_array()
            .expect("semantic non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion == "semantic risk zero is not concluded")
    );
    assert!(
        json["coverageGaps"]
            .as_array()
            .expect("coverage gaps are an array")
            .iter()
            .any(|gap| gap["layer"] == "semantic" && gap["measurementBoundary"] == "UNMEASURED")
    );
}

#[test]
fn cli_theorem_check_blocks_semantic_formal_claim_without_contract_and_test_evidence() {
    let root = air_fixture_root();
    let out_dir = temp_dir("theorem-check-semantic-blocked");
    let report = out_dir.join("semantic-blocked-theorem-check.json");

    run_sig0(&[
        "theorem-check",
        "--air",
        root.join("semantic_formal_claim_blocked.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-coupon-discount-filler-formal-blocked"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .iter()
                        .any(|precondition| precondition == "contract evidence is absent")
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .iter()
                        .any(|precondition| precondition == "test evidence is absent")
            )
    );
}

#[test]
fn cli_theorem_check_reports_static_registry_and_blocks_missing_preconditions() {
    let root = air_fixture_root();
    let out_dir = temp_dir("theorem-check");
    let input = out_dir.join("static-theorem-claim.json");
    let report = out_dir.join("theorem-check.json");
    let mut json = read_json(&root.join("good_extension.json"));

    let claims = json["claims"].as_array_mut().expect("claims is an array");
    claims.push(serde_json::json!({
        "claimId": "claim-static-split-blocked",
        "subjectRef": "extension.split",
        "predicate": "selected static split theorem package applies",
        "claimLevel": "formal",
        "claimClassification": "proved",
        "measurementBoundary": "measuredZero",
        "theoremRefs": ["SelectedStaticSplitExtension"],
        "evidenceRefs": [],
        "requiredAssumptions": ["core edges are preserved"],
        "coverageAssumptions": ["static graph coverage"],
        "exactnessAssumptions": ["AIR ids match Lean parameters"],
        "missingPreconditions": ["declared interface factorization not discharged"],
        "nonConclusions": ["runtime flatness is not concluded"]
    }));
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("theorem-check input is written");

    run_sig0(&[
        "theorem-check",
        "--air",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(
        report["schemaVersion"],
        "theorem-precondition-check-report-v0"
    );
    assert_eq!(
        report["registry"]["scope"],
        "static, runtime, and semantic theorem package registry v0"
    );
    assert!(
        report["registry"]["packages"][0]["theoremRefs"]
            .as_array()
            .expect("theorem refs is an array")
            .iter()
            .any(|theorem_ref| theorem_ref == "SelectedStaticSplitExtension")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["claimId"] == "claim-static-split-blocked"
                && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["claimId"] == "claim-boundary-zero"
                && check["resolvedClaimClassification"] == "MEASURED_WITNESS")
    );
    assert_eq!(report["summary"]["formalProvedClaimCount"], 0);
}

#[test]
fn cli_theorem_check_reports_semantic_package_boundary() {
    let root = air_fixture_root();
    let out_dir = temp_dir("theorem-check-semantic");
    let input = out_dir.join("semantic-theorem-claims.json");
    let report = out_dir.join("semantic-theorem-check.json");
    let mut json = read_json(&root.join("semantic_nonfillability.json"));

    let claims = json["claims"].as_array_mut().expect("claims is an array");
    claims.push(serde_json::json!({
        "claimId": "claim-rounding-order-nonfillability-proved",
        "subjectRef": "semantic.diagram.diagram-coupon-discount-order",
        "predicate": "selected observation difference refutes the selected diagram filler",
        "claimLevel": "formal",
        "claimClassification": "proved",
        "measurementBoundary": "measuredNonzero",
        "theoremRefs": [
            "observationDifference_refutesDiagramFiller",
            "obstructionAsNonFillability_sound"
        ],
        "evidenceRefs": [
            "evidence-rounding-order",
            "evidence-coupon-flow-test",
            "evidence-coupon-contract",
            "evidence-coupon-diagram"
        ],
        "requiredAssumptions": [
            "selected observations are comparable",
            "selected witness value refutes the diagram filler"
        ],
        "coverageAssumptions": [
            "selected business-flow test covers coupon / discount ordering"
        ],
        "exactnessAssumptions": [
            "fixture records both selected workflow observations"
        ],
        "missingPreconditions": [],
        "nonConclusions": [
            "global semantic flatness is not concluded",
            "business semantics completeness is not concluded"
        ]
    }));
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("semantic theorem-check input is written");

    run_sig0(&[
        "theorem-check",
        "--air",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert!(
        report["registry"]["packages"]
            .as_array()
            .expect("packages is array")
            .iter()
            .any(|package| {
                package["packageId"] == "semantic-nonfillability-package-v0"
                    && package["theoremRefs"]
                        .as_array()
                        .expect("theorem refs is array")
                        .iter()
                        .any(|theorem_ref| {
                            theorem_ref == "observationDifference_refutesDiagramFiller"
                        })
            })
    );
    assert!(
        report["registry"]["packages"]
            .as_array()
            .expect("packages is array")
            .iter()
            .any(|package| {
                let package_id_matches =
                    package["packageId"] == "semantic-numerical-curvature-zero-package-v0";
                let theorem_ref_matches = package["theoremRefs"]
                    .as_array()
                    .expect("theorem refs is array")
                    .iter()
                    .any(|theorem_ref| {
                        theorem_ref
                            == "totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction"
                    });
                package_id_matches && theorem_ref_matches
            })
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-rounding-order-nonfillability"
                    && check["resolvedClaimClassification"] == "MEASURED_WITNESS"
                    && check["applicablePackageRefs"]
                        .as_array()
                        .expect("applicable package refs is array")
                        .iter()
                        .any(|package_ref| package_ref == "semantic-nonfillability-package-v0")
            )
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-coupon-discount-filler-blocked"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
            )
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-rounding-order-nonfillability-proved"
                    && check["resolvedClaimClassification"] == "FORMAL_PROVED"
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .is_empty()
            )
    );
}

#[test]
fn cli_theorem_check_reports_runtime_zero_bridge_boundary() {
    let root = air_fixture_root();
    let out_dir = temp_dir("theorem-check-runtime");
    let input = out_dir.join("runtime-theorem-claims.json");
    let report = out_dir.join("runtime-theorem-check.json");
    let mut json = read_json(&root.join("good_extension.json"));

    set_measured_runtime_axis(&mut json, 0);
    let claims = json["claims"].as_array_mut().expect("claims is an array");
    claims.push(runtime_zero_bridge_claim_json(
        "claim-runtime-zero-bridge-proved",
        serde_json::json!([
            "runtimePropagation is computed over a measured 0/1 RuntimeDependencyGraph"
        ]),
        serde_json::json!(["runtime edge evidence coverage"]),
        serde_json::json!(["runtime-edge-projection-v0 exactness"]),
        serde_json::json!([]),
    ));
    claims.push(runtime_zero_bridge_claim_json(
        "claim-runtime-zero-bridge-blocked",
        serde_json::json!([]),
        serde_json::json!([]),
        serde_json::json!([]),
        serde_json::json!([]),
    ));
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("runtime theorem-check input is written");

    run_sig0(&[
        "theorem-check",
        "--air",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert!(
        report["registry"]["packages"]
            .as_array()
            .expect("packages is array")
            .iter()
            .any(|package| package["packageId"] == "runtime-zero-bridge-package-v0"
                && package["theoremRefs"]
                    .as_array()
                    .expect("theorem refs is array")
                    .iter()
                    .any(|theorem_ref| theorem_ref
                        == "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction"))
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["claimId"] == "claim-runtime-exposure-radius"
                && check["resolvedClaimClassification"] == "MEASURED_WITNESS")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-runtime-zero-bridge-proved"
                    && check["resolvedClaimClassification"] == "FORMAL_PROVED"
                    && check["projectionRule"] == "runtime-edge-projection-v0"
            )
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-runtime-zero-bridge-blocked"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .iter()
                        .any(|precondition| precondition
                            == "runtime coverage assumptions are not recorded")
            )
    );
    assert_eq!(report["summary"]["formalProvedClaimCount"], 1);
    assert_eq!(report["summary"]["blockedClaimCount"], 1);
}

#[test]
fn cli_feature_report_includes_theorem_precondition_checks() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-theorem-check");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["theoremPreconditionSummary"]["checkedClaimCount"], 4);
    assert!(
        json["theoremPreconditionChecks"]
            .as_array()
            .expect("theorem checks is array")
            .iter()
            .any(|check| check["claimId"] == "claim-boundary-zero"
                && check["resolvedClaimClassification"] == "MEASURED_WITNESS")
    );
}

#[test]
fn cli_validate_air_accepts_canonical_fixtures() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-fixtures");
    for fixture in [
        "ai_session_generated_patch.json",
        "ai_session_hidden_complexity_warning.json",
        "ai_session_unreviewed_formal_claim.json",
        "good_extension.json",
        "hidden_interaction.json",
        "policy_violation.json",
        "runtime_measured_zero.json",
        "runtime_measured_nonzero.json",
        "runtime_unmeasured.json",
        "runtime_zero_bridge_blocked.json",
        "semantic_measured_zero.json",
        "semantic_nonfillability.json",
        "semantic_unmeasured.json",
        "semantic_formal_claim_blocked.json",
        "unmeasured_runtime_semantic.json",
    ] {
        let report = out_dir.join(format!("{fixture}.report.json"));
        run_sig0(&[
            "validate-air",
            "--input",
            root.join(fixture).to_str().expect("fixture path is utf-8"),
            "--out",
            report.to_str().expect("report path is utf-8"),
        ]);

        let json = read_json(&report);
        assert_eq!(json["schemaVersion"], "aat-air-validation-report-v0");
        assert_eq!(json["summary"]["result"], "pass");
        assert_eq!(json["summary"]["failedCheckCount"], 0);
    }
}

#[test]
fn cli_feature_report_surfaces_ai_generated_review_warnings_without_obstruction_witnesses() {
    let root = air_fixture_root();
    let out_dir = temp_dir("ai-generated-review-warnings");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("ai_session_hidden_complexity_warning.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    let warnings = json["generatedPatchSummary"]["reviewWarnings"]
        .as_array()
        .expect("review warnings is array");
    let hidden_warning = warnings
        .iter()
        .find(|warning| warning["warningKind"] == "hidden_interaction_candidate")
        .expect("hidden interaction candidate warning is reported");
    assert_eq!(
        hidden_warning["classification"],
        "conservative_review_signal"
    );
    assert_eq!(hidden_warning["measurementBoundary"], "unmeasured");
    assert!(
        hidden_warning["relations"]
            .as_array()
            .expect("hidden warning relations is array")
            .iter()
            .any(|relation| relation["relationId"] == "relation-static-coupon-cache")
    );
    assert!(
        hidden_warning["nonConclusions"]
            .as_array()
            .expect("hidden warning non-conclusions is array")
            .iter()
            .any(|conclusion| conclusion
                == "hidden interaction candidate is not a measured hidden_interaction witness")
    );

    let complexity_warning = warnings
        .iter()
        .find(|warning| warning["warningKind"] == "complexity_transfer_warning")
        .expect("complexity transfer warning is reported");
    assert_eq!(
        complexity_warning["classification"],
        "conservative_review_signal"
    );
    assert_eq!(complexity_warning["measurementBoundary"], "measuredNonzero");
    assert!(
        json["complexityTransferCandidates"]
            .as_array()
            .expect("complexity candidates is array")
            .iter()
            .any(|candidate| candidate
                .as_str()
                .expect("candidate is a string")
                .contains("warning-ai-generated-relation-complexity-transfer"))
    );
    assert!(
        json["introducedObstructionWitnesses"]
            .as_array()
            .expect("obstruction witnesses is array")
            .is_empty()
    );
}

#[test]
fn cli_ai_session_human_review_blocks_formal_claim_promotion() {
    let root = air_fixture_root();
    let out_dir = temp_dir("ai-session-human-review");
    let theorem_report = out_dir.join("theorem-check.json");
    let feature_report = out_dir.join("feature-report.json");

    run_sig0(&[
        "theorem-check",
        "--air",
        root.join("ai_session_unreviewed_formal_claim.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        theorem_report.to_str().expect("report path is utf-8"),
    ]);
    let theorem = read_json(&theorem_report);
    assert_eq!(theorem["summary"]["result"], "warn");
    assert_eq!(theorem["summary"]["formalProvedClaimCount"], 0);
    assert_eq!(theorem["summary"]["blockedClaimCount"], 1);
    assert!(
        theorem["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-ai-generated-static-split"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
                    && check["reason"]
                        == "AI session human review boundary blocks formal claim promotion"
                    && check["missingPreconditions"]
                        .as_array()
                        .expect("missing preconditions is array")
                        .iter()
                        .any(|precondition| precondition
                            == "AI session human review is required before promoting formal claim")
            )
    );

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("ai_session_unreviewed_formal_claim.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        feature_report.to_str().expect("report path is utf-8"),
    ]);
    let feature = read_json(&feature_report);
    assert_eq!(
        feature["reviewSummary"]["requiredAction"],
        "complete human review before promoting AI-generated formal claims"
    );
    assert!(
        feature["undischargedAssumptions"]
            .as_array()
            .expect("undischarged assumptions is array")
            .iter()
            .any(|assumption| assumption
                == "claim-ai-generated-static-split: AI session human review is required before promoting formal claim")
    );
    assert!(
        feature["theoremPreconditionChecks"]
            .as_array()
            .expect("theorem checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-ai-generated-static-split"
                    && check["resolvedClaimClassification"] == "BLOCKED_FORMAL_CLAIM"
            )
    );
}

#[test]
fn cli_feature_report_traces_generated_patch_architecture_operations() {
    let root = air_fixture_root();
    let out_dir = temp_dir("generated-patch-operations");
    let report = out_dir.join("feature-report.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("ai_session_generated_patch.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&report);
    let summary = &json["generatedPatchSummary"];
    assert_eq!(summary["isAiSession"], true);
    assert_eq!(summary["generatedPatch"], true);
    assert_eq!(summary["humanReviewed"], false);
    assert!(
        summary["artifactRefs"]
            .as_array()
            .expect("artifact refs is array")
            .iter()
            .any(|artifact_ref| artifact_ref == "artifact-generated-patch")
    );
    assert!(
        summary["evidence"]
            .as_array()
            .expect("generated patch evidence is array")
            .iter()
            .any(
                |evidence| evidence["evidenceRef"] == "evidence-generated-patch"
                    && evidence["kind"] == "generated_patch"
                    && evidence["artifactRef"] == "artifact-generated-patch"
            )
    );

    let operation = summary["operations"]
        .as_array()
        .expect("operations is array")
        .iter()
        .find(|operation| {
            operation["operationRef"]
                == "generated_patch artifact-generated-patch adds relation-static-coupon-port"
        })
        .expect("generated patch operation is reported");
    assert!(
        operation["addedComponents"]
            .as_array()
            .expect("added components is array")
            .iter()
            .any(|component| component == "CouponPort")
    );
    assert!(
        operation["addedComponents"]
            .as_array()
            .expect("added components is array")
            .iter()
            .any(|component| component == "CouponService")
    );
    assert!(
        operation["addedRelations"]
            .as_array()
            .expect("added relations is array")
            .iter()
            .any(
                |relation| relation["relationId"] == "relation-static-coupon-port"
                    && relation["from"] == "UserService"
                    && relation["to"] == "CouponPort"
                    && relation["kind"] == "import"
            )
    );
    assert!(
        operation["evidence"]
            .as_array()
            .expect("operation evidence is array")
            .iter()
            .any(|evidence| evidence["evidenceRef"] == "evidence-generated-patch")
    );
    assert!(
        summary["nonConclusions"]
            .as_array()
            .expect("non conclusions is array")
            .iter()
            .any(|conclusion| conclusion
                == "generated patch summary identifies architecture extension locations, not patch size")
    );
}

#[test]
fn cli_validate_air_detects_ai_session_metadata_inconsistency() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-ai-session-invalid");
    let input = out_dir.join("invalid-ai-session-air.json");
    let report = out_dir.join("invalid-ai-session-air-report.json");
    let mut json = read_json(&root.join("ai_session_generated_patch.json"));

    json["feature"]["aiSession"]["provider"] = serde_json::json!("");
    json["feature"]["aiSession"]["generatedPatch"] = serde_json::json!(false);
    json["artifacts"]
        .as_array_mut()
        .expect("artifacts is an array")
        .retain(|artifact| artifact["kind"] != "generated_patch");
    json["operationTrace"]["operations"] = serde_json::json!([]);
    json["claims"][0]["evidenceRefs"] = serde_json::json!(["evidence-generated-patch"]);
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("invalid AI session AIR is written");

    let output = run_sig0_output(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    assert!(
        !output.status.success(),
        "invalid AI session AIR should fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-ai-session-metadata-consistent"
                && check["result"] == "fail")
    );
}

#[test]
fn cli_validate_air_detects_dangling_refs_and_boundary_mismatch() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-invalid");
    let input = out_dir.join("invalid-air.json");
    let report = out_dir.join("invalid-air-report.json");
    let mut json = read_json(&root.join("good_extension.json"));

    json["relations"][0]["to"] = serde_json::json!("MissingComponent");
    json["claims"][0]["measurementBoundary"] = serde_json::json!("unmeasured");
    json["extension"]["interactionClaimRefs"] = serde_json::json!(["claim-missing"]);
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("invalid AIR is written");

    let output = run_sig0_output(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    assert!(
        !output.status.success(),
        "invalid AIR should fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-component-refs-resolved" && check["result"] == "fail")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "air-claim-boundary-compatible" && check["result"] == "fail"
            )
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-claim-refs-resolved" && check["result"] == "fail")
    );
}

#[test]
fn cli_validate_air_detects_runtime_metadata_inconsistency() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-runtime-invalid");
    let input = out_dir.join("invalid-runtime-air.json");
    let report = out_dir.join("invalid-runtime-air-report.json");
    let mut json = read_json(&root.join("good_extension.json"));

    json["relations"]
        .as_array_mut()
        .expect("relations is an array")
        .push(serde_json::json!({
            "id": "relation-runtime-invalid",
            "layer": "runtime",
            "from": "UserService",
            "to": "CouponService",
            "kind": "grpc",
            "lifecycle": "added",
            "protectedBy": null,
            "extractionRule": null,
            "evidenceRefs": []
        }));
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("invalid runtime AIR is written");

    let output = run_sig0_output(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    assert!(
        !output.status.success(),
        "invalid runtime AIR should fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-runtime-metadata-consistent"
                && check["result"] == "fail")
    );
}

#[test]
fn cli_validate_air_detects_semantic_metadata_inconsistency() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-semantic-invalid");
    let input = out_dir.join("invalid-semantic-air.json");
    let report = out_dir.join("invalid-semantic-air-report.json");
    let mut json = read_json(&root.join("semantic_nonfillability.json"));

    json["semanticDiagrams"][0]["lifecycle"] = serde_json::json!("maybe");
    json["semanticDiagrams"][0]["observationRefs"] = serde_json::json!(["evidence-missing"]);
    json["coverage"]["layers"][0]["measurementBoundary"] = serde_json::json!("unmeasured");
    json["coverage"]["layers"][0]["measuredAxes"] =
        serde_json::json!(["projectionSoundnessViolation"]);
    json["claims"][0]["measurementBoundary"] = serde_json::json!("unmeasured");
    json["evidence"][0]["kind"] = serde_json::json!("unknown_semantic_evidence");
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("invalid semantic AIR is written");

    let output = run_sig0_output(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    assert!(
        !output.status.success(),
        "invalid semantic AIR should fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-semantic-metadata-consistent"
                && check["result"] == "fail")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-evidence-kind-supported" && check["result"] == "fail")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-evidence-refs-resolved" && check["result"] == "fail")
    );
}

#[test]
fn cli_validate_air_can_escalate_missing_measured_evidence_to_failure() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-strict");
    let input = out_dir.join("missing-evidence-air.json");
    let warn_report = out_dir.join("warn-report.json");
    let strict_report = out_dir.join("strict-report.json");
    let mut json = read_json(&root.join("good_extension.json"));

    json["claims"][0]["evidenceRefs"] = serde_json::json!([]);
    fs::write(
        &input,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("AIR with missing measured evidence is written");

    run_sig0(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        warn_report.to_str().expect("warn report path is utf-8"),
    ]);
    let warn = read_json(&warn_report);
    assert_eq!(warn["summary"]["result"], "warn");
    assert!(
        warn["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-measured-claims-have-evidence"
                && check["result"] == "warn")
    );

    let output = run_sig0_output(&[
        "validate-air",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--strict-measured-evidence",
        "--out",
        strict_report.to_str().expect("strict report path is utf-8"),
    ]);
    assert!(!output.status.success(), "strict validation should fail");
    let strict = read_json(&strict_report);
    assert_eq!(strict["summary"]["result"], "fail");
    assert!(
        strict["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-measured-claims-have-evidence"
                && check["result"] == "fail")
    );
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
    assert_eq!(json["schemaVersion"], "archsig-sig0-v0");
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
fn cli_air_normalizes_sig0_validation_and_pr_metadata() {
    let root = fixture_root();
    let out_dir = temp_dir("air");
    let sig0 = out_dir.join("sig0.json");
    let validation = out_dir.join("validation.json");
    let air = out_dir.join("air.json");
    let air_validation = out_dir.join("air-validation.json");

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
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "validate",
        "--input",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    run_sig0(&[
        "air",
        "--sig0",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--validation",
        validation.to_str().expect("validation path is utf-8"),
        "--pr-metadata",
        root.join("pr_metadata.json")
            .to_str()
            .expect("metadata path is utf-8"),
        "--law-policy",
        root.join("policy_measured_zero.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);

    let json = read_json(&air);
    assert_eq!(json["schemaVersion"], "aat-air-v0");
    assert_eq!(json["feature"]["featureId"], "#42");
    assert_eq!(json["revision"]["before"], "base-sha");
    assert_eq!(json["revision"]["after"], "head-sha");
    assert!(
        json["relations"]
            .as_array()
            .expect("relations is array")
            .iter()
            .any(|relation| relation["layer"] == "static" && relation["kind"] == "import")
    );
    assert!(
        json["relations"]
            .as_array()
            .expect("relations is array")
            .iter()
            .any(|relation| {
                relation["layer"] == "runtime"
                    && relation["kind"] == "grpc"
                    && relation["extractionRule"] == "runtime-edge-projection-v0"
                    && !relation["evidenceRefs"]
                        .as_array()
                        .expect("evidenceRefs is array")
                        .is_empty()
            })
    );
    let runtime_coverage = json["coverage"]["layers"]
        .as_array()
        .expect("coverage layers is array")
        .iter()
        .find(|layer| layer["layer"] == "runtime")
        .expect("runtime coverage layer");
    assert_eq!(
        runtime_coverage["projectionRule"],
        "runtime-edge-projection-v0"
    );
    assert_eq!(runtime_coverage["measurementBoundary"], "measuredNonzero");
    assert!(
        runtime_coverage["measuredAxes"]
            .as_array()
            .expect("measuredAxes is array")
            .iter()
            .any(|axis| axis == "runtimePropagation")
    );
    assert!(
        !runtime_coverage["extractionScope"]
            .as_array()
            .expect("extractionScope is array")
            .is_empty()
    );
    assert!(
        !runtime_coverage["exactnessAssumptions"]
            .as_array()
            .expect("exactnessAssumptions is array")
            .is_empty()
    );
    assert!(
        runtime_coverage["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is array")
            .is_empty()
    );
    assert!(
        json["signature"]["axes"]
            .as_array()
            .expect("axes is array")
            .iter()
            .any(|axis| {
                axis["axis"] == "boundaryViolationCount"
                    && axis["measurementBoundary"] == "measuredZero"
            })
    );
    assert!(
        json["signature"]["axes"]
            .as_array()
            .expect("axes is array")
            .iter()
            .any(|axis| {
                axis["axis"] == "runtimePropagation"
                    && axis["measurementBoundary"] == "measuredNonzero"
            })
    );
    assert_eq!(json["extension"]["splitStatus"], "unmeasured");
    assert!(
        json["claims"]
            .as_array()
            .expect("claims is array")
            .iter()
            .any(|claim| {
                claim["claimId"] == "claim-axis-boundaryviolationcount"
                    && claim["claimClassification"] == "measured"
            })
    );

    run_sig0(&[
        "validate-air",
        "--input",
        air.to_str().expect("air path is utf-8"),
        "--out",
        air_validation
            .to_str()
            .expect("air validation path is utf-8"),
    ]);
    let validation = read_json(&air_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| check["id"] == "air-runtime-metadata-consistent"
                && check["result"] == "pass")
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
    let peer_pr_metadata = out_dir.join("peer-pr-metadata.json");
    let report = out_dir.join("signature-diff.json");
    let air = out_dir.join("air.json");

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
    fs::write(
        &peer_pr_metadata,
        serde_json::json!({
            "repository": {
                "owner": "example",
                "name": "service",
                "defaultBranch": "main"
            },
            "pullRequest": {
                "number": 78,
                "author": "bob",
                "createdAt": "2026-04-25T02:00:00Z",
                "mergedAt": "2026-04-26T00:30:00Z",
                "baseCommit": "before-sha",
                "headCommit": "peer-sha",
                "mergeCommit": null,
                "labels": [],
                "isBotGenerated": false
            },
            "prMetrics": {
                "changedFiles": 1,
                "changedLinesAdded": 2,
                "changedLinesDeleted": 0,
                "changedComponents": ["Formal.Arch.B"],
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
    .expect("peer PR metadata is written");

    run_sig0(&[
        "diff",
        "--before",
        before_snapshot
            .to_str()
            .expect("before snapshot path is utf-8"),
        "--after",
        after_snapshot
            .to_str()
            .expect("after snapshot path is utf-8"),
        "--before-sig0",
        before_sig0.to_str().expect("before sig0 path is utf-8"),
        "--after-sig0",
        after_sig0.to_str().expect("after sig0 path is utf-8"),
        "--pr-metadata",
        pr_metadata.to_str().expect("PR metadata path is utf-8"),
        "--pr-metadata",
        peer_pr_metadata
            .to_str()
            .expect("peer PR metadata path is utf-8"),
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
    assert_eq!(
        json["attribution"]["candidates"][0]["confidenceLevel"],
        "high"
    );
    assert_eq!(
        json["attribution"]["candidates"][0]["matchedEdges"][0]["target"],
        "Formal.Arch.C"
    );
    assert!(
        !json["attribution"]["candidates"][0]["affectedAxes"]
            .as_array()
            .expect("affectedAxes is array")
            .is_empty()
    );
    assert!(
        !json["attribution"]["sharedWorsenedAxes"]
            .as_array()
            .expect("sharedWorsenedAxes is array")
            .is_empty()
    );

    run_sig0(&[
        "air",
        "--sig0",
        after_sig0.to_str().expect("after sig0 path is utf-8"),
        "--validation",
        after_validation
            .to_str()
            .expect("after validation path is utf-8"),
        "--diff",
        report.to_str().expect("diff report path is utf-8"),
        "--pr-metadata",
        pr_metadata.to_str().expect("PR metadata path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);

    let json = read_json(&air);
    assert_eq!(json["revision"]["before"], "before-sha");
    assert_eq!(json["revision"]["after"], "after-sha");
    assert!(
        json["components"]
            .as_array()
            .expect("components is array")
            .iter()
            .any(|component| {
                component["id"] == "Formal.Arch.C" && component["lifecycle"] == "added"
            })
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
