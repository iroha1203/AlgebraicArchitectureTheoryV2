use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal")
}

#[test]
fn cli_intentmap_alignment_forecast_and_calibration_workflow() {
    let root = fixture_root();
    let out_dir = temp_dir("intentmap-alignment-workflow");
    let intent_fixture = root.join("intentmap.json");
    let alignment_fixture = root.join("intent_archmap_alignment.json");
    let archmap_fixture = root.join("archmap.json");
    let intent_validation = out_dir.join("intentmap-validation.json");
    let alignment_validation = out_dir.join("alignment-validation.json");
    let forecast_dir = out_dir.join("forecast");
    let pr_quality_validation = out_dir.join("pr-quality-validation.json");
    let calibration_validation = out_dir.join("intent-calibration-validation.json");

    run_sig0(&[
        "intent-map",
        "--input",
        intent_fixture
            .to_str()
            .expect("intent fixture path is utf-8"),
        "--out",
        intent_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    let intent_json = read_json(&intent_validation);
    assert_eq!(intent_json["schema"], "intentmap-validation-report/v0.5.0");
    assert_eq!(intent_json["summary"]["result"], "pass");
    assert!(
        intent_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| check["id"] == "intentmap-boundaries-first-class")
    );
    assert!(
        intent_json["intentMap"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions are array")
            .iter()
            .any(|entry| {
                entry == "IntentMap does not provide an implementation plan completeness guarantee"
            })
    );

    run_sig0(&[
        "intent-archmap-alignment",
        "--input",
        alignment_fixture
            .to_str()
            .expect("alignment fixture path is utf-8"),
        "--intent-map",
        intent_fixture
            .to_str()
            .expect("intent fixture path is utf-8"),
        "--archmap",
        archmap_fixture
            .to_str()
            .expect("archmap fixture path is utf-8"),
        "--out",
        alignment_validation
            .to_str()
            .expect("alignment validation path is utf-8"),
    ]);
    let alignment_json = read_json(&alignment_validation);
    assert_eq!(
        alignment_json["schema"],
        "intent-archmap-alignment-validation-report/v0.5.0"
    );
    assert_eq!(alignment_json["summary"]["result"], "pass");
    assert!(
        alignment_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| {
                check["id"] == "intent-archmap-alignment-boundaries-not-measured-zero"
            })
    );

    run_sig0(&[
        "intent-forecast",
        "--intent-map",
        intent_fixture
            .to_str()
            .expect("intent fixture path is utf-8"),
        "--archmap",
        archmap_fixture
            .to_str()
            .expect("archmap fixture path is utf-8"),
        "--alignment",
        alignment_fixture
            .to_str()
            .expect("alignment fixture path is utf-8"),
        "--out-dir",
        forecast_dir.to_str().expect("forecast dir is utf-8"),
    ]);
    let estimate = read_json(&forecast_dir.join("operation-support-estimate.json"));
    assert_eq!(estimate["schema"], "operation-support-estimate/v0.5.0");
    assert_eq!(
        estimate["descriptorRef"]["descriptorSchemaVersion"],
        "intent-archmap-alignment/v0.5.0"
    );
    assert!(
        estimate["unknownRemainder"][0]["unknownAxes"]
            .as_array()
            .expect("unknown axes are array")
            .iter()
            .any(|axis| {
                axis.as_str()
                    .expect("axis is string")
                    .contains("coupons may stack")
            })
    );
    let cone = read_json(&forecast_dir.join("forecast-cone-skeleton.json"));
    assert_eq!(cone["schema"], "forecast-cone-skeleton/v0.5.0");
    assert!(
        cone["nonConclusions"]
            .as_array()
            .expect("forecast nonConclusions are array")
            .iter()
            .any(|entry| entry == "forecast cone skeleton does not assign probabilities")
    );

    run_sig0(&[
        "pr-quality-analysis",
        "--input",
        root.join("pr_quality_analysis_report.json")
            .to_str()
            .expect("PR quality fixture path is utf-8"),
        "--out",
        pr_quality_validation
            .to_str()
            .expect("PR quality validation path is utf-8"),
    ]);
    let pr_quality = read_json(&pr_quality_validation);
    assert_eq!(
        pr_quality["schema"],
        "pr-quality-analysis-validation-report/v0.5.0"
    );
    assert_eq!(pr_quality["summary"]["result"], "pass");
    assert!(
        pr_quality["report"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions are array")
            .iter()
            .any(|entry| entry
                == "PR quality analysis is reviewer-facing evidence, not merge approval")
    );

    run_sig0(&[
        "intent-calibration-record",
        "--input",
        root.join("intent_calibration_record.json")
            .to_str()
            .expect("calibration fixture path is utf-8"),
        "--out",
        calibration_validation
            .to_str()
            .expect("calibration validation path is utf-8"),
    ]);
    let calibration = read_json(&calibration_validation);
    assert_eq!(
        calibration["schema"],
        "intent-calibration-validation-report/v0.5.0"
    );
    assert_eq!(calibration["summary"]["result"], "pass");
    assert!(
        calibration["record"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions are array")
            .iter()
            .any(|entry| entry
                == "intent calibration record is empirical feedback, not causal proof")
    );
}

#[test]
fn cli_emits_and_validates_aat_observable_bundle() {
    let out_dir = temp_dir("aat-observable-bundle");
    let bundle = out_dir.join("aat-observable-bundle.json");
    let validation = out_dir.join("aat-observable-bundle-validation.json");
    let canonical_fixture = fixture_root().join("aat_observable_bundle.json");

    run_sig0(&[
        "aat-observable-bundle",
        "--fixture",
        "--out",
        bundle.to_str().expect("bundle path is utf-8"),
    ]);
    let bundle_json = read_json(&bundle);
    assert_eq!(bundle_json["schema"], "aat-observable-bundle/v0.5.0");
    assert!(
        bundle_json["conceptMappings"]
            .as_array()
            .expect("concept mappings are array")
            .len()
            >= 10
    );
    assert!(
        bundle_json["conceptMappings"]
            .as_array()
            .expect("concept mappings are array")
            .iter()
            .any(|entry| entry["aatConcept"] == "ArchitectureObject / ComponentUniverse")
    );
    assert!(
        bundle_json["selectedUniverse"]["unavailableRefs"]
            .as_array()
            .expect("unavailable refs are array")
            .iter()
            .any(|entry| entry == "runtime:production-traces")
    );
    assert!(
        bundle_json["llmReviewSurface"]["reviewQuestions"]
            .as_array()
            .expect("review questions are array")
            .iter()
            .any(|entry| entry
                .as_str()
                .expect("review question is string")
                .contains("obstruction witnesses"))
    );

    run_sig0(&[
        "aat-observable-bundle",
        "--input",
        canonical_fixture
            .to_str()
            .expect("canonical bundle path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schema"],
        "aat-observable-bundle-validation-report/v0.5.0"
    );
    assert_eq!(validation_json["summary"]["result"], "pass");
    assert!(
        validation_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| check["id"] == "aat-observable-responsibility-boundary")
    );
    assert!(
        validation_json["bundle"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions are array")
            .iter()
            .any(|entry| entry == "unmeasured is not measured zero")
    );
}

fn expressiveness_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/expressiveness")
}

fn module_root_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/module_root")
}

fn air_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/air")
}

fn python_fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/python_imports")
}

fn python_framework_adapter_fixture() -> PathBuf {
    python_fixture_root().join("framework_adapter.json")
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
    Command::new(env!("CARGO_BIN_EXE_fieldsig"))
        .args(args)
        .output()
        .expect("fieldsig command runs")
}

fn read_json(path: &Path) -> Value {
    let contents = fs::read_to_string(path).expect("json output is readable");
    serde_json::from_str(&contents).expect("json output parses")
}

#[test]
fn cli_projects_archsig_measurement_packet_to_sft_input_boundary() {
    let out_dir = temp_dir("archsig-measurement-sft-input");
    let packet = out_dir.join("archsig-measurement-packet.json");
    let estimate = out_dir.join("operation-support-estimate.json");
    let estimate_validation = out_dir.join("operation-support-estimate-validation.json");
    let packet_json = serde_json::json!({
        "schema": "archsig-measurement-packet/v0.5.0",
        "packetId": "measurement:test-handoff",
        "profile": {
            "schema": "measurement-profile/v0.5.0",
            "profileId": "profile:test-handoff",
            "siteRef": "archmap:/contexts",
            "coverRef": "cover:test",
            "coefficient": "F2",
            "effCoeff": "finite-linear-algebra@1",
            "witnessFamily": [],
            "resolutionSelector": "cech@1",
            "domain": "finite-poset-site",
            "zeroPredicate": "rank-zero@1",
            "nonZeroPredicate": "rank-positive@1",
            "certSelector": "finite-certificate@1",
            "verdictDiscipline": "five-valued-structural-verdict@1"
        },
        "structuralVerdict": [{
            "verdictRef": "structuralVerdict/ag-cech-obstruction/ag-cech-obstruction/computed",
            "evaluator": "ag.cech-obstruction",
            "law": "ag.cech-obstruction",
            "target": {
                "kind": "cover-relative-cech-h1-class",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "scopeSize": {"contexts": 1, "edges": 1, "triangles": 0},
                "classRef": "computedInvariants/cech-cohomology:profile:test-handoff"
            },
            "verdict": "measured_nonzero",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": true,
                "methodStatus": "computed",
                "certRef": "computedInvariants/cech-cohomology:profile:test-handoff"
            },
            "dependsOnAssumptions": ["assumption:part8-4-2:finite-site"],
            "evidence": {
                "computedInvariantRefs": ["cech-cohomology:profile:test-handoff"],
                "sourceRefs": []
            }
        }, {
            "verdictRef": "structuralVerdict/ag-cech-obstruction/ag-cech-obstruction/certificate-missing",
            "evaluator": "ag.cech-obstruction",
            "law": "ag.cech-obstruction",
            "target": {
                "kind": "cover-relative-cech-h1-class",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "scopeSize": {"contexts": 0, "edges": 0, "triangles": 0},
                "classRef": "structuralVerdict/ag-cech-obstruction/ag-cech-obstruction/certificate-missing"
            },
            "verdict": "unknown",
            "reason": "certificate boundary is outside the selected profile",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": false,
                "methodStatus": "certificate_missing"
            },
            "dependsOnAssumptions": ["assumption:part8-10-4:transfer-lower-bound"],
            "evidence": {"computedInvariantRefs": [], "sourceRefs": []}
        }],
        "computedInvariants": [{
            "invariantId": "cech-cohomology:profile:test-handoff",
            "kind": "cech-h1-rank",
            "evaluator": "ag.cech-obstruction",
            "status": "computed",
            "value": {"H0": 1, "H1": 1},
            "representation": {"dimensions": {"H0": 1, "H1": 1}}
        }],
        "analyticReadings": [{
            "readingId": "theorem-candidate:transfer-lower-bound:test",
            "evaluator": "ag.foundation",
            "claimStatus": "candidate",
            "fidelity": "proxy",
            "value": {"transferLowerBound": 3.5},
            "regime": "theorem-candidate",
            "structuralVerdictRef": null
        }],
        "assumptions": [{
            "assumptionId": "assumption:part8-4-2:finite-site",
            "theoremRef": "part8/4.2",
            "assumption": "finite site",
            "status": "checked",
            "checkedBy": "finite-linear-algebra@1",
            "scopeRefs": ["part8/4.2"]
        }, {
            "assumptionId": "assumption:part8-10-4:transfer-lower-bound",
            "theoremRef": "part8/10.4",
            "assumption": "transfer_lower_bound",
            "status": "assumed",
            "assumedBy": "measurement-profile author",
            "scopeRefs": ["part8/10.4"]
        }, {
            "assumptionId": "assumption:part8-10-4:second-transfer-boundary",
            "theoremRef": "part8/10.4",
            "assumption": "second transfer boundary",
            "status": "assumed",
            "assumedBy": "measurement-profile author",
            "scopeRefs": ["part8/10.4"]
        }, {
            "assumptionId": "assumption:part8-11-1:unrelated-runtime-boundary",
            "theoremRef": "part8/11.1",
            "assumption": "unrelated runtime boundary",
            "status": "violated",
            "scopeRefs": ["part8/11.1"]
        }],
        "suppliedData": [{
            "suppliedId": "supplied:archmap",
            "kind": "archmap",
            "sourceArtifactRef": "input:archmap.json",
            "conformance": {
                "status": "validated",
                "checkRef": "archmap/v0.5.0-validation"
            }
        }, {
            "suppliedId": "supplied:law-policy",
            "kind": "law-policy",
            "sourceArtifactRef": "input:law-policy.json",
            "conformance": {
                "status": "validated",
                "checkRef": "law-policy/v0.5.0-validation"
            }
        }, {
            "suppliedId": "supplied:measurement-profile",
            "kind": "measurement-profile",
            "sourceArtifactRef": "input:measurement-profile.json",
            "conformance": {
                "status": "validated",
                "checkRef": "measurement-profile/v0.5.0-validation"
            }
        }],
        "boundaryStatements": [{
            "id": "boundary:assumption:part8-11-1",
            "kind": "violated_assumption_dependency",
            "scopeRefs": ["assumption:part8-11-1:unrelated-runtime-boundary"],
            "reason": "unrelated assumption is violated but no measured structural row depends on it",
            "text": "Unrelated violated assumption is carried as typed boundary data."
        }],
        "nonConclusions": [
            "ArchSig measurement packet is a computation artifact, not a Lean proof object."
        ]
    });
    fs::write(
        &packet,
        serde_json::to_string_pretty(&packet_json).expect("measurement packet serializes"),
    )
    .expect("measurement packet fixture is written");

    run_sig0(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        packet.to_str().expect("measurement packet path is utf-8"),
        "--out",
        estimate.to_str().expect("estimate path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--input",
        estimate.to_str().expect("estimate path is utf-8"),
        "--out",
        estimate_validation
            .to_str()
            .expect("estimate validation path is utf-8"),
    ]);

    let estimate_json = read_json(&estimate);
    assert_eq!(estimate_json["schema"], "operation-support-estimate/v0.5.0");
    assert_eq!(
        estimate_json["descriptorRef"]["artifactKind"],
        "archsig-measurement-packet"
    );
    assert!(
        estimate_json["descriptorRef"]["sourceRefIds"]
            .as_array()
            .expect("source refs are array")
            .iter()
            .any(|source| source == "archsigMeasurementPacket:measurement:test-handoff"),
        "FieldSig must retain the measurement packet id as a handoff source ref"
    );
    assert!(
        estimate_json["candidateOperationFamilies"]
            .as_array()
            .expect("candidate families are array")
            .iter()
            .any(|family| family["supportKind"] == "measurement-packet-structural-verdict"),
        "FieldSig must project measurement-packet structural verdict rows into bounded candidate families"
    );
    let structural_family_ids = estimate_json["candidateOperationFamilies"]
        .as_array()
        .expect("candidate families are array")
        .iter()
        .filter(|family| family["supportKind"] == "measurement-packet-structural-verdict")
        .map(|family| {
            family["familyId"]
                .as_str()
                .expect("family id is string")
                .to_string()
        })
        .collect::<Vec<_>>();
    let unique_structural_family_ids = structural_family_ids
        .iter()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        structural_family_ids.len(),
        2,
        "fixture should contain duplicate evaluator structural rows"
    );
    assert_eq!(
        unique_structural_family_ids.len(),
        structural_family_ids.len(),
        "duplicate evaluator structural rows must still produce distinct family IDs"
    );
    assert!(
        estimate_json["candidateOperationFamilies"]
            .as_array()
            .expect("candidate families are array")
            .iter()
            .any(|family| family["supportKind"] == "measurement-packet-analytic-reading"),
        "FieldSig must retain analytic readings without turning them into structural verdicts"
    );
    assert!(
        estimate_json["evidenceBoundary"]["measurementBoundaryRefs"]
            .as_array()
            .expect("measurement boundary refs are array")
            .iter()
            .any(
                |source| source == "archsigMeasurementVerdict:ag.cech-obstruction:measured_nonzero"
            ),
        "FieldSig must carry measurement packet verdict boundaries"
    );
    assert!(
        estimate_json["unknownRemainder"]
            .as_array()
            .expect("unknown remainder is array")
            .iter()
            .any(|entry| {
                entry["reason"]
                    .as_str()
                    .expect("reason is string")
                    .contains("assumption:part8-10-4:transfer-lower-bound")
                    && entry["treatment"]
                        .as_str()
                        .expect("treatment is string")
                        .contains("do not promote it to proof")
            }),
        "assumed theorem-candidate boundaries must remain unknown remainder"
    );
    let duplicate_theorem_remainders = estimate_json["unknownRemainder"]
        .as_array()
        .expect("unknown remainder is array")
        .iter()
        .filter(|entry| {
            entry["reason"]
                .as_str()
                .expect("reason is string")
                .contains("part8/10.4")
        })
        .map(|entry| {
            entry["remainderId"]
                .as_str()
                .expect("remainder id is string")
                .to_string()
        })
        .collect::<Vec<_>>();
    let unique_duplicate_theorem_remainders = duplicate_theorem_remainders
        .iter()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        duplicate_theorem_remainders.len(),
        2,
        "fixture should contain two same-theorem assumed rows"
    );
    assert_eq!(
        unique_duplicate_theorem_remainders.len(),
        duplicate_theorem_remainders.len(),
        "same theoremRef assumption rows must still produce distinct unknown remainder IDs"
    );
    assert!(
        estimate_json["evidenceBoundary"]["measurementBoundaryRefs"]
            .as_array()
            .expect("measurement boundary refs are array")
            .iter()
            .any(|source| source
                == "archsigMeasurementBoundaryKind:violated_assumption_dependency"),
        "FieldSig must carry typed ArchSig boundaryStatements into SFT evidence boundary refs"
    );
    assert!(
        estimate_json["unknownRemainder"]
            .as_array()
            .expect("unknown remainder is array")
            .iter()
            .any(|entry| {
                entry["reason"]
                    .as_str()
                    .expect("reason is string")
                    .contains("ag.cech-obstruction returned unknown")
                    && entry["unknownAxes"]
                        .as_array()
                        .expect("unknown axes are array")
                        .iter()
                        .any(|axis| axis == "unknown")
            }),
        "unknown structural verdicts must remain unknown remainder"
    );
    assert!(
        estimate_json["knownForbiddenSupport"]
            .as_array()
            .expect("forbidden support entries are array")
            .iter()
            .any(|entry| entry["operationFamily"] == "raw-archmap-truth-promotion"),
        "raw ArchMap observation must not be promoted to forecast truth"
    );
    let validation_json = read_json(&estimate_validation);
    assert_eq!(validation_json["summary"]["result"], "pass");
}

#[test]
fn cli_rejects_archsig_measurement_capacity_reading_as_cech_cert_fallback() {
    let out_dir = temp_dir("archsig-measurement-capacity-not-cert");
    let packet = out_dir.join("archsig-measurement-packet.json");
    let estimate = out_dir.join("operation-support-estimate.json");
    let packet_json = serde_json::json!({
        "schema": "archsig-measurement-packet/v0.5.0",
        "packetId": "measurement:capacity-not-cert",
        "profile": {
            "schema": "measurement-profile/v0.5.0",
            "profileId": "profile:capacity-not-cert",
            "siteRef": "archmap:/contexts",
            "coverRef": "cover:test",
            "coefficient": "F2",
            "effCoeff": "finite-linear-algebra@1",
            "witnessFamily": [],
            "resolutionSelector": "cech@1",
            "domain": "finite-poset-site",
            "zeroPredicate": "rank-zero@1",
            "nonZeroPredicate": "rank-positive@1",
            "certSelector": "finite-certificate@1",
            "verdictDiscipline": "five-valued-structural-verdict@1"
        },
        "structuralVerdict": [{
            "verdictRef": "structuralVerdict/ag-cech-obstruction/ag-cech-obstruction/finite-f2-cech-computed",
            "evaluator": "ag.cech-obstruction",
            "law": "ag.cech-obstruction",
            "target": {
                "kind": "cover-relative-cech-h1-class",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "scopeSize": {"contexts": 1, "edges": 1, "triangles": 0},
                "classRef": "computedInvariants/topological-debt-capacity:profile:capacity-not-cert"
            },
            "verdict": "measured_nonzero",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": true,
                "methodStatus": "finite_f2_cech_computed"
            },
            "evidence": {
                "computedInvariantRefs": [],
                "sourceRefs": []
            }
        }],
        "computedInvariants": [{
            "invariantId": "topological-debt-capacity:profile:capacity-not-cert",
            "kind": "topological-debt-capacity",
            "evaluator": "ag.cech-obstruction",
            "status": "computed",
            "structuralVerdictRef": null,
            "value": 1,
            "representation": {"capacityLowerBound": 1}
        }],
        "analyticReadings": [{
            "readingId": "candidate:semantic-validation",
            "evaluator": "ag.foundation",
            "claimStatus": "candidate",
            "fidelity": "proxy",
            "value": {"state": "not_evaluated"},
            "regime": "theorem-candidate",
            "structuralVerdictRef": null
        }],
        "assumptions": [{
            "assumptionId": "assumption:part4-12-3:constant-coefficient-nerve-b1-comparison",
            "theoremRef": "part4/12.3",
            "assumption": "constant coefficient nerve b1 comparison",
            "status": "checked",
            "checkedBy": "measurement-profile:profile:capacity-not-cert.coefficient=F2",
            "scopeRefs": ["part4/12.3"]
        }],
        "suppliedData": [{
            "suppliedId": "supplied:archmap",
            "kind": "archmap",
            "sourceArtifactRef": "input:archmap.json",
            "conformance": {
                "status": "validated",
                "checkRef": "archmap/v0.5.0-validation"
            }
        }],
        "boundaryStatements": [],
        "nonConclusions": []
    });
    fs::write(
        &packet,
        serde_json::to_string_pretty(&packet_json).expect("measurement packet serializes"),
    )
    .expect("measurement packet fixture is written");

    let output = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        packet.to_str().expect("measurement packet path is utf-8"),
        "--out",
        estimate.to_str().expect("estimate path is utf-8"),
    ]);
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("requires non-empty evidence.computedInvariantRefs"),
        "M7 capacity reading must not act as fallback certificate for a measured Cech verdict"
    );
}

#[test]
fn cli_rejects_invalid_measurement_packet_handoff_inputs() {
    let out_dir = temp_dir("archsig-measurement-sft-input-rejected");
    let schema_only = out_dir.join("schema-only-measurement-packet.json");
    fs::write(
        &schema_only,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "archsig-measurement-packet/v0.5.0"
        }))
        .expect("schema-only packet serializes"),
    )
    .expect("schema-only packet fixture is written");

    let malformed = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        schema_only
            .to_str()
            .expect("schema-only packet path is utf-8"),
        "--out",
        out_dir
            .join("malformed.json")
            .to_str()
            .expect("malformed path is utf-8"),
    ]);
    assert!(!malformed.status.success());
    assert!(
        String::from_utf8_lossy(&malformed.stderr).contains("requires non-empty packetId"),
        "schema-only measurement packet must be rejected before writing a handoff estimate"
    );

    let rejected = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        fixture_root()
            .join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--out",
        out_dir
            .join("rejected.json")
            .to_str()
            .expect("rejected path is utf-8"),
    ]);
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8_lossy(&rejected.stderr)
            .contains("requires archsig-measurement-packet/v0.5.0"),
        "raw ArchMap input must be rejected by the measurement-packet handoff"
    );

    let retired_packet = out_dir.join("retired-packet.json");
    let retired_schema = ["archsig", "analysis", "packet/v0.5.0"].join("-");
    fs::write(
        &retired_packet,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": retired_schema
        }))
        .expect("retired packet serializes"),
    )
    .expect("retired packet fixture writes");
    let retired_rejected = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        retired_packet
            .to_str()
            .expect("retired packet path is utf-8"),
        "--out",
        out_dir
            .join("retired-rejected.json")
            .to_str()
            .expect("retired rejection path is utf-8"),
    ]);
    assert!(!retired_rejected.status.success());
    assert!(
        String::from_utf8_lossy(&retired_rejected.stderr)
            .contains("requires archsig-measurement-packet/v0.5.0"),
        "retired packet schema must be rejected by the measurement-packet handoff"
    );

    let legacy_flag = run_sig0_output(&[
        "archsig-analysis-sft-input",
        &["--analysis", "packet"].join("-"),
        schema_only.to_str().expect("legacy packet path is utf-8"),
        "--out",
        out_dir
            .join(["legacy", "analysis", "packet.json"].join("-"))
            .to_str()
            .expect("legacy output path is utf-8"),
    ]);
    assert!(!legacy_flag.status.success());
    assert!(
        String::from_utf8_lossy(&legacy_flag.stderr).contains("unexpected argument")
            || String::from_utf8_lossy(&legacy_flag.stderr).contains("unrecognized option"),
        "legacy handoff flag must be rejected as an unknown argument"
    );

    let valid_measurement_packet = serde_json::json!({
        "schema": "archsig-measurement-packet/v0.5.0",
        "packetId": "measurement:semantic-validation",
        "profile": {
            "schema": "measurement-profile/v0.5.0",
            "profileId": "profile:semantic-validation"
        },
        "structuralVerdict": [{
            "verdictRef": "structuralVerdict/ag-square-free-repair/ag-square-free-repair/nsdepth-certificate-verified",
            "evaluator": "ag.square-free-repair",
            "law": "ag.square-free-repair",
            "target": {
                "kind": "square-free-repair-support",
                "coverRef": "ag.square-free-repair",
                "coefficient": "F2",
                "scopeSize": {"contexts": 1, "edges": 0, "triangles": 0},
                "classRef": "computedInvariants/square-free-repair:profile:semantic-validation"
            },
            "verdict": "measured_nonzero",
            "verdictData": {
                "inScope": true,
                "zero": false,
                "nonZero": true,
                "methodStatus": "nsdepth_certificate_verified",
                "certRef": "computedInvariants/square-free-repair:profile:semantic-validation"
            },
            "dependsOnAssumptions": ["assumption:part3-7-2B:finite-certificate-verified"],
            "evidence": {
                "computedInvariantRefs": ["square-free-repair:profile:semantic-validation"],
                "sourceRefs": []
            }
        }],
        "computedInvariants": [{
            "invariantId": "square-free-repair:profile:semantic-validation",
            "kind": "minimal-forbidden-supports",
            "evaluator": "ag.square-free-repair",
            "status": "computed",
            "value": [],
            "representation": {}
        }],
        "analyticReadings": [{
            "readingId": "candidate:semantic-validation",
            "evaluator": "ag.foundation",
            "claimStatus": "candidate",
            "fidelity": "proxy",
            "value": {"state": "not_evaluated"},
            "regime": "theorem-candidate",
            "structuralVerdictRef": null
        }],
        "assumptions": [{
            "assumptionId": "assumption:part3-7-2B:finite-certificate-verified",
            "theoremRef": "part3/7.2B",
            "assumption": "finite certificate verified",
            "status": "checked",
            "checkedBy": "ag.square-free-repair",
            "scopeRefs": ["part3/7.2B"]
        }],
        "suppliedData": [{
            "suppliedId": "supplied:archmap",
            "kind": "archmap",
            "sourceArtifactRef": "input:archmap.json",
            "conformance": {
                "status": "validated",
                "checkRef": "archmap/v0.5.0-validation"
            }
        }],
        "boundaryStatements": [],
        "nonConclusions": []
    });

    let invalid_verdict_packet = out_dir.join("invalid-verdict-measurement-packet.json");
    let mut invalid_verdict_json = valid_measurement_packet.clone();
    invalid_verdict_json["structuralVerdict"][0]["verdict"] = serde_json::json!("measured_unknown");
    fs::write(
        &invalid_verdict_packet,
        serde_json::to_string_pretty(&invalid_verdict_json)
            .expect("invalid verdict packet serializes"),
    )
    .expect("invalid verdict packet fixture is written");
    let invalid_verdict = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        invalid_verdict_packet
            .to_str()
            .expect("invalid verdict packet path is utf-8"),
        "--out",
        out_dir
            .join("invalid-verdict.json")
            .to_str()
            .expect("invalid verdict output path is utf-8"),
    ]);
    assert!(!invalid_verdict.status.success());
    assert!(
        String::from_utf8_lossy(&invalid_verdict.stderr)
            .contains("unsupported verdict measured_unknown"),
        "measurement-packet handoff must reject unsupported structural verdicts"
    );

    let violated_assumption_packet = out_dir.join("violated-assumption-measurement-packet.json");
    let mut violated_assumption_json = valid_measurement_packet.clone();
    violated_assumption_json["assumptions"][0]["status"] = serde_json::json!("violated");
    violated_assumption_json["assumptions"][0]
        .as_object_mut()
        .expect("assumption row is object")
        .remove("checkedBy");
    fs::write(
        &violated_assumption_packet,
        serde_json::to_string_pretty(&violated_assumption_json)
            .expect("violated assumption packet serializes"),
    )
    .expect("violated assumption packet fixture is written");
    let violated_assumption = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        violated_assumption_packet
            .to_str()
            .expect("violated assumption packet path is utf-8"),
        "--out",
        out_dir
            .join("violated-assumption.json")
            .to_str()
            .expect("violated assumption output path is utf-8"),
    ]);
    assert!(!violated_assumption.status.success());
    assert!(
        String::from_utf8_lossy(&violated_assumption.stderr)
            .contains("keeps measured verdict while depending on violated assumption"),
        "measurement-packet handoff must reject only measured rows that depend on violated assumptions"
    );

    let missing_evidence_packet = out_dir.join("missing-evidence-measurement-packet.json");
    let mut missing_evidence_json = valid_measurement_packet.clone();
    missing_evidence_json["structuralVerdict"][0]["verdictData"]
        .as_object_mut()
        .expect("verdictData is object")
        .remove("certRef");
    missing_evidence_json["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] =
        serde_json::json!([]);
    fs::write(
        &missing_evidence_packet,
        serde_json::to_string_pretty(&missing_evidence_json)
            .expect("missing evidence packet serializes"),
    )
    .expect("missing evidence packet fixture is written");
    let missing_evidence = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        missing_evidence_packet
            .to_str()
            .expect("missing evidence packet path is utf-8"),
        "--out",
        out_dir
            .join("missing-evidence.json")
            .to_str()
            .expect("missing evidence output path is utf-8"),
    ]);
    assert!(!missing_evidence.status.success());
    assert!(
        String::from_utf8_lossy(&missing_evidence.stderr)
            .contains("requires non-empty evidence.computedInvariantRefs"),
        "measurement-packet handoff must reject measured verdicts without evidence linkage"
    );

    let missing_supplied_packet = out_dir.join("missing-supplied-data-measurement-packet.json");
    let mut missing_supplied_json = valid_measurement_packet.clone();
    missing_supplied_json
        .as_object_mut()
        .expect("packet is object")
        .remove("suppliedData");
    fs::write(
        &missing_supplied_packet,
        serde_json::to_string_pretty(&missing_supplied_json)
            .expect("missing suppliedData packet serializes"),
    )
    .expect("missing suppliedData packet fixture is written");
    let missing_supplied = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        missing_supplied_packet
            .to_str()
            .expect("missing suppliedData packet path is utf-8"),
        "--out",
        out_dir
            .join("missing-supplied-data.json")
            .to_str()
            .expect("missing suppliedData output path is utf-8"),
    ]);
    assert!(!missing_supplied.status.success());
    assert!(
        String::from_utf8_lossy(&missing_supplied.stderr).contains("requires suppliedData array"),
        "measurement-packet handoff must reject packets without suppliedData ledger"
    );

    let missing_target_packet = out_dir.join("missing-target-measurement-packet.json");
    let mut missing_target_json = valid_measurement_packet.clone();
    missing_target_json["structuralVerdict"][0]
        .as_object_mut()
        .expect("structural verdict row is object")
        .remove("target");
    fs::write(
        &missing_target_packet,
        serde_json::to_string_pretty(&missing_target_json)
            .expect("missing target packet serializes"),
    )
    .expect("missing target packet fixture is written");
    let missing_target = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        missing_target_packet
            .to_str()
            .expect("missing target packet path is utf-8"),
        "--out",
        out_dir
            .join("missing-target.json")
            .to_str()
            .expect("missing target output path is utf-8"),
    ]);
    assert!(!missing_target.status.success());
    assert!(
        String::from_utf8_lossy(&missing_target.stderr).contains("requires target object"),
        "measurement-packet handoff must reject structural verdicts without a measurement target"
    );

    let unresolved_evidence_packet = out_dir.join("unresolved-evidence-measurement-packet.json");
    let mut unresolved_evidence_json = valid_measurement_packet.clone();
    unresolved_evidence_json["structuralVerdict"][0]["evidence"]["computedInvariantRefs"] =
        serde_json::json!(["missing-invariant"]);
    fs::write(
        &unresolved_evidence_packet,
        serde_json::to_string_pretty(&unresolved_evidence_json)
            .expect("unresolved evidence packet serializes"),
    )
    .expect("unresolved evidence packet fixture is written");
    let unresolved_evidence = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        unresolved_evidence_packet
            .to_str()
            .expect("unresolved evidence packet path is utf-8"),
        "--out",
        out_dir
            .join("unresolved-evidence.json")
            .to_str()
            .expect("unresolved evidence output path is utf-8"),
    ]);
    assert!(!unresolved_evidence.status.success());
    assert!(
        String::from_utf8_lossy(&unresolved_evidence.stderr)
            .contains("does not resolve to computedInvariants[].invariantId"),
        "measurement-packet handoff must reject unresolved computedInvariantRefs"
    );

    let unresolved_class_ref_packet = out_dir.join("unresolved-class-ref-measurement-packet.json");
    let mut unresolved_class_ref_json = valid_measurement_packet.clone();
    unresolved_class_ref_json["structuralVerdict"][0]["target"]["classRef"] =
        serde_json::json!("computedInvariants/missing-invariant");
    fs::write(
        &unresolved_class_ref_packet,
        serde_json::to_string_pretty(&unresolved_class_ref_json)
            .expect("unresolved classRef packet serializes"),
    )
    .expect("unresolved classRef packet fixture is written");
    let unresolved_class_ref = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        unresolved_class_ref_packet
            .to_str()
            .expect("unresolved classRef packet path is utf-8"),
        "--out",
        out_dir
            .join("unresolved-class-ref.json")
            .to_str()
            .expect("unresolved classRef output path is utf-8"),
    ]);
    assert!(!unresolved_class_ref.status.success());
    assert!(
        String::from_utf8_lossy(&unresolved_class_ref.stderr).contains("target.classRef")
            && String::from_utf8_lossy(&unresolved_class_ref.stderr).contains("does not resolve"),
        "measurement-packet handoff must reject unresolved measured_nonzero classRef"
    );

    let opaque_cert_ref_packet = out_dir.join("opaque-cert-ref-measurement-packet.json");
    let mut opaque_cert_ref_json = valid_measurement_packet.clone();
    opaque_cert_ref_json["structuralVerdict"][0]["verdictData"]["certRef"] =
        serde_json::json!("opaque:non-computed-cert");
    fs::write(
        &opaque_cert_ref_packet,
        serde_json::to_string_pretty(&opaque_cert_ref_json)
            .expect("opaque certRef packet serializes"),
    )
    .expect("opaque certRef packet fixture is written");
    let opaque_cert_ref = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        opaque_cert_ref_packet
            .to_str()
            .expect("opaque certRef packet path is utf-8"),
        "--out",
        out_dir
            .join("opaque-cert-ref.json")
            .to_str()
            .expect("opaque certRef output path is utf-8"),
    ]);
    assert!(!opaque_cert_ref.status.success());
    assert!(
        String::from_utf8_lossy(&opaque_cert_ref.stderr)
            .contains("requires certRef or matching computed invariant evidence"),
        "measurement-packet handoff must reject opaque certRef values that do not resolve to computedInvariants"
    );

    let unknown_invariant_kind_packet =
        out_dir.join("unknown-invariant-kind-measurement-packet.json");
    let mut unknown_invariant_kind_json = valid_measurement_packet.clone();
    unknown_invariant_kind_json["computedInvariants"][0]["kind"] =
        serde_json::json!("unregistered-freeform-kind");
    fs::write(
        &unknown_invariant_kind_packet,
        serde_json::to_string_pretty(&unknown_invariant_kind_json)
            .expect("unknown invariant kind packet serializes"),
    )
    .expect("unknown invariant kind packet fixture is written");
    let unknown_invariant_kind = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        unknown_invariant_kind_packet
            .to_str()
            .expect("unknown invariant kind packet path is utf-8"),
        "--out",
        out_dir
            .join("unknown-invariant-kind.json")
            .to_str()
            .expect("unknown invariant kind output path is utf-8"),
    ]);
    assert!(!unknown_invariant_kind.status.success());
    assert!(
        String::from_utf8_lossy(&unknown_invariant_kind.stderr)
            .contains("unsupported kind unregistered-freeform-kind"),
        "measurement-packet handoff must reject unknown computed invariant kinds"
    );

    let unknown_supplied_kind_packet =
        out_dir.join("unknown-supplied-kind-measurement-packet.json");
    let mut unknown_supplied_kind_json = valid_measurement_packet.clone();
    unknown_supplied_kind_json["suppliedData"][0]["kind"] =
        serde_json::json!("unregistered-supplied-kind");
    fs::write(
        &unknown_supplied_kind_packet,
        serde_json::to_string_pretty(&unknown_supplied_kind_json)
            .expect("unknown supplied kind packet serializes"),
    )
    .expect("unknown supplied kind packet fixture is written");
    let unknown_supplied_kind = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        unknown_supplied_kind_packet
            .to_str()
            .expect("unknown supplied kind packet path is utf-8"),
        "--out",
        out_dir
            .join("unknown-supplied-kind.json")
            .to_str()
            .expect("unknown supplied kind output path is utf-8"),
    ]);
    assert!(!unknown_supplied_kind.status.success());
    assert!(
        String::from_utf8_lossy(&unknown_supplied_kind.stderr)
            .contains("unsupported kind unregistered-supplied-kind"),
        "measurement-packet handoff must reject unknown suppliedData kinds"
    );

    let missing_conformance_status_packet =
        out_dir.join("missing-conformance-status-measurement-packet.json");
    let mut missing_conformance_status_json = valid_measurement_packet.clone();
    missing_conformance_status_json["suppliedData"][0]["conformance"]
        .as_object_mut()
        .expect("conformance is object")
        .remove("status");
    fs::write(
        &missing_conformance_status_packet,
        serde_json::to_string_pretty(&missing_conformance_status_json)
            .expect("missing conformance status packet serializes"),
    )
    .expect("missing conformance status packet fixture is written");
    let missing_conformance_status = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        missing_conformance_status_packet
            .to_str()
            .expect("missing conformance status packet path is utf-8"),
        "--out",
        out_dir
            .join("missing-conformance-status.json")
            .to_str()
            .expect("missing conformance status output path is utf-8"),
    ]);
    assert!(!missing_conformance_status.status.success());
    assert!(
        String::from_utf8_lossy(&missing_conformance_status.stderr)
            .contains("requires conformance.status"),
        "measurement-packet handoff must reject suppliedData without conformance.status"
    );

    let missing_claim_status_packet = out_dir.join("missing-claim-status-measurement-packet.json");
    let mut missing_claim_status_json = valid_measurement_packet;
    missing_claim_status_json["analyticReadings"][0]
        .as_object_mut()
        .expect("analytic reading row is object")
        .remove("claimStatus");
    fs::write(
        &missing_claim_status_packet,
        serde_json::to_string_pretty(&missing_claim_status_json)
            .expect("missing claimStatus packet serializes"),
    )
    .expect("missing claimStatus packet fixture is written");
    let missing_claim_status = run_sig0_output(&[
        "archsig-analysis-sft-input",
        "--measurement-packet",
        missing_claim_status_packet
            .to_str()
            .expect("missing claimStatus packet path is utf-8"),
        "--out",
        out_dir
            .join("missing-claim-status.json")
            .to_str()
            .expect("missing claimStatus output path is utf-8"),
    ]);
    assert!(!missing_claim_status.status.success());
    assert!(
        String::from_utf8_lossy(&missing_claim_status.stderr).contains("claimStatus"),
        "measurement-packet handoff must reject analytic readings without an analytic claimStatus"
    );
}

#[test]
fn cli_validates_archmap_fixture_and_guardrails() {
    let out_dir = temp_dir("archmap-validation");
    let input = fixture_root().join("archmap.json");
    let report = out_dir.join("archmap-validation.json");

    run_sig0(&[
        "archmap",
        "--input",
        input.to_str().expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&report);
    assert_eq!(json["schema"], "archmap-validation-report/v0.5.0");
    assert_eq!(json["summary"]["result"], "warn");
    let source_inventory_checks = json["sourceInventoryChecks"]
        .as_array()
        .expect("source inventory checks are an array");
    assert!(
        source_inventory_checks.iter().any(|check| {
            check["id"] == "archmap-source-inventory-artifact"
                && check["result"] == "pass"
                && check["reason"]
                    .as_str()
                    .expect("source inventory pass has a reason")
                    .contains("included, excluded, unavailable, private")
        }),
        "source inventory artifact boundary should be present and consistent"
    );
    assert!(
        json["conflictChecks"][0]["examples"]
            .as_array()
            .expect("conflict examples are an array")
            .iter()
            .any(|example| example["source"] == "policy-disagreement")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|entry| entry == "ArchMap validation does not prove architecture lawfulness")
    );
    assert_eq!(
        json["atomicObservationSummary"]["atomCandidateCount"], 4,
        "ArchMap validation should expose atom candidate count"
    );
    assert!(
        json["atomicObservationChecks"]
            .as_array()
            .expect("atomic observation checks are an array")
            .iter()
            .any(|check| check["id"] == "archmap-observation-gaps-not-measured-zero")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|entry| entry == "obstruction circuit candidate is not a primitive atom")
    );
    assert!(
        json["leanPreservationVocabulary"]
            .as_array()
            .expect("Lean preservation vocabulary is an array")
            .iter()
            .any(|entry| {
                entry["archmapSelector"] == "mappingKind=object or targetRef.kind=air-component"
                    && entry["leanPackageField"] == "ObjectPreservation"
            })
    );
    let preservation_checklist = json["leanPreservationPreconditionChecklist"]
        .as_array()
        .expect("Lean preservation checklist is an array");
    assert!(
        preservation_checklist.iter().any(|entry| {
            entry["mapItemId"] == "object-route-users"
                && entry["leanPackageField"] == "ObjectPreservation"
                && entry["status"] == "candidate"
        }),
        "object mapping should be tracked as an ObjectPreservation candidate"
    );
    assert!(
        preservation_checklist.iter().any(|entry| {
            entry["mapItemId"] == "policy-layered-route-service"
                && entry["leanPackageField"] == "LawPolicyPreservation"
                && entry["status"] == "satisfiedBySuppliedAssumption"
        }),
        "supplied policy assumptions should stay distinct from proved theorem discharge"
    );
    assert!(
        preservation_checklist.iter().any(|entry| {
            entry["mapItemId"] == "semantic-unmeasured-global-commutation"
                && entry["leanPackageField"] == "SemanticCommutationPreservation"
                && entry["status"] == "blockedByUnmeasuredCoverage"
        }),
        "unmeasured semantic commutation should block preservation discharge"
    );
    assert!(
        preservation_checklist.iter().any(|entry| {
            entry["mapItemId"] == "runtime-unmeasured-boundary"
                && entry["status"] == "blockedByMissingEvidence"
        }),
        "runtime missing evidence should remain visible in the checklist"
    );
    assert!(
        preservation_checklist.iter().any(|entry| {
            entry["leanPackageField"] == "FormalPromotionGuardrail"
                && entry["status"] == "blockedByFormalPromotionGuardrail"
        }),
        "validation success should keep the formal promotion guardrail visible"
    );

    let invalid = out_dir.join("archmap-invalid.json");
    let invalid_report = out_dir.join("archmap-invalid-validation.json");
    let mut invalid_json = read_json(&input);
    invalid_json["mapItems"][0]["sourceRefs"] = serde_json::json!([]);
    invalid_json["mapItems"][1]["claimClassification"] = serde_json::json!("proved");
    fs::write(
        &invalid,
        serde_json::to_string_pretty(&invalid_json).expect("invalid ArchMap serializes"),
    )
    .expect("invalid ArchMap is written");

    let output = run_sig0_output(&[
        "archmap",
        "--input",
        invalid.to_str().expect("invalid path is utf-8"),
        "--out",
        invalid_report.to_str().expect("output path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid ArchMap should fail validation"
    );
    let invalid_report_json = read_json(&invalid_report);
    assert_eq!(invalid_report_json["summary"]["result"], "fail");
    assert_eq!(
        invalid_report_json["claimBoundaryChecks"][0]["id"],
        "archmap-measured-claims-have-evidence"
    );
    assert_eq!(
        invalid_report_json["formalPromotionGuardrailChecks"][0]["id"],
        "archmap-formal-promotion-guardrail"
    );

    let missing_inventory = out_dir.join("archmap-missing-source-inventory.json");
    let missing_inventory_report = out_dir.join("archmap-missing-source-inventory-report.json");
    let mut missing_inventory_json = read_json(&input);
    missing_inventory_json["sourceInventoryRef"]["path"] = serde_json::json!(
        "tools/fieldsig/tests/fixtures/minimal/external/missing_source_inventory.json"
    );
    fs::write(
        &missing_inventory,
        serde_json::to_string_pretty(&missing_inventory_json)
            .expect("missing inventory ArchMap serializes"),
    )
    .expect("missing inventory ArchMap is written");

    run_sig0(&[
        "archmap",
        "--input",
        missing_inventory
            .to_str()
            .expect("missing inventory path is utf-8"),
        "--out",
        missing_inventory_report
            .to_str()
            .expect("output path is utf-8"),
    ]);
    let missing_inventory_report_json = read_json(&missing_inventory_report);
    assert_eq!(missing_inventory_report_json["summary"]["result"], "warn");
    assert!(
        missing_inventory_report_json["sourceInventoryChecks"]
            .as_array()
            .expect("source inventory checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "archmap-source-inventory-artifact"
                    && check["result"] == "warn"
                    && check["examples"]
                        .as_array()
                        .expect("warning examples are an array")
                        .iter()
                        .any(|example| {
                            example["evidence"] == "source inventory artifact path does not exist"
                        })
            })
    );

    let mismatched_inventory = out_dir.join("archmap-source-inventory-mismatched.json");
    let mismatched_archmap = out_dir.join("archmap-mismatched-source-inventory.json");
    let mismatched_inventory_report =
        out_dir.join("archmap-mismatched-source-inventory-report.json");
    let mut inventory_json = read_json(&fixture_root().join("archmap_source_inventory.json"));
    inventory_json["includedRefs"] = serde_json::json!([]);
    fs::write(
        &mismatched_inventory,
        serde_json::to_string_pretty(&inventory_json).expect("mismatched inventory serializes"),
    )
    .expect("mismatched inventory is written");
    let mut mismatched_archmap_json = read_json(&input);
    mismatched_archmap_json["sourceInventoryRef"]["path"] = serde_json::json!(
        mismatched_inventory
            .to_str()
            .expect("mismatched inventory path is utf-8")
    );
    fs::write(
        &mismatched_archmap,
        serde_json::to_string_pretty(&mismatched_archmap_json)
            .expect("mismatched ArchMap serializes"),
    )
    .expect("mismatched ArchMap is written");

    run_sig0(&[
        "archmap",
        "--input",
        mismatched_archmap
            .to_str()
            .expect("mismatched ArchMap path is utf-8"),
        "--out",
        mismatched_inventory_report
            .to_str()
            .expect("output path is utf-8"),
    ]);
    let mismatched_inventory_report_json = read_json(&mismatched_inventory_report);
    assert_eq!(
        mismatched_inventory_report_json["summary"]["result"],
        "warn"
    );
    assert!(
        mismatched_inventory_report_json["sourceInventoryChecks"]
            .as_array()
            .expect("source inventory checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "archmap-source-inventory-artifact"
                    && check["result"] == "warn"
                    && check["examples"]
                        .as_array()
                        .expect("warning examples are an array")
                        .iter()
                        .any(|example| {
                            example["source"] == "sourceUniverse.includedRefs"
                                && example["evidence"]
                                    == "embedded ArchMap sourceUniverse ref is absent from source inventory artifact"
                        })
            })
    );
}

#[test]
fn cli_projects_archmap_to_sft_input_and_generation_protocol() {
    let out_dir = temp_dir("archmap-sft-input");
    let input = fixture_root().join("archmap.json");
    let source_inventory = fixture_root().join("archmap_source_inventory.json");
    let estimate = out_dir.join("archmap-operation-support.json");
    let cone = out_dir.join("archmap-forecast-cone.json");
    let envelope = out_dir.join("archmap-consequence-envelope.json");
    let protocol = out_dir.join("archmap-generation-protocol.json");

    run_sig0(&[
        "archmap-sft-input",
        "--archmap",
        input.to_str().expect("fixture path is utf-8"),
        "--out",
        estimate.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--operation-support",
        estimate.to_str().expect("estimate path is utf-8"),
        "--out",
        cone.to_str().expect("cone path is utf-8"),
    ]);
    run_sig0(&[
        "consequence-envelope",
        "--forecast-cone",
        cone.to_str().expect("cone path is utf-8"),
        "--out",
        envelope.to_str().expect("envelope path is utf-8"),
    ]);
    run_sig0(&[
        "archmap-generate",
        "--source-inventory",
        source_inventory
            .to_str()
            .expect("source inventory path is utf-8"),
        "--prompt-pack",
        ".lake/archmap-prompt.md",
        "--provider",
        "fixture-provider",
        "--model-id",
        "fixture-model",
        "--out",
        protocol.to_str().expect("protocol path is utf-8"),
    ]);

    let estimate_json = read_json(&estimate);
    assert_eq!(estimate_json["schema"], "operation-support-estimate/v0.5.0");
    assert!(
        estimate_json["candidateOperationFamilies"]
            .as_array()
            .expect("candidate families are an array")
            .iter()
            .any(|family| family["operationFamily"] == "runtime-observation")
    );
    assert!(
        estimate_json["unknownRemainder"]
            .as_array()
            .expect("unknown remainder is an array")
            .iter()
            .any(|remainder| {
                remainder["treatment"]
                    .as_str()
                    .expect("treatment is a string")
                    .contains("do not round to absence or measured zero")
            })
    );
    assert!(
        estimate_json["descriptorRef"]["actionClassCandidateIds"]
            .as_array()
            .expect("action class candidate ids are an array")
            .iter()
            .any(|candidate| candidate == "atom:archmap:atom-component-service-user"),
        "FieldSig handoff must retain ArchMap atom refs as observation refs"
    );
    assert!(
        estimate_json["evidenceBoundary"]["measurementBoundaryRefs"]
            .as_array()
            .expect("measurement boundary refs are an array")
            .iter()
            .any(|boundary| boundary == "archmapObservationGap:gap-runtime-user-db-trace"),
        "FieldSig handoff must retain observation gap refs"
    );
    assert!(
        estimate_json["unknownRemainder"]
            .as_array()
            .expect("unknown remainder is an array")
            .iter()
            .any(|remainder| remainder["remainderId"]
                == "unknown:archmap:gap:gap-runtime-user-db-trace")
    );

    let cone_json = read_json(&cone);
    assert!(
        cone_json["operationSupportRef"]["sourceRefIds"]
            .as_array()
            .expect("cone source refs are an array")
            .iter()
            .any(|source| {
                source
                    .as_str()
                    .expect("source ref is a string")
                    .starts_with("source:archmap:")
            })
    );
    let envelope_json = read_json(&envelope);
    assert!(
        envelope_json["forecastConeRef"]["sourceRefIds"]
            .as_array()
            .expect("envelope source refs are an array")
            .iter()
            .any(|source| {
                source
                    .as_str()
                    .expect("source ref is a string")
                    .starts_with("source:archmap:")
            })
    );

    let protocol_json = read_json(&protocol);
    assert_eq!(
        protocol_json["schema"],
        "archmap-generation-protocol/v0.5.0"
    );
    assert_eq!(
        protocol_json["modelProvenance"]["provider"],
        "fixture-provider"
    );
    assert!(
        protocol_json["requiredWorkflow"]
            .as_array()
            .expect("required workflow is an array")
            .iter()
            .any(|step| {
                step.as_str()
                    .expect("workflow step is a string")
                    .contains("invalid, dangling, unsupported, private, and unavailable")
            })
    );
}

#[test]
fn cli_projects_archmap_to_air_and_existing_reports() {
    let out_dir = temp_dir("archmap-air-flow");
    let archmap = fixture_root().join("archmap.json");
    let validation = out_dir.join("archmap-validation.json");
    let air = out_dir.join("air.json");
    let air_validation = out_dir.join("air-validation.json");
    let theorem_report = out_dir.join("theorem-check.json");
    let feature_report = out_dir.join("feature-report.json");

    run_sig0(&[
        "archmap",
        "--input",
        archmap.to_str().expect("fixture path is utf-8"),
        "--out",
        validation.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "air-from-archmap",
        "--archmap",
        archmap.to_str().expect("fixture path is utf-8"),
        "--validation",
        validation.to_str().expect("validation path is utf-8"),
        "--out",
        air.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "validate-air",
        "--input",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        air_validation.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "theorem-check",
        "--air",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        theorem_report.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "feature-report",
        "--air",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        feature_report.to_str().expect("output path is utf-8"),
    ]);

    let air_json = read_json(&air);
    assert_eq!(air_json["schema"], "aat-air/v0.5.0");
    assert!(
        air_json["artifacts"]
            .as_array()
            .expect("AIR artifacts are an array")
            .iter()
            .any(|artifact| {
                artifact["artifactId"] == "source-inventory-fixture"
                    && artifact["kind"] == "source_inventory"
                    && artifact["path"]
                        == "tools/fieldsig/tests/fixtures/minimal/archmap_source_inventory.json"
            })
    );
    assert!(
        air_json["evidence"]
            .as_array()
            .expect("AIR evidence is an array")
            .iter()
            .any(|evidence| {
                evidence["evidenceId"] == "evidence-archmap-source-inventory"
                    && evidence["artifactRef"] == "source-inventory-fixture"
            })
    );
    assert!(
        air_json["semanticDiagrams"]
            .as_array()
            .expect("semantic diagrams are an array")
            .iter()
            .any(|diagram| diagram["id"] == "diagram-create-user")
    );
    assert!(
        air_json["nonfillabilityWitnesses"]
            .as_array()
            .expect("nonfillability witnesses are an array")
            .iter()
            .any(|witness| witness["witnessId"] == "witness-user-saga-missing-compensation")
    );
    assert!(
        air_json["claims"]
            .as_array()
            .expect("claims are an array")
            .iter()
            .any(|claim| claim["predicate"] == "ArchMap conflict review cue: missing-static-edge")
    );

    let air_validation_json = read_json(&air_validation);
    assert_eq!(air_validation_json["summary"]["result"], "pass");
    let theorem_json = read_json(&theorem_report);
    assert_eq!(
        theorem_json["schema"],
        "theorem-precondition-check-report/v0.5.0"
    );
    let theorem_archmap_checklist = theorem_json["archmapPreservationPreconditionChecklist"]
        .as_array()
        .expect("theorem-check ArchMap preservation checklist is an array");
    assert!(
        theorem_archmap_checklist.iter().any(|entry| {
            entry["mapItemId"] == "semantic-create-user-diagram"
                && entry["leanPackageField"] == "SemanticDiagramPreservation"
                && entry["status"] == "candidate"
        }),
        "theorem-check should report semantic diagram preservation candidates"
    );
    assert!(
        theorem_archmap_checklist.iter().any(|entry| {
            entry["mapItemId"] == "semantic-unmeasured-global-commutation"
                && entry["leanPackageField"] == "SemanticCommutationPreservation"
                && entry["status"] == "blockedByUnmeasuredCoverage"
        }),
        "theorem-check should keep unmeasured semantic commutation out of proof promotion"
    );
    assert!(
        theorem_archmap_checklist.iter().any(|entry| {
            entry["mapItemId"] == "runtime-unmeasured-boundary"
                && entry["status"] == "blockedByMissingEvidence"
                && entry["missingEvidence"]
                    .as_array()
                    .expect("missing evidence is an array")
                    .iter()
                    .any(|missing| missing == "runtime trace not supplied")
        }),
        "theorem-check should keep missing runtime evidence out of proof promotion"
    );
    assert!(
        theorem_archmap_checklist.iter().any(|entry| {
            entry["leanPackageField"] == "FormalPromotionGuardrail"
                && entry["status"] == "blockedByFormalPromotionGuardrail"
        }),
        "theorem-check should keep ArchMap formal promotion blocked"
    );
    let feature_json = read_json(&feature_report);
    assert_eq!(feature_json["schema"], "feature-extension-report/v0.5.0");
    assert!(
        feature_json["semanticPathSummary"]["nonfillabilityWitnessCount"]
            .as_u64()
            .expect("witness count is numeric")
            >= 1
    );
}

#[test]
fn cli_locks_archmap_expressiveness_suite_v0_boundaries() {
    let out_dir = temp_dir("archmap-expressiveness-suite");
    let root = expressiveness_fixture_root();
    let archmap = root.join("archmap_expressiveness_suite_v0.json");
    let validation = out_dir.join("archmap-validation.json");
    let air = out_dir.join("air.json");
    let air_validation = out_dir.join("air-validation.json");
    let theorem_report = out_dir.join("theorem-check.json");
    let feature_report = out_dir.join("feature-report.json");

    run_sig0(&[
        "archmap",
        "--input",
        archmap.to_str().expect("fixture path is utf-8"),
        "--out",
        validation.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "air-from-archmap",
        "--archmap",
        archmap.to_str().expect("fixture path is utf-8"),
        "--validation",
        validation.to_str().expect("validation path is utf-8"),
        "--out",
        air.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "validate-air",
        "--input",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        air_validation.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "theorem-check",
        "--air",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        theorem_report.to_str().expect("output path is utf-8"),
    ]);
    run_sig0(&[
        "feature-report",
        "--air",
        air.to_str().expect("AIR path is utf-8"),
        "--out",
        feature_report.to_str().expect("output path is utf-8"),
    ]);

    let validation_json = read_json(&validation);
    assert_eq!(validation_json["summary"]["mapItemCount"], 10);
    assert_eq!(validation_json["summary"]["result"], "warn");
    assert!(
        validation_json["sourceInventoryChecks"]
            .as_array()
            .expect("source inventory checks are an array")
            .iter()
            .any(|check| check["id"] == "archmap-source-inventory-artifact"
                && check["result"] == "pass")
    );
    assert!(
        validation_json["leanPreservationVocabulary"]
            .as_array()
            .expect("vocabulary is an array")
            .iter()
            .any(|entry| {
                entry["vocabularyId"] == "archmap-runtime-static-disagreement-boundary"
                    && entry["leanPackageField"] == "CoverageExactnessBoundary"
            })
    );
    let checklist = validation_json["leanPreservationPreconditionChecklist"]
        .as_array()
        .expect("checklist is an array");
    for (map_item_id, field, status) in [
        (
            "layered_policy_violation",
            "LawPolicyPreservation",
            "satisfiedBySuppliedAssumption",
        ),
        (
            "srp_responsibility_split",
            "LawPolicyPreservation",
            "candidate",
        ),
        (
            "contract_preservation",
            "SemanticDiagramPreservation",
            "candidate",
        ),
        (
            "semantic_commutation",
            "SemanticCommutationPreservation",
            "candidate",
        ),
        (
            "semantic_non_commutation",
            "NonfillabilityWitnessPreservation",
            "candidate",
        ),
        (
            "event_sourcing_projection",
            "SemanticDiagramPreservation",
            "candidate",
        ),
        (
            "saga_compensation",
            "NonfillabilityWitnessPreservation",
            "candidate",
        ),
        (
            "runtime_static_disagreement",
            "CoverageExactnessBoundary",
            "blockedByUnmeasuredCoverage",
        ),
        (
            "framework_convention_boundary",
            "CoverageExactnessBoundary",
            "blockedByUnmeasuredCoverage",
        ),
        (
            "dynamic_plugin_blind_spot",
            "CoverageExactnessBoundary",
            "blockedByUnmeasuredCoverage",
        ),
    ] {
        assert!(
            checklist.iter().any(|entry| {
                entry["mapItemId"] == map_item_id
                    && entry["leanPackageField"] == field
                    && entry["status"] == status
            }),
            "{map_item_id} should map to {field} with {status}"
        );
    }
    assert!(
        validation_json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|entry| entry == "ArchMap validation does not prove architecture lawfulness")
    );

    let air_json = read_json(&air);
    assert_eq!(air_json["schema"], "aat-air/v0.5.0");
    assert!(
        air_json["semanticDiagrams"]
            .as_array()
            .expect("semantic diagrams are an array")
            .iter()
            .any(|diagram| diagram["id"] == "diagram-event-sourcing-projection")
    );
    assert!(
        air_json["nonfillabilityWitnesses"]
            .as_array()
            .expect("nonfillability witnesses are an array")
            .iter()
            .any(|witness| witness["witnessId"] == "witness-saga-compensation-gap")
    );
    let air_validation_json = read_json(&air_validation);
    assert_eq!(air_validation_json["summary"]["result"], "pass");

    let theorem_json = read_json(&theorem_report);
    let theorem_checklist = theorem_json["archmapPreservationPreconditionChecklist"]
        .as_array()
        .expect("theorem-check ArchMap checklist is an array");
    assert!(
        theorem_checklist.iter().any(|entry| {
            entry["mapItemId"] == "dynamic_plugin_blind_spot"
                && entry["leanPackageField"] == "CoverageExactnessBoundary"
                && entry["status"] == "blockedByMissingEvidence"
        }),
        "theorem-check keeps private dynamic plugin evidence out of proof promotion"
    );
    assert!(
        theorem_checklist.iter().any(|entry| {
            entry["mapItemId"] == "framework_convention_boundary"
                && entry["status"] == "blockedByUnmeasuredCoverage"
        }),
        "framework convention remains an unmeasured boundary"
    );

    let feature_json = read_json(&feature_report);
    assert_eq!(feature_json["schema"], "feature-extension-report/v0.5.0");
    assert!(
        feature_json["semanticPathSummary"]["nonfillabilityWitnessCount"]
            .as_u64()
            .expect("witness count is numeric")
            >= 2
    );
}

#[test]
fn cli_extracts_python_import_graph() {
    let root = python_fixture_root();
    let out_dir = temp_dir("python-import-graph");
    let sig0 = out_dir.join("sig0.json");

    run_sig0(&[
        "--language",
        "python",
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--source-root",
        "src",
        "--out",
        sig0.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&sig0);
    assert_eq!(json["schema"], "archsig-sig0/v0.5.0");
    assert_eq!(json["componentKind"], "python-module");
    assert!(
        json["components"]
            .as_array()
            .expect("components are an array")
            .iter()
            .any(|component| component["id"] == "app.service")
    );
    assert!(
        json["edges"]
            .as_array()
            .expect("edges are an array")
            .iter()
            .any(|edge| {
                edge["source"] == "app.service"
                    && edge["target"] == "app.util"
                    && edge["evidence"] == "from . import util"
            })
    );
    assert!(
        json["edges"]
            .as_array()
            .expect("edges are an array")
            .iter()
            .any(|edge| {
                edge["source"] == "app.service"
                    && edge["target"] == "requests"
                    && edge["evidence"] == "import requests as http"
            })
    );
    assert_eq!(
        json["metricStatus"]["pythonDynamicImportCoverage"]["measured"],
        false
    );
    assert_eq!(json["metricStatus"]["hasCycle"]["measured"], true);
    for kind in [
        "dynamic-import",
        "plugin-loading",
        "framework-convention",
        "generated-code",
        "notebook",
    ] {
        assert!(
            json["unsupportedConstructs"]
                .as_array()
                .expect("unsupportedConstructs are an array")
                .iter()
                .any(|construct| construct["kind"] == kind),
            "missing unsupported construct kind {kind}"
        );
    }
    assert!(
        json["metricStatus"]["pythonDynamicImportCoverage"]["reason"]
            .as_str()
            .expect("dynamic import coverage reason is a string")
            .contains("not counted as measured zero")
    );
    assert!(
        json["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs are an array")
            .iter()
            .any(|construct| {
                construct["kind"] == "dynamic-import"
                    && construct["path"] == "src/app/service.py"
                    && construct["line"] == 6
            })
    );
}

#[test]
fn cli_python_sig0_normalizes_to_air_and_reports_theorem_boundary() {
    let root = python_fixture_root();
    let out_dir = temp_dir("python-air");
    let sig0 = out_dir.join("python-sig0.json");
    let air = out_dir.join("python.air.json");
    let air_validation = out_dir.join("python-air-validation.json");
    let feature_report = out_dir.join("python-feature-report.json");
    let theorem_report = out_dir.join("python-theorem-check.json");
    let formal_air = out_dir.join("python-formal.air.json");
    let formal_theorem_report = out_dir.join("python-formal-theorem-check.json");

    run_sig0(&[
        "--language",
        "python",
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--source-root",
        "src",
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "air",
        "--sig0",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);

    let json = read_json(&air);
    assert_eq!(json["schema"], "aat-air/v0.5.0");
    assert_eq!(json["schemaCompatibility"]["artifactId"], "air");
    assert!(
        json["schemaCompatibility"]["fieldMappings"]
            .as_array()
            .expect("fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"] == "claims[].missingPreconditions")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "static"
                && boundary["coverageAssumptions"]
                    .as_array()
                    .expect("coverageAssumptions are an array")
                    .iter()
                    .any(|assumption| assumption
                        .as_str()
                        .expect("coverage assumption is a string")
                        .contains("dynamic-import")))
    );
    assert!(
        json["schemaCompatibility"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|conclusion| {
                conclusion == "compatibility pass does not promote tooling evidence to a Lean theorem claim"
            })
    );
    assert!(
        json["components"]
            .as_array()
            .expect("components are an array")
            .iter()
            .any(|component| component["id"] == "app.service"
                && component["kind"] == "python-module")
    );
    assert!(
        json["components"]
            .as_array()
            .expect("components are an array")
            .iter()
            .any(|component| component["id"] == "requests"
                && component["kind"] == "external-dependency")
    );
    assert!(
        json["relations"]
            .as_array()
            .expect("relations are an array")
            .iter()
            .any(|relation| {
                relation["layer"] == "static"
                    && relation["extractionRule"] == "python-import-graph/v0.5.0"
            })
    );
    assert!(
        json["relations"]
            .as_array()
            .expect("relations are an array")
            .iter()
            .any(|relation| {
                relation["from"] == "app.service"
                    && relation["to"] == "requests"
                    && relation["extractionRule"] == "python-import-graph/v0.5.0"
            })
    );
    assert!(
        json["evidence"]
            .as_array()
            .expect("evidence are an array")
            .iter()
            .any(|evidence| evidence["kind"] == "python_import")
    );
    let static_coverage = json["coverage"]["layers"]
        .as_array()
        .expect("coverage layers are an array")
        .iter()
        .find(|layer| layer["layer"] == "static")
        .expect("static coverage exists");
    assert_eq!(
        static_coverage["projectionRule"],
        "python-import-graph/v0.5.0"
    );
    assert!(
        static_coverage["extractionScope"]
            .as_array()
            .expect("extractionScope is an array")
            .iter()
            .any(|scope| scope == "static import graph from Python ast import/from nodes")
    );
    assert!(
        static_coverage["exactnessAssumptions"]
            .as_array()
            .expect("exactnessAssumptions is an array")
            .iter()
            .any(|assumption| {
                assumption
                    == "Python extractor output is tooling evidence, not a Lean ComponentUniverse completeness proof"
            })
    );
    assert!(
        static_coverage["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is an array")
            .iter()
            .any(|construct| construct
                .as_str()
                .expect("unsupported construct is a string")
                .contains("dynamic-import at src/app/service.py"))
    );
    assert!(
        static_coverage["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is an array")
            .iter()
            .any(|construct| construct
                .as_str()
                .expect("unsupported construct is a string")
                .contains("notebook at src/notebook.ipynb"))
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
    assert_eq!(read_json(&air_validation)["summary"]["result"], "pass");

    run_sig0(&[
        "feature-report",
        "--air",
        air.to_str().expect("air path is utf-8"),
        "--out",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
    ]);
    let feature_json = read_json(&feature_report);
    assert_eq!(feature_json["schema"], "feature-extension-report/v0.5.0");
    assert_eq!(
        feature_json["schemaCompatibility"]["artifactId"],
        "feature-extension-report"
    );
    assert!(
        feature_json["schemaCompatibility"]["fieldMappings"]
            .as_array()
            .expect("feature fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"]
                == "theoremPreconditionChecks[].missingPreconditions")
    );
    assert!(
        feature_json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("feature coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "semantic")
    );
    assert!(
        feature_json["architectureSummary"]["measuredAxes"]
            .as_array()
            .expect("measuredAxes are an array")
            .iter()
            .any(|axis| axis == "hasCycle")
    );
    assert!(
        feature_json["coverageGaps"]
            .as_array()
            .expect("coverageGaps are an array")
            .iter()
            .any(|gap| {
                gap["layer"] == "static"
                    && gap["unsupportedConstructs"]
                        .as_array()
                        .expect("unsupportedConstructs are an array")
                        .iter()
                        .any(|construct| {
                            construct
                                .as_str()
                                .expect("unsupported construct is a string")
                                .contains("plugin-loading")
                        })
            })
    );
    assert!(
        feature_json["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs are an array")
            .iter()
            .any(|construct| construct
                .as_str()
                .expect("unsupported construct is a string")
                .contains("static: generated-code"))
    );

    run_sig0(&[
        "theorem-check",
        "--air",
        air.to_str().expect("air path is utf-8"),
        "--out",
        theorem_report
            .to_str()
            .expect("theorem report path is utf-8"),
    ]);
    let theorem_json = read_json(&theorem_report);
    assert_eq!(
        theorem_json["summary"]["formalProvedClaimCount"],
        serde_json::json!(0)
    );
    assert!(
        theorem_json["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["subjectRef"] == "signature.hasCycle"
                    && check["resolvedClaimClassification"] == "MEASURED_WITNESS"
            })
    );

    let mut formal_json = json;
    formal_json["claims"]
        .as_array_mut()
        .expect("claims are an array")
        .push(serde_json::json!({
            "claimId": "claim-python-static-formal-blocked",
            "subjectRef": "signature.hasCycle",
            "predicate": "Python static import graph has no cycle as a Lean theorem claim",
            "claimLevel": "formal",
            "claimClassification": "proved",
            "measurementBoundary": "measuredZero",
            "theoremRefs": ["SelectedStaticSplitExtension"],
            "evidenceRefs": ["evidence-static-0001"],
            "requiredAssumptions": ["core edges are preserved"],
            "coverageAssumptions": ["static dependency graph is inside the measured universe"],
            "exactnessAssumptions": ["AIR component and relation identifiers match the Lean package parameters"],
            "missingPreconditions": [],
            "nonConclusions": ["Python extractor completeness is not concluded"]
        }));
    fs::write(
        &formal_air,
        serde_json::to_string_pretty(&formal_json).expect("formal AIR serializes"),
    )
    .expect("formal AIR fixture is written");
    run_sig0(&[
        "theorem-check",
        "--air",
        formal_air.to_str().expect("formal AIR path is utf-8"),
        "--out",
        formal_theorem_report
            .to_str()
            .expect("formal theorem report path is utf-8"),
    ]);
    let formal_report = read_json(&formal_theorem_report);
    let blocked = formal_report["checks"]
        .as_array()
        .expect("checks are an array")
        .iter()
        .find(|check| check["claimId"] == "claim-python-static-formal-blocked")
        .expect("formal Python claim is checked");
    assert_eq!(
        blocked["resolvedClaimClassification"],
        "BLOCKED_FORMAL_CLAIM"
    );
    assert!(
        blocked["missingPreconditions"]
            .as_array()
            .expect("missingPreconditions are an array")
            .iter()
            .any(|precondition| precondition.as_str().expect("precondition is string").contains(
                "Python import graph evidence requires an explicit Lean ComponentUniverse bridge precondition"
            ))
    );
}

#[test]
fn cli_traces_framework_adapter_fixture_to_air_and_feature_report() {
    let root = python_fixture_root();
    let adapter = python_framework_adapter_fixture();
    let out_dir = temp_dir("framework-adapter-air");
    let sig0 = out_dir.join("python-sig0.json");
    let air = out_dir.join("python-framework.air.json");
    let air_validation = out_dir.join("python-framework-air-validation.json");
    let feature_report = out_dir.join("python-framework-feature-report.json");

    run_sig0(&[
        "--language",
        "python",
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--source-root",
        "src",
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "air",
        "--sig0",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--framework-adapter",
        adapter.to_str().expect("adapter path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);

    let json = read_json(&air);
    assert!(
        json["artifacts"]
            .as_array()
            .expect("artifacts are an array")
            .iter()
            .any(|artifact| artifact["kind"] == "framework_adapter"
                && artifact["producedBy"] == "fastapi-route-adapter-fixture/v0.5.0")
    );
    assert!(
        json["evidence"]
            .as_array()
            .expect("evidence are an array")
            .iter()
            .any(|evidence| {
                evidence["kind"] == "framework_route"
                    && evidence["path"] == "src/app/web.py"
                    && evidence["symbol"] == "list_users"
            })
    );
    assert!(
        json["relations"]
            .as_array()
            .expect("relations are an array")
            .iter()
            .any(|relation| {
                relation["layer"] == "framework"
                    && relation["from"] == "app.web"
                    && relation["kind"] == "http_route_handler"
                    && relation["extractionRule"] == "fastapi-route-adapter-fixture/v0.5.0"
            })
    );
    let framework_coverage = json["coverage"]["layers"]
        .as_array()
        .expect("coverage layers are an array")
        .iter()
        .find(|layer| layer["layer"] == "framework")
        .expect("framework coverage exists");
    assert_eq!(
        framework_coverage["projectionRule"],
        "fastapi-route-adapter-fixture/v0.5.0"
    );
    assert_eq!(framework_coverage["measurementBoundary"], "measuredNonzero");
    assert!(
        framework_coverage["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs are an array")
            .iter()
            .any(|construct| construct
                .as_str()
                .expect("unsupported construct is a string")
                .contains("fastapi-dependency-injection"))
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
    assert_eq!(read_json(&air_validation)["summary"]["result"], "pass");

    run_sig0(&[
        "feature-report",
        "--air",
        air.to_str().expect("air path is utf-8"),
        "--out",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
    ]);
    let feature_json = read_json(&feature_report);
    assert!(
        feature_json["coverageGaps"]
            .as_array()
            .expect("coverageGaps are an array")
            .iter()
            .any(|gap| {
                gap["layer"] == "framework"
                    && gap["measurementBoundary"] == "measuredNonzero"
                    && gap["unsupportedConstructs"]
                        .as_array()
                        .expect("unsupportedConstructs are an array")
                        .iter()
                        .any(|construct| {
                            construct
                                .as_str()
                                .expect("unsupported construct is a string")
                                .contains("fastapi-dependency-injection")
                        })
            })
    );
    assert!(
        feature_json["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs are an array")
            .iter()
            .any(|construct| construct
                .as_str()
                .expect("unsupported construct is a string")
                .contains("framework: fastapi-dependency-injection"))
    );
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
    axis["source"] = serde_json::json!("runtime-edge-projection/v0.5.0");
    axis["reason"] = Value::Null;

    let layer = runtime_layer_mut(json);
    layer["measurementBoundary"] = serde_json::json!(measurement_boundary);
    layer["universeRefs"] = serde_json::json!(["artifact-sig0"]);
    layer["measuredAxes"] = serde_json::json!(["runtimePropagation"]);
    layer["unmeasuredAxes"] = serde_json::json!([]);
    layer["projectionRule"] = serde_json::json!("runtime-edge-projection/v0.5.0");
    layer["extractionScope"] = serde_json::json!([
        "runtime edge evidence JSON",
        "0/1 runtime dependency graph over measured component pairs"
    ]);
    layer["exactnessAssumptions"] = serde_json::json!([
        "runtime-edge-projection-schema050 maps each observed component pair to one runtime edge",
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
    claim["exactnessAssumptions"] =
        serde_json::json!(["runtime-edge-projection-schema050 exactness"]);
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
            "extractionRule": "runtime-edge-projection/v0.5.0",
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
    assert_eq!(json["schema"], "feature-extension-report/v0.5.0");
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
        "runtime-edge-projection/v0.5.0"
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
        "runtime-edge-projection/v0.5.0"
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
        assert!(
            json["repairSuggestions"]
                .as_array()
                .expect("repair suggestions are an array")
                .iter()
                .any(|suggestion| {
                    suggestion["targetWitnessKind"] == expected_kind
                        && suggestion["repairRuleId"].is_string()
                        && suggestion["sourceWitnessRefs"]
                            .as_array()
                            .expect("source witness refs are an array")
                            .iter()
                            .any(|witness_ref| {
                                witness_ref
                                    .as_str()
                                    .unwrap_or_default()
                                    .starts_with("witness-")
                            })
                        && suggestion["requiredPreconditions"]
                            .as_array()
                            .expect("required preconditions are an array")
                            .iter()
                            .any(|precondition| {
                                precondition
                                    .as_str()
                                    .unwrap_or_default()
                                    .contains("evidence")
                                    || precondition
                                        .as_str()
                                        .unwrap_or_default()
                                        .contains("interface")
                                    || precondition.as_str().unwrap_or_default().contains("edge")
                            })
                        && suggestion["possibleSideEffects"]
                            .as_array()
                            .expect("side effects are an array")
                            .iter()
                            .any(|effect| !effect.as_str().unwrap_or_default().is_empty())
                        && suggestion["nonConclusions"]
                            .as_array()
                            .expect("non conclusions are an array")
                            .iter()
                            .any(|conclusion| conclusion == "repair success is not concluded")
                })
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
    assert!(
        json["repairSuggestions"]
            .as_array()
            .expect("repair suggestions are an array")
            .iter()
            .any(|suggestion| {
                suggestion["targetWitnessKind"] == "coverage_gap"
                    && suggestion["sourceCoverageGapRefs"]
                        .as_array()
                        .expect("source coverage gap refs are an array")
                        .iter()
                        .any(|gap_ref| {
                            gap_ref
                                .as_str()
                                .unwrap_or_default()
                                .starts_with("coverage-gap-")
                        })
                    && suggestion["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|conclusion| conclusion == "all obstruction removal is not concluded")
            })
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
    assert_eq!(report["schema"], "theorem-precondition-check-report/v0.5.0");
    assert_eq!(
        report["registry"]["scope"],
        "static, runtime, semantic, and synthesis theorem package registry v0"
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
fn cli_repair_registry_reports_static_rules_and_boundaries() {
    let out_dir = temp_dir("repair-registry-static");
    let report = out_dir.join("repair-registry.json");

    run_sig0(&[
        "repair-registry",
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(
        report["schema"],
        "repair-rule-registry-validation-report/v0.5.0"
    );
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(report["registry"]["schema"], "repair-rule-registry/v0.5.0");
    assert!(
        report["registry"]["rules"]
            .as_array()
            .expect("repair rules are an array")
            .iter()
            .any(|rule| {
                rule["repairRuleId"] == "repair-hidden-interaction-through-interface/v0.5.0"
                    && rule["targetWitnessKind"] == "hidden_interaction"
                    && rule["relativeTo"]["selectedObstructionUniverse"]
                        == "selected obstruction witnesses in the current Feature Extension Report"
                    && rule["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|boundary| boundary == "all obstruction removal is not concluded")
            })
    );
}

#[test]
fn cli_repair_registry_rejects_invalid_success_boundary() {
    let out_dir = temp_dir("repair-registry-invalid");
    let input = out_dir.join("invalid-repair-registry.json");
    let report = out_dir.join("invalid-repair-registry-report.json");

    fs::write(
        &input,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "repair-rule-registry/v0.5.0",
            "scope": "invalid fixture",
            "selectedObstructionUniverse": "",
            "explicitAssumptions": [],
            "rules": [{
                "repairRuleId": "bad-rule",
                "targetWitnessKind": "unknown_witness",
                "proposedOperation": "auto_rewrite",
                "requiredPreconditions": [],
                "expectedEffect": "guarantee",
                "preservedInvariants": [],
                "possibleSideEffects": [],
                "proofObligationRefs": [],
                "patchStrategy": "autonomous",
                "confidence": "certain",
                "relativeTo": {
                    "selectedObstructionUniverse": "",
                    "explicitAssumptions": []
                },
                "nonConclusions": []
            }],
            "nonConclusions": []
        }))
        .expect("json serializes"),
    )
    .expect("invalid repair registry input is written");

    let output = run_sig0_output(&[
        "repair-registry",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(!output.status.success());

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "repair-rule-non-conclusion-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_synthesis_constraints_reports_static_candidate_boundary() {
    let root = fixture_root();
    let out_dir = temp_dir("synthesis-constraints-static");
    let report = out_dir.join("synthesis-constraints.json");

    run_sig0(&[
        "synthesis-constraints",
        "--input",
        root.join("synthesis_constraints_candidate.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(
        report["schema"],
        "synthesis-constraint-validation-report/v0.5.0"
    );
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(
        report["artifact"]["schema"],
        "synthesis-constraint-artifact/v0.5.0"
    );
    assert!(
        report["artifact"]["candidates"]
            .as_array()
            .expect("synthesis candidates are an array")
            .iter()
            .any(|candidate| {
                candidate["candidateId"] == "candidate-split-coupon-interface/v0.5.0"
                    && candidate["constraintRefs"]
                        .as_array()
                        .expect("constraint refs are an array")
                        .iter()
                        .any(|constraint_ref| {
                            constraint_ref == "constraint-static-boundary-coupon/v0.5.0"
                        })
                    && candidate["soundnessPackageRefs"]
                        .as_array()
                        .expect("soundness package refs are an array")
                        .iter()
                        .any(|package_ref| {
                            package_ref == "SynthesisSoundnessPackage.candidate_satisfies"
                        })
                    && candidate["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|boundary| boundary == "solver completeness is not concluded")
            })
    );
    assert_eq!(
        report["artifact"]["noSolutionBoundary"]["solverStatus"],
        "candidate_produced"
    );
    assert!(
        report["artifact"]["noSolutionBoundary"]["nonConclusions"]
            .as_array()
            .expect("no-solution non conclusions are an array")
            .iter()
            .any(|boundary| boundary
                == "solver no-candidate result is not a no-solution certificate")
    );
}

#[test]
fn cli_synthesis_constraints_reports_valid_no_solution_certificate_boundary() {
    let root = fixture_root();
    let out_dir = temp_dir("synthesis-constraints-no-solution");
    let report = out_dir.join("synthesis-constraints-no-solution.json");

    run_sig0(&[
        "synthesis-constraints",
        "--input",
        root.join("synthesis_constraints_no_solution_certificate.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(
        report["artifact"]["noSolutionBoundary"]["solverStatus"],
        "certificate_supplied"
    );
    assert_eq!(
        report["artifact"]["noSolutionBoundary"]["noSolutionCertificateRef"],
        "certificate-coupon-no-solution/v0.5.0"
    );
    assert!(
        report["artifact"]["noSolutionBoundary"]["nonConclusions"]
            .as_array()
            .expect("no-solution non conclusions are an array")
            .iter()
            .any(|boundary| boundary == "solver completeness is not concluded")
    );
}

#[test]
fn cli_synthesis_constraints_rejects_solver_completeness_confusion() {
    let out_dir = temp_dir("synthesis-constraints-invalid");
    let input = out_dir.join("invalid-synthesis-constraints.json");
    let report = out_dir.join("invalid-synthesis-constraints-report.json");

    fs::write(
        &input,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "synthesis-constraint-artifact/v0.5.0",
            "scope": "invalid fixture",
            "constraintRefs": ["missing-constraint"],
            "candidateRefs": ["missing-candidate"],
            "requiredAssumptions": [],
            "coverageAssumptions": [],
            "exactnessAssumptions": [],
            "unsupportedConstructs": [],
            "constraints": [{
                "constraintId": "bad-constraint",
                "kind": "global",
                "subjectRef": "",
                "predicate": "",
                "evidenceRefs": [],
                "theoremPreconditionRefs": []
            }],
            "candidates": [{
                "candidateId": "bad-candidate",
                "producedBy": "",
                "operationRefs": [],
                "constraintRefs": ["missing-constraint"],
                "soundnessPackageRefs": [],
                "requiredAssumptions": [],
                "coverageAssumptions": [],
                "exactnessAssumptions": [],
                "unsupportedConstructs": [],
                "nonConclusions": []
            }],
            "noSolutionBoundary": {
                "solverStatus": "no_candidate",
                "candidateRefs": [],
                "noSolutionCertificateRef": null,
                "validCertificateClaimRef": null,
                "nonConclusions": []
            },
            "nonConclusions": []
        }))
        .expect("json serializes"),
    )
    .expect("invalid synthesis constraints input is written");

    let output = run_sig0_output(&[
        "synthesis-constraints",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(!output.status.success());

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "synthesis-no-solution-boundary-distinguished"
                    && check["result"] == "fail"
            })
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "synthesis-non-conclusion-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_no_solution_certificate_accepts_valid_certificate() {
    let root = fixture_root();
    let out_dir = temp_dir("no-solution-certificate-valid");
    let report = out_dir.join("no-solution-certificate.json");

    run_sig0(&[
        "no-solution-certificate",
        "--input",
        root.join("no_solution_certificate_valid.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(report["summary"]["caseCount"], 2);
    assert_eq!(
        report["certificate"]["validCertificateClaimRef"],
        "claim-valid-no-solution-certificate"
    );
    assert!(
        report["certificate"]["proofObligationRefs"]
            .as_array()
            .expect("proof obligation refs are an array")
            .iter()
            .any(|proof_ref| proof_ref == "NoSolutionCertificate.sound_of_valid")
    );
    assert!(
        report["certificate"]["nonConclusions"]
            .as_array()
            .expect("non conclusions are an array")
            .iter()
            .any(|boundary| boundary
                == "solver no-candidate result is not a no-solution certificate")
    );
}

#[test]
fn cli_no_solution_certificate_rejects_missing_certificate_claim() {
    let out_dir = temp_dir("no-solution-certificate-invalid");
    let input = out_dir.join("invalid-no-solution-certificate.json");
    let report = out_dir.join("invalid-no-solution-certificate-report.json");

    fs::write(
        &input,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "no-solution-certificate/v0.5.0",
            "certificateId": "certificate-invalid",
            "scope": "invalid fixture",
            "constraintRefs": ["constraint-static-boundary-coupon/v0.5.0"],
            "refutedCandidateRefs": ["candidate-direct-cache-access/v0.5.0"],
            "obstructionWitnessRefs": ["witness-hidden-cache-access"],
            "requiredAssumptions": ["candidate universe is finite"],
            "coverageAssumptions": ["cases cover recorded candidates"],
            "exactnessAssumptions": ["case refs match selected package"],
            "unsupportedConstructs": [],
            "proofObligationRefs": [],
            "validCertificateClaimRef": null,
            "cases": [{
                "caseId": "case-invalid",
                "constraintRefs": ["constraint-static-boundary-coupon/v0.5.0"],
                "refutedCandidateRef": "candidate-direct-cache-access/v0.5.0",
                "evidenceRefs": ["evidence-hidden-edge"],
                "theoremPreconditionRefs": ["ValidNoSolutionCertificate"],
                "reason": "candidate remains blocked"
            }],
            "nonConclusions": []
        }))
        .expect("json serializes"),
    )
    .expect("invalid no-solution certificate input is written");

    let output = run_sig0_output(&[
        "no-solution-certificate",
        "--input",
        input.to_str().expect("input path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(!output.status.success());

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "fail");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "no-solution-certificate-validity-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["id"] == "no-solution-certificate-non-conclusion-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_validate_air_accepts_b5_repair_synthesis_boundary_fixture() {
    let root = air_fixture_root();
    let out_dir = temp_dir("air-b5-boundary");
    let report = out_dir.join("air-b5-boundary-validation.json");

    run_sig0(&[
        "validate-air",
        "--input",
        root.join("repair_synthesis_boundary.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(report["summary"]["claimCount"], 4);
}

#[test]
fn cli_feature_report_keeps_b5_repair_suggestions_advisory() {
    let root = air_fixture_root();
    let out_dir = temp_dir("feature-report-b5");
    let report = out_dir.join("feature-report-b5.json");

    run_sig0(&[
        "feature-report",
        "--air",
        root.join("repair_synthesis_boundary.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(report["splitStatus"], "non_split");
    assert!(
        report["repairSuggestions"]
            .as_array()
            .expect("repair suggestions are an array")
            .iter()
            .any(|suggestion| {
                suggestion["targetWitnessKind"] == "hidden_interaction"
                    && suggestion["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|boundary| boundary == "repair success is not concluded")
                    && suggestion["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|boundary| boundary == "global flatness preservation is not concluded")
            })
    );
}

#[test]
fn cli_theorem_check_reports_no_solution_certificate_package_boundary() {
    let root = air_fixture_root();
    let out_dir = temp_dir("theorem-check-b5");
    let report = out_dir.join("theorem-check-b5.json");

    run_sig0(&[
        "theorem-check",
        "--air",
        root.join("repair_synthesis_boundary.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| {
                check["claimId"] == "claim-valid-no-solution-certificate"
                    && check["resolvedClaimClassification"] == "FORMAL_PROVED"
                    && check["applicablePackageRefs"]
                        .as_array()
                        .expect("package refs are an array")
                        .iter()
                        .any(|package_ref| package_ref == "no-solution-certificate-package/v0.5.0")
                    && check["nonConclusions"]
                        .as_array()
                        .expect("non conclusions are an array")
                        .iter()
                        .any(|boundary| boundary == "solver completeness is not concluded")
            })
    );
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
                package["packageId"] == "semantic-nonfillability-package/v0.5.0"
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
                    package["packageId"] == "semantic-numerical-curvature-zero-package/v0.5.0";
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
                        .any(|package_ref| package_ref == "semantic-nonfillability-package/v0.5.0")
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
        serde_json::json!(["runtime-edge-projection-schema050 exactness"]),
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
            .any(|package| package["packageId"] == "runtime-zero-bridge-package/v0.5.0"
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
                    && check["projectionRule"] == "runtime-edge-projection/v0.5.0"
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
        "ai_metadata_missing_unmeasured.json",
        "ai_session_generated_patch.json",
        "ai_session_hidden_complexity_warning.json",
        "ai_session_split_candidate.json",
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
        assert_eq!(json["schema"], "aat-air-validation-report/v0.5.0");
        assert_eq!(json["summary"]["result"], "pass");
        assert_eq!(json["summary"]["failedCheckCount"], 0);
    }
}

#[test]
fn cli_feature_report_locks_ai_generated_split_candidate_and_missing_metadata_boundaries() {
    let root = air_fixture_root();
    let out_dir = temp_dir("ai-generated-canonical-boundaries");

    let split_report = out_dir.join("ai-split-candidate.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("ai_session_split_candidate.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        split_report.to_str().expect("report path is utf-8"),
    ]);
    let split = read_json(&split_report);
    assert_eq!(
        split["architectureId"],
        "canonical-ai-session-split-candidate"
    );
    assert_eq!(split["splitStatus"], "split");
    assert_eq!(split["generatedPatchSummary"]["isAiSession"], true);
    assert_eq!(split["generatedPatchSummary"]["generatedPatch"], true);
    assert_eq!(split["generatedPatchSummary"]["humanReviewed"], true);
    assert!(
        split["introducedObstructionWitnesses"]
            .as_array()
            .expect("obstruction witnesses is array")
            .is_empty()
    );
    assert!(
        split["theoremPreconditionChecks"]
            .as_array()
            .expect("theorem checks is array")
            .iter()
            .any(
                |check| check["claimId"] == "claim-ai-generated-static-split-reviewed"
                    && check["resolvedClaimClassification"] == "FORMAL_PROVED"
            )
    );
    assert!(
        split["generatedPatchSummary"]["nonConclusions"]
            .as_array()
            .expect("generated patch non-conclusions is array")
            .iter()
            .any(|conclusion| conclusion
                == "AI generated status is not evidence for architecture lawfulness")
    );

    let missing_report = out_dir.join("ai-metadata-missing.report.json");
    run_sig0(&[
        "feature-report",
        "--air",
        root.join("ai_metadata_missing_unmeasured.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        missing_report.to_str().expect("report path is utf-8"),
    ]);
    let missing = read_json(&missing_report);
    assert_eq!(
        missing["architectureId"],
        "canonical-ai-metadata-missing-unmeasured"
    );
    assert_eq!(missing["splitStatus"], "unmeasured");
    assert_eq!(
        missing["reviewSummary"]["claimClassification"],
        "UNMEASURED"
    );
    assert_eq!(missing["generatedPatchSummary"]["isAiSession"], false);
    assert_eq!(missing["generatedPatchSummary"]["generatedPatch"], true);
    assert_eq!(
        missing["generatedPatchSummary"]["humanReviewed"],
        Value::Null
    );
    assert!(
        missing["coverageGaps"]
            .as_array()
            .expect("coverage gaps is array")
            .iter()
            .any(|gap| gap["layer"] == "provenance"
                && gap["measurementBoundary"] == "UNMEASURED"
                && gap["unmeasuredAxes"]
                    .as_array()
                    .expect("static gap axes is array")
                    .iter()
                    .any(|axis| axis == "boundaryViolationCount"))
    );
    assert!(
        missing["generatedPatchSummary"]["operations"]
            .as_array()
            .expect("operations is array")
            .iter()
            .any(|operation| {
                operation["operationRef"]
                    == "generated_patch artifact-generated-patch adds relation-static-coupon-service"
                    && operation["addedRelations"]
                        .as_array()
                        .expect("added relations is array")
                        .iter()
                        .any(|relation| relation["relationId"]
                            == "relation-static-coupon-service")
            })
    );
    assert!(
        missing["nonConclusions"]
            .as_array()
            .expect("non-conclusions is array")
            .iter()
            .any(|conclusion| conclusion
                == "generated patch artifact alone is not AI session traceability")
    );
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
fn cli_validate_air_detects_incomplete_schema_compatibility_metadata() {
    let root = air_fixture_root();
    let out_dir = temp_dir("validate-air-schema-compatibility-invalid");
    let input = out_dir.join("invalid-schema-compatibility-air.json");
    let report = out_dir.join("invalid-schema-compatibility-air-report.json");
    let mut json = read_json(&root.join("good_extension.json"));

    json["schemaCompatibility"] = serde_json::json!({
        "artifactId": "air",
        "schemaName": "aat-air/v0.5.0",
        "compatibilityPolicyRef": "b9-compatibility-policy/v0.5.0",
        "fieldMappings": [],
        "deprecatedFields": [],
        "requiredAssumptions": [],
        "coverageExactnessBoundaries": [],
        "nonConclusions": []
    });
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
        "invalid schema compatibility metadata should fail"
    );
    let report = read_json(&report);
    assert!(
        report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "air-schema-compatibility-metadata-complete"
                    && check["result"] == "fail"
            )
    );
}

#[test]
fn cli_schema_compatibility_accepts_backward_compatible_sig0_fixture() {
    let root = fixture_root();
    let out_dir = temp_dir("schema-compatibility-sig0");
    let sig0 = out_dir.join("sig0.json");
    let report = out_dir.join("schema-compatibility-report.json");

    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "schema-compatibility",
        "--before",
        sig0.to_str().expect("before path is utf-8"),
        "--after",
        sig0.to_str().expect("after path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);

    let report = read_json(&report);
    assert_eq!(report["schema"], "schema-compatibility-check-report/v0.5.0");
    assert_eq!(report["summary"]["result"], "pass");
    assert_eq!(report["after"]["artifactId"], "signature-artifact");
    assert_eq!(
        report["after"]["hasSchemaCompatibilityMetadata"], false,
        "B0-B8 Sig0 fixture remains backward-compatible input"
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(
                |check| check["id"] == "schema-compatibility-metadata-present"
                    && check["severity"] == "warning"
            )
    );
    assert!(
        report["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|item| item
                .as_str()
                .expect("nonConclusion is a string")
                .contains("semantic-preservation"))
    );
}

#[test]
fn cli_schema_compatibility_blocks_missing_formal_claim_guardrail() {
    let root = python_fixture_root();
    let out_dir = temp_dir("schema-compatibility-formal-claim");
    let sig0 = out_dir.join("python-sig0.json");
    let air = out_dir.join("python.air.json");
    let before = out_dir.join("feature-report-before.json");
    let after = out_dir.join("feature-report-after.json");
    let report = out_dir.join("schema-compatibility-report.json");

    run_sig0(&[
        "--language",
        "python",
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--source-root",
        "src",
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    run_sig0(&[
        "air",
        "--sig0",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--out",
        air.to_str().expect("air path is utf-8"),
    ]);
    run_sig0(&[
        "feature-report",
        "--air",
        air.to_str().expect("air path is utf-8"),
        "--out",
        before.to_str().expect("feature report path is utf-8"),
    ]);

    let mut json = read_json(&before);
    json["schemaCompatibility"]["nonConclusions"] =
        serde_json::json!(["schema compatibility metadata does not prove semantic preservation"]);
    fs::write(
        &after,
        serde_json::to_string_pretty(&json).expect("json serializes"),
    )
    .expect("after feature report is written");

    let output = run_sig0_output(&[
        "schema-compatibility",
        "--before",
        before.to_str().expect("before path is utf-8"),
        "--after",
        after.to_str().expect("after path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "missing formal claim guardrail should fail compatibility check"
    );

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "blockedFormalClaimPromotion");
    assert!(
        report["fieldMappings"]
            .as_array()
            .expect("fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"] == "nonConclusions")
    );
    assert!(
        report["newRequiredAssumptions"]
            .as_array()
            .expect("newRequiredAssumptions are an array")
            .iter()
            .any(|assumption| assumption["fallbackWhenMissing"]
                .as_str()
                .expect("fallbackWhenMissing is a string")
                .contains("do not infer"))
    );
    assert!(
        report["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "runtime")
    );
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(|check| check["id"] == "formal-claim-promotion-blocked"
                && check["result"] == "blockedFormalClaimPromotion")
    );
}

#[test]
fn cli_schema_compatibility_locks_obstruction_witness_and_drift_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("schema-compatibility-obstruction-drift");
    let witness = root.join("obstruction_witness.json");
    let ledger = root.join("architecture_drift_ledger.json");
    let witness_pass = out_dir.join("witness-pass.json");
    let ledger_pass = out_dir.join("ledger-pass.json");
    let ledger_after = out_dir.join("architecture-drift-ledger-rounded.json");
    let ledger_report = out_dir.join("ledger-rounded-report.json");

    run_sig0(&[
        "schema-compatibility",
        "--before",
        witness.to_str().expect("witness path is utf-8"),
        "--after",
        witness.to_str().expect("witness path is utf-8"),
        "--out",
        witness_pass.to_str().expect("witness report path is utf-8"),
    ]);
    let witness_report = read_json(&witness_pass);
    assert_eq!(witness_report["summary"]["result"], "pass");
    assert_eq!(witness_report["after"]["artifactId"], "obstruction-witness");
    assert!(
        witness_report["coverageExactnessBoundaries"]
            .as_array()
            .expect("witness boundaries are an array")
            .iter()
            .any(
                |boundary| boundary["axisOrLayer"] == "witness.evidence.private-or-missing"
                    && boundary["measurementBoundary"] == "unmeasured"
            )
    );

    run_sig0(&[
        "schema-compatibility",
        "--before",
        ledger.to_str().expect("ledger path is utf-8"),
        "--after",
        ledger.to_str().expect("ledger path is utf-8"),
        "--out",
        ledger_pass.to_str().expect("ledger report path is utf-8"),
    ]);
    let pass_report = read_json(&ledger_pass);
    assert_eq!(pass_report["summary"]["result"], "pass");
    assert_eq!(
        pass_report["after"]["artifactId"],
        "architecture-drift-ledger"
    );
    assert!(
        pass_report["fieldMappings"]
            .as_array()
            .expect("ledger fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"] == "retentionManifestRef")
    );
    assert!(
        pass_report["fieldMappings"]
            .as_array()
            .expect("ledger fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"] == "suppressionWorkflowRefs")
    );

    let mut rounded = read_json(&ledger);
    rounded["schemaCompatibility"]["coverageExactnessBoundaries"][1]["measurementBoundary"] =
        serde_json::json!("measuredZero");
    rounded["entries"][1]["measurementBoundary"] = serde_json::json!("measuredZero");
    fs::write(
        &ledger_after,
        serde_json::to_string_pretty(&rounded).expect("ledger json serializes"),
    )
    .expect("rounded ledger fixture is written");

    let output = run_sig0_output(&[
        "schema-compatibility",
        "--before",
        ledger.to_str().expect("ledger path is utf-8"),
        "--after",
        ledger_after.to_str().expect("rounded ledger path is utf-8"),
        "--out",
        ledger_report.to_str().expect("ledger report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "rounding unmeasured evidence to measuredZero should require migration"
    );

    let report = read_json(&ledger_report);
    assert_eq!(report["summary"]["result"], "requiresMigration");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(
                |check| check["id"] == "coverage-exactness-boundaries-preserved"
                    && check["severity"] == "migrationRequired"
                    && check["message"]
                        .as_str()
                        .expect("message is a string")
                        .contains("ledger.private-or-missing-evidence:unmeasured")
            )
    );
}

#[test]
fn cli_reported_axes_catalog_locks_benchmark_and_axis_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("reported-axes-catalog");
    let generated = out_dir.join("reported-axes-catalog.json");
    let changed = out_dir.join("reported-axes-catalog-boundary-change.json");
    let report = out_dir.join("reported-axes-compatibility-report.json");

    run_sig0(&[
        "reported-axes-catalog",
        "--out",
        generated.to_str().expect("catalog path is utf-8"),
    ]);
    let json = read_json(&generated);
    assert_eq!(
        json["schema"],
        "detectable-values-reported-axes-catalog/v0.5.0"
    );
    assert_eq!(
        json["benchmarkSuiteVersion"],
        "archsig-benchmark-suite/v0.5.0"
    );
    assert!(
        json["frozenFixtures"]
            .as_array()
            .expect("frozenFixtures are an array")
            .iter()
            .any(|fixture| fixture["expectedBoundaries"]
                .as_array()
                .expect("expectedBoundaries are an array")
                .iter()
                .any(|boundary| boundary == "runtimePropagation:unmeasured"))
    );

    let mut changed_json = read_json(&root.join("detectable_values_reported_axes_catalog.json"));
    changed_json["axes"]
        .as_array_mut()
        .expect("axes are an array")
        .iter_mut()
        .find(|axis| axis["axisId"] == "runtimePropagation")
        .expect("runtimePropagation axis exists")["defaultMeasurementBoundary"] =
        serde_json::json!("measuredZero");
    fs::write(
        &changed,
        serde_json::to_string_pretty(&changed_json).expect("changed catalog serializes"),
    )
    .expect("changed catalog is written");

    let output = run_sig0_output(&[
        "schema-compatibility",
        "--before",
        root.join("detectable_values_reported_axes_catalog.json")
            .to_str()
            .expect("before catalog path is utf-8"),
        "--after",
        changed.to_str().expect("changed catalog path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "measurement boundary change should require migration"
    );

    let report = read_json(&report);
    assert_eq!(report["summary"]["result"], "requiresMigration");
    assert!(
        report["checks"]
            .as_array()
            .expect("checks are an array")
            .iter()
            .any(
                |check| check["id"] == "reported-axes-measurement-boundary-preserved"
                    && check["severity"] == "migrationRequired"
                    && check["message"]
                        .as_str()
                        .expect("message is a string")
                        .contains("runtimePropagation")
            )
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
    assert_eq!(json["schema"], "archsig-sig0/v0.5.0");
    assert_eq!(json["policies"]["policyId"], "minimal-measured-zero");
    assert_eq!(
        json["metricStatus"]["boundaryViolationCount"]["measured"],
        true
    );
    assert_eq!(json["metricStatus"]["runtimePropagation"]["measured"], true);
    assert_eq!(
        json["runtimeDependencyGraph"]["projectionRule"],
        "runtime-edge-projection/v0.5.0"
    );
    assert_eq!(
        json["runtimeEdgeEvidence"][0]["evidenceLocation"]["path"],
        "runtime/routes.json"
    );
}

#[test]
fn cli_evaluates_architecture_policy_law_report_and_python_policy_status() {
    let root = fixture_root();
    let out_dir = temp_dir("architecture-policy");
    let policy = root.join("architecture_policy.json");
    let validation = out_dir.join("architecture-policy-validation.json");
    let sig0 = out_dir.join("sig0.json");
    let report = out_dir.join("law-violation-report.json");
    let python_sig0 = out_dir.join("python-sig0.json");

    run_sig0(&[
        "architecture-policy",
        "--input",
        policy.to_str().expect("policy path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schema"],
        "architecture-policy-validation-report/v0.5.0"
    );
    assert_eq!(validation_json["summary"]["result"], "pass");
    assert!(
        validation_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| check["id"] == "architecture-policy-srp-evidence-boundary-recorded")
    );
    assert!(
        validation_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| {
                check["id"] == "architecture-policy-sft-governance-boundary-recorded"
                    && check["result"] == "pass"
            })
    );
    assert!(
        validation_json["policy"]["sftGovernance"]["forbiddenFuturePathClasses"]
            .as_array()
            .expect("forbidden futures are array")
            .iter()
            .any(|rule| rule["disposition"] == "forbidden")
    );

    run_sig0(&[
        "--root",
        root.to_str().expect("fixture path is utf-8"),
        "--policy",
        policy.to_str().expect("policy path is utf-8"),
        "--out",
        sig0.to_str().expect("sig0 path is utf-8"),
    ]);
    let sig0_json = read_json(&sig0);
    assert_eq!(
        sig0_json["policies"]["schema"],
        "architecture-policy/v0.5.0"
    );
    assert_eq!(
        sig0_json["metricStatus"]["boundaryViolationCount"]["measured"],
        true
    );
    assert_eq!(sig0_json["signature"]["boundaryViolationCount"], 1);
    assert!(
        sig0_json["policyViolations"]
            .as_array()
            .expect("policy violations are array")
            .iter()
            .any(|violation| {
                violation["relationIds"]
                    .as_array()
                    .expect("relation ids are array")
                    .iter()
                    .any(|id| id == "forbid-domain-app")
            })
    );

    run_sig0(&[
        "law-violation-report",
        "--sig0",
        sig0.to_str().expect("sig0 path is utf-8"),
        "--policy",
        policy.to_str().expect("policy path is utf-8"),
        "--out",
        report.to_str().expect("report path is utf-8"),
    ]);
    let report_json = read_json(&report);
    assert_eq!(report_json["schema"], "law-violation-report/v0.5.0");
    assert_eq!(report_json["summary"]["deterministicViolationCount"], 1);
    assert!(
        report_json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are array")
            .iter()
            .any(|entry| entry == "SRP findings are evidence cues for LLM review, not tool-only violation judgments")
    );

    let python_root = python_fixture_root();
    run_sig0(&[
        "--language",
        "python",
        "--root",
        python_root.to_str().expect("python fixture path is utf-8"),
        "--source-root",
        "src",
        "--package-root",
        "src",
        "--policy",
        policy.to_str().expect("policy path is utf-8"),
        "--out",
        python_sig0.to_str().expect("python sig0 path is utf-8"),
    ]);
    let python_json = read_json(&python_sig0);
    assert_eq!(
        python_json["policies"]["schema"],
        "architecture-policy/v0.5.0"
    );
    assert_eq!(
        python_json["metricStatus"]["boundaryViolationCount"]["measured"], false,
        "selector mismatch must stay unmeasured instead of measured zero"
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
    assert_eq!(json["schema"], "empirical-signature-dataset/v0.5.0");
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
fn cli_pr_history_dataset_generates_record_from_github_json() {
    let root = fixture_root();
    let out_dir = temp_dir("pr-history-dataset");
    let out = out_dir.join("pr_history_dataset.json");

    run_sig0(&[
        "pr-history-dataset",
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
        "--signature-artifact",
        "base=artifacts/signature-before.json",
        "--signature-artifact",
        "head=artifacts/signature-after.json",
        "--feature-report-artifact",
        "artifacts/feature-extension-report.json",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "pr-history-dataset/v0.5.0");
    assert_eq!(json["repository"]["owner"], "example");
    assert_eq!(json["records"][0]["pullRequest"]["number"], 42);
    assert_eq!(
        json["records"][0]["changedFileSummary"]["changedComponents"],
        serde_json::json!(["Formal", "Formal.Arch.A"])
    );
    assert_eq!(json["records"][0]["changedFileSummary"]["changedFiles"], 3);
    assert_eq!(
        json["records"][0]["changedFileSummary"]["files"][0]["path"],
        "Formal.lean"
    );
    assert_eq!(json["records"][0]["reviewMetadata"]["reviewerCount"], 1);
    assert_eq!(
        json["records"][0]["reviewMetadata"]["reviewStates"],
        serde_json::json!(["COMMENTED"])
    );
    assert_eq!(
        json["records"][0]["artifactRefs"]["signatureArtifacts"][0]["commitRole"],
        "base"
    );
    assert_eq!(
        json["records"][0]["artifactRefs"]["featureExtensionReports"][0]["schema"],
        "feature-extension-report/v0.5.0"
    );
    assert!(
        json["analysisMetadata"]["nonConclusions"]
            .as_array()
            .expect("non-conclusions are an array")
            .iter()
            .any(|claim| claim == "does not conclude architecture lawfulness")
    );
}

#[test]
fn cli_feature_extension_dataset_joins_pr_history_and_feature_report() {
    let github_root = fixture_root();
    let air_root = air_fixture_root();
    let out_dir = temp_dir("feature-extension-dataset");
    let feature_report = out_dir.join("feature-extension-report.json");
    let theorem_check = out_dir.join("theorem-check.json");
    let pr_history = out_dir.join("pr-history.json");
    let dataset = out_dir.join("feature-extension-dataset.json");

    run_sig0(&[
        "feature-report",
        "--air",
        air_root
            .join("good_extension.json")
            .to_str()
            .expect("AIR path is utf-8"),
        "--out",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
    ]);
    run_sig0(&[
        "theorem-check",
        "--air",
        air_root
            .join("good_extension.json")
            .to_str()
            .expect("AIR path is utf-8"),
        "--out",
        theorem_check.to_str().expect("theorem check path is utf-8"),
    ]);
    run_sig0(&[
        "pr-history-dataset",
        "--pull-request",
        github_root
            .join("github_pr.json")
            .to_str()
            .expect("pull request path is utf-8"),
        "--files",
        github_root
            .join("github_files.json")
            .to_str()
            .expect("files path is utf-8"),
        "--feature-report-artifact",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
        "--out",
        pr_history.to_str().expect("PR history path is utf-8"),
    ]);
    run_sig0(&[
        "feature-extension-dataset",
        "--pr-history",
        pr_history.to_str().expect("PR history path is utf-8"),
        "--feature-report",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
        "--theorem-check-report",
        theorem_check.to_str().expect("theorem check path is utf-8"),
        "--out",
        dataset.to_str().expect("dataset path is utf-8"),
    ]);

    let json = read_json(&dataset);
    assert_eq!(json["schema"], "feature-extension-dataset/v0.5.0");
    assert_eq!(json["repository"]["owner"], "example");
    assert_eq!(json["records"][0]["pullRequest"]["number"], 42);
    assert_eq!(json["records"][0]["splitStatus"], "split");
    assert_eq!(
        json["records"][0]["changedComponents"],
        serde_json::json!(["Formal", "Formal.Arch.A"])
    );
    assert!(
        json["records"][0]["coverageGaps"]
            .as_array()
            .expect("coverage gaps are an array")
            .iter()
            .any(|gap| gap["layer"] == "runtime" && gap["measurementBoundary"] == "UNMEASURED")
    );
    assert!(
        json["records"][0]["repairSuggestionAdoptionCandidates"]
            .as_array()
            .expect("repair candidates are an array")
            .iter()
            .any(|candidate| candidate["adoptionStatus"] == "candidate")
    );
    assert_eq!(
        json["records"][0]["theoremPreconditionBoundary"]["summary"],
        read_json(&theorem_check)["summary"]
    );
    assert!(
        json["analysisMetadata"]["nonConclusions"]
            .as_array()
            .expect("non-conclusions are an array")
            .iter()
            .any(|claim| claim
                == "does not infer causal outcome effects from feature report classifications")
    );
}

#[test]
fn cli_outcome_linkage_dataset_joins_feature_dataset_and_bounded_outcomes() {
    let github_root = fixture_root();
    let air_root = air_fixture_root();
    let out_dir = temp_dir("outcome-linkage-dataset");
    let feature_report = out_dir.join("feature-extension-report.json");
    let theorem_check = out_dir.join("theorem-check.json");
    let pr_history = out_dir.join("pr-history.json");
    let feature_dataset = out_dir.join("feature-extension-dataset.json");
    let outcome_input = out_dir.join("outcome-observations.json");
    let outcome_dataset = out_dir.join("outcome-linkage-dataset.json");
    let daily_ledger = out_dir.join("report-outcome-daily-ledger.json");

    run_sig0(&[
        "feature-report",
        "--air",
        air_root
            .join("runtime_measured_nonzero.json")
            .to_str()
            .expect("AIR path is utf-8"),
        "--out",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
    ]);
    run_sig0(&[
        "theorem-check",
        "--air",
        air_root
            .join("runtime_measured_nonzero.json")
            .to_str()
            .expect("AIR path is utf-8"),
        "--out",
        theorem_check.to_str().expect("theorem check path is utf-8"),
    ]);
    run_sig0(&[
        "pr-history-dataset",
        "--pull-request",
        github_root
            .join("github_pr.json")
            .to_str()
            .expect("pull request path is utf-8"),
        "--files",
        github_root
            .join("github_files.json")
            .to_str()
            .expect("files path is utf-8"),
        "--reviews",
        github_root
            .join("github_reviews.json")
            .to_str()
            .expect("reviews path is utf-8"),
        "--feature-report-artifact",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
        "--out",
        pr_history.to_str().expect("PR history path is utf-8"),
    ]);
    run_sig0(&[
        "feature-extension-dataset",
        "--pr-history",
        pr_history.to_str().expect("PR history path is utf-8"),
        "--feature-report",
        feature_report
            .to_str()
            .expect("feature report path is utf-8"),
        "--theorem-check-report",
        theorem_check.to_str().expect("theorem check path is utf-8"),
        "--out",
        feature_dataset
            .to_str()
            .expect("feature dataset path is utf-8"),
    ]);

    let measured_comment_count = serde_json::json!({
        "boundary": "measured",
        "value": 2,
        "reason": null,
        "sourceRefs": ["github:pulls/42/reviews"],
        "nonConclusions": ["review comments are not a complete review effort measure"]
    });
    let measured_latency = serde_json::json!({
        "boundary": "measured",
        "value": 4.5,
        "reason": null,
        "sourceRefs": ["github:pulls/42/reviews"],
        "nonConclusions": ["latency is calendar-time observation, not architecture causality"]
    });
    let unavailable_latency = serde_json::json!({
        "boundary": "unavailable",
        "value": null,
        "reason": "approval timestamp not present in fixture",
        "sourceRefs": [],
        "nonConclusions": ["unavailable approval latency is not measured-zero evidence"]
    });
    fs::write(
        &outcome_input,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "outcome-linkage-input/v0.5.0",
            "repository": {
                "owner": "example",
                "name": "service",
                "defaultBranch": "main"
            },
            "records": [{
                "prNumber": 42,
                "reviewCost": {
                    "reviewCommentCount": measured_comment_count,
                    "reviewThreadCount": {
                        "boundary": "measured",
                        "value": 1,
                        "reason": null,
                        "sourceRefs": ["github:pulls/42/reviewThreads"],
                        "nonConclusions": []
                    },
                    "reviewRoundCount": {
                        "boundary": "measured",
                        "value": 1,
                        "reason": null,
                        "sourceRefs": ["github:pulls/42/reviews"],
                        "nonConclusions": []
                    },
                    "reviewerCount": {
                        "boundary": "measured",
                        "value": 1,
                        "reason": null,
                        "sourceRefs": ["github:pulls/42/reviews"],
                        "nonConclusions": []
                    },
                    "firstReviewLatencyHours": measured_latency,
                    "approvalLatencyHours": unavailable_latency,
                    "mergeLatencyHours": {
                        "boundary": "measured",
                        "value": 24.0,
                        "reason": null,
                        "sourceRefs": ["github:pulls/42"],
                        "nonConclusions": []
                    }
                },
                "followUpFixCount": {
                    "boundary": "measured",
                    "value": 1,
                    "reason": null,
                    "sourceRefs": ["github:issues/99"],
                    "nonConclusions": ["follow-up fix count is observational, not proof of defect cause"]
                },
                "rollback": {
                    "boundary": "measured",
                    "value": true,
                    "reason": null,
                    "sourceRefs": ["github:pulls/43"],
                    "nonConclusions": ["rollback is not attributed to a specific obstruction by this schema"]
                },
                "incidentAffectedComponentCount": {
                    "boundary": "measured",
                    "value": 2,
                    "reason": null,
                    "sourceRefs": ["incident:inc-7"],
                    "nonConclusions": []
                },
                "mttrHours": {
                    "boundary": "measured",
                    "value": 5.5,
                    "reason": null,
                    "sourceRefs": ["incident:inc-7"],
                    "nonConclusions": ["MTTR is operational observation, not semantic completeness"]
                },
                "traceability": {
                    "prRefs": [{
                        "kind": "github_pr",
                        "id": "42",
                        "url": "https://example.invalid/pulls/42",
                        "visibility": "public",
                        "labels": ["feature"],
                        "affectedComponents": ["Formal", "Formal.Arch.A"]
                    }],
                    "issueRefs": [{
                        "kind": "github_issue",
                        "id": "99",
                        "url": "https://example.invalid/issues/99",
                        "visibility": "public",
                        "labels": ["follow-up-fix"],
                        "affectedComponents": ["Formal.Arch.A"]
                    }],
                    "incidentRefs": [{
                        "kind": "incident",
                        "id": "inc-7",
                        "url": null,
                        "visibility": "private",
                        "labels": ["runtime"],
                        "affectedComponents": ["Formal", "Formal.Arch.A"]
                    }],
                    "artifactRefs": [{
                        "kind": "outcomeObservation",
                        "path": "outcomes/pr-42.json",
                        "schema": "outcome-linkage-input/v0.5.0"
                    }],
                    "missingOrPrivateData": ["incident timeline redacted"],
                    "nonConclusions": ["private incident data is not absence of incident evidence"]
                },
                "nonConclusions": [
                    "outcome observations are correlation inputs, not causal proof"
                ]
            }],
            "analysisMetadata": {
                "leanStatus": "empirical hypothesis / tooling validation",
                "measurementBoundary": "explicitly bounded review, follow-up, rollback, and incident observations",
                "joinKeys": ["repository owner/name", "pull request number"],
                "nonConclusions": [
                    "does not infer causal effects from obstruction profile to outcome"
                ]
            }
        }))
        .expect("outcome input serializes"),
    )
    .expect("outcome input is written");

    run_sig0(&[
        "outcome-linkage-dataset",
        "--feature-dataset",
        feature_dataset
            .to_str()
            .expect("feature dataset path is utf-8"),
        "--outcome",
        outcome_input.to_str().expect("outcome path is utf-8"),
        "--out",
        outcome_dataset
            .to_str()
            .expect("outcome dataset path is utf-8"),
    ]);

    let json = read_json(&outcome_dataset);
    assert_eq!(json["schema"], "outcome-linkage-dataset/v0.5.0");
    assert_eq!(json["repository"]["owner"], "example");
    assert_eq!(json["records"][0]["pullRequest"]["number"], 42);
    assert_eq!(
        json["records"][0]["outcomeObservation"]["rollback"]["value"],
        true
    );
    assert_eq!(
        json["records"][0]["outcomeObservation"]["mttrHours"]["value"],
        5.5
    );
    assert_eq!(
        json["records"][0]["outcomeObservation"]["reviewCost"]["approvalLatencyHours"]["boundary"],
        "unavailable"
    );
    assert!(
        json["records"][0]["correlationInputs"]["nonConclusions"]
            .as_array()
            .expect("correlation non-conclusions are an array")
            .iter()
            .any(
                |claim| claim == "does not infer obstruction witnesses caused the observed outcome"
            )
    );
    assert!(
        json["records"][0]["nonConclusions"]
            .as_array()
            .expect("record non-conclusions are an array")
            .iter()
            .any(|claim| claim == "private incident data is not absence of incident evidence")
    );
    assert!(
        json["analysisMetadata"]["nonConclusions"]
            .as_array()
            .expect("analysis non-conclusions are an array")
            .iter()
            .any(|claim| claim == "does not rank architecture quality with a single score")
    );

    run_sig0(&[
        "report-outcome-daily-ledger",
        "--outcome-linkage",
        outcome_dataset
            .to_str()
            .expect("outcome dataset path is utf-8"),
        "--drift-ledger",
        github_root
            .join("architecture_drift_ledger.json")
            .to_str()
            .expect("drift ledger path is utf-8"),
        "--generated-at",
        "2026-05-05T00:00:00Z",
        "--window-start",
        "2026-05-04T00:00:00Z",
        "--window-end",
        "2026-05-05T00:00:00Z",
        "--out",
        daily_ledger.to_str().expect("daily ledger path is utf-8"),
    ]);

    let ledger = read_json(&daily_ledger);
    assert_eq!(ledger["schema"], "report-outcome-daily-ledger/v0.5.0");
    assert!(
        ledger["sourceReportRefs"]
            .as_array()
            .expect("sourceReportRefs are an array")
            .iter()
            .any(|source| source["kind"] == "outcome-linkage-dataset")
    );
    assert_eq!(
        ledger["retention"]["retentionManifestRef"],
        "report-artifacts:fixture-b7-report-artifact-retention"
    );
    assert!(
        ledger["batches"][0]["missingPrivateUnmeasuredBoundaries"]
            .as_array()
            .expect("boundary counts are an array")
            .iter()
            .any(
                |boundary| boundary["metricRef"] == "reviewCost.approvalLatencyHours"
                    && boundary["boundary"] == "unavailable"
            )
    );
    assert!(
        ledger["batches"][0]["missingPrivateUnmeasuredBoundaries"]
            .as_array()
            .expect("boundary counts are an array")
            .iter()
            .any(
                |boundary| boundary["metricRef"] == "driftLedger.private_runtime_evidence_count"
                    && boundary["boundary"] == "unmeasured"
            )
    );
    assert!(
        ledger["schemaCompatibility"]["fieldMappings"]
            .as_array()
            .expect("fieldMappings are an array")
            .iter()
            .any(|mapping| mapping["sourceField"]
                == "batches[].missingPrivateUnmeasuredBoundaries")
    );
    assert!(
        ledger["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim == "schema migration pass is not semantic preservation")
    );
}

#[test]
fn cli_calibration_review_record_fixture_preserves_review_boundaries() {
    let out_dir = temp_dir("calibration-review-record");
    let out = out_dir.join("calibration-review-record.json");

    run_sig0(&[
        "calibration-review-record",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "calibration-review-record/v0.5.0");
    assert_eq!(json["reviewerDecision"]["decision"], "falsePositive");
    assert!(
        json["reportFindingRefs"]
            .as_array()
            .expect("reportFindingRefs are an array")
            .iter()
            .any(
                |finding| finding["metricRef"] == "runtime.privateEvidenceCount"
                    && finding["measurementBoundary"] == "unmeasured"
            )
    );
    assert!(
        json["missingEvidence"]
            .as_array()
            .expect("missingEvidence is an array")
            .iter()
            .any(|evidence| evidence["boundary"] == "private")
    );
    assert!(
        json["calibrationInput"]["nonConclusions"]
            .as_array()
            .expect("calibration nonConclusions are an array")
            .iter()
            .any(|claim| claim == "calibration input is not theorem precondition discharge")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(
                |boundary| boundary["axisOrLayer"] == "calibration-review.missing-evidence"
                    && boundary["measurementBoundary"] == "unmeasured"
            )
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim == "missing or private evidence is not measured-zero evidence")
    );
}

#[test]
fn cli_team_threshold_policy_fixture_preserves_policy_boundaries() {
    let out_dir = temp_dir("team-threshold-policy");
    let out = out_dir.join("team-threshold-policy.json");

    run_sig0(&[
        "team-threshold-policy",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "team-threshold-policy/v0.5.0");
    assert_eq!(json["teamRef"], "team:checkout-platform");
    assert!(
        json["axisThresholds"]
            .as_array()
            .expect("axisThresholds are an array")
            .iter()
            .any(|axis| axis["metricRef"] == "runtime.privateEvidenceCount"
                && axis["ciMode"] == "advisory")
    );
    assert!(
        json["calibrationSourceRefs"]
            .as_array()
            .expect("calibrationSourceRefs are an array")
            .iter()
            .any(|source| source["sourceKind"] == "calibration-review-record"
                && source["boundary"] == "boundedEmpiricalReview")
    );
    assert!(
        json["rollbackPolicy"]["nonConclusions"]
            .as_array()
            .expect("rollback nonConclusions are an array")
            .iter()
            .any(|claim| claim == "incident linkage alone does not prove causality")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "team-threshold-policy.axis-threshold")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| {
                claim == "team threshold policy is empirical calibration, not theorem precondition discharge"
            })
    );
}

#[test]
fn cli_ownership_boundary_monitor_fixture_preserves_boundary_evidence() {
    let out_dir = temp_dir("ownership-boundary-monitor");
    let out = out_dir.join("ownership-boundary-monitor.json");

    run_sig0(&[
        "ownership-boundary-monitor",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "ownership-boundary-monitor/v0.5.0");
    assert_eq!(json["teamRef"], "team:checkout-platform");
    assert!(
        json["ownershipScopes"]
            .as_array()
            .expect("ownershipScopes are an array")
            .iter()
            .any(|scope| scope["scopeRef"] == "ownership-scope:checkout-api"
                && scope["observationBoundary"] == "boundedOperationalObservation")
    );
    assert!(
        json["boundaryErosionSignals"]
            .as_array()
            .expect("boundaryErosionSignals are an array")
            .iter()
            .any(
                |signal| signal["metricRef"] == "runtime.privateEvidenceCount"
                    && signal["measurementBoundary"] == "unmeasuredPrivateEvidence"
            )
    );
    assert!(
        json["missingEvidence"]
            .as_array()
            .expect("missingEvidence is an array")
            .iter()
            .any(|evidence| evidence["boundary"] == "private")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| {
                boundary["axisOrLayer"] == "ownership-boundary-monitor.boundary-erosion"
            })
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim == "boundary erosion monitoring does not prove repair correctness")
    );
}

#[test]
fn cli_repair_adoption_record_fixture_preserves_adoption_boundaries() {
    let out_dir = temp_dir("repair-adoption-record");
    let out = out_dir.join("repair-adoption-record.json");

    run_sig0(&[
        "repair-adoption-record",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "repair-adoption-record/v0.5.0");
    assert_eq!(json["adoptionDecision"]["decision"], "deferred");
    assert!(
        json["suggestionRefs"]
            .as_array()
            .expect("suggestionRefs are an array")
            .iter()
            .any(|suggestion| {
                suggestion["suggestionRef"] == "repair-suggestion:split-runtime-adapter-boundary"
                    && suggestion["evidenceBoundary"] == "suggestionFromUnmeasuredRuntimeEvidence"
            })
    );
    assert!(
        json["followUpOutcomeRefs"]
            .as_array()
            .expect("followUpOutcomeRefs are an array")
            .iter()
            .any(|outcome| outcome["outcomeKind"] == "ownership-boundary-monitor")
    );
    assert!(
        json["sideEffectNotes"]
            .as_array()
            .expect("sideEffectNotes are an array")
            .iter()
            .any(|note| note["severity"] == "watch")
    );
    assert!(
        json["missingEvidence"]
            .as_array()
            .expect("missingEvidence is an array")
            .iter()
            .any(|evidence| evidence["boundary"] == "private")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "repair-adoption.decision")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim
                == "adopted, rejected, or deferred decision does not prove repair correctness")
    );
}

#[test]
fn cli_incident_correlation_monitor_fixture_preserves_correlation_boundaries() {
    let out_dir = temp_dir("incident-correlation-monitor");
    let out = out_dir.join("incident-correlation-monitor.json");

    run_sig0(&[
        "incident-correlation-monitor",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "incident-correlation-monitor/v0.5.0");
    assert_eq!(json["teamRef"], "team:checkout-platform");
    assert_eq!(json["correlationWindow"]["windowKind"], "monthly");
    assert!(
        json["metricAxes"]
            .as_array()
            .expect("metricAxes are an array")
            .iter()
            .any(|axis| axis["metricRef"] == "mttrHours"
                && axis["measurementBoundary"] == "boundedOutcomeObservation")
    );
    assert!(
        json["confounderNotes"]
            .as_array()
            .expect("confounderNotes are an array")
            .iter()
            .any(|note| note["boundary"] == "private")
    );
    assert!(
        json["missingPrivateData"]
            .as_array()
            .expect("missingPrivateData is an array")
            .iter()
            .any(|evidence| evidence["boundary"] == "private")
    );
    assert_eq!(json["refreshDecision"]["decision"], "refreshHypothesis");
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "incident-correlation.missing-private-data")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim == "correlation does not imply causation")
    );
}

#[test]
fn cli_hypothesis_refresh_cycle_fixture_preserves_refresh_boundaries() {
    let out_dir = temp_dir("hypothesis-refresh-cycle");
    let out = out_dir.join("hypothesis-refresh-cycle.json");

    run_sig0(&[
        "hypothesis-refresh-cycle",
        "--out",
        out.to_str().expect("output path is utf-8"),
    ]);

    let json = read_json(&out);
    assert_eq!(json["schema"], "hypothesis-refresh-cycle/v0.5.0");
    assert_eq!(json["refreshDecision"]["decision"], "reviseAndRetain");
    assert!(
        json["versionedHypothesisRefs"]
            .as_array()
            .expect("versionedHypothesisRefs are an array")
            .iter()
            .any(
                |hypothesis| hypothesis["hypothesisRef"] == "H5-runtime-exposure-incident-scope"
                    && hypothesis["hypothesisVersion"] == "2026-04"
            )
    );
    assert!(
        json["rejectedHypotheses"]
            .as_array()
            .expect("rejectedHypotheses are an array")
            .iter()
            .any(|hypothesis| hypothesis["disposition"] == "rejected")
    );
    assert!(
        json["retainedHypotheses"]
            .as_array()
            .expect("retainedHypotheses are an array")
            .iter()
            .any(|hypothesis| hypothesis["disposition"] == "retained")
    );
    assert!(
        json["schemaCompatibility"]["coverageExactnessBoundaries"]
            .as_array()
            .expect("coverageExactnessBoundaries are an array")
            .iter()
            .any(|boundary| boundary["axisOrLayer"] == "hypothesis-refresh.formal-claim-boundary")
    );
    assert!(
        json["nonConclusions"]
            .as_array()
            .expect("nonConclusions are an array")
            .iter()
            .any(|claim| claim == "retained hypothesis is not a proved claim")
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
    assert_eq!(json["schema"], "relation-complexity-observation/v0.5.0");
    assert_eq!(json["relationComplexity"], 3);
    assert_eq!(
        json["measurementUniverse"]["ruleSetVersion"],
        "relation-complexity-rules/v0.5.0"
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
    assert_eq!(json["schema"], "aat-air/v0.5.0");
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
                    && relation["extractionRule"] == "runtime-edge-projection/v0.5.0"
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
        "runtime-edge-projection/v0.5.0"
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
    assert_eq!(json["schema"], "signature-diff-report/v0.5.0");
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

#[test]
fn cli_organization_policy_validates_static_policy_and_input_fixture() {
    let root = fixture_root();
    let out_dir = temp_dir("organization-policy");
    let static_report = out_dir.join("organization-policy-static.json");
    let fixture_report = out_dir.join("organization-policy-fixture.json");

    run_sig0(&[
        "organization-policy",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "organization-policy",
        "--input",
        root.join("organization_policy.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "organization-policy-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(json["summary"]["requiredAxisCount"].as_u64().unwrap() >= 3);
    assert!(
        json["policy"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "organization policy is CI decision support, not a Lean theorem"
            })
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["policy"]["allowedUnmeasuredGaps"]
            .as_array()
            .expect("allowedUnmeasuredGaps is array")
            .iter()
            .any(|gap| gap["axis"] == "semanticDiagramCommutation")
    );
}

#[test]
fn cli_law_policy_templates_validate_fixture_and_non_conclusion_boundary() {
    let root = fixture_root();
    let out_dir = temp_dir("law-policy-templates");
    let static_report = out_dir.join("law-policy-templates-static.json");
    let fixture_report = out_dir.join("law-policy-templates-fixture.json");
    let invalid_registry = out_dir.join("invalid-law-policy-templates.json");
    let invalid_report = out_dir.join("invalid-law-policy-templates-report.json");

    run_sig0(&[
        "law-policy-templates",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "law-policy-templates",
        "--input",
        root.join("law_policy_templates.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "law-policy-template-registry-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(json["summary"]["templateCount"].as_u64().unwrap() >= 3);
    assert!(
        json["registry"]["templates"]
            .as_array()
            .expect("templates is array")
            .iter()
            .any(|template| {
                template["templateId"] == "python-boundary-allowlist-template/v0.5.0"
                    && template["targetComponentKind"] == "python-module"
                    && template["lawPolicyFamily"] == "boundary"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "law-policy-template-non-conclusion-boundary-recorded"
                    && check["result"] == "pass"
            })
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["registry"]["templates"]
            .as_array()
            .expect("templates is array")
            .iter()
            .any(|template| {
                template["templateId"] == "fixture-service-runtime-template/v0.5.0"
                    && template["selectorSemantics"] == "adapter-provided"
                    && template["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion == "unmeasured gaps are not measured-zero evidence"
                        })
            })
    );

    let mut invalid_json = read_json(&root.join("law_policy_templates.json"));
    invalid_json["templates"][0]["nonConclusions"] = serde_json::json!([]);
    fs::write(
        &invalid_registry,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid registry is written");
    let output = run_sig0_output(&[
        "law-policy-templates",
        "--input",
        invalid_registry
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "missing template non-conclusions should fail validation"
    );
    let json = read_json(&invalid_report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "law-policy-template-non-conclusion-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_custom_rule_plugins_validate_fixture_and_formal_promotion_boundary() {
    let root = fixture_root();
    let out_dir = temp_dir("custom-rule-plugins");
    let static_report = out_dir.join("custom-rule-plugins-static.json");
    let fixture_report = out_dir.join("custom-rule-plugins-fixture.json");
    let invalid_registry = out_dir.join("invalid-custom-rule-plugins.json");
    let invalid_report = out_dir.join("invalid-custom-rule-plugins-report.json");

    run_sig0(&[
        "custom-rule-plugins",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "custom-rule-plugins",
        "--input",
        root.join("custom_rule_plugins.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "custom-rule-plugin-registry-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(json["summary"]["pluginCount"].as_u64().unwrap() >= 2);
    assert!(
        json["registry"]["plugins"]
            .as_array()
            .expect("plugins is array")
            .iter()
            .any(|plugin| {
                plugin["pluginId"] == "runtime-hot-path-annotation-plugin/v0.5.0"
                    && plugin["formalClaimPromotion"] == "requires-theorem-precondition-check"
                    && plugin["theoremPreconditionRefs"]
                        .as_array()
                        .expect("theorem refs are an array")
                        .iter()
                        .any(|reference| reference == "runtime-zero-bridge-theorem-package/v0.5.0")
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "custom-rule-plugin-formal-promotion-boundary-recorded"
                    && check["result"] == "pass"
            })
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["registry"]["plugins"]
            .as_array()
            .expect("plugins is array")
            .iter()
            .any(|plugin| {
                plugin["pluginId"] == "fixture-semantic-workflow-plugin/v0.5.0"
                    && plugin["permittedClaimLevels"]
                        .as_array()
                        .expect("claim levels are array")
                        .iter()
                        .any(|level| level == "formal")
                    && plugin["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion
                                == "formal claim promotion requires explicit theorem precondition checks"
                        })
            })
    );

    let mut invalid_json = read_json(&root.join("custom_rule_plugins.json"));
    invalid_json["plugins"][1]["theoremPreconditionRefs"] = serde_json::json!([]);
    invalid_json["plugins"][1]["requiredTheoremPreconditions"] = serde_json::json!([]);
    fs::write(
        &invalid_registry,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid registry is written");
    let output = run_sig0_output(&[
        "custom-rule-plugins",
        "--input",
        invalid_registry
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "formal plugin promotion without theorem preconditions should fail validation"
    );
    let json = read_json(&invalid_report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "custom-rule-plugin-formal-promotion-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_measurement_units_validate_fixture_and_boundary_refs() {
    let root = fixture_root();
    let out_dir = temp_dir("measurement-units");
    let static_report = out_dir.join("measurement-units-static.json");
    let fixture_report = out_dir.join("measurement-units-fixture.json");
    let invalid_registry = out_dir.join("invalid-measurement-units.json");
    let invalid_report = out_dir.join("invalid-measurement-units-report.json");

    run_sig0(&[
        "measurement-units",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "measurement-units",
        "--input",
        root.join("measurement_units.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "measurement-unit-registry-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(json["summary"]["unitCount"].as_u64().unwrap() >= 3);
    assert!(
        json["registry"]["units"]
            .as_array()
            .expect("units is array")
            .iter()
            .any(|unit| {
                unit["unitKind"] == "deployment-unit"
                    && unit["serviceRoot"] == "services/billing"
                    && unit["deploymentUnit"] == "deployments/billing-worker"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "measurement-unit-evidence-adapter-boundaries-recorded"
                    && check["result"] == "pass"
            })
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["registry"]["evidenceAdapters"]
            .as_array()
            .expect("evidenceAdapters is array")
            .iter()
            .any(|adapter| {
                adapter["adapterId"] == "fixture-semantic-workflow-measurement-unit-adapter/v0.5.0"
                    && adapter["measurementUnitRefs"]
                        .as_array()
                        .expect("unit refs are array")
                        .iter()
                        .any(|unit_ref| unit_ref == "fixture-repository-root")
                    && adapter["unsupportedConstructs"]
                        .as_array()
                        .expect("unsupported constructs are array")
                        .iter()
                        .any(|construct| construct == "unmapped-workflow-node")
            })
    );
    assert!(
        json["registry"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion
                    == "selected measurement units do not conclude Lean ComponentUniverse completeness"
            })
    );

    let mut invalid_json = read_json(&root.join("measurement_units.json"));
    invalid_json["evidenceAdapters"][0]["measurementUnitRefs"] =
        serde_json::json!(["missing-unit"]);
    fs::write(
        &invalid_registry,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid registry is written");
    let output = run_sig0_output(&[
        "measurement-units",
        "--input",
        invalid_registry
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "dangling measurement unit refs should fail validation"
    );
    let json = read_json(&invalid_report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "measurement-unit-evidence-adapter-boundaries-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_dynamics_measurements_validate_common_contract() {
    let root = fixture_root();
    let out_dir = temp_dir("dynamics-measurements");
    let static_report = out_dir.join("dynamics-measurements-static.json");
    let fixture_report = out_dir.join("dynamics-measurements-fixture.json");
    let invalid_contract = out_dir.join("invalid-dynamics-measurements.json");
    let invalid_report = out_dir.join("invalid-dynamics-measurements-report.json");

    run_sig0(&[
        "dynamics-measurements",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "dynamics-measurements",
        "--input",
        root.join("dynamics_measurement_contract.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "dynamics-measurement-contract-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["contract"]["metrics"]
            .as_array()
            .expect("metrics is array")
            .iter()
            .any(|metric| {
                metric["status"] == "estimated"
                    && metric["confidence"] == "medium"
                    && metric["sourceRefs"]
                        .as_array()
                        .expect("sourceRefs is array")
                        .iter()
                        .any(|source| source["kind"] == "pr-history-dataset")
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "dynamics-null-value-not-measured-or-derived"
                    && check["result"] == "pass"
            })
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["contract"]["metrics"]
            .as_array()
            .expect("metrics is array")
            .iter()
            .any(|metric| {
                metric["status"] == "unmeasured"
                    && metric["value"].is_null()
                    && metric["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion == "unmeasured dynamics metric is not measured-zero evidence"
                        })
            })
    );

    let mut invalid_json = read_json(&root.join("dynamics_measurement_contract.json"));
    invalid_json["metrics"][0]["value"] = serde_json::Value::Null;
    invalid_json["metrics"][1]["confidence"] = serde_json::Value::Null;
    invalid_json["metrics"][1]["sourceRefs"] = serde_json::json!([]);
    invalid_json["metrics"][2]["status"] = serde_json::json!("forecast");
    fs::write(
        &invalid_contract,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid contract is written");
    let output = run_sig0_output(&[
        "dynamics-measurements",
        "--input",
        invalid_contract
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_report.to_str().expect("report path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid dynamics measurement contract should fail validation"
    );
    let json = read_json(&invalid_report);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "dynamics-measurement-status-values-supported"
                    && check["result"] == "fail"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "dynamics-null-value-not-measured-or-derived"
                    && check["result"] == "fail"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "dynamics-estimated-metric-evidence-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_pr_force_report_fixture_and_validator_preserve_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("pr-force-report");
    let static_report = out_dir.join("pr-force-report-static-validation.json");
    let fixture_artifact = out_dir.join("pr-force-report-fixture.json");
    let fixture_validation = out_dir.join("pr-force-report-fixture-validation.json");
    let invalid_report = out_dir.join("invalid-pr-force-report.json");
    let invalid_validation = out_dir.join("invalid-pr-force-report-validation.json");

    run_sig0(&[
        "pr-force-report",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "pr-force-report",
        "--fixture",
        "--out",
        fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "pr-force-report",
        "--input",
        root.join("pr_force_report.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(json["schema"], "pr-force-report-validation-report/v0.5.0");
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["report"]["observedForce"]
            .as_array()
            .expect("observedForce is array")
            .iter()
            .any(|metric| {
                metric["metricId"] == "observedForce.boundaryViolationDelta"
                    && metric["status"] == "measured"
                    && metric["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion == "observed force excludes rejected raw proposal force"
                        })
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "pr-force-decomposition-remains-advisory"
                    && check["result"] == "pass"
            })
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "pr-force-report/v0.5.0");
    assert!(
        artifact["forceDecomposition"]["components"]
            .as_array()
            .expect("components is array")
            .iter()
            .any(|component| {
                component["decompositionMethod"] == "heuristic"
                    && component["contribution"]["status"] == "advisory"
                    && component["theoremClaimRefs"]
                        .as_array()
                        .expect("theoremClaimRefs is array")
                        .is_empty()
            })
    );

    let json = read_json(&fixture_validation);
    assert_eq!(json["summary"]["result"], "pass");

    let mut invalid_json = read_json(&root.join("pr_force_report.json"));
    invalid_json["observedForce"][0]["metricId"] = serde_json::json!("observedForce.rejectedRaw");
    invalid_json["observedForce"][0]["nonConclusions"] = serde_json::json!([]);
    invalid_json["forceDecomposition"]["components"][0]["contribution"]["status"] =
        serde_json::json!("measured");
    invalid_json["forceDecomposition"]["components"][0]["theoremClaimRefs"] =
        serde_json::json!(["Formal.Arch.SignatureDynamics.fakeClaim"]);
    fs::write(
        &invalid_report,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid PR force report is written");
    let output = run_sig0_output(&[
        "pr-force-report",
        "--input",
        invalid_report
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid PR force report should fail validation"
    );
    let json = read_json(&invalid_validation);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "pr-force-observed-force-excludes-rejected-raw-force"
                    && check["result"] == "fail"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "pr-force-decomposition-remains-advisory"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_signature_trajectory_report_fixture_and_validator_preserve_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("signature-trajectory-report");
    let static_report = out_dir.join("signature-trajectory-report-static-validation.json");
    let fixture_artifact = out_dir.join("signature-trajectory-report-fixture.json");
    let fixture_validation = out_dir.join("signature-trajectory-report-validation.json");
    let invalid_report = out_dir.join("signature-trajectory-report-invalid.json");
    let invalid_validation = out_dir.join("signature-trajectory-report-invalid-validation.json");

    run_sig0(&[
        "signature-trajectory-report",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "signature-trajectory-report",
        "--fixture",
        "--out",
        fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "signature-trajectory-report",
        "--input",
        root.join("signature_trajectory_report.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "signature-trajectory-report-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["report"]["selectedRegions"]
            .as_array()
            .expect("selectedRegions is array")
            .iter()
            .any(|region| {
                region["regionKind"] == "attractorCandidate"
                    && region["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion == "attractor candidate is not a global attractor theorem"
                        })
            })
    );
    assert!(
        json["report"]["excursionSignals"]
            .as_array()
            .expect("excursionSignals is array")
            .iter()
            .any(|metric| {
                metric["metricId"] == "trajectory.excursion.selectedBadRegionVisit"
                    && metric["status"] == "measured"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "signature-trajectory-comparison-boundary-recorded"
                    && check["result"] == "pass"
            })
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "signature-trajectory-report/v0.5.0");
    assert!(
        artifact["selectedRegions"]
            .as_array()
            .expect("selectedRegions is array")
            .iter()
            .any(|region| region["regionKind"] == "safeRegion")
    );
    assert!(
        artifact["selectedRegions"]
            .as_array()
            .expect("selectedRegions is array")
            .iter()
            .any(|region| region["regionKind"] == "badRegion")
    );
    assert!(
        artifact["selectedRegions"]
            .as_array()
            .expect("selectedRegions is array")
            .iter()
            .any(|region| region["regionKind"] == "debtWell")
    );
    assert!(
        artifact["selectedRegions"]
            .as_array()
            .expect("selectedRegions is array")
            .iter()
            .any(|region| region["regionKind"] == "attractorCandidate")
    );

    let json = read_json(&fixture_validation);
    assert_eq!(json["summary"]["result"], "pass");

    let mut invalid_json = read_json(&root.join("signature_trajectory_report.json"));
    invalid_json["trajectoryPoints"][1]["measurementBoundary"]["schema"] =
        serde_json::json!("signature-trajectory-report/legacy-test");
    invalid_json["driftSignals"][1]["status"] = serde_json::json!("unmeasured");
    invalid_json["measurementBoundary"]["missingEvidence"] = serde_json::json!([]);
    invalid_json["selectedRegions"][3]["nonConclusions"] = serde_json::json!([]);
    fs::write(
        &invalid_report,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid Signature trajectory report is written");
    let output = run_sig0_output(&[
        "signature-trajectory-report",
        "--input",
        invalid_report
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid Signature trajectory report should fail validation"
    );
    let json = read_json(&invalid_validation);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "signature-trajectory-comparison-boundary-recorded"
                    && check["result"] == "fail"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "signature-trajectory-selected-regions-recorded"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_field_snapshot_and_operation_proposal_log_preserve_selected_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("architecture-field-artifacts");
    let field_static_validation = out_dir.join("architecture-field-snapshot-static.json");
    let field_fixture_artifact = out_dir.join("architecture-field-snapshot-fixture.json");
    let field_fixture_validation = out_dir.join("architecture-field-snapshot-validation.json");
    let field_invalid_validation = out_dir.join("architecture-field-snapshot-invalid.json");
    let proposal_static_validation = out_dir.join("operation-proposal-log-static.json");
    let proposal_fixture_artifact = out_dir.join("operation-proposal-log-fixture.json");
    let proposal_fixture_validation = out_dir.join("operation-proposal-log-validation.json");
    let proposal_invalid_validation = out_dir.join("operation-proposal-log-invalid.json");

    run_sig0(&[
        "architecture-field-snapshot",
        "--out",
        field_static_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    run_sig0(&[
        "architecture-field-snapshot",
        "--fixture",
        "--out",
        field_fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "architecture-field-snapshot",
        "--input",
        root.join("architecture_field_snapshot.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        field_fixture_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);

    let json = read_json(&field_static_validation);
    assert_eq!(
        json["schema"],
        "architecture-field-snapshot-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["snapshot"]["fieldSignals"]
            .as_array()
            .expect("fieldSignals is array")
            .iter()
            .any(|signal| {
                signal["selectedSignal"] == "boundary-and-non-goal-alignment"
                    && signal["sourceRefs"]
                        .as_array()
                        .expect("sourceRefs is array")
                        .len()
                        > 0
                    && signal["measurementBoundary"]["aggregationWindow"].is_object()
            })
    );
    assert!(json["snapshot"]["nonConclusions"]
        .as_array()
        .expect("nonConclusions is array")
        .iter()
        .any(|conclusion| {
            conclusion
                == "architecture field snapshot is selected-window tooling evidence, not global architecture field completeness"
        }));

    let artifact = read_json(&field_fixture_artifact);
    assert_eq!(artifact["schema"], "architecture-field-snapshot/v0.5.0");
    assert_eq!(
        read_json(&field_fixture_validation)["summary"]["result"],
        "pass"
    );

    let output = run_sig0_output(&[
        "architecture-field-snapshot",
        "--input",
        root.join("architecture_field_snapshot_invalid.json")
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        field_invalid_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid architecture field snapshot should fail validation"
    );
    let json = read_json(&field_invalid_validation);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "architecture-field-snapshot-boundaries-recorded"
                    && check["result"] == "fail"
            )
    );

    run_sig0(&[
        "operation-proposal-log",
        "--out",
        proposal_static_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    run_sig0(&[
        "operation-proposal-log",
        "--fixture",
        "--out",
        proposal_fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "operation-proposal-log",
        "--input",
        root.join("operation_proposal_log.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        proposal_fixture_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);

    let json = read_json(&proposal_static_validation);
    assert_eq!(
        json["schema"],
        "operation-proposal-log-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["log"]["proposals"]
            .as_array()
            .expect("proposals is array")
            .iter()
            .any(|proposal| {
                proposal["operationKind"] == "runtime-bypass"
                    && proposal["status"] == "rejected"
                    && proposal["measurementBoundary"]["aggregationWindow"].is_object()
            })
    );
    assert!(json["log"]["nonConclusions"]
        .as_array()
        .expect("nonConclusions is array")
        .iter()
        .any(|conclusion| {
            conclusion
                == "operation proposal log is selected-window tooling evidence, not AI proposal distribution completeness"
        }));

    let artifact = read_json(&proposal_fixture_artifact);
    assert_eq!(artifact["schema"], "operation-proposal-log/v0.5.0");
    assert_eq!(
        read_json(&proposal_fixture_validation)["summary"]["result"],
        "pass"
    );

    let output = run_sig0_output(&[
        "operation-proposal-log",
        "--input",
        root.join("operation_proposal_log_invalid.json")
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        proposal_invalid_validation
            .to_str()
            .expect("validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid operation proposal log should fail validation"
    );
    let json = read_json(&proposal_invalid_validation);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "operation-proposal-log-boundaries-recorded"
                    && check["result"] == "fail"
            )
    );
}

#[test]
fn cli_ai_proposal_governance_projects_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("ai-proposal-governance");
    let descriptor = out_dir.join("artifact-descriptor.json");
    let governance_from_descriptor = out_dir.join("ai-proposal-governance-from-descriptor.json");
    let fixture_artifact = out_dir.join("ai-proposal-governance.json");
    let fixture_validation = out_dir.join("ai-proposal-governance-validation.json");
    let invalid_artifact = out_dir.join("ai-proposal-governance-invalid.json");
    let invalid_validation = out_dir.join("ai-proposal-governance-invalid-validation.json");

    run_sig0(&[
        "artifact-descriptor",
        "--from-ai-proposal-json",
        root.join("ai_proposal_sft_adapter.json")
            .to_str()
            .expect("AI proposal fixture path is utf-8"),
        "--out",
        descriptor
            .to_str()
            .expect("descriptor output path is utf-8"),
    ]);
    run_sig0(&[
        "ai-proposal-governance",
        "--descriptor",
        descriptor.to_str().expect("descriptor path is utf-8"),
        "--operation-support-id",
        "fixture-operation-support-estimate/v0.5.0",
        "--consequence-envelope-id",
        "fixture-consequence-envelope-report/v0.5.0",
        "--out",
        governance_from_descriptor
            .to_str()
            .expect("governance output path is utf-8"),
    ]);
    run_sig0(&[
        "ai-proposal-governance",
        "--fixture",
        "--out",
        fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "ai-proposal-governance",
        "--input",
        root.join("ai_proposal_governance.json")
            .to_str()
            .expect("governance fixture path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);

    let json = read_json(&governance_from_descriptor);
    assert_eq!(json["schema"], "ai-proposal-governance/v0.5.0");
    assert_eq!(
        json["proposalRef"]["operationSupportEstimateId"],
        "fixture-operation-support-estimate/v0.5.0"
    );
    assert!(
        json["supportAssessments"]
            .as_array()
            .expect("supportAssessments is array")
            .iter()
            .any(|assessment| {
                assessment["supportCategory"] == "forbidden"
                    && assessment["appliesToRef"] == "architecture-lawfulness-claim"
            })
    );
    assert!(
        json["shortcutWitnesses"]
            .as_array()
            .expect("shortcutWitnesses is array")
            .iter()
            .any(|witness| witness["shortcutKind"] == "runtime-boundary shortcut")
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["governance"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| conclusion == "AI proposal governance is a reviewer-facing artifact, not an AI safety theorem")
    );

    let mut invalid_json = read_json(&fixture_artifact);
    invalid_json["supportAssessments"][0]["supportCategory"] = serde_json::json!("safe");
    fs::write(
        &invalid_artifact,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid AI governance artifact is written");
    let output = run_sig0_output(&[
        "ai-proposal-governance",
        "--input",
        invalid_artifact
            .to_str()
            .expect("invalid artifact path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid AI governance artifact should fail validation"
    );
    let json = read_json(&invalid_validation);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "ai-governance-support-categories" && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_architecture_dynamics_metrics_fixture_and_validator_preserve_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("architecture-dynamics-metrics");
    let static_report = out_dir.join("architecture-dynamics-metrics-static-validation.json");
    let fixture_artifact = out_dir.join("architecture-dynamics-metrics-report.json");
    let fixture_validation = out_dir.join("architecture-dynamics-metrics-validation.json");
    let invalid_report = out_dir.join("architecture-dynamics-metrics-invalid.json");
    let invalid_validation = out_dir.join("architecture-dynamics-metrics-invalid-validation.json");
    let missing_attractor_report =
        out_dir.join("architecture-dynamics-metrics-missing-attractor.json");
    let missing_attractor_validation =
        out_dir.join("architecture-dynamics-metrics-missing-attractor-validation.json");
    let invalid_attractor_report =
        out_dir.join("architecture-dynamics-metrics-invalid-attractor.json");
    let invalid_attractor_validation =
        out_dir.join("architecture-dynamics-metrics-invalid-attractor-validation.json");

    run_sig0(&[
        "architecture-dynamics-metrics",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "architecture-dynamics-metrics",
        "--fixture",
        "--out",
        fixture_artifact
            .to_str()
            .expect("fixture artifact path is utf-8"),
    ]);
    run_sig0(&[
        "architecture-dynamics-metrics",
        "--input",
        root.join("architecture_dynamics_metrics_report.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "architecture-dynamics-metrics-report-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["report"]["forceMetrics"]
            .as_array()
            .expect("forceMetrics is array")
            .iter()
            .any(|metric| {
                metric["metricId"] == "force.observedForce"
                    && metric["status"] == "measured"
                    && metric["nonConclusions"]
                        .as_array()
                        .expect("nonConclusions is array")
                        .iter()
                        .any(|conclusion| {
                            conclusion
                                == "ObservedForce, LatentForceEstimate, and DissipatedForceEstimate remain separate force classes"
                        })
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "architecture-dynamics-metrics-force-classes-separated"
                    && check["result"] == "pass"
            })
    );
    assert_eq!(json["summary"]["attractorSelectedRegionCount"], 1);
    assert!(
        json["report"]["attractorEngineering"]["supportRiskMass"]["status"] == "derived"
            && json["report"]["attractorEngineering"]["designFieldStrength"]["status"]
                == "advisory"
            && json["report"]["attractorEngineering"]["seedAttractorStrength"]["status"]
                == "advisory"
            && json["report"]["attractorEngineering"]["basinBoundaryFragility"]["status"]
                == "derived"
            && json["report"]["attractorEngineering"]["trajectoryReturnTime"]["status"]
                == "derived"
            && json["report"]["attractorEngineering"]["observabilityDebt"]["status"] == "derived"
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["supportRiskMass"]["value"]["measuredRiskMass"],
        serde_json::json!(0.04)
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["supportRiskMass"]["value"]["unknownSupportWeight"],
        serde_json::json!(0.25)
    );
    assert!(
        json["report"]["attractorEngineering"]["supportRiskMass"]["value"]
            ["theoremPreconditionRefs"]
            .as_array()
            .expect("theoremPreconditionRefs is array")
            .iter()
            .any(|reference| {
                reference
                    == "Formal.Arch.OperationRoleSchema.preservesInvariant_of_discharged_preserve"
            })
    );
    assert_eq!(json["summary"]["basinCandidateCount"], 3);
    assert!(
        json["report"]["attractorEngineering"]["basinCandidates"]
            .as_array()
            .expect("basinCandidates is array")
            .iter()
            .any(|candidate| {
                candidate["status"] == "candidate"
                    && candidate["measurementBoundary"]["aggregationWindow"].is_object()
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["basinCandidates"]
            .as_array()
            .expect("basinCandidates is array")
            .iter()
            .any(|candidate| candidate["status"] == "nonCandidate")
    );
    assert!(
        json["report"]["attractorEngineering"]["basinCandidates"]
            .as_array()
            .expect("basinCandidates is array")
            .iter()
            .any(|candidate| {
                candidate["status"] == "missingEvidence"
                    && candidate["measurementBoundary"]["missingEvidence"]
                        .as_array()
                        .expect("missingEvidence is array")
                        .iter()
                        .any(|evidence| evidence["boundary"] == "unmeasured")
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["basinSimulations"]
            .as_array()
            .expect("basinSimulations is array")
            .iter()
            .any(|simulation| {
                simulation["boundedHorizon"] == 4
                    && simulation["basinClassifications"]
                        .as_array()
                        .expect("basinClassifications is array")
                        .iter()
                        .any(|entry| entry["classification"] == "nonCandidate")
                    && simulation["basinClassifications"]
                        .as_array()
                        .expect("basinClassifications is array")
                        .iter()
                        .any(|entry| entry["classification"] == "missingEvidence")
            })
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["basinBoundaryFragility"]["value"]["fragilityRatio"],
        serde_json::json!(0.5)
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["trajectoryReturnTime"]["value"]["missingReturnEvidenceCount"],
        serde_json::json!(2)
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["observabilityDebt"]["value"]["debtWeight"],
        serde_json::json!(0.3)
    );
    assert_eq!(
        json["report"]["attractorEngineering"]["supportRiskEntries"]
            .as_array()
            .expect("supportRiskEntries is array")
            .len(),
        5
    );
    assert!(
        json["report"]["attractorEngineering"]["supportRiskEntries"]
            .as_array()
            .expect("supportRiskEntries is array")
            .iter()
            .any(|entry| {
                entry["riskState"] == "safePreservingProved"
                    && entry["preservationPreconditionStatus"] == "proved"
                    && entry["riskMassContribution"]["confidence"] == "formal-proof"
                    && entry["theoremPreconditionRefs"]
                        .as_array()
                        .expect("theoremPreconditionRefs is array")
                        .iter()
                        .any(|reference| {
                            reference == "Formal/Arch/Operation/OperationInvariant.lean#preservesInvariant_of_discharged_preserve"
                        })
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["supportRiskEntries"]
            .as_array()
            .expect("supportRiskEntries is array")
            .iter()
            .any(|entry| {
                entry["riskState"] == "safePreservingMeasured"
                    && entry["preservationPreconditionStatus"] == "measured"
                    && entry["riskMassContribution"]["confidence"] == "empirical-measured"
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["supportRiskEntries"]
            .as_array()
            .expect("supportRiskEntries is array")
            .iter()
            .any(|entry| {
                entry["riskState"] == "safePreservingEstimated"
                    && entry["preservationPreconditionStatus"] == "estimated"
                    && entry["riskMassContribution"]["confidence"] == "model-estimate"
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["designFieldSignals"]
            .as_array()
            .expect("designFieldSignals is array")
            .iter()
            .any(|signal| {
                signal["selectedSignal"] == "boundary-and-non-goal-alignment"
                    && signal["status"] == "advisory"
                    && signal["confidence"] == "bounded-fixture-signal"
                    && signal["sourceRefs"]
                        .as_array()
                        .expect("signal sourceRefs is array")
                        .len()
                        > 0
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["seedAttractorSignals"]
            .as_array()
            .expect("seedAttractorSignals is array")
            .iter()
            .any(|signal| {
                signal["selectedSignal"] == "canonical-example-copyability"
                    && signal["confidence"] == "bounded-fixture-signal"
                    && signal["sourceRefs"]
                        .as_array()
                        .expect("seed signal sourceRefs is array")
                        .iter()
                        .any(|artifact_ref| artifact_ref["kind"] == "canonical-example-ref")
                    && signal["sourceRefs"]
                        .as_array()
                        .expect("seed signal sourceRefs is array")
                        .iter()
                        .any(|artifact_ref| artifact_ref["kind"] == "patch-similarity-evidence")
            })
    );
    assert!(
        json["report"]["attractorEngineering"]["seedAttractorStrength"]["sourceRefs"]
            .as_array()
            .expect("SeedAttractorStrength sourceRefs is array")
            .iter()
            .any(|artifact_ref| artifact_ref["kind"] == "canonical-example-ref")
            && json["report"]["attractorEngineering"]["seedAttractorStrength"]["sourceRefs"]
                .as_array()
                .expect("SeedAttractorStrength sourceRefs is array")
                .iter()
                .any(|artifact_ref| artifact_ref["kind"] == "patch-similarity-evidence")
            && json["report"]["attractorEngineering"]["seedAttractorStrength"]["value"]["protocol"]
                == "selected-seed-attractor-pilot"
    );
    assert!(
        json["report"]["attractorEngineering"]["fieldShapingDelta"]["status"] == "notComparable"
            && json["report"]["attractorEngineering"]["fieldShapingDelta"]["value"]["comparisonStatus"]
                == "notComparable"
    );
    let readiness_axes = json["report"]["attractorEngineering"]["vibeCodingReadinessAxes"]
        .as_array()
        .expect("vibeCodingReadinessAxes is array");
    assert_eq!(readiness_axes.len(), 8);
    assert!(readiness_axes.iter().any(|axis| {
        axis["metricId"] == "vibeCodingReadiness.GoodAttractorBasinMass"
            && axis["status"] == "notComparable"
    }));
    assert!(readiness_axes.iter().all(|axis| {
        !axis["metricId"]
            .as_str()
            .expect("readiness metricId is string")
            .to_ascii_lowercase()
            .contains("score")
    }));

    let artifact = read_json(&fixture_artifact);
    assert_eq!(
        artifact["schema"],
        "architecture-dynamics-metrics-report/v0.5.0"
    );
    assert!(
        artifact["gapMetrics"]
            .as_array()
            .expect("gapMetrics is array")
            .iter()
            .any(|metric| {
                metric["metricId"] == "gap.forceCancellationRatio"
                    && metric["status"] == "notComparable"
            })
    );
    assert!(
        artifact["attractorEngineering"]["nonConclusions"]
            .as_array()
            .expect("Attractor Engineering nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion
                    == "attractorEngineering is bounded tooling evidence, not a global attractor theorem"
            })
    );
    assert!(
        artifact["attractorEngineering"]["measurementBoundary"]["sourceArtifactRefs"]
            .as_array()
            .expect("Attractor Engineering sourceArtifactRefs is array")
            .iter()
            .any(|artifact_ref| artifact_ref["kind"] == "architecture-field-snapshot")
    );
    assert!(
        artifact["attractorEngineering"]["measurementBoundary"]["sourceArtifactRefs"]
            .as_array()
            .expect("Attractor Engineering sourceArtifactRefs is array")
            .iter()
            .any(|artifact_ref| artifact_ref["kind"] == "operation-proposal-log")
    );

    let json = read_json(&fixture_validation);
    assert_eq!(json["summary"]["result"], "pass");

    let mut invalid_json = read_json(&root.join("architecture_dynamics_metrics_report.json"));
    invalid_json["forceMetrics"][0]["metricId"] =
        serde_json::json!("force.observedForce.latentForceEstimate");
    invalid_json["forceMetrics"][0]["nonConclusions"] = serde_json::json!([]);
    invalid_json["forceMetrics"][1]["metricId"] = serde_json::json!("force.hiddenPressure");
    invalid_json["forceMetrics"][2]["metricId"] = serde_json::json!("force.filteredPressure");
    fs::write(
        &invalid_report,
        serde_json::to_string_pretty(&invalid_json).expect("json serializes"),
    )
    .expect("invalid Architecture Dynamics metrics report is written");
    let output = run_sig0_output(&[
        "architecture-dynamics-metrics",
        "--input",
        invalid_report
            .to_str()
            .expect("invalid fixture path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid Architecture Dynamics metrics report should fail validation"
    );
    let json = read_json(&invalid_validation);
    assert_eq!(json["summary"]["result"], "fail");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "architecture-dynamics-metrics-force-classes-separated"
                    && check["result"] == "fail"
            })
    );

    let mut missing_attractor_json =
        read_json(&root.join("architecture_dynamics_metrics_report.json"));
    missing_attractor_json
        .as_object_mut()
        .expect("Architecture Dynamics metrics report is object")
        .remove("attractorEngineering");
    fs::write(
        &missing_attractor_report,
        serde_json::to_string_pretty(&missing_attractor_json).expect("json serializes"),
    )
    .expect("missing Attractor Engineering report is written");
    let output = run_sig0_output(&[
        "architecture-dynamics-metrics",
        "--input",
        missing_attractor_report
            .to_str()
            .expect("missing Attractor Engineering path is utf-8"),
        "--out",
        missing_attractor_validation
            .to_str()
            .expect("missing Attractor Engineering validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "missing Attractor Engineering section should fail validation"
    );
    let json = read_json(&missing_attractor_validation);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"]
                    == "architecture-dynamics-metrics-attractor-engineering-section-recorded"
                    && check["result"] == "fail"
            })
    );

    let mut invalid_attractor_json =
        read_json(&root.join("architecture_dynamics_metrics_report.json"));
    invalid_attractor_json["attractorEngineering"]["supportRiskMass"]["status"] =
        serde_json::json!("measuredish");
    invalid_attractor_json["attractorEngineering"]["nonConclusions"] = serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["attractorCandidates"][0]["status"] =
        serde_json::json!("global");
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][4]["riskState"] =
        serde_json::json!("private");
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][4]["riskMassContribution"]
        ["status"] = serde_json::json!("measured");
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][4]["riskMassContribution"]
        ["value"] = serde_json::json!(0.0);
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][0]["theoremPreconditionRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["supportRiskMass"]["value"]["unknownSupportWeight"] =
        serde_json::json!(0.0);
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][1]["riskMassContribution"]
        ["confidence"] = serde_json::json!("formal-proof");
    invalid_attractor_json["attractorEngineering"]["supportRiskEntries"][2]["riskMassContribution"]
        ["confidence"] = serde_json::json!("formal-proof");
    invalid_attractor_json["attractorEngineering"]["basinCandidates"][0]["measurementBoundary"]["sourceArtifactRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["basinCandidates"][0]["measurementBoundary"]
        .as_object_mut()
        .expect("bounded basin measurementBoundary is object")
        .remove("aggregationWindow");
    invalid_attractor_json["attractorEngineering"]["basinCandidates"][2]["measurementBoundary"]["missingEvidence"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["basinSimulations"][0]["basinClassifications"]
        [2]["missingEvidence"] = serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["basinSimulations"][0]["perturbationEvidence"]
        [1]["perturbedClassification"] = serde_json::json!("candidate");
    invalid_attractor_json["attractorEngineering"]["basinBoundaryFragility"]["status"] =
        serde_json::json!("measured");
    invalid_attractor_json["attractorEngineering"]["basinBoundaryFragility"]["value"] =
        serde_json::json!(0.0);
    invalid_attractor_json["attractorEngineering"]["basinBoundaryFragility"]["sourceRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["observabilityDebt"]["status"] =
        serde_json::json!("measured");
    invalid_attractor_json["attractorEngineering"]["observabilityDebt"]["value"] =
        serde_json::json!(0.0);
    invalid_attractor_json["attractorEngineering"]["observabilityDebt"]["nonConclusions"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["designFieldSignals"][0]["sourceRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["designFieldSignals"][0]["confidence"] =
        serde_json::json!(null);
    invalid_attractor_json["attractorEngineering"]["designFieldSignals"][0]["nonConclusions"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["seedAttractorSignals"][0]["sourceRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["seedAttractorStrength"]["sourceRefs"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["seedAttractorStrength"]["confidence"] =
        serde_json::json!(null);
    invalid_attractor_json["attractorEngineering"]["seedAttractorStrength"]["value"] =
        serde_json::json!({});
    invalid_attractor_json["attractorEngineering"]["fieldShapingDelta"]["status"] =
        serde_json::json!("measured");
    invalid_attractor_json["attractorEngineering"]["fieldShapingDelta"]["value"] =
        serde_json::json!(0.0);
    invalid_attractor_json["attractorEngineering"]["fieldShapingDelta"]["nonConclusions"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["fieldShapingDelta"]["measurementBoundary"]["missingEvidence"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["vibeCodingReadinessAxes"][0]["metricId"] =
        serde_json::json!("vibeCodingReadiness.score");
    invalid_attractor_json["attractorEngineering"]["vibeCodingReadinessAxes"][0]["nonConclusions"] =
        serde_json::json!([]);
    invalid_attractor_json["attractorEngineering"]["vibeCodingReadinessAxes"]
        .as_array_mut()
        .expect("readiness axes is array")
        .pop();
    fs::write(
        &invalid_attractor_report,
        serde_json::to_string_pretty(&invalid_attractor_json).expect("json serializes"),
    )
    .expect("invalid Attractor Engineering report is written");
    let output = run_sig0_output(&[
        "architecture-dynamics-metrics",
        "--input",
        invalid_attractor_report
            .to_str()
            .expect("invalid Attractor Engineering path is utf-8"),
        "--out",
        invalid_attractor_validation
            .to_str()
            .expect("invalid Attractor Engineering validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "invalid Attractor Engineering status and non-conclusions should fail validation"
    );
    let json = read_json(&invalid_attractor_validation);
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "architecture-dynamics-metrics-status-values-supported"
                    && check["result"] == "fail"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"]
                    == "architecture-dynamics-metrics-attractor-engineering-section-recorded"
                    && check["result"] == "fail"
            })
    );
    let attractor_check = json["checks"]
        .as_array()
        .expect("checks is array")
        .iter()
        .find(|check| {
            check["id"] == "architecture-dynamics-metrics-attractor-engineering-section-recorded"
        })
        .expect("Attractor Engineering validation check exists");
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("must not be emitted as measured numeric zero"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("must retain Lean theorem or theorem index precondition refs"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("must not be collapsed to measured zero"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("must retain canonical example refs and patch similarity evidence"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("must not share one confidence level"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("finite source refs, selected region refs, and an aggregation window"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("missing-evidence basin classifications must retain missing evidence"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(
                |example| example["evidence"].as_str().unwrap_or_default().contains(
                    "BasinBoundaryFragility needs selected 1-step or k-step perturbation evidence"
                )
            )
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("field shaping signals must record selected signal"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("FieldShapingDelta must keep its comparability non-conclusion explicit"))
    );
    assert!(
        attractor_check["examples"]
            .as_array()
            .expect("examples is array")
            .iter()
            .any(|example| example["evidence"]
                .as_str()
                .unwrap_or_default()
                .contains("VibeCodingReadiness must not be emitted as a single numeric score"))
    );
}

#[test]
fn cli_policy_decision_reports_fail_and_pass_boundaries() {
    let fixture = fixture_root();
    let air = air_fixture_root();
    let out_dir = temp_dir("policy-decision");

    let unmeasured_feature_report = out_dir.join("unmeasured-feature-report.json");
    let unmeasured_policy_decision = out_dir.join("unmeasured-policy-decision.json");
    run_sig0(&[
        "feature-report",
        "--air",
        air.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        unmeasured_feature_report
            .to_str()
            .expect("report path is utf-8"),
    ]);
    let output = run_sig0_output(&[
        "policy-decision",
        "--feature-report",
        unmeasured_feature_report
            .to_str()
            .expect("report path is utf-8"),
        "--policy",
        fixture
            .join("organization_policy.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        unmeasured_policy_decision
            .to_str()
            .expect("decision path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "unmeasured required runtime axis should fail policy decision"
    );
    let json = read_json(&unmeasured_policy_decision);
    assert_eq!(json["schema"], "policy-decision-report/v0.5.0");
    assert_eq!(json["summary"]["decision"], "fail");
    assert!(
        json["requiredAxisDecisions"]
            .as_array()
            .expect("requiredAxisDecisions is array")
            .iter()
            .any(|decision| decision["axis"] == "runtimePropagation"
                && decision["status"] == "fail"
                && decision["actualMeasurementBoundary"] == "unmeasured")
    );
    assert!(json["nonConclusions"]
        .as_array()
        .expect("nonConclusions is array")
        .iter()
        .any(|conclusion| conclusion == "unmeasured axes are not treated as measured-zero risk"));

    let mut measured_zero_input = read_json(&air.join("good_extension.json"));
    set_measured_runtime_axis(&mut measured_zero_input, 0);
    measured_zero_input["claims"]
        .as_array_mut()
        .expect("claims is an array")
        .push(runtime_zero_bridge_claim_json(
            "claim-runtime-zero-bridge-policy-proved",
            serde_json::json!([
                "runtimePropagation is computed over a measured 0/1 RuntimeDependencyGraph"
            ]),
            serde_json::json!(["runtime edge evidence coverage"]),
            serde_json::json!(["runtime-edge-projection-schema050 exactness"]),
            serde_json::json!([]),
        ));
    let measured_zero_air = out_dir.join("runtime-measured-zero.air.json");
    let measured_zero_feature_report = out_dir.join("runtime-measured-zero.report.json");
    let measured_zero_policy_decision = out_dir.join("runtime-measured-zero.policy.json");
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
        measured_zero_feature_report
            .to_str()
            .expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "policy-decision",
        "--feature-report",
        measured_zero_feature_report
            .to_str()
            .expect("report path is utf-8"),
        "--policy",
        fixture
            .join("organization_policy.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        measured_zero_policy_decision
            .to_str()
            .expect("decision path is utf-8"),
    ]);
    let json = read_json(&measured_zero_policy_decision);
    assert_eq!(json["summary"]["decision"], "pass");
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "policy-decision-required-axes" && check["result"] == "pass"
            )
    );
}

#[test]
fn cli_pr_comment_renders_levelled_markdown_summary() {
    let fixture = fixture_root();
    let air = air_fixture_root();
    let out_dir = temp_dir("pr-comment");
    let feature_report = out_dir.join("feature-report.json");
    let policy_decision = out_dir.join("policy-decision.json");
    let pr_comment = out_dir.join("pr-comment.md");

    run_sig0(&[
        "feature-report",
        "--air",
        air.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        feature_report.to_str().expect("report path is utf-8"),
    ]);
    let output = run_sig0_output(&[
        "policy-decision",
        "--feature-report",
        feature_report.to_str().expect("report path is utf-8"),
        "--policy",
        fixture
            .join("organization_policy.json")
            .to_str()
            .expect("policy path is utf-8"),
        "--out",
        policy_decision.to_str().expect("decision path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "fixture keeps unmeasured required runtime axis as policy fail"
    );

    run_sig0(&[
        "pr-comment",
        "--feature-report",
        feature_report.to_str().expect("report path is utf-8"),
        "--policy-decision",
        policy_decision.to_str().expect("decision path is utf-8"),
        "--out",
        pr_comment.to_str().expect("comment path is utf-8"),
    ]);

    let markdown = fs::read_to_string(&pr_comment).expect("PR comment markdown is readable");
    assert!(markdown.contains("<!-- schema: pr-comment-summary/v0.5.0 -->"));
    assert!(markdown.contains("### Level 1 Review Summary"));
    assert!(markdown.contains("<summary>Level 2 Evidence Detail</summary>"));
    assert!(markdown.contains("<summary>Level 3 Formal Detail</summary>"));
    assert!(markdown.contains("Policy decision: `fail`"));
    assert!(markdown.contains("runtimePropagation"));
    assert!(markdown.contains("This summary does not approve architecture lawfulness."));
}

#[test]
fn cli_report_artifacts_validates_static_manifest_and_input_fixture() {
    let root = fixture_root();
    let out_dir = temp_dir("report-artifacts");
    let static_report = out_dir.join("report-artifacts-static.json");
    let fixture_report = out_dir.join("report-artifacts-fixture.json");

    run_sig0(&[
        "report-artifacts",
        "--out",
        static_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "report-artifacts",
        "--input",
        root.join("report_artifact_retention.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        fixture_report.to_str().expect("report path is utf-8"),
    ]);

    let json = read_json(&static_report);
    assert_eq!(
        json["schema"],
        "report-artifact-retention-validation-report/v0.5.0"
    );
    assert_eq!(json["summary"]["result"], "pass");
    assert_eq!(json["summary"]["artifactCount"], 4);
    assert!(
        json["manifest"]["artifacts"]
            .as_array()
            .expect("artifacts is array")
            .iter()
            .any(|artifact| artifact["kind"] == "policyDecisionReport"
                && artifact["repository"]["name"] == "AlgebraicArchitectureTheoryV2"
                && artifact["pullRequestNumber"] == 575
                && artifact["policyVersion"] == "2026-05-05")
    );

    let json = read_json(&fixture_report);
    assert_eq!(json["summary"]["result"], "pass");
    assert!(
        json["manifest"]["missingOrPrivateArtifacts"]
            .as_array()
            .expect("missingOrPrivateArtifacts is array")
            .iter()
            .any(|artifact| artifact["kind"] == "prCommentSummary"
                && artifact["nonConclusions"]
                    .as_array()
                    .expect("nonConclusions is array")
                    .iter()
                    .any(|conclusion| {
                        conclusion == "missing or private artifacts are not measured-zero evidence"
                    }))
    );
    assert!(
        json["manifest"]["traceability"]["suppressionWorkflowRefs"]
            .as_array()
            .expect("suppressionWorkflowRefs is array")
            .iter()
            .any(|reference| reference == "suppression-workflow:pr-575")
    );
}

#[test]
fn cli_artifact_descriptor_emits_fixture_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("artifact-descriptor");
    let static_validation = out_dir.join("artifact-descriptor-static-validation.json");
    let fixture_artifact = out_dir.join("artifact-descriptor-fixture.json");
    let fixture_validation = out_dir.join("artifact-descriptor-validation.json");
    let generated_descriptor = out_dir.join("artifact-descriptor-generated.json");
    let generated_validation = out_dir.join("artifact-descriptor-generated-validation.json");
    let github_issue_descriptor = out_dir.join("artifact-descriptor-github-issue.json");
    let github_issue_validation = out_dir.join("artifact-descriptor-github-issue-validation.json");
    let ai_proposal_descriptor = out_dir.join("artifact-descriptor-ai-proposal.json");
    let ai_proposal_validation = out_dir.join("artifact-descriptor-ai-proposal-validation.json");
    let invalid_descriptor = out_dir.join("artifact-descriptor-invalid.json");
    let invalid_validation = out_dir.join("artifact-descriptor-invalid-validation.json");

    run_sig0(&[
        "artifact-descriptor",
        "--out",
        static_validation
            .to_str()
            .expect("static validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--fixture",
        "--out",
        fixture_artifact.to_str().expect("fixture path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--input",
        root.join("artifact_descriptor.json")
            .to_str()
            .expect("fixture input path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-markdown",
        root.join("artifact_descriptor_prd.md")
            .to_str()
            .expect("markdown fixture path is utf-8"),
        "--artifact-kind",
        "prd",
        "--out",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--input",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
        "--out",
        generated_validation
            .to_str()
            .expect("generated validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-github-issue-json",
        root.join("github_issue_sft_adapter.json")
            .to_str()
            .expect("GitHub Issue JSON fixture path is utf-8"),
        "--out",
        github_issue_descriptor
            .to_str()
            .expect("GitHub Issue descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--input",
        github_issue_descriptor
            .to_str()
            .expect("GitHub Issue descriptor path is utf-8"),
        "--out",
        github_issue_validation
            .to_str()
            .expect("GitHub Issue validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-ai-proposal-json",
        root.join("ai_proposal_sft_adapter.json")
            .to_str()
            .expect("AI proposal JSON fixture path is utf-8"),
        "--out",
        ai_proposal_descriptor
            .to_str()
            .expect("AI proposal descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--input",
        ai_proposal_descriptor
            .to_str()
            .expect("AI proposal descriptor path is utf-8"),
        "--out",
        ai_proposal_validation
            .to_str()
            .expect("AI proposal validation path is utf-8"),
    ]);

    let static_json = read_json(&static_validation);
    assert_eq!(
        static_json["schema"],
        "artifact-descriptor-validation-report/v0.5.0"
    );
    assert_eq!(static_json["summary"]["result"], "pass");
    assert_eq!(static_json["summary"]["actionClassCandidateCount"], 3);
    assert!(
        static_json["descriptor"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "artifact descriptor does not provide a causal forecast"
            })
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(artifact["artifactKind"], "issue");
    assert!(
        artifact["actionClassCandidates"]
            .as_array()
            .expect("actionClassCandidates is array")
            .iter()
            .any(|candidate| candidate["actionClass"] == "tooling-validation")
    );
    assert!(
        artifact["forecastNonConclusions"]
            .as_array()
            .expect("forecastNonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "descriptor boundary does not assign probability to future outcomes"
            })
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "artifact-descriptor-scope-and-measurement-boundary"
                    && check["result"] == "pass"
            })
    );

    let generated = read_json(&generated_descriptor);
    assert_eq!(generated["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(generated["artifactKind"], "prd");
    assert_eq!(
        generated["artifactTitle"],
        "Coupon Forecast Descriptor Builder"
    );
    assert!(
        generated["sourceRefs"]
            .as_array()
            .expect("sourceRefs is array")
            .iter()
            .any(|source| {
                source["sourceKind"] == "markdown"
                    && source["retainedFields"]
                        .as_array()
                        .expect("retainedFields is array")
                        .iter()
                        .any(|field| field == "body")
            })
    );
    assert!(
        generated["actionClassCandidates"]
            .as_array()
            .expect("actionClassCandidates is array")
            .iter()
            .any(|candidate| candidate["actionClass"] == "cli-entrypoint")
    );
    assert!(
        generated["missingEvidence"]
            .as_array()
            .expect("missingEvidence is array")
            .iter()
            .any(|evidence| {
                evidence["evidenceId"] == "missing:runtime-evidence"
                    && evidence["status"] == "unmeasured"
            })
    );
    let generated_report = read_json(&generated_validation);
    assert_eq!(generated_report["summary"]["result"], "pass");
    assert!(
        generated_report["descriptor"]["forecastNonConclusions"]
            .as_array()
            .expect("forecastNonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "descriptor evidence does not establish causal prediction"
            })
    );

    let github_issue = read_json(&github_issue_descriptor);
    assert_eq!(github_issue["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(github_issue["artifactKind"], "issue");
    assert_eq!(
        github_issue["sourceRefs"][0]["sourceKind"],
        "github-issue-json"
    );
    assert!(
        github_issue["missingEvidence"]
            .as_array()
            .expect("missingEvidence is array")
            .iter()
            .any(|evidence| evidence["evidenceId"] == "missing:github-api-context")
    );
    let github_issue_report = read_json(&github_issue_validation);
    assert_eq!(github_issue_report["summary"]["result"], "pass");

    let ai_proposal = read_json(&ai_proposal_descriptor);
    assert_eq!(ai_proposal["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(ai_proposal["artifactKind"], "ai-proposal");
    assert_eq!(
        ai_proposal["sourceRefs"][0]["sourceKind"],
        "ai-proposal-json"
    );
    assert!(
        ai_proposal["missingEvidence"]
            .as_array()
            .expect("missingEvidence is array")
            .iter()
            .any(|evidence| evidence["evidenceId"] == "missing:human-review")
    );
    let ai_proposal_report = read_json(&ai_proposal_validation);
    assert_eq!(ai_proposal_report["summary"]["result"], "pass");

    let mut invalid = artifact;
    invalid["forecastNonConclusions"] = serde_json::json!([]);
    fs::write(
        &invalid_descriptor,
        serde_json::to_string_pretty(&invalid).expect("invalid descriptor serializes"),
    )
    .expect("invalid descriptor is written");
    let output = run_sig0_output(&[
        "artifact-descriptor",
        "--input",
        invalid_descriptor
            .to_str()
            .expect("invalid descriptor path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "missing forecast non-conclusions should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["summary"]["result"], "fail");
    assert!(
        invalid_report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "artifact-descriptor-non-conclusions-preserved"
                    && check["result"] == "fail"
            })
    );
}

#[test]
fn cli_operation_support_estimate_emits_fixture_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("operation-support-estimate");
    let static_validation = out_dir.join("operation-support-estimate-static-validation.json");
    let fixture_artifact = out_dir.join("operation-support-estimate-fixture.json");
    let fixture_validation = out_dir.join("operation-support-estimate-validation.json");
    let generated_descriptor = out_dir.join("artifact-descriptor-generated.json");
    let generated_estimate = out_dir.join("operation-support-estimate-generated.json");
    let generated_validation = out_dir.join("operation-support-estimate-generated-validation.json");
    let invalid_estimate = out_dir.join("operation-support-estimate-invalid.json");
    let invalid_validation = out_dir.join("operation-support-estimate-invalid-validation.json");

    run_sig0(&[
        "operation-support-estimate",
        "--out",
        static_validation
            .to_str()
            .expect("static validation path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--fixture",
        "--out",
        fixture_artifact.to_str().expect("fixture path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--input",
        root.join("operation_support_estimate.json")
            .to_str()
            .expect("fixture input path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-markdown",
        root.join("artifact_descriptor_prd.md")
            .to_str()
            .expect("markdown fixture path is utf-8"),
        "--artifact-kind",
        "prd",
        "--out",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--descriptor",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
        "--out",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--input",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
        "--out",
        generated_validation
            .to_str()
            .expect("generated validation path is utf-8"),
    ]);

    let static_json = read_json(&static_validation);
    assert_eq!(
        static_json["schema"],
        "operation-support-estimate-validation-report/v0.5.0"
    );
    assert_eq!(static_json["summary"]["result"], "pass");
    assert_eq!(static_json["summary"]["candidateOperationFamilyCount"], 2);
    assert!(
        static_json["estimate"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "operation support estimate is not actual future support"
            })
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "operation-support-estimate/v0.5.0");
    assert_eq!(
        artifact["descriptorRef"]["descriptorSchemaVersion"],
        "artifact-descriptor/v0.5.0"
    );
    assert!(
        artifact["candidateOperationFamilies"]
            .as_array()
            .expect("candidateOperationFamilies is array")
            .iter()
            .any(|family| family["operationFamily"] == "schema-and-validator")
    );
    assert!(
        artifact["unknownRemainder"]
            .as_array()
            .expect("unknownRemainder is array")
            .iter()
            .any(|remainder| {
                remainder["unknownAxes"]
                    .as_array()
                    .expect("unknownAxes is array")
                    .iter()
                    .any(|axis| axis == "future accepted PR history")
            })
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "operation-support-estimate-unknown-remainder-not-measured-zero"
                    && check["result"] == "pass"
            })
    );

    let generated = read_json(&generated_estimate);
    assert_eq!(generated["schema"], "operation-support-estimate/v0.5.0");
    assert_eq!(generated["descriptorRef"]["artifactKind"], "prd");
    assert!(
        generated["descriptorRef"]["sourceRefIds"]
            .as_array()
            .expect("sourceRefIds is array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-forecast-descriptor-builder")
    );
    assert!(
        generated["candidateOperationFamilies"]
            .as_array()
            .expect("candidateOperationFamilies is array")
            .iter()
            .any(|family| family["operationFamily"] == "cli-fixture-validation")
    );
    assert!(
        generated["knownForbiddenSupport"]
            .as_array()
            .expect("knownForbiddenSupport is array")
            .iter()
            .any(|forbidden| forbidden["operationFamily"] == "causal-probability-assignment")
    );
    assert!(
        generated["unknownRemainder"]
            .as_array()
            .expect("unknownRemainder is array")
            .iter()
            .any(|remainder| {
                remainder["treatment"]
                    .as_str()
                    .expect("unknown treatment is a string")
                    .contains("retain as unknown support remainder")
            })
    );
    let generated_report = read_json(&generated_validation);
    assert_eq!(generated_report["summary"]["result"], "pass");
    assert!(
        generated_report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "operation-support-estimate-evidence-boundary-retained"
                    && check["result"] == "pass"
            })
    );

    let mut invalid = artifact;
    invalid["candidateOperationFamilies"][0]["sourceRefIds"] =
        serde_json::json!(["source:missing"]);
    invalid["policyConstraints"][0]["safetyClaimBoundary"] =
        serde_json::json!("global safety is guaranteed");
    invalid["unknownRemainder"][0]["treatment"] = serde_json::json!("treated as zero");
    fs::write(
        &invalid_estimate,
        serde_json::to_string_pretty(&invalid).expect("invalid estimate serializes"),
    )
    .expect("invalid estimate is written");
    let output = run_sig0_output(&[
        "operation-support-estimate",
        "--input",
        invalid_estimate
            .to_str()
            .expect("invalid estimate path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "dangling source refs, global safety claims, and measured-zero unknowns should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["summary"]["result"], "fail");
    for expected_check in [
        "operation-support-estimate-candidate-families-bounded",
        "operation-support-estimate-policy-constraints-bounded",
        "operation-support-estimate-unknown-remainder-not-measured-zero",
    ] {
        assert!(
            invalid_report["checks"]
                .as_array()
                .expect("checks is array")
                .iter()
                .any(|check| check["id"] == expected_check && check["result"] == "fail"),
            "missing failed check {expected_check}"
        );
    }
}

#[test]
fn cli_forecast_cone_skeleton_emits_fixture_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("forecast-cone-skeleton");
    let static_validation = out_dir.join("forecast-cone-static-validation.json");
    let fixture_artifact = out_dir.join("forecast-cone-fixture.json");
    let fixture_validation = out_dir.join("forecast-cone-validation.json");
    let generated_descriptor = out_dir.join("artifact-descriptor-generated.json");
    let generated_estimate = out_dir.join("operation-support-estimate-generated.json");
    let generated_cone = out_dir.join("forecast-cone-generated.json");
    let generated_validation = out_dir.join("forecast-cone-generated-validation.json");
    let invalid_cone = out_dir.join("forecast-cone-invalid.json");
    let invalid_validation = out_dir.join("forecast-cone-invalid-validation.json");

    run_sig0(&[
        "forecast-cone-skeleton",
        "--out",
        static_validation
            .to_str()
            .expect("static validation path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--fixture",
        "--out",
        fixture_artifact.to_str().expect("fixture path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--input",
        root.join("forecast_cone_skeleton.json")
            .to_str()
            .expect("fixture input path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-markdown",
        root.join("artifact_descriptor_prd.md")
            .to_str()
            .expect("markdown fixture path is utf-8"),
        "--artifact-kind",
        "prd",
        "--out",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--descriptor",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
        "--out",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--operation-support",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
        "--horizon-steps",
        "4",
        "--horizon-window",
        "Coupon PRD bounded forecast horizon",
        "--out",
        generated_cone
            .to_str()
            .expect("generated cone path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--input",
        generated_cone
            .to_str()
            .expect("generated cone path is utf-8"),
        "--out",
        generated_validation
            .to_str()
            .expect("generated validation path is utf-8"),
    ]);

    let static_json = read_json(&static_validation);
    assert_eq!(
        static_json["schema"],
        "forecast-cone-skeleton-validation-report/v0.5.0"
    );
    assert_eq!(static_json["summary"]["result"], "pass");
    assert_eq!(static_json["summary"]["pathClassCandidateCount"], 2);
    assert!(
        static_json["cone"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| conclusion == "forecast cone skeleton does not assign probabilities")
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "forecast-cone-skeleton/v0.5.0");
    assert_eq!(
        artifact["operationSupportRef"]["estimateSchemaVersion"],
        "operation-support-estimate/v0.5.0"
    );
    assert!(
        artifact["forecastBoundary"]["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is array")
            .iter()
            .any(|construct| construct == "probability assignment")
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "forecast-cone-unknown-remainder-not-measured-zero"
                    && check["result"] == "pass"
            })
    );

    let generated = read_json(&generated_cone);
    assert_eq!(generated["schema"], "forecast-cone-skeleton/v0.5.0");
    assert_eq!(
        generated["operationSupportRef"]["estimateSchemaVersion"],
        "operation-support-estimate/v0.5.0"
    );
    assert_eq!(generated["boundedHorizon"]["maxSteps"], 4);
    assert!(
        generated["operationSupportRef"]["sourceRefIds"]
            .as_array()
            .expect("sourceRefIds is array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-forecast-descriptor-builder")
    );
    assert!(
        generated["finiteSupportRefs"]
            .as_array()
            .expect("finiteSupportRefs is array")
            .iter()
            .any(|support| support["operationFamilyIds"].as_array().is_some())
    );
    assert!(
        generated["forecastBoundary"]["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is array")
            .iter()
            .any(|construct| construct == "probability assignment")
    );
    assert!(
        generated["unknownRemainder"]
            .as_array()
            .expect("unknownRemainder is array")
            .iter()
            .any(|remainder| {
                remainder["treatment"]
                    .as_str()
                    .expect("unknown treatment is a string")
                    .contains("unknown forecast remainder")
            })
    );
    let generated_report = read_json(&generated_validation);
    assert_eq!(generated_report["summary"]["result"], "pass");
    assert!(
        generated_report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "forecast-cone-boundary-retained" && check["result"] == "pass"
            })
    );

    let mut invalid = artifact;
    invalid["boundedHorizon"]["maxSteps"] = serde_json::json!(0);
    invalid["pathClassCandidates"][0]["supportRefIds"] = serde_json::json!(["support:missing"]);
    invalid["pathClassCandidates"][0]["probabilityBoundary"] = serde_json::json!("probability 0.8");
    invalid["unknownRemainder"][0]["treatment"] = serde_json::json!("treated as zero");
    fs::write(
        &invalid_cone,
        serde_json::to_string_pretty(&invalid).expect("invalid cone serializes"),
    )
    .expect("invalid cone is written");
    let output = run_sig0_output(&[
        "forecast-cone-skeleton",
        "--input",
        invalid_cone.to_str().expect("invalid cone path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "zero horizon, probability claims, and measured-zero unknowns should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["summary"]["result"], "fail");
    for expected_check in [
        "forecast-cone-bounded-horizon-present",
        "forecast-cone-path-classes-bounded",
        "forecast-cone-unknown-remainder-not-measured-zero",
    ] {
        assert!(
            invalid_report["checks"]
                .as_array()
                .expect("checks is array")
                .iter()
                .any(|check| check["id"] == expected_check && check["result"] == "fail"),
            "missing failed check {expected_check}"
        );
    }
}

#[test]
fn cli_consequence_envelope_emits_fixture_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("consequence-envelope");
    let static_validation = out_dir.join("consequence-envelope-static-validation.json");
    let fixture_artifact = out_dir.join("consequence-envelope-fixture.json");
    let fixture_validation = out_dir.join("consequence-envelope-validation.json");
    let generated_descriptor = out_dir.join("artifact-descriptor-generated.json");
    let generated_estimate = out_dir.join("operation-support-estimate-generated.json");
    let generated_cone = out_dir.join("forecast-cone-generated.json");
    let generated_envelope = out_dir.join("consequence-envelope-generated.json");
    let generated_validation = out_dir.join("consequence-envelope-generated-validation.json");
    let invalid_envelope = out_dir.join("consequence-envelope-invalid.json");
    let invalid_validation = out_dir.join("consequence-envelope-invalid-validation.json");

    run_sig0(&[
        "consequence-envelope",
        "--out",
        static_validation
            .to_str()
            .expect("static validation path is utf-8"),
    ]);
    run_sig0(&[
        "consequence-envelope",
        "--fixture",
        "--out",
        fixture_artifact.to_str().expect("fixture path is utf-8"),
    ]);
    run_sig0(&[
        "consequence-envelope",
        "--input",
        root.join("consequence_envelope_report.json")
            .to_str()
            .expect("fixture input path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);
    run_sig0(&[
        "artifact-descriptor",
        "--from-markdown",
        root.join("artifact_descriptor_prd.md")
            .to_str()
            .expect("markdown fixture path is utf-8"),
        "--artifact-kind",
        "prd",
        "--out",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
    ]);
    run_sig0(&[
        "operation-support-estimate",
        "--descriptor",
        generated_descriptor
            .to_str()
            .expect("generated descriptor path is utf-8"),
        "--out",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-cone-skeleton",
        "--operation-support",
        generated_estimate
            .to_str()
            .expect("generated estimate path is utf-8"),
        "--horizon-steps",
        "4",
        "--horizon-window",
        "Coupon PRD bounded forecast horizon",
        "--out",
        generated_cone
            .to_str()
            .expect("generated cone path is utf-8"),
    ]);
    run_sig0(&[
        "consequence-envelope",
        "--forecast-cone",
        generated_cone
            .to_str()
            .expect("generated cone path is utf-8"),
        "--out",
        generated_envelope
            .to_str()
            .expect("generated envelope path is utf-8"),
    ]);
    run_sig0(&[
        "consequence-envelope",
        "--input",
        generated_envelope
            .to_str()
            .expect("generated envelope path is utf-8"),
        "--out",
        generated_validation
            .to_str()
            .expect("generated validation path is utf-8"),
    ]);

    let static_json = read_json(&static_validation);
    assert_eq!(
        static_json["schema"],
        "consequence-envelope-report-validation-report/v0.5.0"
    );
    assert_eq!(static_json["summary"]["result"], "pass");
    assert_eq!(static_json["summary"]["affectedRegionCount"], 2);
    assert!(
        static_json["envelope"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| conclusion == "consequence envelope does not prove global safety")
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "consequence-envelope-report/v0.5.0");
    assert!(
        artifact["summaryProjection"]["reviewerNotes"]
            .as_array()
            .expect("reviewerNotes is array")
            .iter()
            .any(|note| note == "No probability or causal safety claim is emitted.")
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "consequence-envelope-unknown-remainder-not-measured-zero"
                    && check["result"] == "pass"
            })
    );

    let generated = read_json(&generated_envelope);
    assert_eq!(generated["schema"], "consequence-envelope-report/v0.5.0");
    assert_eq!(
        generated["forecastConeRef"]["forecastConeSchemaVersion"],
        "forecast-cone-skeleton/v0.5.0"
    );
    assert!(
        generated["forecastConeRef"]["sourceRefIds"]
            .as_array()
            .expect("sourceRefIds is array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-forecast-descriptor-builder")
    );
    assert!(
        generated["affectedArchitectureRegions"]
            .as_array()
            .expect("affectedArchitectureRegions is array")
            .iter()
            .any(|region| region["effectKind"] == "forecast-path-class")
    );
    assert!(
        generated["comparableSignatureAxes"]
            .as_array()
            .expect("comparableSignatureAxes is array")
            .iter()
            .any(|axis| axis["axisName"] == "boundaryRetention")
    );
    assert!(
        generated["recommendations"]["ci"]
            .as_array()
            .expect("ci recommendations is array")
            .iter()
            .any(|recommendation| {
                recommendation == "retain forecast cone skeleton validation as an upstream check"
            })
    );
    assert!(
        generated["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion
                    == "consequence envelope does not identify a unique causal artifact action"
            })
    );
    let generated_report = read_json(&generated_validation);
    assert_eq!(generated_report["summary"]["result"], "pass");
    assert!(
        generated_report["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "consequence-envelope-boundaries-and-summary-retained"
                    && check["result"] == "pass"
            })
    );

    let mut invalid = artifact;
    invalid["affectedArchitectureRegions"][0]["sourceRefIds"] =
        serde_json::json!(["source:missing"]);
    invalid["summaryProjection"]["affectedRegionCount"] = serde_json::json!(99);
    invalid["unknownRemainder"][0]["treatment"] = serde_json::json!("safe and absent");
    fs::write(
        &invalid_envelope,
        serde_json::to_string_pretty(&invalid).expect("invalid envelope serializes"),
    )
    .expect("invalid envelope is written");
    let output = run_sig0_output(&[
        "consequence-envelope",
        "--input",
        invalid_envelope
            .to_str()
            .expect("invalid envelope path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "dangling source refs, summary mismatch, and measured-zero unknowns should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["summary"]["result"], "fail");
    for expected_check in [
        "consequence-envelope-source-refs-retained",
        "consequence-envelope-boundaries-and-summary-retained",
        "consequence-envelope-unknown-remainder-not-measured-zero",
    ] {
        assert!(
            invalid_report["checks"]
                .as_array()
                .expect("checks is array")
                .iter()
                .any(|check| check["id"] == expected_check && check["result"] == "fail"),
            "missing failed check {expected_check}"
        );
    }
}

#[test]
fn cli_sft_review_summary_projects_reviewer_judgement_contract() {
    let root = fixture_root();
    let out_dir = temp_dir("sft-review-summary");
    let summary = out_dir.join("sft-review-summary.json");
    let validation = out_dir.join("sft-review-summary-validation.json");
    let generated_summary = out_dir.join("sft-review-summary-generated.json");
    let invalid_summary = out_dir.join("sft-review-summary-invalid.json");
    let invalid_validation = out_dir.join("sft-review-summary-invalid-validation.json");

    run_sig0(&[
        "sft-review-summary",
        "--fixture",
        "--out",
        summary.to_str().expect("summary path is utf-8"),
    ]);
    run_sig0(&[
        "sft-review-summary",
        "--input",
        summary.to_str().expect("summary path is utf-8"),
        "--out",
        validation.to_str().expect("validation path is utf-8"),
    ]);
    run_sig0(&[
        "sft-review-summary",
        "--consequence-envelope",
        root.join("consequence_envelope_report.json")
            .to_str()
            .expect("envelope fixture path is utf-8"),
        "--out",
        generated_summary
            .to_str()
            .expect("generated summary path is utf-8"),
    ]);

    let validation_json = read_json(&validation);
    assert_eq!(
        validation_json["schema"],
        "sft-review-summary-validation-report/v0.5.0"
    );
    assert_eq!(validation_json["validationSummary"]["result"], "pass");
    assert!(
        validation_json["checks"]
            .as_array()
            .expect("checks are array")
            .iter()
            .any(|check| {
                check["id"] == "sft-review-summary-evidence-and-boundary-refs-required"
                    && check["result"] == "pass"
            })
    );

    let generated = read_json(&generated_summary);
    assert_eq!(generated["schema"], "sft-review-summary/v0.5.0");
    assert!(
        generated["openedFutures"]
            .as_array()
            .expect("opened futures are array")
            .iter()
            .any(|future| !future["evidenceRefs"].as_array().unwrap().is_empty())
    );
    assert!(
        generated["llmJudgementContract"]["forbiddenReadings"]
            .as_array()
            .expect("forbidden readings are array")
            .iter()
            .any(|reading| reading == "Lean theorem promotion")
    );

    let mut invalid = generated;
    invalid["status"] = serde_json::json!("approved");
    invalid["nextActions"][0]["evidenceRefs"] = serde_json::json!([]);
    fs::write(
        &invalid_summary,
        serde_json::to_string_pretty(&invalid).expect("invalid summary serializes"),
    )
    .expect("invalid summary is written");
    let output = run_sig0_output(&[
        "sft-review-summary",
        "--input",
        invalid_summary
            .to_str()
            .expect("invalid summary path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "unsupported status and missing evidence refs should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["validationSummary"]["result"], "fail");
}

#[test]
fn cli_sft_forecast_generates_coupon_pipeline_and_retains_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("sft-forecast");
    let descriptor = out_dir.join("artifact-descriptor.json");
    let descriptor_validation = out_dir.join("artifact-descriptor-validation.json");
    let estimate = out_dir.join("operation-support-estimate.json");
    let estimate_validation = out_dir.join("operation-support-estimate-validation.json");
    let cone = out_dir.join("forecast-cone-skeleton.json");
    let cone_validation = out_dir.join("forecast-cone-skeleton-validation.json");
    let envelope = out_dir.join("consequence-envelope-report.json");
    let envelope_validation = out_dir.join("consequence-envelope-validation.json");
    let review_summary = out_dir.join("sft-review-summary.json");
    let review_summary_validation = out_dir.join("sft-review-summary-validation.json");

    run_sig0(&[
        "sft-forecast",
        "--artifact",
        root.join("coupon_prd.md")
            .to_str()
            .expect("coupon PRD fixture path is utf-8"),
        "--artifact-kind",
        "prd",
        "--horizon-steps",
        "4",
        "--horizon-window",
        "Coupon PRD bounded forecast horizon",
        "--out-dir",
        out_dir.to_str().expect("output dir path is utf-8"),
    ]);

    for path in [
        &descriptor,
        &descriptor_validation,
        &estimate,
        &estimate_validation,
        &cone,
        &cone_validation,
        &envelope,
        &envelope_validation,
        &review_summary,
        &review_summary_validation,
    ] {
        assert!(path.exists(), "expected sft-forecast output {path:?}");
    }

    let descriptor_json = read_json(&descriptor);
    assert_eq!(descriptor_json["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(descriptor_json["artifactKind"], "prd");
    assert_eq!(
        descriptor_json["artifactTitle"],
        "Coupon PRD Forecast Pipeline"
    );
    assert!(
        descriptor_json["measurementBoundary"]["sourceRefIds"]
            .as_array()
            .expect("descriptor boundary source refs are an array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-prd-forecast-pipeline")
    );
    assert!(
        descriptor_json["forecastNonConclusions"]
            .as_array()
            .expect("forecast non-conclusions are an array")
            .iter()
            .any(|conclusion| {
                conclusion == "descriptor evidence does not establish causal prediction"
            })
    );
    assert_eq!(
        read_json(&descriptor_validation)["summary"]["result"],
        "pass"
    );

    let estimate_json = read_json(&estimate);
    assert_eq!(estimate_json["schema"], "operation-support-estimate/v0.5.0");
    assert!(
        estimate_json["descriptorRef"]["sourceRefIds"]
            .as_array()
            .expect("estimate source refs are an array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-prd-forecast-pipeline")
    );
    assert!(
        estimate_json["unknownRemainder"]
            .as_array()
            .expect("estimate unknown remainder is an array")
            .iter()
            .any(|remainder| {
                remainder["treatment"]
                    .as_str()
                    .expect("estimate treatment is a string")
                    .contains("unknown support remainder")
            })
    );
    assert_eq!(read_json(&estimate_validation)["summary"]["result"], "pass");

    let cone_json = read_json(&cone);
    assert_eq!(cone_json["schema"], "forecast-cone-skeleton/v0.5.0");
    assert_eq!(cone_json["boundedHorizon"]["maxSteps"], 4);
    assert!(
        cone_json["operationSupportRef"]["sourceRefIds"]
            .as_array()
            .expect("cone source refs are an array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-prd-forecast-pipeline")
    );
    assert!(
        cone_json["forecastBoundary"]["unsupportedConstructs"]
            .as_array()
            .expect("unsupported constructs are an array")
            .iter()
            .any(|construct| construct == "probability assignment")
    );
    assert!(
        cone_json["nonConclusions"]
            .as_array()
            .expect("cone non-conclusions are an array")
            .iter()
            .any(|conclusion| conclusion == "forecast cone skeleton does not assign probabilities")
    );
    assert_eq!(read_json(&cone_validation)["summary"]["result"], "pass");

    let envelope_json = read_json(&envelope);
    assert_eq!(
        envelope_json["schema"],
        "consequence-envelope-report/v0.5.0"
    );
    let review_summary_json = read_json(&review_summary);
    assert_eq!(review_summary_json["schema"], "sft-review-summary/v0.5.0");
    assert!(
        review_summary_json["boundaryFailures"]
            .as_array()
            .expect("boundary failures are array")
            .iter()
            .any(|failure| !failure["evidenceRefs"].as_array().unwrap().is_empty())
    );
    assert!(
        envelope_json["forecastConeRef"]["sourceRefIds"]
            .as_array()
            .expect("envelope source refs are an array")
            .iter()
            .any(|source_ref| source_ref == "source:markdown:coupon-prd-forecast-pipeline")
    );
    assert!(
        envelope_json["missingBoundaryItems"]
            .as_array()
            .expect("missing boundary items are an array")
            .iter()
            .any(|item| item["itemKind"] == "unsupported-construct-boundary")
    );
    assert!(
        envelope_json["nonConclusions"]
            .as_array()
            .expect("envelope non-conclusions are an array")
            .iter()
            .any(|conclusion| {
                conclusion
                    == "consequence envelope does not identify a unique causal artifact action"
            })
    );
    assert_eq!(read_json(&envelope_validation)["summary"]["result"], "pass");

    let golden_envelope =
        read_json(&root.join("sft_forecast_coupon_golden/consequence-envelope-report.json"));
    assert_eq!(envelope_json, golden_envelope);
}

#[test]
fn cli_sft_forecast_accepts_json_adapters_and_retains_source_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("sft-forecast-github-issue-json");
    let descriptor = out_dir.join("artifact-descriptor.json");
    let envelope = out_dir.join("consequence-envelope-report.json");

    run_sig0(&[
        "sft-forecast",
        "--artifact",
        root.join("github_issue_sft_adapter.json")
            .to_str()
            .expect("GitHub Issue JSON fixture path is utf-8"),
        "--artifact-format",
        "github-issue-json",
        "--horizon-steps",
        "2",
        "--horizon-window",
        "GitHub Issue JSON bounded forecast horizon",
        "--out-dir",
        out_dir.to_str().expect("output dir path is utf-8"),
    ]);

    assert!(descriptor.exists(), "expected descriptor output");
    assert!(envelope.exists(), "expected consequence envelope output");

    let descriptor_json = read_json(&descriptor);
    assert_eq!(descriptor_json["schema"], "artifact-descriptor/v0.5.0");
    assert_eq!(descriptor_json["artifactKind"], "issue");
    assert_eq!(
        descriptor_json["sourceRefs"][0]["sourceKind"],
        "github-issue-json"
    );
    assert!(
        descriptor_json["measurementBoundary"]["unsupportedConstructs"]
            .as_array()
            .expect("unsupportedConstructs is array")
            .iter()
            .any(|construct| {
                construct == "implicit requirements not present in the supplied JSON artifact"
            })
    );
}

#[test]
fn cli_forecast_calibration_hook_emits_fixture_and_validates_boundaries() {
    let root = fixture_root();
    let out_dir = temp_dir("forecast-calibration-hook");
    let static_validation = out_dir.join("forecast-calibration-static-validation.json");
    let fixture_artifact = out_dir.join("forecast-calibration-fixture.json");
    let fixture_validation = out_dir.join("forecast-calibration-validation.json");
    let invalid_hook = out_dir.join("forecast-calibration-invalid.json");
    let invalid_validation = out_dir.join("forecast-calibration-invalid-validation.json");

    run_sig0(&[
        "forecast-calibration-hook",
        "--out",
        static_validation
            .to_str()
            .expect("static validation path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-calibration-hook",
        "--fixture",
        "--out",
        fixture_artifact.to_str().expect("fixture path is utf-8"),
    ]);
    run_sig0(&[
        "forecast-calibration-hook",
        "--input",
        root.join("forecast_calibration_hook.json")
            .to_str()
            .expect("fixture input path is utf-8"),
        "--out",
        fixture_validation
            .to_str()
            .expect("fixture validation path is utf-8"),
    ]);

    let static_json = read_json(&static_validation);
    assert_eq!(
        static_json["schema"],
        "forecast-calibration-hook-validation-report/v0.5.0"
    );
    assert_eq!(static_json["summary"]["result"], "pass");
    assert_eq!(static_json["summary"]["matchCount"], 2);
    assert!(
        static_json["hook"]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| conclusion == "calibration hook does not prove forecast correctness")
    );

    let artifact = read_json(&fixture_artifact);
    assert_eq!(artifact["schema"], "forecast-calibration-hook/v0.5.0");
    assert!(
        artifact["referenceBoundaries"]["b10Refs"]
            .as_array()
            .expect("b10Refs is array")
            .iter()
            .any(|reference| reference == "report-outcome-daily-ledger/v0.5.0")
    );
    assert!(
        artifact["matches"]
            .as_array()
            .expect("matches is array")
            .iter()
            .any(|item| item["status"] == "private")
    );

    let validation = read_json(&fixture_validation);
    assert_eq!(validation["summary"]["result"], "pass");
    assert!(
        validation["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(|check| {
                check["id"] == "forecast-calibration-hook-statuses-not-measured-zero"
                    && check["result"] == "pass"
            })
    );

    let mut invalid = artifact;
    invalid["matches"][0]["forecastItemId"] = serde_json::json!("forecast-item:missing");
    invalid["matches"][1]["status"] = serde_json::json!("measuredZero");
    invalid["referenceBoundaries"]["measurementBoundary"] =
        serde_json::json!("unavailable refs are treated as zero");
    fs::write(
        &invalid_hook,
        serde_json::to_string_pretty(&invalid).expect("invalid hook serializes"),
    )
    .expect("invalid hook is written");
    let output = run_sig0_output(&[
        "forecast-calibration-hook",
        "--input",
        invalid_hook.to_str().expect("invalid hook path is utf-8"),
        "--out",
        invalid_validation
            .to_str()
            .expect("invalid validation path is utf-8"),
    ]);
    assert!(
        !output.status.success(),
        "dangling forecast refs, invalid statuses, and measured-zero boundaries should fail validation"
    );
    let invalid_report = read_json(&invalid_validation);
    assert_eq!(invalid_report["summary"]["result"], "fail");
    for expected_check in [
        "forecast-calibration-hook-forecast-and-observed-refs-linked",
        "forecast-calibration-hook-statuses-not-measured-zero",
        "forecast-calibration-hook-b10-b11-boundaries-retained",
    ] {
        assert!(
            invalid_report["checks"]
                .as_array()
                .expect("checks is array")
                .iter()
                .any(|check| check["id"] == expected_check && check["result"] == "fail"),
            "missing failed check {expected_check}"
        );
    }
}

#[test]
fn cli_baseline_suppression_reports_deltas_without_resolving_suppressed_witnesses() {
    let fixture = fixture_root();
    let air = air_fixture_root();
    let out_dir = temp_dir("baseline-suppression");
    let baseline_report = out_dir.join("baseline-feature-report.json");
    let current_report = out_dir.join("current-feature-report.json");
    let baseline_policy = out_dir.join("baseline-policy-decision.json");
    let current_policy = out_dir.join("current-policy-decision.json");
    let suppression = out_dir.join("suppression.json");
    let baseline_suppression = out_dir.join("baseline-suppression.json");

    run_sig0(&[
        "feature-report",
        "--air",
        air.join("good_extension.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        baseline_report.to_str().expect("report path is utf-8"),
    ]);
    run_sig0(&[
        "feature-report",
        "--air",
        air.join("hidden_interaction.json")
            .to_str()
            .expect("fixture path is utf-8"),
        "--out",
        current_report.to_str().expect("report path is utf-8"),
    ]);
    for (report, decision) in [
        (&baseline_report, &baseline_policy),
        (&current_report, &current_policy),
    ] {
        let output = run_sig0_output(&[
            "policy-decision",
            "--feature-report",
            report.to_str().expect("report path is utf-8"),
            "--policy",
            fixture
                .join("organization_policy.json")
                .to_str()
                .expect("policy path is utf-8"),
            "--out",
            decision.to_str().expect("decision path is utf-8"),
        ]);
        assert!(
            !output.status.success(),
            "fixture policy decisions intentionally keep required runtime axis failing"
        );
    }

    let current_json = read_json(&current_report);
    let witness_ref = current_json["introducedObstructionWitnesses"][0]["witnessId"]
        .as_str()
        .expect("current fixture has a witness");
    fs::write(
        &suppression,
        serde_json::to_string_pretty(&serde_json::json!({
            "dispositionId": "suppression-hidden-interaction-001",
            "kind": "suppression",
            "status": "requested",
            "reason": "fixture records temporary review suppression for the hidden interaction witness",
            "approvedBy": "architecture-reviewer",
            "approvedAt": "2026-05-05T00:00:00Z",
            "expiresAt": "2026-06-05T00:00:00Z",
            "scope": "minimal fixture PR review",
            "policyRef": "fixture-b7-organization-policy",
            "witnessRef": witness_ref,
            "appliesToCurrentWitness": false,
            "reviewerStatus": "",
            "nonConclusions": [
                "suppression does not prove repair success"
            ]
        }))
        .expect("suppression json serializes"),
    )
    .expect("suppression fixture is written");

    run_sig0(&[
        "baseline-suppression",
        "--baseline-feature-report",
        baseline_report.to_str().expect("report path is utf-8"),
        "--current-feature-report",
        current_report.to_str().expect("report path is utf-8"),
        "--baseline-policy-decision",
        baseline_policy.to_str().expect("decision path is utf-8"),
        "--current-policy-decision",
        current_policy.to_str().expect("decision path is utf-8"),
        "--retention-manifest",
        fixture
            .join("report_artifact_retention.json")
            .to_str()
            .expect("retention path is utf-8"),
        "--suppression",
        suppression.to_str().expect("suppression path is utf-8"),
        "--out",
        baseline_suppression
            .to_str()
            .expect("baseline suppression path is utf-8"),
    ]);

    let json = read_json(&baseline_suppression);
    assert_eq!(json["schema"], "baseline-suppression-report/v0.5.0");
    assert_eq!(json["summary"]["suppressedCount"], 1);
    assert_eq!(json["summary"]["newlyIntroducedWitnessCount"], 1);
    assert!(
        json["witnessDelta"]["newlyIntroduced"]
            .as_array()
            .expect("newlyIntroduced witnesses is array")
            .iter()
            .any(|witness| witness["witnessId"] == witness_ref)
    );
    assert_eq!(
        json["suppressions"][0]["reviewerStatus"],
        "suppressed for review workflow; witness remains unresolved"
    );
    assert!(
        json["suppressions"][0]["nonConclusions"]
            .as_array()
            .expect("nonConclusions is array")
            .iter()
            .any(|conclusion| {
                conclusion == "suppressed and accepted-risk witnesses are not resolved witnesses"
            })
    );
    assert!(
        json["checks"]
            .as_array()
            .expect("checks is array")
            .iter()
            .any(
                |check| check["id"] == "baseline-suppression-disposition-non-resolution"
                    && check["result"] == "advisory"
            )
    );
}
