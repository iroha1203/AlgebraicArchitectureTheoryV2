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

fn sharded_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sharded")
}

#[test]
fn cli_help_exposes_only_llm_atom_archmap_surface() {
    let output = run_sig0_output(&["--help"]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);

    for command in [
        "archmap",
        "archmap-generate",
        "law-policy",
        "interpretation-profile",
        "archsig-analysis",
        "aat-analysis",
        "llm-native-workflow",
        "north-star-workflow",
        "schema-catalog",
    ] {
        assert!(
            stdout.contains(command),
            "ArchSig help must expose retained command {command}\n{stdout}"
        );
    }

    for removed in removed_commands() {
        assert!(
            !stdout.contains(removed),
            "ArchSig help still exposes removed command {removed}\n{stdout}"
        );
    }
}

#[test]
fn cli_accepts_north_star_command_aliases() {
    let out_dir = temp_dir("north-star-aliases");
    let root = fixture_root();
    let profile_validation = out_dir.join("interpretation-profile-validation.json");
    run_sig0(&[
        "interpretation-profile",
        "--input",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out",
        profile_validation
            .to_str()
            .expect("profile validation path is utf-8"),
    ]);

    let packet = out_dir.join("aat-analysis-packet.json");
    run_sig0(&[
        "aat-analysis",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out",
        packet.to_str().expect("packet path is utf-8"),
    ]);
    assert_north_star_packet_surfaces(&read_json(&packet));

    let workflow_dir = out_dir.join("workflow");
    run_sig0(&[
        "north-star-workflow",
        "--archmap",
        root.join("archmap.json")
            .to_str()
            .expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("profile path is utf-8"),
        "--out-dir",
        workflow_dir.to_str().expect("workflow dir is utf-8"),
    ]);
    assert!(workflow_dir.join("archsig-analysis-packet.json").is_file());
}

#[test]
fn cli_rejects_implicit_scan_default() {
    let output = run_sig0_output(&[]);
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("LLM-native ArchMap/LawPolicy/analysis-packet primary"),
        "implicit scan should be rejected with an LLM-native boundary\n{stderr}"
    );
}

#[test]
fn removed_legacy_commands_are_not_accepted() {
    for command in removed_commands() {
        let output = run_sig0_output(&[command, "--help"]);
        assert!(
            !output.status.success(),
            "removed command {command} should not be accepted"
        );
    }
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

    let expected = [
        "archmap-validation.json",
        "law-policy-validation.json",
        "archsig-analysis-packet.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ];
    for file in expected {
        assert!(
            out_dir.join(file).is_file(),
            "LLM-native workflow must write {file}"
        );
    }
    for removed_file in [
        "air.json",
        "air-validation.json",
        "theorem-precondition-check.json",
        "feature-report.json",
        "aat-observable-bundle.json",
        "aat-observable-bundle-validation.json",
    ] {
        assert!(
            !out_dir.join(removed_file).exists(),
            "LLM-native workflow must not emit legacy artifact {removed_file}"
        );
    }

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
    assert_north_star_packet_surfaces(&analysis_packet);
    let analysis_validation = read_json(&out_dir.join("archsig-analysis-validation.json"));
    assert_eq!(
        analysis_validation["summary"]["result"].as_str(),
        Some("pass")
    );
    assert_eq!(analysis_validation["summary"]["aatConceptSurfaceCount"], 12);
    assert_eq!(
        analysis_validation["summary"]["designPrincipleReadingCount"],
        9
    );
    assert!(
        analysis_validation["summary"]["boundedJudgementCount"]
            .as_u64()
            .is_some_and(|count| count >= 10),
        "validation summary must count bounded judgements"
    );
    let llm_packet = read_json(&out_dir.join("llm-interpretation-packet.json"));
    assert_eq!(llm_packet, analysis_packet);
}

#[test]
fn sharded_archmap_design_fixture_uses_horizontal_slices() {
    let root = sharded_root();
    let manifest = read_json(&root.join("manifest.json"));
    assert_eq!(manifest["schemaVersion"], "archmap-shard-manifest-v0");
    assert_eq!(
        manifest["shardingMode"],
        "horizontal-bounded-observation-slices"
    );

    let slices = manifest["slices"]
        .as_array()
        .expect("manifest slices are an array");
    assert!(
        slices.len() >= 2,
        "horizontal fixture should include multiple bounded slices"
    );
    for slice in slices {
        assert_eq!(slice["sliceKind"], "boundedObservationSlice");
        let path = slice["path"].as_str().expect("slice path is present");
        let slice_json = read_json(&root.join(path));
        assert_eq!(slice_json["schemaVersion"], "archmap-observation-slice-v0");
        assert_eq!(slice_json["sliceId"], slice["sliceId"]);
        assert_eq!(slice_json["surface"], slice["surface"]);
        assert!(
            slice_json.get("sourceUniverseFragment").is_some(),
            "slice {path} must carry its local source universe fragment"
        );
        assert!(
            slice_json.get("atomObservations").is_some(),
            "slice {path} must retain ArchMap observation arrays"
        );
    }

    assert_eq!(
        manifest["exportPolicy"]["targetSchemaVersion"],
        "archmap-observation-map-v0"
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
    assert_north_star_packet_surfaces(&packet_json);
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
        has_check_result(
            &concern_json,
            "archmap-concern-hints-are-not-obstruction-circuits",
            "fail"
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
        has_check_result(
            &gap_json,
            "archmap-observation-gaps-not-measured-zero",
            "fail"
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
fn cli_locks_archmap_atom_observation_regression() {
    let out_dir = temp_dir("archmap-atom-observation-regression");
    let root = fixture_root();
    let archmap = expressiveness_root().join("archmap_atom_observation_suite_v0.json");
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
        json["atomicObservationSummary"]["atomObservationCount"], 4,
        "Atom observation regression must lock source-grounded atom observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["moleculeObservationCount"], 1,
        "Atom observation regression must lock molecule observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["semanticObservationCount"], 1,
        "Atom observation regression must lock semantic observations"
    );
    assert_eq!(
        json["atomicObservationSummary"]["observationGapCount"], 1,
        "Atom observation regression must preserve observation gaps"
    );
    assert_eq!(
        json["atomicObservationSummary"]["concernHintCount"], 1,
        "Atom observation regression must keep concern hints as review cues"
    );
    assert!(
        json.get(&["legacy", "SchemaChecks"].concat()).is_none(),
        "ArchMap validation report must not retain legacy compatibility checks"
    );
    assert!(
        json.get(&["homo", "morphismDiagnostics"].concat())
            .is_none(),
        "ArchMap validation report must not retain pre-Atom projection diagnostics"
    );

    let full_packet = out_dir.join("archsig-analysis-full.json");
    let full_validation = out_dir.join("archsig-analysis-full-validation.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy.json")
            .to_str()
            .expect("law policy path is utf-8"),
        "--out",
        full_packet.to_str().expect("full packet path is utf-8"),
        "--validation-out",
        full_validation
            .to_str()
            .expect("full validation path is utf-8"),
    ]);
    let full = read_json(&full_packet);
    assert_north_star_packet_surfaces(&full);
    assert!(
        full["obstructionCircuits"]
            .as_array()
            .expect("full obstruction circuits are array")
            .iter()
            .any(|entry| entry["lawRef"] == "law:semantic-contract-alignment"),
        "semantic LawPolicy should construct law-relative obstruction from the same ArchMap"
    );

    let layer_packet = out_dir.join("archsig-analysis-layer-only.json");
    let layer_validation = out_dir.join("archsig-analysis-layer-only-validation.json");
    run_sig0(&[
        "archsig-analysis",
        "--archmap",
        archmap.to_str().expect("archmap path is utf-8"),
        "--law-policy",
        root.join("law_policy_layer_only.json")
            .to_str()
            .expect("layer-only law policy path is utf-8"),
        "--out",
        layer_packet.to_str().expect("layer packet path is utf-8"),
        "--validation-out",
        layer_validation
            .to_str()
            .expect("layer validation path is utf-8"),
    ]);
    let layer_only = read_json(&layer_packet);
    assert_eq!(
        layer_only["obstructionCircuits"]
            .as_array()
            .expect("layer-only obstruction circuits are array")
            .len(),
        0,
        "layer-only LawPolicy should reanalyze the same ArchMap without semantic obstruction"
    );
}

#[test]
fn cli_rejects_legacy_archmap_fields() {
    let out_dir = temp_dir("legacy-archmap-fields");
    let mut archmap = read_json(&fixture_root().join("archmap.json"));
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
fn legacy_archsig_surface_does_not_reenter_source_or_paths() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src_root = crate_root.join("src");
    let disallowed_source_symbols = [
        "pub struct Sig0Document",
        "AIR_SCHEMA_VERSION",
        "SIGNATURE_DIFF_REPORT_SCHEMA_VERSION",
        "FEATURE_EXTENSION_REPORT_SCHEMA_VERSION",
        "THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION",
        "RepairRuleRegistryV0",
        "SynthesisConstraint",
        "NoSolutionCertificate",
        "AatObservableBundle",
        "OrganizationPolicy",
        "ArchitecturePolicy",
        "PolicyDecision",
        "PrQuality",
        "SnapshotAttribution",
        "FrameworkAdapter",
    ];
    for file in collect_files(&src_root) {
        let text = fs::read_to_string(&file).expect("source file is utf-8");
        for symbol in disallowed_source_symbols {
            assert!(
                !text.contains(symbol),
                "legacy ArchSig symbol {symbol} re-entered {}",
                file.display()
            );
        }
    }

    for removed_path in [
        "skills/aat-reviewer",
        "skills/arch-pr-analyzer",
        "tests/fixtures/air",
        "tests/fixtures/module_root",
        "tests/fixtures/python_imports",
    ] {
        assert!(
            !crate_root.join(removed_path).exists(),
            "legacy ArchSig path {removed_path} re-entered"
        );
    }
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
    assert_eq!(
        ids,
        vec![
            "archmap",
            "archmap-validation-report",
            "law-policy",
            "law-policy-validation-report",
            "archsig-analysis-packet",
            "archsig-analysis-packet-validation-report",
        ]
    );
    for entry in artifacts {
        assert_eq!(entry["artifactRole"].as_str(), Some("primary"));
    }
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

fn has_check_result(json: &Value, id: &str, result: &str) -> bool {
    json.as_object().is_some_and(|object| {
        object.values().any(|value| {
            value.as_array().is_some_and(|checks| {
                checks
                    .iter()
                    .any(|check| check["id"] == id && check["result"] == result)
            })
        })
    })
}

fn assert_north_star_packet_surfaces(json: &Value) {
    for concept in [
        "Atom",
        "Configuration",
        "ArchitectureObject",
        "Invariant",
        "LawUniverse",
        "ObstructionCircuit",
        "ArchitectureSignature",
        "Operation",
        "Path",
        "Homotopy",
        "Diagram",
        "AnalyticRepresentation",
    ] {
        assert!(
            json["aatConceptSurfaces"]
                .as_array()
                .expect("aat concept surfaces are array")
                .iter()
                .any(|entry| entry["concept"] == concept),
            "North Star packet must expose AAT concept {concept}"
        );
    }
    for family in [
        "weightedAdjacencyMatrix",
        "walkCount",
        "reachableConeSize",
        "nilpotenceBoundary",
        "selectedSubgraphSpectrum",
        "propagationDepth",
        "spectralRadius",
        "curvatureValuation",
        "stateAlgebra",
        "zeroReflectingAggregateBoundary",
    ] {
        assert!(
            json["analyticRepresentations"]
                .as_array()
                .expect("analytic representations are array")
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose analytic representation {family}"
        );
    }
    for principle in [
        "InformationHiding",
        "Encapsulation",
        "SeparationOfConcerns",
        "Substitutability",
        "OpenClosedExtension",
        "DependencyInversion",
        "RepresentationIndependence",
        "IdempotencyAndReplaySafety",
        "AuthorityAndTrustBoundary",
    ] {
        assert!(
            json["designPrincipleReadings"]
                .as_array()
                .expect("design principle readings are array")
                .iter()
                .any(|entry| entry["principle"] == principle),
            "North Star packet must expose design principle {principle}"
        );
    }
    assert!(
        json["boundedJudgements"]
            .as_array()
            .expect("bounded judgements are array")
            .iter()
            .any(|entry| entry["status"] == "actionable"),
        "bounded judgements must include actionable readings"
    );
    let workflow_risks = json["workflowRiskReadings"]
        .as_array()
        .expect("workflow risk readings are array");
    assert!(
        !workflow_risks.is_empty(),
        "North Star packet must expose workflow risk readings"
    );
    assert!(
        workflow_risks.iter().all(|entry| {
            entry["moleculeObservationRef"].as_str().is_some()
                && entry["riskScore"].as_i64().is_some_and(|score| score >= 0)
                && entry["topAxes"]
                    .as_array()
                    .is_some_and(|axes| !axes.is_empty())
                && entry["reviewFocus"]
                    .as_array()
                    .is_some_and(|focus| !focus.is_empty())
                && entry["evidenceBoundary"].as_str().is_some()
        }),
        "workflow risk readings must carry molecule refs, non-negative scores, axes, review focus, and evidence boundaries"
    );
    let spectral_readings = json["spectralAnalysisReadings"]
        .as_array()
        .expect("spectral analysis readings are array");
    assert!(
        !spectral_readings.is_empty(),
        "North Star packet must expose spectral analysis readings"
    );
    for family in [
        "workflowRiskAxisPressureMatrix",
        "moleculeAtomOverlapCouplingMatrix",
        "obstructionAxisCurvatureMatrix",
        "operationSignatureDeltaMatrix",
    ] {
        assert!(
            spectral_readings
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose spectral representation {family}"
        );
    }
    assert!(
        spectral_readings.iter().all(|entry| {
            entry["matrixShape"]["rowDomain"].as_str().is_some()
                && entry["matrixShape"]["columnDomain"].as_str().is_some()
                && entry["entryRule"].as_str().is_some()
                && entry["values"]
                    .as_array()
                    .is_some_and(|values| !values.is_empty())
                && entry["coverageBoundary"].as_str().is_some()
                && entry["zeroReflectingBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral analysis readings must carry matrix shape, entry rule, values, and evidence boundaries"
    );
    let spectral_modes = json["spectralModeReadings"]
        .as_array()
        .expect("spectral mode readings are array");
    assert!(
        !spectral_modes.is_empty(),
        "North Star packet must expose spectral mode readings"
    );
    for family in [
        "workflowRiskAxisPressureMatrix",
        "moleculeAtomOverlapCouplingMatrix",
        "obstructionAxisCurvatureMatrix",
        "operationSignatureDeltaMatrix",
    ] {
        assert!(
            spectral_modes
                .iter()
                .any(|entry| entry["representationFamily"] == family),
            "North Star packet must expose spectral mode for representation {family}"
        );
    }
    assert!(
        spectral_modes.iter().all(|entry| {
            entry["sourceSpectralReadingRef"].as_str().is_some()
                && entry["modeKind"].as_str().is_some()
                && entry["spectralGapProxy"]["value"].as_str().is_some()
                && entry["localizationIndex"]["value"].as_str().is_some()
                && entry["matrixDensity"]["value"].as_str().is_some()
                && entry["decomposabilityReading"].as_str().is_some()
                && entry["repairPerturbationReading"].as_str().is_some()
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral mode readings must carry source refs, mode metrics, decomposability, repair perturbation, and evidence boundaries"
    );
    let spectral_drilldowns = json["spectralDrilldownReadings"]
        .as_array()
        .expect("spectral drilldown readings are array");
    assert!(
        !spectral_drilldowns.is_empty(),
        "North Star packet must expose spectral drilldown readings"
    );
    assert!(
        spectral_drilldowns.iter().all(|entry| {
            entry["sourceSpectralModeRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
                && entry["dominantAtomFamilyComposition"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["repairAxisDeltaReadings"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "spectral drilldown readings must carry source mode refs, atom-family composition, repair axis deltas, and evidence boundaries"
    );
    assert!(
        spectral_drilldowns.iter().all(|entry| {
            entry["dominantAtomFamilyComposition"]
                .as_array()
                .expect("dominant atom family composition is array")
                .iter()
                .all(|composition| {
                    composition["atomFamily"].as_str().is_some()
                        && composition["count"].as_u64().is_some_and(|count| count > 0)
                        && composition["atomObservationRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                })
        }),
        "dominant atom-family composition must carry atom family counts and refs"
    );
    let transfer_bridges = json["transferBridgeReadings"]
        .as_array()
        .expect("transfer bridge readings are array");
    assert!(
        !transfer_bridges.is_empty(),
        "North Star packet must expose transfer bridge readings"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["transferBridgeId"].as_str().is_some()
                && entry["status"].as_str().is_some()
                && entry["transferMatrixEntries"].as_array().is_some()
                && entry["bridgeAtomFamilies"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evolutionRiskRanking"]["repairTransferRiskRanking"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && entry["evolutionRiskRanking"]["boundaryPreparationRanking"]
                    .as_array()
                    .is_some()
                && entry["reading"].as_str().is_some()
                && entry["evidenceBoundary"].as_str().is_some()
                && entry["recommendedNextAction"].as_str().is_some()
        }),
        "transfer bridge readings must carry transfer matrix, bridge atom families, evolution risk ranking, and evidence boundaries"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["transferMatrixEntries"]
                .as_array()
                .expect("transfer matrix entries are array")
                .iter()
                .all(|matrix_entry| {
                    matrix_entry["operationDeltaRef"].as_str().is_some()
                        && matrix_entry["transferredAxisRef"].as_str().is_some()
                        && matrix_entry["transferWeight"]
                            .as_i64()
                            .is_some_and(|weight| weight > 0)
                        && matrix_entry["transferKind"].as_str().is_some()
                        && matrix_entry["reading"].as_str().is_some()
                })
        }),
        "transfer matrix entries must carry operation x transferred-axis readings when present"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["bridgeAtomFamilies"]
                .as_array()
                .expect("bridge atom families are array")
                .iter()
                .all(|bridge| {
                    bridge["sourceHubMoleculeRef"].as_str().is_some()
                        && bridge["targetHubMoleculeRef"].as_str().is_some()
                        && bridge["bridgeAtomFamilies"].as_array().is_some()
                        && bridge["pathPairRefs"].as_array().is_some()
                        && bridge["edgeBreakdowns"].as_array().is_some()
                        && bridge["reviewRisk"].as_str().is_some()
                        && bridge["recommendedBoundaryPreparation"].as_str().is_some()
                        && bridge["evidenceBoundary"].as_str().is_some()
                })
        }),
        "bridge atom family readings must carry hub refs, bridge families, path refs, review risk, and evidence boundaries"
    );
    assert!(
        transfer_bridges.iter().all(|entry| {
            entry["bridgeAtomFamilies"]
                .as_array()
                .expect("bridge atom families are array")
                .iter()
                .flat_map(|bridge| {
                    bridge["edgeBreakdowns"]
                        .as_array()
                        .expect("edge breakdowns are array")
                })
                .all(|edge| {
                    edge["sourceMoleculeRef"].as_str().is_some()
                        && edge["targetMoleculeRef"].as_str().is_some()
                        && edge["pairRef"].as_str().is_some()
                        && edge["overlapScore"].as_i64().is_some_and(|score| score > 0)
                        && edge["sharedAtomFamilies"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["familySupportingAtomRefs"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["sourceRefs"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["sourceRefRationale"].as_str().is_some()
                        && edge["dependencyKind"].as_str().is_some()
                        && edge["dependencyReading"].as_str().is_some()
                        && edge["reviewFocus"]
                            .as_array()
                            .is_some_and(|items| !items.is_empty())
                        && edge["recommendedCutKind"].as_str().is_some()
                        && edge["cutRationale"].as_str().is_some()
                        && edge["llmReviewSummary"].as_str().is_some()
                })
        }),
        "bridge edge breakdowns must carry molecule refs, source refs, review focus, dependency reading, and cut recommendation"
    );
    for surface in [
        "representationStrengthReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "operationInvariantGaloisReadings",
        "splitReadinessReadings",
    ] {
        assert!(
            json[surface]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
            "North Star packet must expose AAT structural surface {surface}"
        );
    }
    assert!(
        json["representationStrengthReadings"]
            .as_array()
            .expect("representation strength readings are array")
            .iter()
            .all(|reading| {
                reading["sourceReadingRef"].as_str().is_some()
                    && reading["representationFamily"].as_str().is_some()
                    && reading["zeroReflecting"].as_str().is_some()
                    && reading["obstructionReflecting"].as_str().is_some()
                    && reading["requiredAssumptions"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "representation strength readings must carry strength classes and assumptions"
    );
    assert!(
        json["threeLayerFlatnessReadings"]
            .as_array()
            .expect("three-layer flatness readings are array")
            .iter()
            .all(|reading| {
                reading["staticStatus"].as_str().is_some()
                    && reading["runtimeStatus"].as_str().is_some()
                    && reading["semanticStatus"].as_str().is_some()
                    && reading["nonImplicationReading"].as_str().is_some()
                    && reading["recommendedNextAction"].as_str().is_some()
            }),
        "three-layer flatness readings must carry static/runtime/semantic statuses"
    );
    assert!(
        json["observationProjectionReadings"]
            .as_array()
            .expect("observation projection readings are array")
            .iter()
            .all(|reading| {
                reading["observedAtomFamilies"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["coarseProjectionRisks"]
                        .as_array()
                        .is_some_and(|items| !items.is_empty())
                    && reading["evidenceBoundary"].as_str().is_some()
            }),
        "observation projection readings must carry observed families and projection risks"
    );
    assert!(
        json["stateTransitionAlgebraReadings"]
            .as_array()
            .expect("state transition algebra readings are array")
            .iter()
            .all(|reading| {
                reading["requiredRelations"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                    && reading["reading"].as_str().is_some()
                    && reading["recommendedNextAction"].as_str().is_some()
            }),
        "state transition algebra readings must carry required transition relations"
    );
    assert!(
        json["splitReadinessReadings"]
            .as_array()
            .expect("split readiness readings are array")
            .iter()
            .all(|reading| {
                reading["moleculeRef"].as_str().is_some()
                    && reading["status"].as_str().is_some()
                    && reading["readinessScore"].as_i64().is_some()
                    && reading["recommendedBoundaryOperation"].as_str().is_some()
            }),
        "split readiness readings must carry molecule refs, score, and boundary operation"
    );
    assert!(
        json["structuralReadingReviewSurface"]["connectedReadingRefs"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && json["structuralReadingReviewSurface"]["reviewFocus"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
            && json["structuralReadingReviewSurface"]["currentStateReading"]
                .as_str()
                .is_some_and(|reading| reading.contains("current architecture state")),
        "structural reading review surface must connect AAT readings as current architecture state"
    );
    assert!(
        json["currentStateEvolutionBoundary"]["handoffArtifactRef"] == "archsig-analysis-packet-v0"
            && json["currentStateEvolutionBoundary"]["archsigCurrentStateScope"]
                .as_str()
                .is_some_and(|scope| scope.contains("current AAT structural state"))
            && json["currentStateEvolutionBoundary"]["fieldsigEvolutionScope"]
                .as_str()
                .is_some_and(|scope| scope.contains("PR, diff, change-vector"))
            && json["currentStateEvolutionBoundary"]["forbiddenReadings"]
                .as_array()
                .is_some_and(|items| items.len() >= 3),
        "current-state/evolution boundary must separate ArchSig and FieldSig responsibilities"
    );
    assert!(
        json["llmInterpretationPacket"]["structuralReadingReviewSummary"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
            && json["llmInterpretationPacket"]["currentStateEvolutionBoundarySummary"]
                .as_array()
                .is_some_and(|items| !items.is_empty()),
        "LLM interpretation packet must summarize structural readings and current-state/evolution boundary"
    );
    assert!(
        json["llmInterpretationPacket"]["recommendedHumanReviewFocus"]
            .as_array()
            .is_some_and(|items| !items.is_empty()),
        "LLM interpretation packet must provide review focus"
    );
}

fn collect_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(path) = stack.pop() {
        for entry in fs::read_dir(&path).expect("directory can be read") {
            let entry = entry.expect("directory entry can be read");
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files
}
