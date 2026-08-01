fn temp_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("archsig-{test_name}-{nanos}"));
    fs::create_dir_all(&dir).expect("temporary directory can be created");
    dir
}

fn write_gate_packet(path: &Path, verdict: &str) {
    fs::write(
        path,
        serde_json::to_vec_pretty(&json!({
            "schema": "archsig-measurement-packet/v0.5.4",
            "packetId": "measurement:gate-test",
            "profile": {
                "schema": "measurement-profile/v0.5.4",
                "profileId": "profile:gate-test@1",
                "siteRef": "site:gate-test",
                "coverRef": "cover:gate-test",
                "coefficient": "constant:Z",
                "effCoeff": "constant",
                "resolutionSelector": "gate-test",
                "domain": "gate-test",
                "zeroPredicate": "gate-test-zero",
                "nonZeroPredicate": "gate-test-nonzero",
                "certSelector": "gate-test-cert",
                "verdictDiscipline": "five-valued",
                "finiteBounds": {
                    "maxSquareFreeWitnessVariables": 12,
                    "maxCoherenceContexts": 12,
                    "maxTorWitnessVariables": 12,
                    "maxBoundaryResidueVariables": 16,
                    "maxLaplacianCells": 16,
                    "maxPeriodCycles": 16,
                    "maxTransferTargets": 16
                }
            },
            "structuralVerdict": [{
                "verdictRef": "structuralVerdict/ag-cech-obstruction/ag-cech-h1/computed",
                "evaluator": "ag.cech-obstruction",
                "law": "ag.cech-h1",
                "target": {
                    "kind": "cover-relative-cech-h1-class",
                    "coverRef": "cover:gate-test",
                    "coefficient": "constant:Z",
                    "scopeSize": {
                        "contexts": 1,
                        "edges": 1,
                        "triangles": 0
                    },
                    "classRef": "computedInvariants/gate-test:computed"
                },
                "verdict": verdict,
                "verdictData": {
                    "inScope": true,
                    "zero": verdict == "measured_zero",
                    "nonZero": verdict == "measured_nonzero",
                    "methodStatus": "computed",
                    "certRef": "computedInvariants/gate-test:computed"
                },
                "dependsOnAssumptions": [],
                "evidence": {
                    "computedInvariantRefs": ["gate-test:computed"],
                    "sourceRefs": []
                }
            }],
            "computedInvariants": [{
                "invariantId": "gate-test:computed",
                "kind": "cech-h1-rank",
                "evaluator": "ag.cech-obstruction",
                "value": 0,
                "representation": {
                    "coefficient": "constant:Z"
                }
            }],
            "analyticReadings": [],
            "assumptions": [],
            "suppliedData": [{
                "suppliedId": "supplied:archmap",
                "kind": "archmap",
                "sourceArtifactRef": "input:archmap.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "archmap/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:law-policy",
                "kind": "law-policy",
                "sourceArtifactRef": "input:law-policy.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "law-policy/v0.5.4-validation"
                }
            }, {
                "suppliedId": "supplied:measurement-profile",
                "kind": "measurement-profile",
                "sourceArtifactRef": "input:measurement-profile.json",
                "conformance": {
                    "status": "validated",
                    "checkRef": "measurement-profile/v0.5.4-validation"
                }
            }],
            "boundaryStatements": [{
                "id": "boundary:gate-test",
                "kind": "silence_by_design",
                "scopeRefs": [
                    "measurement:gate-test"
                ],
                "reason": "gate_test_fixture",
                "text": "gate test packet is a minimal measurement packet fixture"
            }],
            "nonConclusions": [
                "gate test packet is a minimal measurement packet fixture"
            ]
        }))
        .expect("packet serializes"),
    )
    .expect("packet fixture can be written");
}

fn json_contains_exact_string(value: &Value, needle: &str) -> bool {
    match value {
        Value::String(text) => text == needle,
        Value::Array(items) => items
            .iter()
            .any(|item| json_contains_exact_string(item, needle)),
        Value::Object(object) => object
            .values()
            .any(|item| json_contains_exact_string(item, needle)),
        _ => false,
    }
}

fn has_absolute_sheaf_cohomology_notation(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    while index + 1 < bytes.len() {
        if bytes[index] == b'H' && bytes[index + 1] == b'^' {
            let mut degree_end = index + 2;
            if degree_end < bytes.len() && bytes[degree_end] == b'n' {
                degree_end += 1;
            } else if degree_end < bytes.len() && bytes[degree_end].is_ascii_digit() {
                while degree_end < bytes.len() && bytes[degree_end].is_ascii_digit() {
                    degree_end += 1;
                }
            } else {
                index += 1;
                continue;
            }
            if bytes.get(degree_end) == Some(&b'(') {
                return true;
            }
        }
        index += 1;
    }
    false
}

fn json_contains_substring(value: &Value, needle: &str) -> bool {
    match value {
        Value::String(text) => text.contains(needle),
        Value::Array(items) => items
            .iter()
            .any(|item| json_contains_substring(item, needle)),
        Value::Object(object) => object
            .values()
            .any(|item| json_contains_substring(item, needle)),
        _ => false,
    }
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

fn run_sig0_expect_code(args: &[&str], expected_code: i32) {
    let output = run_sig0_output(args);
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "archsig {:?} exit code mismatch\nstdout:\n{}\nstderr:\n{}",
        args,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_sig0_output(args: &[&str]) -> std::process::Output {
    run_sig0_raw_output(args)
}
fn run_sig0_raw_output(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_archsig"))
        .args(args)
        .output()
        .expect("archsig command runs")
}

fn help_command_names(help: &str) -> BTreeSet<&str> {
    help.lines()
        .filter_map(|line| {
            let trimmed = line.trim_start();
            line.starts_with("  ")
                .then(|| trimmed.split_whitespace().next())
                .flatten()
        })
        .collect()
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
        "archmap",
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
        "scope-manifest",
        "extraction-diff",
        "supply-bench",
    ]
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("json fixture can be read"))
        .expect("json fixture parses")
}

fn refresh_run_measurement_packet_digest(run: &Path) {
    let packet_path = run.join("archsig-measurement-packet.json");
    let packet = read_json(&packet_path);
    let digest = format!(
        "{:x}",
        Sha256::digest(serde_json::to_vec(&packet).expect("measurement packet canonicalizes")),
    );
    let manifest_path = run.join("archsig-run-manifest.json");
    let mut manifest = read_json(&manifest_path);
    manifest["artifactDigests"]["measurementPacket"] = json!({
        "path": "archsig-measurement-packet.json",
        "sha256": digest,
    });
    fs::write(
        manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("manifest serializes"),
    )
    .expect("manifest writes");
}

fn sidecar_measurement_profile_path(policy_path: &Path) -> PathBuf {
    if policy_path.file_name().and_then(|name| name.to_str()) == Some("law_policy.json") {
        policy_path.with_file_name("measurement_profile.json")
    } else if let Some(file_name) = policy_path.file_name().and_then(|name| name.to_str()) {
        if let Some(suffix) = file_name.strip_prefix("law_policy_") {
            policy_path.with_file_name(format!("measurement_profile_{suffix}"))
        } else {
            policy_path.with_file_name("measurement_profile.json")
        }
    } else {
        policy_path.with_file_name("measurement_profile.json")
    }
}

fn read_fixture_policy_profile(policy_path: &Path) -> (Value, Value) {
    (
        read_json(policy_path),
        read_json(&sidecar_measurement_profile_path(policy_path)),
    )
}

fn test_measurement_profile_path(policy_path: &Path) -> PathBuf {
    let profile_path = sidecar_measurement_profile_path(policy_path);
    assert!(
        profile_path.exists(),
        "test must create measurement profile sidecar before invoking analyze"
    );
    profile_path
}

fn write_test_policy_and_profile(policy_path: &Path, mut policy: Value, profile: Value) {
    policy["schema"] = json!("law-policy/v0.5.4");
    if policy.get("lawSurfaceRef").is_none() {
        policy["lawSurfaceRef"] = json!("law-surface:ag-measurement-v052");
    }
    if policy.get("basisLedger").is_none() {
        policy["basisLedger"] = json!([{
            "basisId": "policy-basis:layering",
            "kind": "repo-document",
            "path": "docs/tool/ag_measurement_input_contract.md",
            "revision": "ag-measurement-current"
        }]);
    }
    let mut surface_laws = Vec::new();
    let witness_family = profile
        .get("witnessFamily")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    if let Some(entries) = policy["policies"].as_array_mut() {
        for (entry_index, entry) in entries.iter_mut().enumerate() {
            let evaluator = entry["evaluator"].as_str().unwrap_or_default().to_string();
            if evaluator == "ag.cech-obstruction" {
                continue;
            }
            let use_generated_law = !witness_family.is_empty()
                && evaluator != "ag.cech-obstruction"
                && evaluator != "ag.section-factorization";
            let law_id = if !use_generated_law {
                entry["law"].as_str().unwrap_or(&evaluator).to_string()
            } else {
                format!("law:generated:{entry_index}")
            };
            if use_generated_law {
                entry["law"] = json!(law_id);
            }
            let variables = witness_family
                .iter()
                .filter(|witness| witness["law"].as_str() == Some(evaluator.as_str()))
                .filter_map(|witness| witness["variable"].as_str().map(str::to_string))
                .collect::<Vec<_>>();
            if variables.is_empty() {
                let condition_type = match evaluator.as_str() {
                    "ag.saga-descent"
                    | "ag.cech-obstruction"
                    | "ag.coherence-obstruction"
                    | "ag.restriction-compatibility"
                    | "ag.boundary-residue" => "descent",
                    "ag.period-stokes" | "ag.period-stokes-audit" => "temporal",
                    _ => "constructible",
                };
                surface_laws.push(json!({
                    "lawId": law_id,
                    "conditionType": condition_type,
                    "evaluatorRef": evaluator
                }));
            } else {
                let axis = match evaluator.as_str() {
                    "ag.cech-obstruction" => "cech",
                    "ag.section-factorization" => "section-factorization",
                    "ag.sheaf-laplacian" => "laplacian",
                    "ag.period-stokes" | "ag.period-stokes-audit" => "period",
                    "ag.support-transfer" => "transfer",
                    _ => "square-free",
                };
                let predicate = match axis {
                    "laplacian" => "cellularCochain",
                    "period" => "periodIntegral",
                    "transfer" => "transferPairing",
                    "cech" => "sectionValue",
                    _ => "support",
                };
                surface_laws.push(json!({
                    "lawId": law_id,
                    "conditionType": "closed-equational",
                    "witnessVariables": variables.iter().map(|variable| json!({
                        "variable": variable,
                        "binding": {"axis": axis, "predicate": predicate}
                    })).collect::<Vec<_>>(),
                    "forbiddenSupportGenerators": [json!({"support": variables})]
                }));
            }
        }
    }
    if !surface_laws.is_empty() {
        let surface_path = policy_path.with_file_name("law_surface.json");
        fs::write(
            &surface_path,
            serde_json::to_vec_pretty(&json!({
                "schema": "law-equation-surface/v0.5.4",
                "id": "law-surface:ag-measurement-v052",
                "laws": surface_laws
            }))
            .expect("generated law surface serializes"),
        )
        .expect("generated law surface writes");
    }
    fs::write(
        policy_path,
        serde_json::to_vec_pretty(&policy).expect("policy serializes"),
    )
    .expect("test law policy can be written");
    let mut profile = profile;
    profile["schema"] = json!("measurement-profile/v0.5.4");
    profile
        .as_object_mut()
        .map(|object| object.remove("witnessFamily"));
    if profile.get("finiteBounds").is_none() {
        profile["finiteBounds"] = json!({
            "maxSquareFreeWitnessVariables": 12,
            "maxCoherenceContexts": 12,
            "maxTorWitnessVariables": 12,
            "maxBoundaryResidueVariables": 16,
            "maxLaplacianCells": 16,
            "maxPeriodCycles": 16,
            "maxTransferTargets": 16
        });
    }
    fs::write(
        sidecar_measurement_profile_path(policy_path),
        serde_json::to_vec_pretty(&profile).expect("profile serializes"),
    )
    .expect("test measurement profile can be written");
}

fn check_by_id<'a>(report: &'a Value, check_id: &str) -> &'a Value {
    report["checks"]
        .as_array()
        .expect("checks is array")
        .iter()
        .find(|check| check["id"] == check_id)
        .unwrap_or_else(|| panic!("missing validation check {check_id}"))
}

fn saga_row<'a>(packet: &'a Value, law: &str) -> &'a Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structural verdict array")
        .iter()
        .find(|row| row["evaluator"] == "ag.saga-descent" && row["law"] == law)
        .unwrap_or_else(|| panic!("missing saga row {law}"))
}

fn assert_saga_summary_has_no_class_vocabulary(summary: &Value) {
    assert!(
        !json_contains_substring(summary, "class"),
        "SAGA summary must not introduce layer C class vocabulary"
    );
}

fn run_analyze_fixture_lock(
    case_id: &str,
    archmap: &str,
    law_policy: &str,
    law_surface: &str,
) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let law_policy_path = root.join(law_policy);
    let measurement_profile_path = if matches!(
        law_policy,
        "law_policy_cech_h1.json" | "law_policy_cech_b8.json"
    ) {
        root.join("measurement_profile_ag.json")
    } else {
        test_measurement_profile_path(&law_policy_path)
    };
    let mut args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join(archmap)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        law_policy_path.to_str().expect("path is utf-8").to_string(),
        "--measurement-profile".to_string(),
        measurement_profile_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join(law_surface)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
    ];
    args.push("--out-dir".to_string());
    args.push(out_dir.to_str().expect("path is utf-8").to_string());
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

fn run_analyze_fixture_lock_with_surface(
    case_id: &str,
    archmap: &str,
    law_policy: &str,
    law_surface: &str,
) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    let source_law_policy_path = root.join(law_policy);
    let measurement_profile_path = if matches!(
        law_policy,
        "law_policy_cech_h1.json" | "law_policy_cech_b8.json"
    ) {
        root.join("measurement_profile_ag.json")
    } else {
        test_measurement_profile_path(&source_law_policy_path)
    };
    let law_surface_path = root.join(law_surface);
    let policy = read_json(&source_law_policy_path);
    let surface = read_json(&law_surface_path);
    assert_eq!(
        policy["lawSurfaceRef"], surface["id"],
        "R9 fixture policy must explicitly resolve to its supplied law surface"
    );
    let law_policy_path = source_law_policy_path;
    let mut args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join(archmap)
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        law_policy_path.to_str().expect("path is utf-8").to_string(),
        "--measurement-profile".to_string(),
        measurement_profile_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        law_surface_path
            .to_str()
            .expect("path is utf-8")
            .to_string(),
    ];
    args.push("--out-dir".to_string());
    args.push(out_dir.to_str().expect("path is utf-8").to_string());
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

fn run_square_free_analysis(case_id: &str, archmap_path: &Path) -> PathBuf {
    let root = ag_measurement_root();
    let out_dir = temp_dir(case_id);
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        root.join("law_policy_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--measurement-profile",
        root.join("measurement_profile_square_free.json")
            .to_str()
            .expect("path is utf-8"),
        "--law-surface",
        root.join("law_surface_ag_v052.json")
            .to_str()
            .expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    out_dir
}

fn run_square_free_gate(run_dir: &Path, expected_exit_code: i32) -> Value {
    let root = ag_measurement_root();
    let packet_path = run_dir.join("archsig-measurement-packet.json");
    let policy_path = root.join("gate_policy_conservative.json");
    let report_path = run_dir.join("archsig-gate-report.json");
    let args = [
        "gate",
        "--packet",
        packet_path.to_str().expect("packet path is utf-8"),
        "--policy",
        policy_path.to_str().expect("policy path is utf-8"),
        "--out",
        report_path.to_str().expect("report path is utf-8"),
    ];
    run_sig0_expect_code(&args, expected_exit_code);
    read_json(&report_path)
}

fn assert_byte_identical_analysis_artifacts(first_out: &Path, second_out: &Path) {
    for artifact in [
        "normalized-archmap.json",
        "archsig-measurement-packet.json",
        "archsig-analysis-summary.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
        "archsig-atom-viewer-data.json",
        "archsig-measurement-view-model.json",
        "archsig-run-manifest.json",
    ] {
        if !first_out.join(artifact).exists() && !second_out.join(artifact).exists() {
            continue;
        }
        assert_eq!(
            fs::read(first_out.join(artifact)).expect("first artifact is readable"),
            fs::read(second_out.join(artifact)).expect("second artifact is readable"),
            "{artifact} must be byte-identical across repeated SAGA fixture runs"
        );
    }
}

fn invariant_by_id<'a>(packet: &'a Value, invariant_id: &str) -> &'a Value {
    packet["computedInvariants"]
        .as_array()
        .expect("computedInvariants is array")
        .iter()
        .find(|invariant| invariant["invariantId"] == invariant_id)
        .unwrap_or_else(|| panic!("missing computed invariant {invariant_id}"))
}

fn coherence_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.coherence-obstruction")
        .expect("coherence row exists")
}

fn restriction_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.restriction-compatibility")
        .expect("restriction compatibility row exists")
}

fn section_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.section-factorization")
        .expect("section factorization row exists")
}

fn boundary_residue_row(packet: &Value) -> &Value {
    packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array")
        .iter()
        .find(|row| row["evaluator"] == "ag.boundary-residue")
        .expect("boundary residue row exists")
}

fn run_generated_ag_measurement_case(
    root_out: &Path,
    case: &str,
    archmap: Value,
    policy: Value,
    profile: Value,
) -> Value {
    let out_dir = root_out.join(case);
    fs::create_dir_all(&out_dir).expect("case dir exists");
    let archmap_path = out_dir.join("archmap.json");
    let policy_path = out_dir.join("law_policy.json");
    let profile_path = sidecar_measurement_profile_path(&policy_path);
    fs::write(
        &archmap_path,
        serde_json::to_vec_pretty(&archmap).expect("archmap serializes"),
    )
    .expect("case archmap is written");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let law_surface_path = policy_path.with_file_name("law_surface.json");
    run_sig0(&[
        "analyze",
        "--archmap",
        archmap_path.to_str().expect("path is utf-8"),
        "--law-policy",
        policy_path.to_str().expect("path is utf-8"),
        "--measurement-profile",
        profile_path.to_str().expect("path is utf-8"),
        "--law-surface",
        law_surface_path.to_str().expect("path is utf-8"),
        "--out-dir",
        out_dir.to_str().expect("path is utf-8"),
    ]);
    read_json(&out_dir.join("archsig-measurement-packet.json"))
}

fn assert_common_structural_verdict_discipline(packet: &Value, evaluator: &str) {
    let allowed_verdicts = BTreeSet::from([
        "measured_zero",
        "measured_nonzero",
        "unmeasured",
        "unknown",
        "not_computed",
    ]);
    let structural = packet["structuralVerdict"]
        .as_array()
        .expect("structuralVerdict is array");
    assert_eq!(
        structural
            .iter()
            .filter(|row| row["evaluator"] == evaluator)
            .count(),
        1,
        "{evaluator} must emit exactly one structural verdict row"
    );

    let violated = packet["assumptions"]
        .as_array()
        .expect("assumptions is array")
        .iter()
        .filter(|row| row["status"] == "violated")
        .filter_map(|row| row["theoremRef"].as_str())
        .collect::<BTreeSet<_>>();

    for row in structural {
        let verdict = row["verdict"].as_str().expect("verdict is string");
        assert!(
            allowed_verdicts.contains(verdict),
            "structural verdict must stay in the five-value vocabulary"
        );
        if verdict == "measured_zero" {
            assert_eq!(row["verdictData"]["inScope"], true);
            assert_eq!(row["verdictData"]["zero"], true);
            assert_eq!(row["verdictData"]["nonZero"], false);
            assert!(
                row["verdictData"]["certRef"]
                    .as_str()
                    .is_some_and(|cert_ref| !cert_ref.is_empty()),
                "measured_zero must carry a certificate reference in PRD M common fixtures"
            );
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") {
            let depends_on = row["dependsOnAssumptions"]
                .as_array()
                .map(|dependencies| {
                    dependencies
                        .iter()
                        .filter_map(|dependency| dependency.as_str())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            assert!(
                depends_on
                    .iter()
                    .all(|dependency| !violated.contains(dependency)),
                "measured structural verdicts must not depend on violated assumptions"
            );
        }
    }
}

fn restriction_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-restriction-policy",
        "measurementProfileRef": "profile:ag-restriction@1",
        "policies": [{
            "law": "ag.restriction-compatibility",
            "evaluator": "ag.restriction-compatibility",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn restriction_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-restriction@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:restriction",
        "coefficient": "F2",
        "effCoeff": "finite-support-inclusion@1",
        "witnessFamily": [
            {"law": "ag.restriction-compatibility", "variable": "x"},
            {"law": "ag.restriction-compatibility", "variable": "y"}
        ],
        "resolutionSelector": "support-inclusion@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "all-inclusions-hold@1",
        "nonZeroPredicate": "some-inclusion-fails@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn boundary_residue_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-boundary-residue-policy",
        "measurementProfileRef": "profile:ag-boundary-residue@1",
        "policies": [{
            "law": "ag.boundary-residue",
            "evaluator": "ag.boundary-residue",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn boundary_residue_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-boundary-residue@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:boundary-residue",
        "coefficient": "F2",
        "effCoeff": "finite-mayer-vietoris-d0@1",
        "witnessFamily": [
            {"law": "ag.boundary-residue", "variable": "b0"},
            {"law": "ag.boundary-residue", "variable": "b1"}
        ],
        "resolutionSelector": "mayer-vietoris-d0@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "boundary-residue-zero@1",
        "nonZeroPredicate": "boundary-residue-nonzero@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn section_policy() -> Value {
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-section-policy",
        "measurementProfileRef": "profile:ag-section@1",
        "policies": [{
            "law": "ag.section-factorization",
            "evaluator": "ag.section-factorization",
            "basis": ["policy-basis:layering"],
            "scope": ["src/"],
            "severity": "high"
        }]
    })
}

fn section_profile() -> Value {
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-section@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:section",
        "coefficient": "F2",
        "effCoeff": "finite-section-evaluation@1",
        "witnessFamily": [
            {"law": "ag.section-factorization", "variable": "x"},
            {"law": "ag.section-factorization", "variable": "y"}
        ],
        "resolutionSelector": "section-factorization@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "pullback-zero@1",
        "nonZeroPredicate": "pullback-nonzero@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn restriction_archmap(case: &str) -> Value {
    let source_generator = match case {
        "compatible" => Some(("atom:gen-source-xy", "x,y", "src:source-generator")),
        "violated" | "missing-target" => Some(("atom:gen-source-x", "x", "src:source-generator")),
        "empty-edges" => Some(("atom:gen-source-x", "x", "src:source-generator")),
        _ => panic!("unknown restriction fixture case: {case}"),
    };
    let target_generator = match case {
        "compatible" => Some(("atom:gen-target-x", "x", "src:target-generator")),
        "violated" => Some(("atom:gen-target-xy", "x,y", "src:target-generator")),
        "empty-edges" => Some(("atom:gen-target-x", "x", "src:target-generator")),
        "missing-target" => None,
        _ => panic!("unknown restriction fixture case: {case}"),
    };
    let mut atoms = vec![
        atom_json(
            "atom:source",
            "component",
            "src:source",
            "static",
            "component",
            None,
            vec!["src:source"],
        ),
        atom_json(
            "atom:target",
            "component",
            "src:target",
            "static",
            "component",
            None,
            vec!["src:target"],
        ),
    ];
    if let Some((atom_id, support, source_ref)) = source_generator {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "ctx:source",
            "restriction-compatibility",
            "restrictionIdealGenerator",
            Some(support),
            vec!["ctx:source", source_ref],
        ));
    }
    if let Some((atom_id, support, source_ref)) = target_generator {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "ctx:target",
            "restriction-compatibility",
            "restrictionIdealGenerator",
            Some(support),
            vec!["ctx:target", source_ref],
        ));
    }
    let mut source_atoms = vec!["atom:source"];
    if let Some((atom_id, _, _)) = source_generator {
        source_atoms.push(atom_id);
    }
    let mut target_atoms = vec!["atom:target"];
    if let Some((atom_id, _, _)) = target_generator {
        target_atoms.push(atom_id);
    }
    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-restriction-fixture-{case}"),
        "extractionDoctrineRef": canonical_extraction_doctrine_ref(),
        "sources": {
            "src:source": {"kind": "rust", "path": "src/source.rs", "symbol": "Source", "line": 1},
            "src:target": {"kind": "rust", "path": "src/target.rs", "symbol": "Target", "line": 1},
            "src:source-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M2 source generator"},
            "src:target-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M2 target generator"},
            "ctx:source": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M2"},
            "ctx:target": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M2"}
        },
        "atoms": atoms,
        "contexts": [
            {
                "id": "ctx:source",
                "atoms": source_atoms,
                "restrictsTo": if case == "empty-edges" { json!([]) } else { json!(["ctx:target"]) },
                "refs": ["ctx:source"]
            },
            {
                "id": "ctx:target",
                "atoms": target_atoms,
                "refs": ["ctx:target"]
            }
        ],
        "covers": [{
            "id": "cover:restriction",
            "contexts": ["ctx:source", "ctx:target"],
            "refs": ["ctx:source", "ctx:target"]
        }]
    })
}

fn boundary_residue_archmap(case: &str) -> Value {
    let include_roles = case != "missing-classification";
    let include_mismatch = case != "missing-mismatch";
    let include_columns = case != "missing-matrix";
    let mismatch_support = match case {
        "zero"
        | "missing-classification"
        | "missing-mismatch"
        | "missing-matrix"
        | "duplicate-role"
        | "invalid-boundary-column"
        | "invalid-core-mismatch" => "b0",
        "sum-zero" => "b0,b1",
        "nonzero" => "b1",
        "unknown-variable" => "b2",
        _ => panic!("unknown boundary residue fixture case: {case}"),
    };
    let mut atoms = vec![
        atom_json(
            "atom:core-component",
            "component",
            "ctx:core",
            "static",
            "component",
            None,
            vec!["ctx:core", "src:core"],
        ),
        atom_json(
            "atom:feature-component",
            "component",
            "ctx:feature",
            "static",
            "component",
            None,
            vec!["ctx:feature", "src:feature"],
        ),
        atom_json(
            "atom:boundary-component",
            "component",
            "ctx:boundary",
            "static",
            "component",
            None,
            vec!["ctx:boundary", "src:boundary"],
        ),
    ];
    if include_roles {
        atoms.extend([
            atom_json(
                "atom:role-core",
                "semantic",
                "ctx:core",
                "boundary-residue",
                "patchRole",
                Some("core"),
                vec!["ctx:core", "src:role"],
            ),
            atom_json(
                "atom:role-feature",
                "semantic",
                "ctx:feature",
                "boundary-residue",
                "patchRole",
                Some("feature"),
                vec!["ctx:feature", "src:role"],
            ),
            atom_json(
                "atom:role-boundary",
                "semantic",
                "ctx:boundary",
                "boundary-residue",
                "patchRole",
                Some("boundary"),
                vec!["ctx:boundary", "src:role"],
            ),
        ]);
        if case == "duplicate-role" {
            atoms.push(atom_json(
                "atom:role-core-duplicate",
                "semantic",
                "ctx:core",
                "boundary-residue",
                "patchRole",
                Some("feature"),
                vec!["ctx:core", "src:role"],
            ));
        }
    }
    if include_columns {
        atoms.push(atom_json(
            "atom:d0-core-b0",
            "relation",
            if case == "invalid-boundary-column" {
                "ctx:boundary"
            } else {
                "ctx:core"
            },
            "boundary-residue",
            "restrictionColumn",
            Some("b0"),
            if case == "invalid-boundary-column" {
                vec!["ctx:boundary", "src:d0-core"]
            } else {
                vec!["ctx:core", "ctx:boundary", "src:d0-core"]
            },
        ));
        if case == "sum-zero" {
            atoms.push(atom_json(
                "atom:d0-feature-b1",
                "relation",
                "ctx:feature",
                "boundary-residue",
                "restrictionColumn",
                Some("b1"),
                vec!["ctx:feature", "ctx:boundary", "src:d0-feature"],
            ));
        }
    }
    if include_mismatch {
        atoms.push(atom_json(
            "atom:boundary-section",
            "relation",
            "boundary:section",
            "boundary-residue",
            "boundarySection",
            Some(mismatch_support),
            if case == "invalid-core-mismatch" {
                vec!["ctx:core", "src:boundary-section"]
            } else {
                vec!["ctx:boundary", "src:boundary-section"]
            },
        ));
    }

    let core_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:core")
                .then_some(id)
        })
        .collect::<Vec<_>>();
    let feature_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:feature")
                .then_some(id)
        })
        .collect::<Vec<_>>();
    let boundary_atoms = atoms
        .iter()
        .filter_map(|atom| {
            let id = atom["id"].as_str().unwrap();
            atom["refs"]
                .as_array()
                .unwrap()
                .iter()
                .any(|source_ref| source_ref == "ctx:boundary")
                .then_some(id)
        })
        .collect::<Vec<_>>();

    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-boundary-residue-fixture-{case}"),
        "extractionDoctrineRef": canonical_extraction_doctrine_ref(),
        "sources": {
            "src:core": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 core patch"},
            "src:feature": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 feature patch"},
            "src:boundary": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 boundary patch"},
            "src:role": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 patch role"},
            "src:d0-core": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 Mayer-Vietoris d0"},
            "src:d0-feature": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 Mayer-Vietoris d0"},
            "src:boundary-section": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6 boundary section"},
            "ctx:core": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6"},
            "ctx:feature": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6"},
            "ctx:boundary": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M6"}
        },
        "atoms": atoms,
        "contexts": [
            {
                "id": "ctx:core",
                "atoms": core_atoms,
                "restrictsTo": ["ctx:boundary"],
                "refs": ["ctx:core"]
            },
            {
                "id": "ctx:feature",
                "atoms": feature_atoms,
                "restrictsTo": ["ctx:boundary"],
                "refs": ["ctx:feature"]
            },
            {
                "id": "ctx:boundary",
                "atoms": boundary_atoms,
                "refs": ["ctx:boundary"]
            }
        ],
        "covers": [{
            "id": "cover:boundary-residue",
            "contexts": ["ctx:core", "ctx:feature", "ctx:boundary"],
            "refs": ["ctx:core", "ctx:feature", "ctx:boundary"]
        }]
    })
}

fn section_archmap(case: &str) -> Value {
    let assignment = match case {
        "lawful" => Some((
            "atom:section-assignment-a",
            "x=1,y=0",
            "src:section-assignment-a",
        )),
        "unlawful" => Some((
            "atom:section-assignment-b",
            "x=1,y=1",
            "src:section-assignment-b",
        )),
        "partial" => Some(("atom:section-partial", "x=1", "src:section-partial")),
        "missing-generator" => Some((
            "atom:section-assignment-no-generator",
            "x=0,y=0",
            "src:section-assignment-no-generator",
        )),
        "absent" => None,
        _ => panic!("unknown section fixture case: {case}"),
    };
    let include_generator = case != "missing-generator";
    let mut atoms = vec![atom_json(
        "atom:section-carrier",
        "component",
        "section:selected",
        "section-factorization",
        "selectedSection",
        None,
        vec!["src:section-carrier"],
    )];
    if include_generator {
        atoms.push(atom_json(
            "atom:forbid-xy",
            "relation",
            "I_Ob^U",
            "section-factorization",
            "support",
            Some("x,y"),
            vec!["src:forbidden-support", "ctx:section"],
        ));
    }
    if let Some((atom_id, object, source_ref)) = assignment {
        atoms.push(atom_json(
            atom_id,
            "relation",
            "section:selected",
            "section-factorization",
            "witnessAssignment",
            Some(object),
            vec![source_ref, "ctx:section"],
        ));
    }
    let mut context_atoms = vec!["atom:section-carrier"];
    if include_generator {
        context_atoms.push("atom:forbid-xy");
    }
    if let Some((atom_id, _, _)) = assignment {
        context_atoms.push(atom_id);
    }
    json!({
        "schema": "archmap/v0.5.4",
        "id": format!("ag-section-fixture-{case}"),
        "extractionDoctrineRef": canonical_extraction_doctrine_ref(),
        "sources": {
            "src:section-carrier": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 section"},
            "src:forbidden-support": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 minimal forbidden support"},
            "src:section-assignment-a": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 total section assignment A"},
            "src:section-assignment-b": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 total section assignment B"},
            "src:section-partial": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 partial section"},
            "src:section-assignment-no-generator": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3 assignment without raw support"},
            "ctx:section": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M3"}
        },
        "atoms": atoms,
        "contexts": [{
            "id": "ctx:section",
            "atoms": context_atoms,
            "refs": ["ctx:section"]
        }],
        "covers": [{
            "id": "cover:section",
            "contexts": ["ctx:section"],
            "refs": ["ctx:section"]
        }]
    })
}

fn coherence_policy(_coefficient: &str, include_cech: bool) -> Value {
    let mut policies = vec![json!({
        "law": "ag.coherence-obstruction",
        "evaluator": "ag.coherence-obstruction",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    })];
    if include_cech {
        policies.insert(
            0,
            json!({
                "law": "surface:cech-surface-v052",
                "evaluator": "ag.cech-obstruction",
                "basis": ["policy-basis:layering"],
                "scope": ["src/"],
                "severity": "high"
            }),
        );
    }
    json!({
        "schema": "law-policy/v0.5.4",
        "id": "ag-coherence-policy",
        "measurementProfileRef": "profile:ag-coherence@1",
        "policies": policies
    })
}

fn coherence_profile(coefficient: &str, include_cech: bool) -> Value {
    let mut witness_family = vec![json!({
        "law": "ag.coherence-obstruction",
        "variable": "h2"
    })];
    if include_cech {
        witness_family.push(json!({
            "law": "ag.cech-obstruction",
            "variable": "x_coherence"
        }));
    }
    json!({
        "schema": "measurement-profile/v0.5.4",
        "profileId": "profile:ag-coherence@1",
        "siteRef": "archmap:/contexts",
        "coverRef": "cover:coherence",
        "coefficient": coefficient,
        "effCoeff": "finite-linear-algebra@1",
        "witnessFamily": witness_family,
        "resolutionSelector": "h2-coherence@1",
        "domain": "finite-poset-site",
        "zeroPredicate": "rank-zero@1",
        "nonZeroPredicate": "rank-positive@1",
        "certSelector": "finite-certificate@1",
        "verdictDiscipline": "five-valued-structural-verdict@1"
    })
}

fn coherence_triangle_archmap(include_witness: bool) -> Value {
    let mut atoms = vec![
        atom_json(
            "atom:a",
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ),
        atom_json(
            "atom:b",
            "component",
            "src:b",
            "static",
            "component",
            None,
            vec!["src:b"],
        ),
        atom_json(
            "atom:c",
            "component",
            "src:c",
            "static",
            "component",
            None,
            vec!["src:c"],
        ),
        atom_json(
            "atom:abc",
            "component",
            "src:abc",
            "static",
            "tripleOverlapWitness",
            None,
            vec!["src:abc"],
        ),
    ];
    if include_witness {
        atoms.push(atom_json(
            "atom:h2-abc",
            "relation",
            "ctx:a",
            "coherence",
            "tripleSection",
            Some("ctx:a,ctx:b,ctx:c"),
            vec!["ctx:a", "ctx:b", "ctx:c"],
        ));
    }
    let c_atoms = if include_witness {
        vec!["atom:c", "atom:abc", "atom:h2-abc"]
    } else {
        vec!["atom:c", "atom:abc"]
    };
    archmap_with_contexts(
        atoms,
        vec![
            context_json("ctx:a", vec!["atom:a", "atom:abc"], vec!["ctx:b", "ctx:c"]),
            context_json("ctx:b", vec!["atom:b", "atom:abc"], vec!["ctx:c"]),
            context_json("ctx:c", c_atoms, vec![]),
        ],
    )
}

fn coherence_boundary_archmap(include_witnesses: bool) -> Value {
    let face_specs = [
        ("abc", vec!["ctx:a", "ctx:b", "ctx:c"]),
        ("abd", vec!["ctx:a", "ctx:b", "ctx:d"]),
        ("acd", vec!["ctx:a", "ctx:c", "ctx:d"]),
        ("bcd", vec!["ctx:b", "ctx:c", "ctx:d"]),
    ];
    let mut atoms = vec![
        atom_json(
            "atom:a",
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ),
        atom_json(
            "atom:b",
            "component",
            "src:b",
            "static",
            "component",
            None,
            vec!["src:b"],
        ),
        atom_json(
            "atom:c",
            "component",
            "src:c",
            "static",
            "component",
            None,
            vec!["src:c"],
        ),
        atom_json(
            "atom:d",
            "component",
            "src:d",
            "static",
            "component",
            None,
            vec!["src:d"],
        ),
    ];
    for (name, contexts) in face_specs.iter() {
        atoms.push(atom_json(
            &format!("atom:face-{name}"),
            "component",
            &format!("src:face-{name}"),
            "static",
            "tripleOverlapWitness",
            None,
            vec![&format!("src:face-{name}")],
        ));
        if include_witnesses && *name == "abc" {
            atoms.push(atom_json(
                &format!("atom:h2-{name}"),
                "relation",
                contexts[0],
                "coherence",
                "tripleSection",
                Some(&contexts.join(",")),
                contexts.clone(),
            ));
        }
    }
    let contexts = if include_witnesses {
        vec![
            context_json(
                "ctx:a",
                vec![
                    "atom:a",
                    "atom:face-abc",
                    "atom:face-abd",
                    "atom:face-acd",
                    "atom:h2-abc",
                ],
                vec!["ctx:b", "ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:b",
                vec![
                    "atom:b",
                    "atom:face-abc",
                    "atom:face-abd",
                    "atom:face-bcd",
                    "atom:h2-abc",
                ],
                vec!["ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:c",
                vec![
                    "atom:c",
                    "atom:face-abc",
                    "atom:face-acd",
                    "atom:face-bcd",
                    "atom:h2-abc",
                ],
                vec!["ctx:d"],
            ),
            context_json(
                "ctx:d",
                vec!["atom:d", "atom:face-abd", "atom:face-acd", "atom:face-bcd"],
                vec![],
            ),
        ]
    } else {
        vec![
            context_json(
                "ctx:a",
                vec!["atom:a", "atom:face-abc", "atom:face-abd", "atom:face-acd"],
                vec!["ctx:b", "ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:b",
                vec!["atom:b", "atom:face-abc", "atom:face-abd", "atom:face-bcd"],
                vec!["ctx:c", "ctx:d"],
            ),
            context_json(
                "ctx:c",
                vec!["atom:c", "atom:face-abc", "atom:face-acd", "atom:face-bcd"],
                vec!["ctx:d"],
            ),
            context_json(
                "ctx:d",
                vec!["atom:d", "atom:face-abd", "atom:face-acd", "atom:face-bcd"],
                vec![],
            ),
        ]
    };
    archmap_with_contexts(atoms, contexts)
}

fn coherence_boundary_zero_cochain_archmap() -> Value {
    let mut archmap = coherence_boundary_archmap(true);
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .push(atom_json(
            "atom:h2-abc-duplicate",
            "relation",
            "ctx:a",
            "coherence",
            "tripleSection",
            Some("ctx:a,ctx:b,ctx:c"),
            vec!["ctx:a", "ctx:b", "ctx:c"],
        ));
    for context_id in ["ctx:a", "ctx:b", "ctx:c"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:h2-abc-duplicate".to_string()));
    }
    archmap
}

fn coherence_empty_archmap() -> Value {
    archmap_with_contexts(
        vec![
            atom_json(
                "atom:a",
                "component",
                "src:a",
                "static",
                "component",
                None,
                vec!["src:a"],
            ),
            atom_json(
                "atom:b",
                "component",
                "src:b",
                "static",
                "component",
                None,
                vec!["src:b"],
            ),
        ],
        vec![
            context_json("ctx:a", vec!["atom:a"], vec!["ctx:b"]),
            context_json("ctx:b", vec!["atom:b"], vec![]),
        ],
    )
}

fn coherence_incomplete_triangle_archmap() -> Value {
    archmap_with_contexts(
        vec![
            atom_json(
                "atom:a",
                "component",
                "src:a",
                "static",
                "component",
                None,
                vec!["src:a"],
            ),
            atom_json(
                "atom:b",
                "component",
                "src:b",
                "static",
                "component",
                None,
                vec!["src:b"],
            ),
            atom_json(
                "atom:c",
                "component",
                "src:c",
                "static",
                "component",
                None,
                vec!["src:c"],
            ),
            atom_json(
                "atom:abc",
                "component",
                "src:abc",
                "static",
                "tripleOverlapWitness",
                None,
                vec!["src:abc"],
            ),
            atom_json(
                "atom:h2-abc",
                "relation",
                "ctx:a",
                "coherence",
                "tripleSection",
                Some("ctx:a,ctx:b,ctx:c"),
                vec!["ctx:a", "ctx:b", "ctx:c"],
            ),
        ],
        vec![
            context_json(
                "ctx:a",
                vec!["atom:a", "atom:abc", "atom:h2-abc"],
                vec!["ctx:b"],
            ),
            context_json("ctx:b", vec!["atom:b", "atom:abc", "atom:h2-abc"], vec![]),
            context_json("ctx:c", vec!["atom:c", "atom:abc", "atom:h2-abc"], vec![]),
        ],
    )
}

fn coherence_oversized_archmap() -> Value {
    let mut atoms = Vec::new();
    let mut contexts = Vec::new();
    for index in 0..13 {
        let context_id = format!("ctx:n{index}");
        let atom_id = format!("atom:n{index}");
        atoms.push(atom_json(
            &atom_id,
            "component",
            "src:a",
            "static",
            "component",
            None,
            vec!["src:a"],
        ));
        contexts.push(json!({
            "id": context_id,
            "atoms": [atom_id],
            "refs": ["src:a"]
        }));
    }
    let mut archmap = archmap_with_contexts(atoms, contexts);
    for index in 0..13 {
        archmap["sources"][format!("ctx:n{index}")] = json!({
            "kind": "policy",
            "path": "docs/tool/ag_measurement_input_contract.md",
            "section": "M5"
        });
    }
    archmap
}

fn coherence_filled_tetrahedron_archmap() -> Value {
    let mut archmap = coherence_boundary_archmap(false);
    archmap["atoms"]
        .as_array_mut()
        .expect("atoms is array")
        .extend([
            atom_json(
                "atom:abcd",
                "component",
                "src:abcd",
                "static",
                "quadrupleOverlapWitness",
                None,
                vec!["src:abc"],
            ),
            atom_json(
                "atom:h2-abc",
                "relation",
                "ctx:a",
                "coherence",
                "tripleSection",
                Some("ctx:a,ctx:b,ctx:c"),
                vec!["ctx:a", "ctx:b", "ctx:c"],
            ),
        ]);
    for context_id in ["ctx:a", "ctx:b", "ctx:c", "ctx:d"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:abcd".to_string()));
    }
    for context_id in ["ctx:a", "ctx:b", "ctx:c"] {
        let context = archmap["contexts"]
            .as_array_mut()
            .expect("contexts is array")
            .iter_mut()
            .find(|context| context["id"] == context_id)
            .unwrap_or_else(|| panic!("context {context_id} exists"));
        context["atoms"]
            .as_array_mut()
            .expect("context atoms is array")
            .push(Value::String("atom:h2-abc".to_string()));
    }
    archmap
}

fn archmap_with_contexts(atoms: Vec<Value>, contexts: Vec<Value>) -> Value {
    let cover_contexts = contexts
        .iter()
        .filter_map(|context| context["id"].as_str())
        .collect::<Vec<_>>();
    json!({
        "schema": "archmap/v0.5.4",
        "id": "ag-coherence-fixture",
        "extractionDoctrineRef": canonical_extraction_doctrine_ref(),
        "sources": {
            "src:a": {"kind": "rust", "path": "src/a.rs", "symbol": "A", "line": 1},
            "src:b": {"kind": "rust", "path": "src/b.rs", "symbol": "B", "line": 1},
            "src:c": {"kind": "rust", "path": "src/c.rs", "symbol": "C", "line": 1},
            "src:d": {"kind": "rust", "path": "src/d.rs", "symbol": "D", "line": 1},
            "src:abc": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "src:face-abc": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "src:face-abd": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "src:face-acd": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "src:face-bcd": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "ctx:a": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "ctx:b": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "ctx:c": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"},
            "ctx:d": {"kind": "policy", "path": "docs/tool/ag_measurement_input_contract.md", "section": "M5"}
        },
        "atoms": atoms,
        "contexts": contexts,
        "covers": [{
            "id": "cover:coherence",
            "contexts": cover_contexts.clone(),
            "refs": cover_contexts
        }]
    })
}

fn canonical_extraction_doctrine_ref() -> Value {
    json!({
        "doctrineId": "doctrine:aat-canonical@1",
        "fingerprint": "sha256:aat-canonical-doctrine-schema052",
        "components": ["V", "Gamma", "R", "rho", "E", "N"]
    })
}

fn atom_json(
    id: &str,
    kind: &str,
    subject: &str,
    axis: &str,
    predicate: &str,
    object: Option<&str>,
    refs: Vec<&str>,
) -> Value {
    let mut atom = json!({
        "id": id,
        "kind": kind,
        "subject": subject,
        "axis": axis,
        "predicate": predicate,
        "refs": refs
    });
    if let Some(object) = object {
        atom["object"] = Value::String(object.to_string());
    }
    atom
}

fn context_json(id: &str, atoms: Vec<&str>, restricts_to: Vec<&str>) -> Value {
    let mut context = json!({
        "id": id,
        "atoms": atoms,
        "refs": [id]
    });
    if !restricts_to.is_empty() {
        context["restrictsTo"] = json!(restricts_to);
    }
    context
}

#[test]
fn cli_analyze_practical_grounded_emits_defect_quotient_invariant() {
    let out_dir = run_practical_saga_head_analyze("grounded-defect-quotient");
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));
    let invariant = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants are an array")
        .iter()
        .find(|invariant| invariant["invariantId"] == "saga-grounded:defect-quotient")
        .expect("grounded defect quotient invariant exists");
    assert_eq!(invariant["evaluator"], "ag.saga-grounded");
    let laws_hold = &invariant["displayedRequiredLawsHold"];
    assert_eq!(laws_hold["checkKind"], "holds-criterion-raw-value");
    assert!(
        laws_hold["perChart"]
            .as_array()
            .is_some_and(|rows| !rows.is_empty()),
        "per-chart holds readings are computed from observation and law surface"
    );
    assert!(
        invariant["generatedQuotient"]["obstructionIdeal"]["source"]
            .as_str()
            .is_some_and(|source| source.contains("forbiddenSupportGenerators")),
        "the generated quotient must name its law-surface provenance"
    );
    assert!(
        packet["assumptions"]
            .as_array()
            .is_some_and(|rows| rows.iter().any(|row| row["theoremRef"] == "archsig-contract:law-surface-quotient-sheaf-condition")),
        "the law-side quotient sheaf condition must be disclosed as an assumption"
    );
}

fn run_practical_saga_head_analyze(test_name: &str) -> PathBuf {
    let out_dir = temp_dir(test_name);
    let root = practical_rust_service_root();
    let args = vec![
        "analyze".to_string(),
        "--archmap".to_string(),
        root.join("archmap/archmap_head.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-policy".to_string(),
        root.join("law_policy/law_policy.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--measurement-profile".to_string(),
        root.join("law_policy/measurement_profile_drift.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--law-surface".to_string(),
        root.join("law_policy/law_surface.json")
            .to_str()
            .expect("path is utf-8")
            .to_string(),
        "--out-dir".to_string(),
        out_dir.to_str().expect("path is utf-8").to_string(),
    ];
    let arg_refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    run_sig0(&arg_refs);
    out_dir
}

#[test]
fn cli_analyze_emits_measurement_view_model_typed_sections() {
    let out_dir = run_practical_saga_head_analyze("view-model-typed-sections");
    let view_model = read_json(&out_dir.join("archsig-measurement-view-model.json"));
    let packet = read_json(&out_dir.join("archsig-measurement-packet.json"));

    assert_eq!(
        view_model["schema"],
        "archsig-measurement-view-model/v0.5.4"
    );
    assert!(view_model["runId"].is_string());
    assert!(view_model["inputDigests"]["measurementPacket"]["sha256"].is_string());

    // complex mirrors the packet cover nerve projection (no viewer-side faces).
    let cech = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants")
        .iter()
        .find(|inv| {
            inv["invariantId"]
                .as_str()
                .is_some_and(|id| id.starts_with("cech-cohomology:"))
        })
        .expect("cech invariant");
    let projection = &cech["representation"]["coverNerveProjection"];
    let complex = &view_model["complex"];
    assert_eq!(
        complex["vertices"].as_array().map(Vec::len),
        projection["vertices"].as_array().map(Vec::len)
    );
    assert_eq!(
        complex["edges"].as_array().map(Vec::len),
        projection["edges"].as_array().map(Vec::len)
    );
    assert_eq!(
        complex["triples"].as_array().map(Vec::len),
        projection["faces"].as_array().map(Vec::len)
    );

    // edge witness rows are three-state and cover every complex edge.
    let mismatch_rows = view_model["edgeMismatch"].as_array().expect("edge rows");
    assert_eq!(
        mismatch_rows.len(),
        complex["edges"].as_array().expect("edges").len()
    );
    for row in mismatch_rows {
        let status = row["status"].as_str().expect("status");
        assert!(
            [
                "mismatch_observed",
                "agreement_observed",
                "witness_not_supplied"
            ]
            .contains(&status),
            "unexpected edge witness status {status}"
        );
    }

    // class support is undirected and carries no orientation channel.
    let class_support = &view_model["classSupport"];
    assert_eq!(class_support["undirected"], true);
    assert_eq!(
        class_support["classNonzero"],
        Value::Null,
        "the practical head's unmeasured Cech class must remain typed silence in the view model"
    );
    assert!(class_support["representativeEdgeRefs"].is_array());
    for forbidden in ["direction", "rotation", "orientation", "magnitude"] {
        assert!(
            class_support.get(forbidden).is_none(),
            "class support must not carry {forbidden}"
        );
    }

    // coverage rows exist for every complex vertex and only reference them.
    let vertex_refs = complex["vertices"]
        .as_array()
        .expect("vertices")
        .iter()
        .map(|vertex| vertex["contextRef"].as_str().expect("contextRef"))
        .collect::<std::collections::BTreeSet<_>>();
    let coverage = view_model["observationCoverage"]
        .as_array()
        .expect("coverage rows");
    assert!(!coverage.is_empty());
    let mut covered_contexts = std::collections::BTreeSet::new();
    for row in coverage {
        let context_ref = row["contextRef"].as_str().expect("contextRef");
        assert!(
            vertex_refs.contains(context_ref),
            "coverage row references unknown context {context_ref}"
        );
        assert!(row["measurementAxis"].is_string());
        assert!(row["status"].is_string());
        covered_contexts.insert(context_ref);
    }
    assert_eq!(covered_contexts.len(), vertex_refs.len());

    // per-chart grounding rows project the saga-grounded premise.
    let local = &view_model["localObservations"];
    assert_eq!(local["evaluator"], "ag.saga-grounded");
    assert_eq!(local["verdict"], "measured_zero");
    assert_eq!(
        local["perChart"].as_array().map(Vec::len),
        Some(vertex_refs.len())
    );

    // boundary statements are projected verbatim.
    assert_eq!(
        view_model["boundaryStatements"],
        packet["boundaryStatements"]
    );

    // harmonic edge values are not recorded in current packets: absent, not zero.
    assert!(view_model["harmonicFlow"].is_null());

    // measured scalars carry packet provenance.
    for field in view_model["scalarFields"]
        .as_array()
        .expect("scalar fields")
    {
        assert!(field["sourceInvariantId"].is_string());
        assert_eq!(field["scope"], "cover");
    }
}

#[test]
fn cli_view_model_field_names_exclude_display_vocabulary() {
    let out_dir = run_practical_saga_head_analyze("view-model-vocabulary-lint");
    let view_model = read_json(&out_dir.join("archsig-measurement-view-model.json"));
    fn collect_keys(value: &serde_json::Value, keys: &mut Vec<String>) {
        match value {
            serde_json::Value::Object(map) => {
                for (key, child) in map {
                    keys.push(key.to_ascii_lowercase());
                    collect_keys(child, keys);
                }
            }
            serde_json::Value::Array(items) => {
                for child in items {
                    collect_keys(child, keys);
                }
            }
            _ => {}
        }
    }
    let mut keys = Vec::new();
    collect_keys(&view_model, &mut keys);
    for forbidden in [
        "weather", "front", "vortex", "cyclone", "fog", "storm", "wind", "cloud",
    ] {
        assert!(
            !keys.iter().any(|key| key.contains(forbidden)),
            "display vocabulary {forbidden} leaked into view model field names"
        );
    }
}

fn saga_derivation_fault_packet(
    case_id: &str,
    mutate_archmap: impl FnOnce(&mut Value),
    mutate_profile_coefficient: Option<&str>,
) -> Value {
    let out_dir = temp_dir(case_id);
    let root = ag_measurement_root();
    let (mut policy, mut profile) = read_fixture_policy_profile(&root.join("law_policy_ag.json"));
    policy["policies"] = json!([{
        "law": "ag.saga-descent",
        "evaluator": "ag.saga-descent",
        "basis": ["policy-basis:layering"],
        "scope": ["src/"],
        "severity": "high"
    }]);
    if let Some(coefficient) = mutate_profile_coefficient {
        profile["coefficient"] = json!(coefficient);
    }
    let policy_path = out_dir.join("law_policy_saga_descent.json");
    write_test_policy_and_profile(&policy_path, policy, profile);
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    ensure_restrictions(&mut archmap, &[("ctx:order", "ctx:inventory")]);
    mutate_archmap(&mut archmap);
    let archmap_path = write_archmap_variant(&out_dir, archmap, "archmap_saga.json");
    let output = run_sig0_output(&[
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
    assert!(
        output.status.success(),
        "saga fixture analyze failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    read_json(&out_dir.join("archsig-measurement-packet.json"))
}

fn assert_derivation_fault(packet: &Value, fault_fragment: &str) {
    let derivation = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants")
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:residual-derivation")
        .expect("residual derivation invariant exists");
    assert_eq!(derivation["residualDerivation"]["derived"], false);
    let fault = derivation["residualDerivation"]["fault"]
        .as_str()
        .expect("derivation fault is named");
    assert!(
        fault.contains(fault_fragment),
        "fault `{fault}` must contain `{fault_fragment}`"
    );
    let membership = saga_row(packet, "saga.residual-boundary-membership");
    assert_eq!(membership["verdict"], "not_computed");
    assert_eq!(
        membership["verdictData"]["methodStatus"],
        "residual_derivation_fault"
    );
    let statements = packet["boundaryStatements"]
        .as_array()
        .expect("boundary statements");
    assert!(
        statements.iter().any(|statement| {
            statement["reason"] == "residual_derivation_fault"
                && statement["text"]
                    .as_str()
                    .is_some_and(|text| text.contains(fault_fragment))
        }),
        "boundary statements must surface the derivation fault"
    );
}

#[test]
fn cli_analyze_saga_descent_faults_on_unobserved_section() {
    let packet = saga_derivation_fault_packet(
        "ag-saga-derivation-fault-unobserved-section",
        |archmap| {
            archmap["atoms"]
                .as_array_mut()
                .expect("atoms")
                .retain(|atom| atom["id"] != "atom:order-cech-section-value");
            archmap["contexts"]
                .as_array_mut()
                .expect("contexts")
                .iter_mut()
                .for_each(|context| {
                    if let Some(atoms) = context["atoms"].as_array_mut() {
                        atoms.retain(|atom| atom != "atom:order-cech-section-value");
                    }
                });
        },
        None,
    );
    assert_derivation_fault(&packet, "unobserved cech section");
}

#[test]
fn cli_analyze_saga_descent_measures_observed_mismatch_edge_without_law_witness_union() {
    let packet = saga_derivation_fault_packet(
        "ag-saga-derivation-fault-unbound-mismatch",
        |archmap| {
            archmap["atoms"]
                .as_array_mut()
                .expect("atoms")
                .iter_mut()
                .for_each(|atom| {
                    if atom["id"] == "atom:order-cech-section-value" {
                        atom["object"] = json!("section=order-divergent-contract");
                    }
                });
        },
        None,
    );
    let membership = saga_row(&packet, "saga.residual-boundary-membership");
    assert_eq!(membership["verdict"], "measured_zero");
    let derivation = packet["computedInvariants"]
        .as_array()
        .expect("computed invariants")
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:residual-derivation")
        .expect("residual derivation invariant");
    assert_eq!(derivation["residualDerivation"]["derived"], true);
    assert!(
        derivation["residualDerivation"]["edges"]
            .as_array()
            .is_some_and(|edges| edges.iter().any(|edge| edge["value"] == 1))
    );
}

#[test]
fn cli_analyze_saga_descent_faults_on_non_f2_profile_coefficient() {
    let packet = saga_derivation_fault_packet(
        "ag-saga-derivation-fault-non-f2-coefficient",
        |_| {},
        Some("Z5"),
    );
    assert_derivation_fault(&packet, "outside the F2 saga-descent vocabulary");
}

#[test]
fn cli_analyze_saga_descent_reads_explicit_cocycle_atoms_like_cech() {
    let out_dir = temp_dir("ag-saga-derivation-explicit-cocycle");
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
    add_cech_witness_variables(
        &policy_path,
        &[
            ("e_order_inventory", "ctx:order", "ctx:inventory"),
            ("e_inventory_shared", "ctx:inventory", "ctx:shared"),
            ("e_order_shared", "ctx:order", "ctx:shared"),
        ],
    );
    let mut archmap = read_json(&root.join("archmap_v2.json"));
    ensure_restrictions(&mut archmap, &[("ctx:order", "ctx:inventory")]);
    for (id, subject) in [
        ("atom:cocycle-order-inventory", "ctx:order->ctx:inventory"),
        ("atom:cocycle-inventory-shared", "ctx:inventory->ctx:shared"),
        ("atom:cocycle-order-shared", "ctx:order->ctx:shared"),
    ] {
        archmap["atoms"].as_array_mut().expect("atoms").push(json!({
            "id": id,
            "kind": "semantic",
            "subject": subject,
            "object": "1",
            "axis": "cech",
            "predicate": "cocycleValue",
            "refs": ["src:cover"]
        }));
    }
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
    assert_eq!(
        membership["verdict"], "measured_nonzero",
        "explicit cocycleValue atoms must drive the derived residual exactly like the cech evaluator"
    );
    let derivation = packet["computedInvariants"]
        .as_array()
        .expect("invariants")
        .iter()
        .find(|row| row["invariantId"] == "saga-descent:residual-derivation")
        .expect("derivation invariant");
    let edges = derivation["residualDerivation"]["edges"]
        .as_array()
        .expect("edges");
    assert!(
        edges.iter().all(|edge| edge["value"] == 1
            && edge["supportAtomRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())),
        "explicit cocycle edges must carry value 1 with cocycle atom provenance"
    );
}
