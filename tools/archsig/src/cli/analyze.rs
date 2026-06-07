pub(crate) fn enforce_strict_distance_contract(
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) -> Result<(), Box<dyn Error>> {
    let mut violations = Vec::new();
    if law_policy_validation
        .policy
        .part4_distance_profile
        .is_none()
    {
        violations.push(
            "part4DistanceProfile is required for --strict-distance; legacy profile fallback is disabled"
                .to_string(),
        );
    }
    if law_policy_validation.summary.result != "pass" {
        violations.push(format!(
            "LawPolicy validation must pass for --strict-distance (result={}, failed={}, warnings={})",
            law_policy_validation.summary.result,
            law_policy_validation.summary.failed_check_count,
            law_policy_validation.summary.warning_check_count
        ));
    }
    if analysis_validation.summary.result != "pass" {
        violations.push(format!(
            "analysis packet validation must pass for --strict-distance (result={}, failed={}, warnings={}, proxyRegressionChecks={})",
            analysis_validation.summary.result,
            analysis_validation.summary.failed_check_count,
            analysis_validation.summary.warning_check_count,
            analysis_validation.summary.proxy_regression_check_count
        ));
    }
    if analysis_validation.summary.proxy_regression_check_count == 0 {
        violations
            .push("analysis packet validation did not run proxy-regression guardrails".to_string());
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "--strict-distance rejected incomplete Part IV distance measurement contract: {}",
            violations.join("; ")
        )
        .into())
    }
}

const COMPACT_REF_ARRAY_THRESHOLD: usize = 50;
const COMPACT_REF_SAMPLE_COUNT: usize = 5;

pub(crate) fn write_analysis_packet_artifacts(
    out: Option<PathBuf>,
    packet: &archsig::ArchSigAnalysisPacketV0,
    detail_out: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    let mut packet_value = serde_json::to_value(packet)?;
    let detail_path = match (&out, detail_out) {
        (_, Some(path)) => Some(path),
        (Some(path), None) => Some(default_detail_index_path(path)),
        (None, None) => None,
    };
    let detail_ref_base = detail_path
        .as_ref()
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "detail-index-not-written".to_string());
    let mut compact = CompactRefContext::new(detail_ref_base);
    let mut json_pointer = Vec::new();
    compact_ref_arrays(&mut packet_value, &mut json_pointer, &mut compact);
    attach_detail_index_ref(&mut packet_value, &compact);

    if let Some(path) = detail_path {
        write_json_minified(Some(path), &compact.detail_index_value())?;
    }
    write_json_minified(out, &packet_value)?;
    Ok(())
}

pub(crate) fn build_analyze_run_manifest(
    archmap: &Path,
    law_policy: &Path,
    emit_raw_artifacts: bool,
    archmap_validation: &ArchMapValidationReportV0,
    law_policy_validation: &LawPolicyValidationReportV0,
    analysis_validation: &ArchSigAnalysisPacketValidationReportV0,
) -> ArchSigRunManifestV0 {
    let mut generated_artifacts = vec![
        "archmap-validation.json",
        "law-policy-validation.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ];
    let mut omitted_artifacts = Vec::new();
    if emit_raw_artifacts {
        generated_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    } else {
        omitted_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    }

    ArchSigRunManifestV0 {
        schema_version: ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION.to_string(),
        command_name: "analyze".to_string(),
        archmap_input_path: archmap.display().to_string(),
        law_policy_input_path: law_policy.display().to_string(),
        output_mode: if emit_raw_artifacts {
            "summary-viewer-manifest-with-raw-artifacts"
        } else {
            "summary-viewer-manifest"
        }
        .to_string(),
        raw_artifact_retention: if emit_raw_artifacts { "full" } else { "omitted" }.to_string(),
        generated_artifacts: generated_artifacts.into_iter().map(str::to_string).collect(),
        omitted_artifacts: omitted_artifacts.into_iter().map(str::to_string).collect(),
        summary_path: "archsig-analysis-summary.json".to_string(),
        atom_viewer_data_path: "archsig-atom-viewer-data.json".to_string(),
        validation_reports: ArchSigRunManifestValidationReportPathsV0 {
            archmap: "archmap-validation.json".to_string(),
            law_policy: "law-policy-validation.json".to_string(),
            analysis: "archsig-analysis-validation.json".to_string(),
        },
        raw_artifact_paths: emit_raw_artifacts.then(|| ArchSigRunManifestRawArtifactPathsV0 {
            analysis_packet: "archsig-analysis-packet.json".to_string(),
            analysis_detail_index: "archsig-analysis-detail-index.json".to_string(),
            llm_interpretation_packet: "llm-interpretation-packet.json".to_string(),
        }),
        validation_result_summary: ArchSigRunManifestValidationResultSummaryV0 {
            archmap: ArchSigArtifactValidationResultV0 {
                result: archmap_validation.summary.result.clone(),
                failed_check_count: archmap_validation.summary.failed_check_count,
                warning_check_count: archmap_validation.summary.warning_check_count,
            },
            law_policy: ArchSigArtifactValidationResultV0 {
                result: law_policy_validation.summary.result.clone(),
                failed_check_count: law_policy_validation.summary.failed_check_count,
                warning_check_count: law_policy_validation.summary.warning_check_count,
            },
            analysis: ArchSigArtifactValidationResultV0 {
                result: analysis_validation.summary.result.clone(),
                failed_check_count: analysis_validation.summary.failed_check_count,
                warning_check_count: analysis_validation.summary.warning_check_count,
            },
        },
        non_conclusions: vec![
            "run manifest records generated and omitted artifacts for this ArchSig analyze run"
                .to_string(),
            "omitted raw artifacts can be regenerated by rerunning analyze with --emit-raw-artifacts"
                .to_string(),
            "manifest paths are artifact navigation aids, not source completeness proof".to_string(),
        ],
    }
}

pub(crate) fn build_analyze_run_manifest_v1(
    archmap: &Path,
    law_policy: &Path,
    emit_raw_artifacts: bool,
    archmap_validation_result: &str,
    law_policy_validation_result: &str,
    analysis_validation_result: &str,
) -> serde_json::Value {
    let mut generated_artifacts = vec![
        "archmap-validation.json",
        "law-policy-validation.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "archsig-analysis-validation.json",
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
    ];
    let mut omitted_artifacts = Vec::new();
    if emit_raw_artifacts {
        generated_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    } else {
        omitted_artifacts.extend([
            "archsig-analysis-packet.json",
            "archsig-analysis-detail-index.json",
            "llm-interpretation-packet.json",
        ]);
    }

    serde_json::json!({
        "schemaVersion": "archsig-run-manifest-v1",
        "commandName": "analyze",
        "archmapInputPath": archmap.display().to_string(),
        "lawPolicyInputPath": law_policy.display().to_string(),
        "outputMode": if emit_raw_artifacts {
            "v1-summary-viewer-manifest-with-raw-artifacts"
        } else {
            "v1-summary-viewer-manifest"
        },
        "rawArtifactRetention": if emit_raw_artifacts { "full" } else { "omitted" },
        "generatedArtifacts": generated_artifacts,
        "omittedArtifacts": omitted_artifacts,
        "summaryPath": "archsig-analysis-summary.json",
        "atomViewerDataPath": "archsig-atom-viewer-data.json",
        "typedEvaluatorResultsPath": "typed-evaluator-results.json",
        "validationReports": {
            "archmap": "archmap-validation.json",
            "lawPolicy": "law-policy-validation.json",
            "analysis": "archsig-analysis-validation.json"
        },
        "rawArtifactPaths": if emit_raw_artifacts {
            serde_json::json!({
                "analysisPacket": "archsig-analysis-packet.json",
                "analysisDetailIndex": "archsig-analysis-detail-index.json",
                "llmInterpretationPacket": "llm-interpretation-packet.json"
            })
        } else {
            serde_json::Value::Null
        },
        "validationResultSummary": {
            "archmap": { "result": archmap_validation_result },
            "lawPolicy": { "result": law_policy_validation_result },
            "analysis": { "result": analysis_validation_result }
        },
        "nonConclusions": [
            "v1 run manifest records generated and omitted typed evaluator artifacts for this ArchSig analyze run",
            "manifest paths are artifact navigation aids, not source completeness proof",
            "ArchSig v1 run manifest does not claim Lean theorem discharge"
        ]
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_archmap_sidecar_path(archmap_path: &Path, sidecar_path: &str) -> Option<PathBuf> {
    let raw_path = PathBuf::from(sidecar_path);
    if raw_path.is_absolute() {
        return raw_path.exists().then_some(raw_path);
    }

    if let Ok(current_dir) = std::env::current_dir() {
        let candidate = current_dir.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let archmap_parent = archmap_path.parent()?;
    let local_candidate = archmap_parent.join(&raw_path);
    if local_candidate.exists() {
        return Some(local_candidate);
    }
    for ancestor in archmap_parent.ancestors() {
        let candidate = ancestor.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }
    None
}
