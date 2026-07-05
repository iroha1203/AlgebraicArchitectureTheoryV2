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
        "architecture-distance.json",
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
        "schema": "archsig-run-manifest/v0.5.0",
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
        "architectureDistancePath": "architecture-distance.json",
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
