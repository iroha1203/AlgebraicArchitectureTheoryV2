use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestV0 {
    pub schema_version: String,
    pub command_name: String,
    pub archmap_input_path: String,
    pub law_policy_input_path: String,
    pub output_mode: String,
    pub raw_artifact_retention: String,
    pub generated_artifacts: Vec<String>,
    pub omitted_artifacts: Vec<String>,
    pub summary_path: String,
    pub atom_viewer_data_path: String,
    pub validation_reports: ArchSigRunManifestValidationReportPathsV0,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw_artifact_paths: Option<ArchSigRunManifestRawArtifactPathsV0>,
    pub validation_result_summary: ArchSigRunManifestValidationResultSummaryV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestValidationReportPathsV0 {
    pub archmap: String,
    pub law_policy: String,
    pub analysis: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestRawArtifactPathsV0 {
    pub analysis_packet: String,
    pub analysis_detail_index: String,
    pub llm_interpretation_packet: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestValidationResultSummaryV0 {
    pub archmap: ArchSigArtifactValidationResultV0,
    pub law_policy: ArchSigArtifactValidationResultV0,
    pub analysis: ArchSigArtifactValidationResultV0,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArtifactValidationResultV0 {
    pub result: String,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
