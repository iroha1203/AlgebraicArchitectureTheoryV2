use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestV1 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub tool_version: String,
    pub run_id: String,
    pub input_digests: Value,
    pub command_name: String,
    pub mode: String,
    pub conclusion_code: Option<String>,
    pub archmap_input_path: String,
    pub law_policy_input_path: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub law_surface_input_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub measurement_profile_input_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repair_plan_input_path: Option<String>,
    pub raw_artifact_retention: String,
    pub generated_artifacts: Vec<String>,
    pub omitted_artifacts: Vec<String>,
    pub artifact_links: Value,
    pub validation_reports: ArchSigRunManifestValidationReportPathsV1,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw_artifact_paths: Option<ArchSigRunManifestRawArtifactPathsV1>,
    pub validation_result_summary: ArchSigRunManifestValidationResultSummaryV1,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestValidationReportPathsV1 {
    pub archmap: String,
    pub law_policy: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub law_surface: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repair_plan: Option<String>,
    pub analysis: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestRawArtifactPathsV1 {
    pub analysis_packet: String,
    pub analysis_detail_index: String,
    pub llm_interpretation_packet: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRunManifestValidationResultSummaryV1 {
    pub archmap: ArchSigArtifactValidationResultV1,
    pub law_policy: ArchSigArtifactValidationResultV1,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub law_surface: Option<ArchSigArtifactValidationResultV1>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repair_plan: Option<ArchSigArtifactValidationResultV1>,
    pub analysis: ArchSigArtifactValidationResultV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArtifactValidationResultV1 {
    pub result: String,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
