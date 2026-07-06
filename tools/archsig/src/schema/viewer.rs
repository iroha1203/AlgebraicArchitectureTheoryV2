use serde::{Deserialize, Serialize};

use super::archmap::ArchMapSourceRef;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerDataV1 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub data_kind: String,
    pub source_artifact_refs: ArchSigAtomViewerSourceArtifactRefsV1,
    pub layout_settings: ArchSigAtomViewerLayoutSettingsV1,
    pub atom_nodes: Vec<ArchSigAtomViewerAtomNodeV1>,
    pub molecule_groups: Vec<ArchSigAtomViewerMoleculeGroupV1>,
    pub atom_edges: Vec<ArchSigAtomViewerEdgeV1>,
    pub law_axis_overlays: serde_json::Value,
    pub analysis_overlays: serde_json::Value,
    #[serde(default)]
    pub aat_geometry_overlays: serde_json::Value,
    pub report_pane: serde_json::Value,
    pub omitted_detail_counts: ArchSigAtomViewerOmittedDetailCountsV1,
    pub truncation_policy: ArchSigAtomViewerTruncationPolicyV1,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerSourceArtifactRefsV1 {
    pub archmap: String,
    pub law_policy: String,
    pub summary: String,
    pub manifest: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerLayoutSettingsV1 {
    pub layout_kind: String,
    pub node_limit: usize,
    pub molecule_group_limit: usize,
    pub edge_limit: usize,
    pub overlay_limit: usize,
    pub label_limit: usize,
    pub source_ref_sample_limit: usize,
    pub distance_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerAtomNodeV1 {
    pub node_id: String,
    pub atom_family: String,
    pub subject_ref: String,
    pub predicate: String,
    pub observation_status: String,
    pub confidence: String,
    pub object_ref_count: usize,
    pub source_ref_count: usize,
    pub source_ref_samples: Vec<ArchMapSourceRef>,
    pub labels: Vec<String>,
    pub projection_refs: Vec<String>,
    pub selection_reason: String,
    pub priority_score: i64,
    pub visual: ArchSigAtomViewerVisualV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerMoleculeGroupV1 {
    pub group_id: String,
    pub molecule_family: String,
    pub role_name: String,
    pub atom_observation_refs: Vec<String>,
    pub observation_status: String,
    pub confidence: String,
    pub source_ref_count: usize,
    pub source_ref_samples: Vec<ArchMapSourceRef>,
    pub labels: Vec<String>,
    pub omitted_atom_observation_ref_count: usize,
    pub selection_reason: String,
    pub priority_score: i64,
    pub visual: ArchSigAtomViewerVisualV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerEdgeV1 {
    pub edge_id: String,
    pub source_node_ref: String,
    pub target_node_ref: String,
    pub edge_kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relation_ref: Option<String>,
    pub visual: ArchSigAtomViewerVisualV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerVisualV1 {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub color_by: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub size_by: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hull_by: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerOmittedDetailCountsV1 {
    pub atom_nodes: usize,
    pub molecule_groups: usize,
    pub atom_edges: usize,
    pub source_refs: usize,
    pub labels: usize,
    pub overlay_items: usize,
    pub raw_packet_detail: String,
    pub omitted_reasons: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomViewerTruncationPolicyV1 {
    pub atom_nodes: String,
    pub molecule_groups: String,
    pub overlays: String,
    pub future_work: String,
}
