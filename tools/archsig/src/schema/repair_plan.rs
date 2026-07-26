use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanDocumentV1 {
    pub schema: String,
    pub id: String,
    pub complex: RepairPlanComplexV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanComplexV1 {
    pub charts: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_cover_ref: Option<String>,
    pub overlaps: Vec<RepairPlanOverlapV1>,
    #[serde(default)]
    pub triple_overlaps: Vec<RepairPlanTripleOverlapV1>,
    pub enumeration_complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanOverlapV1 {
    pub id: String,
    pub left: String,
    pub right: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_context_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanTripleOverlapV1 {
    pub id: String,
    pub overlap_refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_context_ref: Option<String>,
}
