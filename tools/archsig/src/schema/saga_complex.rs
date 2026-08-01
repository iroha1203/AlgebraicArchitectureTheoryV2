use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DerivedSagaComplexV1 {
    pub schema: String,
    pub id: String,
    pub complex: DerivedSagaComplexDataV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DerivedSagaComplexDataV1 {
    pub charts: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_cover_ref: Option<String>,
    pub overlaps: Vec<DerivedSagaOverlapV1>,
    #[serde(default)]
    pub triple_overlaps: Vec<DerivedSagaTripleV1>,
    pub enumeration_complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DerivedSagaOverlapV1 {
    pub id: String,
    pub left: String,
    pub right: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_context_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DerivedSagaTripleV1 {
    pub id: String,
    pub overlap_refs: Vec<String>,
    pub archmap_atom_refs: Vec<String>,
}
