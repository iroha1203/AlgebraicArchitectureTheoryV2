use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanDocumentV1 {
    pub schema: String,
    pub id: String,
    pub residual: RepairPlanResidualV1,
    pub complex: RepairPlanComplexV1,
    pub primitives: Vec<RepairPlanPrimitiveV1>,
    pub semantic_projection: RepairPlanSemanticProjectionV1,
    pub faithfulness: RepairPlanFaithfulnessV1,
    pub coefficient: RepairPlanCoefficientV1,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub true_sheaf_certificate: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub gluing_data: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparison: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub grounding: Option<serde_json::Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanResidualV1 {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub packet_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub invariant_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanComplexV1 {
    pub charts: Vec<String>,
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
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanTripleOverlapV1 {
    pub id: String,
    pub overlap_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanPrimitiveV1 {
    pub id: String,
    pub overlap_ref: String,
    pub res_l: Vec<String>,
    pub res_r: Vec<String>,
    pub support: RepairPlanSupportV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSupportV1 {
    pub kind: String,
    pub variables: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSemanticProjectionV1 {
    pub lambda: Vec<String>,
    pub k: Vec<String>,
    pub pi: Vec<RepairPlanProjectionRowV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanProjectionRowV1 {
    pub atom_ref: String,
    pub subject: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanFaithfulnessV1 {
    pub mode: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub supplied: Option<RepairPlanSuppliedFaithfulnessV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RepairPlanCoefficientV1 {
    Named(String),
    Supplied(RepairPlanSuppliedCoefficientV1),
}

impl RepairPlanCoefficientV1 {
    pub fn is_f2_additive(&self) -> bool {
        matches!(self, Self::Named(name) if name == "f2-additive")
    }

    pub fn supplied(&self) -> Option<&RepairPlanSuppliedCoefficientV1> {
        match self {
            Self::Supplied(value) => Some(value),
            Self::Named(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSuppliedCoefficientV1 {
    pub kind: String,
    pub characteristic: u8,
    pub additive: bool,
    pub delta_one_after_delta_zero: bool,
    pub zero_maps_to_zero: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSuppliedFaithfulnessV1 {
    pub zero_primitive_ref: String,
    pub residual_support_predicate: String,
    pub faithfulness_law: String,
}
