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
pub struct H1ComparisonSupportV052 {
    pub overlap_ref: String,
    pub support: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonVariableMapV052 {
    pub source: String,
    pub target: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonChartMapRowV052 {
    pub source_chart_ref: String,
    pub target_chart_ref: String,
    pub variable_map: Vec<H1ComparisonVariableMapV052>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonOverlapMapRowV052 {
    pub source_overlap_ref: String,
    pub target_overlap_ref: String,
    pub variable_map: Vec<H1ComparisonVariableMapV052>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonTripleMapRowV052 {
    pub source_triple_ref: String,
    pub target_triple_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonDegreeTwoV052 {
    pub basis_map: Vec<H1ComparisonTripleMapRowV052>,
    pub zero_image: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonCochainMapV052 {
    pub degree_zero: Vec<H1ComparisonChartMapRowV052>,
    pub degree_one: Vec<H1ComparisonOverlapMapRowV052>,
    pub degree_two: H1ComparisonDegreeTwoV052,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationCellV052 {
    pub cell_ref: String,
    pub semantic_generators: Vec<String>,
    pub repair_relation_matrix: Vec<Vec<u8>>,
    pub equation_generators: Vec<String>,
    pub equation_relation_matrix: Vec<Vec<u8>>,
    pub generator_map: Vec<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationRestrictionV052 {
    pub from_ref: String,
    pub to_ref: String,
    pub semantic_matrix: Vec<Vec<u8>>,
    pub equation_matrix: Vec<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationEquationLiftV052 {
    pub chart_ref: String,
    pub coefficients: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationEquationTransitionV052 {
    pub overlap_ref: String,
    pub coefficients: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationEquationLiftAtlasV052 {
    pub local_lifts: Vec<H1PresentationEquationLiftV052>,
    pub transition_differences: Vec<H1PresentationEquationTransitionV052>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationDataV052 {
    pub cells: Vec<H1PresentationCellV052>,
    pub restrictions: Vec<H1PresentationRestrictionV052>,
    pub equation_lift_atlas: H1PresentationEquationLiftAtlasV052,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1ComparisonDataV052 {
    pub schema: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cochain_map_ref: Option<String>,
    pub source_complex_fingerprint: String,
    pub target_complex_fingerprint: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_cochain_support: Option<Vec<H1ComparisonSupportV052>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cochain_map: Option<H1ComparisonCochainMapV052>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub presentation: Option<H1PresentationDataV052>,
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
    pub residual_support_predicate: RepairPlanSuppliedPredicateV1,
    pub faithfulness_law: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSuppliedPredicateV1 {
    pub kind: String,
    #[serde(default)]
    pub support_variables: Vec<String>,
    pub zero_on_zero_primitive: bool,
}
