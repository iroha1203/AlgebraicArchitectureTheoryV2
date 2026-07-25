use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanDocumentV1 {
    pub schema: String,
    pub id: String,
    pub complex: RepairPlanComplexV1,
    pub faithfulness: RepairPlanFaithfulnessV1,
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
    pub repair_relation_matrix: Vec<Vec<i64>>,
    pub equation_generators: Vec<String>,
    pub equation_relation_matrix: Vec<Vec<i64>>,
    pub generator_map: Vec<Vec<i64>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationRestrictionV052 {
    pub from_ref: String,
    pub to_ref: String,
    pub semantic_matrix: Vec<Vec<i64>>,
    pub equation_matrix: Vec<Vec<i64>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationEquationLiftV052 {
    pub chart_ref: String,
    pub coefficients: Vec<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct H1PresentationEquationTransitionV052 {
    pub overlap_ref: String,
    pub coefficients: Vec<i64>,
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
    /// `"f2"`(既定)または `"integers"`。第X部 定義 10.1 の有限生成可換群版は後者を要する。
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coefficient_ring: Option<String>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanFaithfulnessV1 {
    pub mode: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub supplied: Option<RepairPlanSuppliedFaithfulnessV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSuppliedFaithfulnessV1 {
    pub residual_support_predicate: RepairPlanSuppliedPredicateV1,
    pub faithfulness_law: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RepairPlanSuppliedPredicateV1 {
    pub kind: String,
    #[serde(default)]
    pub support_variables: Vec<String>,
}
