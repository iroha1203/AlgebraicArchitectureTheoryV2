use serde::{Deserialize, Serialize};

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawPolicyDocumentV1 {
    pub schema: String,
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub distance_profile_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub measurement_profile_ref: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub measurement_profiles: Vec<MeasurementProfileV1>,
    #[serde(default)]
    pub policies: Vec<LawPolicyEntryV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MeasurementProfileV1 {
    pub schema: String,
    pub profile_id: String,
    pub site_ref: String,
    pub cover_ref: String,
    pub coefficient: String,
    pub eff_coeff: String,
    #[serde(default)]
    pub witness_family: Vec<MeasurementProfileWitnessV1>,
    pub resolution_selector: String,
    pub domain: String,
    pub zero_predicate: String,
    pub non_zero_predicate: String,
    pub cert_selector: String,
    pub verdict_discipline: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MeasurementProfileWitnessV1 {
    pub law: String,
    pub variable: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawPolicyEntryV1 {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pack: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub law: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evaluator: Option<String>,
    #[serde(default)]
    pub basis: Vec<String>,
    #[serde(default)]
    pub scope: Vec<String>,
    pub severity: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationReportV1 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub input: LawPolicyValidationInputV1,
    pub expanded_policies: Vec<ExpandedLawPolicyEntryV1>,
    pub checks: Vec<ValidationCheck>,
    pub summary: LawPolicyValidationSummaryV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationInputV1 {
    pub schema: String,
    pub path: String,
    pub id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationSummaryV1 {
    pub result: String,
    pub policy_entry_count: usize,
    pub expanded_policy_entry_count: usize,
    pub pack_entry_count: usize,
    pub explicit_law_entry_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawEvaluatorRegistryV1 {
    pub schema: String,
    pub registry_id: String,
    pub evaluators: Vec<LawEvaluatorManifestV1>,
    pub replacement_registry: Vec<ReplacementEvaluatorManifestV1>,
    pub policy_packs: Vec<LawPolicyPackManifestV1>,
    pub basis_refs: Vec<LawPolicyBasisManifestV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawEvaluatorManifestV1 {
    pub evaluator_id: String,
    pub law_id: String,
    pub required_atom_constructors: Vec<String>,
    pub required_predicates: Vec<String>,
    pub required_molecule_condition: String,
    pub scope_filtering_rule: String,
    pub missing_blocker_rule: String,
    pub pass_criteria: String,
    pub violation_criteria: String,
    pub typed_result_schema: String,
    pub distance_contribution: String,
    pub summary_output_refs: Vec<String>,
    pub detail_output_refs: Vec<String>,
    pub negative_fixtures: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReplacementEvaluatorManifestV1 {
    pub replacement_id: String,
    pub replaced_v0_field: String,
    pub evaluator_id: String,
    pub law_id: String,
    pub required_atom_constructors: Vec<String>,
    pub required_molecule_membership: String,
    pub typed_output_packet_refs: Vec<String>,
    pub positive_fixtures: Vec<String>,
    pub negative_fixtures: Vec<String>,
    pub missing_blocker_rule: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyPackManifestV1 {
    pub pack_id: String,
    pub entries: Vec<LawPolicyPackEntryV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyPackEntryV1 {
    pub law: String,
    pub evaluator: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyBasisManifestV1 {
    pub basis_ref: String,
    pub title: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExpandedLawPolicyEntryV1 {
    pub source_policy_index: usize,
    pub source_selector: String,
    pub law: String,
    pub evaluator: String,
    pub basis: Vec<String>,
    pub scope: Vec<String>,
    pub severity: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TypedEvaluatorResultsV1 {
    pub schema: String,
    pub pipeline_id: String,
    pub normalized_archmap_ref: String,
    pub law_policy_ref: String,
    pub replacement_registry_ref: String,
    pub replacement_registry: Vec<ReplacementEvaluatorManifestV1>,
    pub results: Vec<TypedEvaluatorResultV1>,
    pub replacement_evaluator_results: Vec<TypedEvaluatorResultV1>,
    pub summary: TypedEvaluatorResultsSummaryV1,
    pub replacement_summary: TypedEvaluatorResultsSummaryV1,
    pub replacement_registry_resolution: ReplacementRegistryResolutionV1,
    pub positive_bounded_conclusions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TypedEvaluatorResultV1 {
    pub evaluator: String,
    pub law: String,
    pub status: String,
    pub support_atom_refs: Vec<String>,
    pub support_molecule_refs: Vec<String>,
    pub basis_refs: Vec<String>,
    pub detail_refs: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replacement_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replacement_for_v0_field: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub typed_output_packet_refs: Vec<String>,
    pub summary: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub blocker_reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TypedEvaluatorResultsSummaryV1 {
    pub result_count: usize,
    pub measured_pass_count: usize,
    pub measured_violation_count: usize,
    pub blocked_count: usize,
    pub unknown_count: usize,
    pub unmeasured_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReplacementRegistryResolutionV1 {
    pub schema: String,
    pub registry_ref: String,
    pub manifest_count: usize,
    pub resolved_replacement_count: usize,
    pub blocked_replacement_count: usize,
    pub non_diagnostic_replacement_count: usize,
    pub replaced_v0_fields: Vec<String>,
    pub non_conclusions: Vec<String>,
}
