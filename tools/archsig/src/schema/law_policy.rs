use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawPolicyDocumentV1 {
    pub schema: String,
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub law_surface_ref: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub measurement_profile_ref: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub basis_ledger: Vec<LawPolicyBasisLedgerEntryV1>,
    #[serde(default)]
    pub policies: Vec<LawPolicyEntryV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawPolicyBasisLedgerEntryV1 {
    pub basis_id: String,
    pub kind: String,
    pub path: String,
    pub revision: String,
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
    #[serde(
        default,
        deserialize_with = "deserialize_present_value",
        skip_serializing_if = "Option::is_none"
    )]
    pub diagnostic_ceiling: Option<Option<Value>>,
    pub finite_bounds: MeasurementProfileFiniteBoundsV1,
}

fn deserialize_present_value<'de, D>(deserializer: D) -> Result<Option<Option<Value>>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    Ok(Some(Option::<Value>::deserialize(deserializer)?))
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct MeasurementProfileFiniteBoundsV1 {
    pub max_square_free_witness_variables: usize,
    pub max_coherence_contexts: usize,
    pub max_tor_witness_variables: usize,
    pub max_boundary_residue_variables: usize,
    pub max_laplacian_cells: usize,
    pub max_period_cycles: usize,
    pub max_transfer_targets: usize,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub profile_ref: Option<Value>,
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
    pub policy_packs: Vec<LawPolicyPackManifestV1>,
    pub basis_refs: Vec<LawPolicyBasisManifestV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawEvaluatorManifestV1 {
    pub evaluator_id: String,
    pub law_id: String,
    #[serde(default)]
    pub condition_types: Vec<String>,
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
