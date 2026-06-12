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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawPolicyDocumentV0 {
    pub schema_version: String,
    pub law_policy_id: String,
    pub policy_version: String,
    pub scope: String,
    pub archmap_schema_ref: String,
    pub selected_laws: Vec<LawPolicySelectedLawV0>,
    pub required_zero_axes: Vec<LawPolicyAxisDefinitionV0>,
    #[serde(default)]
    pub optional_axes: Vec<LawPolicyAxisDefinitionV0>,
    pub witness_rules: Vec<LawPolicyWitnessRuleV0>,
    #[serde(default)]
    pub molecule_patterns: Vec<LawPolicyMoleculePatternV0>,
    pub obstruction_circuit_definitions: Vec<LawPolicyObstructionCircuitDefinitionV0>,
    pub signature_axis_definitions: Vec<LawPolicySignatureAxisDefinitionV0>,
    pub measurement_policy: LawPolicyMeasurementPolicyV0,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub part4_distance_profile: Option<LawPolicyPart4DistanceProfileV0>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub spectrum_measurement_profile: Option<LawPolicySpectrumMeasurementProfileV0>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub homotopy_measurement_profile: Option<LawPolicyHomotopyMeasurementProfileV0>,
    pub exactness_assumptions: Vec<String>,
    pub coverage_requirements: Vec<LawPolicyCoverageRequirementV0>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyMeasurementPolicyV0 {
    pub policy_id: String,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    pub distance_kind: String,
    pub weight_policy: String,
    pub coverage_policy: String,
    #[serde(default)]
    pub arch_map_store_ref_kinds: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyPart4DistanceProfileV0 {
    pub profile_id: String,
    #[serde(default)]
    pub atom_weights: Vec<LawPolicyPart4DistanceWeightV0>,
    #[serde(default)]
    pub signature_weights: Vec<LawPolicyPart4DistanceWeightV0>,
    #[serde(default)]
    pub operation_costs: Vec<LawPolicyPart4OperationCostV0>,
    pub aggregation_policy: String,
    pub unmeasured_policy: String,
    pub law_overlay_policy: String,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    pub evidence_boundary: String,
    #[serde(default)]
    pub calibration_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyPart4DistanceWeightV0 {
    pub axis_ref: String,
    pub weight: i64,
    pub source_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyPart4OperationCostV0 {
    pub operation_kind: String,
    pub cost: i64,
    pub source_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySpectrumMeasurementProfileV0 {
    pub profile_id: String,
    #[serde(default)]
    pub reading_boundary: LawPolicyReadingBoundaryV0,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    #[serde(default)]
    pub measured_witness_rule_refs: Vec<String>,
    #[serde(default)]
    pub distance_kinds: Vec<LawPolicySpectrumDistanceKindV0>,
    pub weight_policy: String,
    pub support_projection_rule: String,
    pub transfer_edge_rule: String,
    #[serde(default)]
    pub clustering_ranking_options: Vec<String>,
    #[serde(default)]
    pub report_focus_options: Vec<String>,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    pub coverage_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySpectrumDistanceKindV0 {
    pub axis_ref: String,
    pub distance_kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyMeasurementProfileV0 {
    pub profile_id: String,
    #[serde(default)]
    pub reading_boundary: LawPolicyReadingBoundaryV0,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    #[serde(default)]
    pub path_discovery_rules: Vec<LawPolicyHomotopyPathDiscoveryRuleV0>,
    #[serde(default)]
    pub filler_rules: Vec<LawPolicyHomotopyFillerRuleV0>,
    pub loop_measurement_policy: LawPolicyHomotopyLoopMeasurementPolicyV0,
    pub continuation_policy: String,
    pub distance_policy: String,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    pub coverage_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyReadingBoundaryV0 {
    #[serde(default)]
    pub reading_strength: String,
    #[serde(default)]
    pub zero_reflection_assumptions: Vec<String>,
    #[serde(default)]
    pub obstruction_reflection_assumptions: Vec<String>,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    #[serde(default)]
    pub witness_completeness_boundary: String,
}

impl Default for LawPolicyReadingBoundaryV0 {
    fn default() -> Self {
        Self {
            reading_strength: String::new(),
            zero_reflection_assumptions: Vec::new(),
            obstruction_reflection_assumptions: Vec::new(),
            coverage_requirement_refs: Vec::new(),
            witness_completeness_boundary: String::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyPathDiscoveryRuleV0 {
    pub rule_id: String,
    pub path_source_kind: String,
    pub endpoint_policy: String,
    pub candidate_source: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyFillerRuleV0 {
    pub rule_id: String,
    pub filler_kind: String,
    #[serde(default)]
    pub required_source_ref_kinds: Vec<String>,
    pub missing_filler_behavior: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyLoopMeasurementPolicyV0 {
    pub policy_id: String,
    #[serde(default)]
    pub loop_candidate_sources: Vec<String>,
    pub filled_loop_reading: String,
    pub unfilled_loop_reading: String,
    pub holonomy_distance_kind: String,
    pub local_curvature_reading_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySelectedLawV0 {
    pub law_id: String,
    pub law_family: String,
    pub description: String,
    pub enforcement_boundary: String,
    #[serde(default)]
    pub applies_to_atom_families: Vec<String>,
    #[serde(default)]
    pub required_witness_refs: Vec<String>,
    #[serde(default)]
    pub required_axis_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyAxisDefinitionV0 {
    pub axis_id: String,
    pub axis_family: String,
    pub value_type: String,
    pub zero_reading: String,
    pub measurement_boundary: String,
    #[serde(default)]
    pub evidence_requirements: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyWitnessRuleV0 {
    pub witness_rule_id: String,
    pub law_ref: String,
    pub witness_kind: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub molecule_pattern_refs: Vec<String>,
    pub evidence_boundary: String,
    #[serde(default)]
    pub missing_evidence_behavior: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyMoleculePatternV0 {
    pub molecule_pattern_id: String,
    pub role_name: String,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub optional_atom_families: Vec<String>,
    pub interpretation_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyObstructionCircuitDefinitionV0 {
    pub obstruction_circuit_id: String,
    pub law_ref: String,
    pub witness_rule_ref: String,
    pub circuit_kind: String,
    pub minimality_reading: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub signature_axis_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySignatureAxisDefinitionV0 {
    pub signature_axis_id: String,
    pub law_ref: String,
    pub axis_ref: String,
    pub valuation_rule: String,
    pub value_type: String,
    pub zero_reading: String,
    pub coverage_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyCoverageRequirementV0 {
    pub coverage_requirement_id: String,
    #[serde(default)]
    pub applies_to_law_refs: Vec<String>,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub required_source_ref_kinds: Vec<String>,
    pub missing_coverage_behavior: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationReportV0 {
    pub schema_version: String,
    pub input: LawPolicyValidationInputV0,
    pub policy: LawPolicyDocumentV0,
    pub summary: LawPolicyValidationSummaryV0,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationInputV0 {
    pub schema_version: String,
    pub path: String,
    pub law_policy_id: String,
    pub policy_version: String,
    pub archmap_schema_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationSummaryV0 {
    pub result: String,
    pub selected_law_count: usize,
    pub required_zero_axis_count: usize,
    pub witness_rule_count: usize,
    pub obstruction_circuit_definition_count: usize,
    pub signature_axis_definition_count: usize,
    pub coverage_requirement_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
