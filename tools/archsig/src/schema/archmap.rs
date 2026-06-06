use serde::{Deserialize, Serialize};

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapDocumentV0 {
    pub schema_version: String,
    pub map_id: String,
    pub architecture_id: String,
    pub generated_at: String,
    pub generator: ArchMapGenerator,
    #[serde(default)]
    pub prompt_refs: Vec<ArchMapArtifactRef>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_inventory_ref: Option<ArchMapArtifactRef>,
    pub generation_boundary: ArchMapGenerationBoundary,
    pub source_universe: ArchMapSourceUniverse,
    #[serde(default)]
    pub provenance: ArchMapProvenanceV0,
    #[serde(default)]
    pub atom_observations: Vec<ArchMapAtomObservationV0>,
    #[serde(default)]
    pub molecule_observations: Vec<ArchMapMoleculeObservationV0>,
    #[serde(default)]
    pub semantic_observations: Vec<ArchMapSemanticObservationV0>,
    #[serde(default)]
    pub observation_gaps: Vec<ArchMapObservationGapV0>,
    #[serde(default)]
    pub projection_info: Vec<ArchMapProjectionInfoV0>,
    #[serde(default)]
    pub operation_square_evidence: Vec<ArchMapOperationSquareEvidenceV0>,
    #[serde(default)]
    pub concern_hints: Vec<ArchMapConcernHintV0>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapGenerator {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provider: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapArtifactRef {
    pub artifact_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_hash: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapGenerationBoundary {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token_budget: Option<String>,
    #[serde(default)]
    pub scope: Vec<String>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceUniverse {
    pub root: String,
    #[serde(default)]
    pub included_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub hashes: Vec<ArchMapArtifactRef>,
    #[serde(default)]
    pub known_blind_spots: Vec<String>,
    pub selection_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceInventoryV0 {
    pub schema_version: String,
    pub inventory_id: String,
    pub root: String,
    #[serde(default)]
    pub included_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub hashes: Vec<ArchMapArtifactRef>,
    #[serde(default)]
    pub known_blind_spots: Vec<String>,
    pub selection_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceRef {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_id: Option<String>,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub section: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapProvenanceV0 {
    pub observer: String,
    pub observation_method: String,
    pub source_root: String,
    pub observation_boundary: String,
    #[serde(default)]
    pub reviewed_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapAtomObservationV0 {
    pub atom_observation_id: String,
    pub atom_family: String,
    pub predicate: String,
    pub subject_ref: String,
    #[serde(default)]
    pub object_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub uncertainty: Vec<String>,
    #[serde(default)]
    pub projection_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapMoleculeObservationV0 {
    pub molecule_observation_id: String,
    pub molecule_family: String,
    pub role_name: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSemanticObservationV0 {
    pub semantic_observation_id: String,
    pub semantic_family: String,
    pub subject_ref: String,
    pub predicate: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapProjectionInfoV0 {
    pub projection_id: String,
    pub projection_family: String,
    pub source_observation_ref: String,
    pub target_surface: String,
    pub reading: String,
    pub projection_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapOperationSquareEvidenceV0 {
    pub operation_square_evidence_id: String,
    pub evidence_kind: String,
    pub left_operation_ref: String,
    pub right_operation_ref: String,
    #[serde(default)]
    pub p_operation_sequence: Vec<String>,
    #[serde(default)]
    pub q_operation_sequence: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    #[serde(default)]
    pub generator_candidate_refs: Vec<String>,
    #[serde(default)]
    pub shared_endpoint_refs: Vec<String>,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub semantic_observation_refs: Vec<String>,
    #[serde(default)]
    pub projection_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapConcernHintV0 {
    pub concern_hint_id: String,
    pub concern_family: String,
    pub subject_ref: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub semantic_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub evidence_boundary: String,
    pub analysis_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapObservationGapV0 {
    pub gap_id: String,
    pub gap_kind: String,
    pub subject_ref: String,
    pub evidence_status: String,
    pub reason: String,
    #[serde(default)]
    pub expected_atom_families: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationReportV0 {
    pub schema_version: String,
    pub archmap_ref: String,
    pub lean_preservation_vocabulary: Vec<ArchMapLeanPreservationVocabularyEntry>,
    pub lean_preservation_precondition_checklist: Vec<ArchMapLeanPreservationChecklistEntry>,
    pub source_inventory_checks: Vec<ValidationCheck>,
    pub source_ref_checks: Vec<ValidationCheck>,
    pub claim_boundary_checks: Vec<ValidationCheck>,
    pub semantic_coverage_checks: Vec<ValidationCheck>,
    pub formal_promotion_guardrail_checks: Vec<ValidationCheck>,
    pub atomic_observation_checks: Vec<ValidationCheck>,
    pub atomic_observation_summary: ArchMapAtomicObservationSummary,
    pub responsibility_checks: Vec<ValidationCheck>,
    pub summary: ArchMapValidationSummary,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapAtomicObservationSummary {
    pub atom_observation_count: usize,
    pub observed_atom_count: usize,
    pub promotable_atom_observation_count: usize,
    pub rejected_or_uncertain_observation_count: usize,
    pub molecule_observation_count: usize,
    pub observed_molecule_count: usize,
    pub semantic_observation_count: usize,
    pub concern_hint_count: usize,
    pub observation_gap_count: usize,
    pub lean_presentation_candidate_count: usize,
    pub sft_handoff_ref_count: usize,
    pub zero_curvature_reading: String,
    pub promotion_boundary: String,
    pub boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationSummary {
    pub result: String,
    pub atom_observation_count: usize,
    pub molecule_observation_count: usize,
    pub semantic_observation_count: usize,
    pub observation_gap_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapLeanPreservationVocabularyEntry {
    pub vocabulary_id: String,
    pub archmap_selector: String,
    pub lean_package_field: String,
    pub preservation_role: String,
    pub report_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapLeanPreservationChecklistEntry {
    pub checklist_id: String,
    pub lean_package_field: String,
    pub status: String,
    pub candidate_sources: Vec<String>,
    pub blocking_reasons: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}
