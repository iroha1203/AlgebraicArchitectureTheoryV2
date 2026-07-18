use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapDocumentV2 {
    pub schema: String,
    pub id: String,
    #[serde(default = "canonical_archmap_extraction_doctrine_ref_v2")]
    pub extraction_doctrine_ref: ArchMapExtractionDoctrineRefV2,
    #[serde(default)]
    pub sources: BTreeMap<String, ArchMapSource>,
    #[serde(default)]
    pub atoms: Vec<ArchMapAtomV2>,
    #[serde(default)]
    pub contexts: Vec<ArchMapContextV2>,
    #[serde(default)]
    pub covers: Vec<ArchMapCoverV2>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapExtractionDoctrineRefV2 {
    pub doctrine_id: String,
    pub fingerprint: String,
    #[serde(default)]
    pub components: Vec<String>,
}

pub fn canonical_archmap_extraction_doctrine_ref_v2() -> ArchMapExtractionDoctrineRefV2 {
    ArchMapExtractionDoctrineRefV2 {
        doctrine_id: "doctrine:aat-canonical@1".to_string(),
        fingerprint: "sha256:aat-canonical-doctrine-schema052".to_string(),
        components: ["V", "Gamma", "R", "rho", "E", "N"]
            .into_iter()
            .map(str::to_string)
            .collect(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatAtomVocabularyV1 {
    pub schema: String,
    pub vocabulary_id: String,
    pub doctrine_ref: String,
    pub required_doctrine_components: Vec<String>,
    pub entries: Vec<AatAtomVocabularyEntryV1>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatAtomVocabularyEntryV1 {
    pub kind: String,
    pub doctrine_ref: String,
    pub provenance_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapAtomV2 {
    pub id: String,
    pub kind: String,
    pub subject: String,
    pub axis: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub predicate: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapContextV2 {
    pub id: String,
    #[serde(default)]
    pub atoms: Vec<String>,
    #[serde(default)]
    pub restricts_to: Vec<String>,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapCoverV2 {
    pub id: String,
    #[serde(default)]
    pub contexts: Vec<String>,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapSource {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub section: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapScopeManifestV1 {
    pub schema: String,
    pub id: String,
    pub repository: ArchmapScopeManifestRepositoryV1,
    pub scope_spec: ArchmapScopeManifestScopeSpecV1,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub baseline_ref: Option<String>,
    pub worklist: Vec<ArchmapScopeManifestWorklistEntryV1>,
    #[serde(default)]
    pub exclusions: Vec<ArchmapScopeManifestExclusionV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapScopeManifestRepositoryV1 {
    pub root: String,
    pub revision: Option<String>,
    pub dirty: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapScopeManifestScopeSpecV1 {
    pub include_globs: Vec<String>,
    pub exclude_globs: Vec<String>,
    #[serde(default)]
    pub added_evidence: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requested_scope: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub approved_by: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapScopeManifestWorklistEntryV1 {
    pub order: usize,
    pub source_id: String,
    pub path: String,
    pub kind: String,
    pub content_hash: String,
    pub size_bytes: u64,
    pub author_added: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapScopeManifestExclusionV1 {
    pub path: String,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapCandidatePacketV1 {
    pub schema: String,
    pub id: String,
    pub scope_manifest_ref: String,
    pub pass_id: String,
    pub chunk: BTreeMap<String, usize>,
    #[serde(default)]
    pub reviewed_sources: Vec<String>,
    #[serde(default)]
    pub candidate_sources: BTreeMap<String, ArchMapSource>,
    #[serde(default)]
    pub candidate_atoms: Vec<ArchMapAtomV2>,
    #[serde(default)]
    pub candidate_contexts: Vec<ArchMapContextV2>,
    #[serde(default)]
    pub candidate_covers: Vec<ArchMapCoverV2>,
    #[serde(default)]
    pub survey_rows: Vec<ArchmapCandidatePacketSurveyRowV1>,
    #[serde(default)]
    pub private_unavailable_notes: Vec<String>,
    pub self_review: ArchmapCandidatePacketSelfReviewV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapCandidatePacketSurveyRowV1 {
    pub source_id: String,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(default)]
    pub surveyed_kinds: Vec<String>,
    #[serde(default)]
    pub candidate_atom_ids: Vec<String>,
    #[serde(default)]
    pub notes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapCandidatePacketSelfReviewV1 {
    pub not_script_generated: bool,
    pub not_coarse_when_evidence_was_richer: bool,
    pub semantic_atoms_have_use_evidence: bool,
    pub no_diagnostic_shortcut_atoms: bool,
    pub worklist_chunk_fully_read: bool,
    pub alias_preserving_semantics: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionConsistencyV1 {
    pub schema: String,
    pub id: String,
    pub scope_manifest_ref: String,
    pub pass_a_refs: Vec<String>,
    pub pass_b_refs: Vec<String>,
    pub atom_match_key_spec: String,
    pub matched: ArchmapExtractionMatchCountV1,
    #[serde(default)]
    pub only_in_pass_a: Vec<ArchmapExtractionOnlyInCandidateV1>,
    #[serde(default)]
    pub only_in_pass_b: Vec<ArchmapExtractionOnlyInCandidateV1>,
    pub match_rate: f64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub atom_match_key1_comparison: Option<ArchmapExtractionKeyComparisonV1>,
    pub context_diff: ArchmapExtractionContextDiffV1,
    #[serde(default)]
    pub adjudications: Vec<ArchmapExtractionAdjudicationV1>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionKeyComparisonV1 {
    pub atom_match_key_spec: String,
    pub matched_count: usize,
    pub match_rate: f64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionMatchCountV1 {
    pub count: usize,
    #[serde(default)]
    pub rows: Vec<ArchmapExtractionMatchedCandidateV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionMatchedCandidateV1 {
    pub key: String,
    #[serde(default)]
    pub pass_a_atom_ids: Vec<String>,
    #[serde(default)]
    pub pass_b_atom_ids: Vec<String>,
    #[serde(default)]
    pub refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionOnlyInCandidateV1 {
    pub key: String,
    pub candidate_atom_id: String,
    #[serde(default)]
    pub refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionContextDiffV1 {
    pub matched: usize,
    #[serde(default)]
    pub only_in_pass_a: Vec<String>,
    #[serde(default)]
    pub only_in_pass_b: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapExtractionAdjudicationV1 {
    pub key: String,
    pub decision: String,
    pub basis: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapCoverageLedgerV1 {
    pub schema: String,
    pub id: String,
    pub scope_manifest_ref: String,
    pub archmap_ref: String,
    #[serde(default)]
    pub pass_refs: Vec<String>,
    pub rows: Vec<ArchmapCoverageLedgerRowV1>,
    pub claim_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchmapCoverageLedgerRowV1 {
    pub source_id: String,
    pub survey_status: String,
    #[serde(default)]
    pub passes: Vec<String>,
    #[serde(default)]
    pub surveyed_kinds: Vec<String>,
    #[serde(default)]
    pub adopted_atom_ids: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationReportV1 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub archmap_ref: String,
    pub input_schema: String,
    pub checks: Vec<ValidationCheck>,
    pub summary: ArchMapValidationSummaryV1,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationSummaryV1 {
    pub result: String,
    pub source_count: usize,
    pub atom_count: usize,
    pub molecule_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationReportV2 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub archmap_ref: String,
    pub input_schema: String,
    pub checks: Vec<ValidationCheck>,
    pub summary: ArchMapValidationSummaryV2,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationSummaryV2 {
    pub result: String,
    pub source_count: usize,
    pub atom_count: usize,
    pub context_count: usize,
    pub cover_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedArchMapV2 {
    pub schema: String,
    pub normalizer_id: String,
    pub source_archmap_ref: String,
    pub source_archmap_id: String,
    pub extraction_doctrine_ref: ArchMapExtractionDoctrineRefV2,
    pub atoms: Vec<NormalizedAtomV2>,
    pub contexts: Vec<NormalizedContextV2>,
    pub covers: Vec<NormalizedCoverV2>,
    pub summary: NormalizedArchMapSummaryV2,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedAtomV2 {
    pub source_atom_id: String,
    pub normalized_atom_id: String,
    pub atom_kind: String,
    pub subject: String,
    pub axis: String,
    pub predicate: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    pub source_refs: Vec<String>,
    pub context_memberships: Vec<String>,
    pub normalization_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedContextV2 {
    pub source_context_id: String,
    pub normalized_context_id: String,
    pub atom_ids: Vec<String>,
    pub restricts_to: Vec<String>,
    pub source_refs: Vec<String>,
    pub poset_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedCoverV2 {
    pub source_cover_id: String,
    pub normalized_cover_id: String,
    pub context_ids: Vec<String>,
    pub source_refs: Vec<String>,
    pub coverage_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedArchMapSummaryV2 {
    pub atom_count: usize,
    pub normalized_atom_count: usize,
    pub context_count: usize,
    pub cover_count: usize,
    pub doctrine_fingerprint: String,
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
