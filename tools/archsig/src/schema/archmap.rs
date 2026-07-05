use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapDocumentV1 {
    pub schema: String,
    pub id: String,
    #[serde(default)]
    pub sources: BTreeMap<String, ArchMapSourceV1>,
    #[serde(default)]
    pub atoms: Vec<ArchMapAtomV1>,
    #[serde(default)]
    pub molecules: Vec<ArchMapMoleculeV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapDocumentV2 {
    pub schema: String,
    pub id: String,
    #[serde(default = "canonical_archmap_extraction_doctrine_ref_v2")]
    pub extraction_doctrine_ref: ArchMapExtractionDoctrineRefV2,
    #[serde(default)]
    pub sources: BTreeMap<String, ArchMapSourceV1>,
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
        fingerprint: "sha256:aat-canonical-doctrine-v1".to_string(),
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
pub struct ArchMapSourceV1 {
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
pub struct ArchMapAtomV1 {
    pub id: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subject: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub edge: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagram: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub predicate: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub state: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub effect: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contract: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meaning: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interaction: Option<String>,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapMoleculeV1 {
    pub id: String,
    #[serde(default)]
    pub atoms: Vec<String>,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationReportV1 {
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
pub struct NormalizedArchMapV1 {
    pub schema: String,
    pub normalizer_id: String,
    pub source_archmap_ref: String,
    pub source_archmap_id: String,
    pub atoms: Vec<NormalizedAtomV1>,
    pub molecules: Vec<NormalizedMoleculeV1>,
    pub summary: NormalizedArchMapSummaryV1,
    pub non_conclusions: Vec<String>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedAtomV1 {
    pub source_atom_id: String,
    pub normalized_atom_id: String,
    pub atom_kind: String,
    pub axis: String,
    pub predicate: NormalizedAtomPredicateV1,
    pub shape_coordinate_status: String,
    pub valence_template_id: String,
    pub molecule_memberships: Vec<String>,
    pub normalization_status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalization_blocker_reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedAtomPredicateV1 {
    pub constructor: String,
    pub normalized_name: String,
    pub bindings: Vec<NormalizedAtomBindingV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedAtomBindingV1 {
    pub role: String,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedMoleculeV1 {
    pub source_molecule_id: String,
    pub normalized_molecule_id: String,
    pub atom_ids: Vec<String>,
    pub generated_molecule_candidate_status: String,
    pub required_port_status: String,
    pub composition_status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalization_blocker_reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedArchMapSummaryV1 {
    pub atom_count: usize,
    pub normalized_atom_count: usize,
    pub molecule_count: usize,
    pub generated_molecule_candidate_count: usize,
    pub blocked_molecule_candidate_count: usize,
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
