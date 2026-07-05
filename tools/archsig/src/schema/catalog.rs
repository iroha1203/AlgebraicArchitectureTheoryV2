use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaVersionCatalogV0 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub catalog_id: String,
    pub catalog_version: String,
    pub phase: String,
    pub artifacts: Vec<SchemaVersionCatalogEntryV0>,
    pub compatibility_policy: SchemaCompatibilityPolicyV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaVersionCatalogEntryV0 {
    pub artifact_id: String,
    pub artifact_name: String,
    #[serde(rename = "schemaName")]
    pub schema_version_name: String,
    pub artifact_role: String,
    pub owner_phase: String,
    pub status: String,
    pub primary_docs: Vec<String>,
    pub downstream_issues: Vec<String>,
    pub compatibility_boundary: SchemaCompatibilityBoundaryV0,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityBoundaryV0 {
    pub field_mapping_policy: String,
    pub deprecated_fields: Vec<String>,
    pub new_required_assumptions: Vec<String>,
    pub coverage_exactness_boundary: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityPolicyV0 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub policy_id: String,
    pub policy_version: String,
    pub applies_to_catalog_version: String,
    pub dimensions: Vec<SchemaCompatibilityDimensionV0>,
    pub required_checks: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityDimensionV0 {
    pub dimension: String,
    pub required_metadata: Vec<String>,
    pub checker_boundary: String,
}
