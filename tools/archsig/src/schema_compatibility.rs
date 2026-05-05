use std::collections::BTreeSet;

use serde_json::Value;

use crate::{
    SCHEMA_COMPATIBILITY_CHECK_REPORT_SCHEMA_VERSION, SchemaArtifactCompatibilityV0,
    SchemaCompatibilityArtifactRefV0, SchemaCompatibilityCheckReportV0,
    SchemaCompatibilityCheckSummaryV0, SchemaCompatibilityCheckV0, SchemaCompatibilityPolicyV0,
    SchemaCoverageExactnessBoundaryV0, SchemaVersionCatalogEntryV0, SchemaVersionCatalogV0,
};

pub fn build_schema_compatibility_check_report(
    before: &Value,
    before_path: &str,
    after: &Value,
    after_path: &str,
    catalog: &SchemaVersionCatalogV0,
) -> SchemaCompatibilityCheckReportV0 {
    let before_schema = schema_version(before);
    let after_schema = schema_version(after);
    let before_entry = before_schema.and_then(|version| catalog_entry(catalog, version));
    let after_entry = after_schema.and_then(|version| catalog_entry(catalog, version));
    let before_metadata = schema_compatibility_metadata(before);
    let after_metadata = schema_compatibility_metadata(after);
    let before_metadata_parse_failed =
        before.get("schemaCompatibility").is_some() && before_metadata.is_none();
    let after_metadata_parse_failed =
        after.get("schemaCompatibility").is_some() && after_metadata.is_none();

    let mut checks = Vec::new();
    checks.push(check_known_schema_version(
        "before-schema-version-known",
        "before",
        before_schema,
        before_entry,
    ));
    checks.push(check_known_schema_version(
        "after-schema-version-known",
        "after",
        after_schema,
        after_entry,
    ));
    checks.push(check_schema_compatibility_metadata_parse(
        "before-schema-compatibility-metadata-parses",
        "before",
        before_metadata_parse_failed,
    ));
    checks.push(check_schema_compatibility_metadata_parse(
        "after-schema-compatibility-metadata-parses",
        "after",
        after_metadata_parse_failed,
    ));
    checks.push(check_schema_version_delta(
        before_schema,
        after_schema,
        after_metadata.as_ref(),
    ));
    checks.push(check_metadata_presence(
        before_schema,
        after_schema,
        after_entry,
        after_metadata.as_ref(),
    ));

    if let Some(metadata) = after_metadata.as_ref() {
        checks.extend(check_metadata_completeness(
            metadata,
            &catalog.compatibility_policy,
        ));
        checks.extend(check_formal_claim_promotion_boundary(metadata));
        checks.extend(check_deprecated_fields(metadata));
    }
    if let (Some(before_metadata), Some(after_metadata)) =
        (before_metadata.as_ref(), after_metadata.as_ref())
    {
        checks.extend(check_preserved_metadata(before_metadata, after_metadata));
    }

    let non_conclusions = merged_non_conclusions(catalog, after_metadata.as_ref());
    let field_mappings = after_metadata
        .as_ref()
        .map(|metadata| metadata.field_mappings.clone())
        .unwrap_or_default();
    let deprecated_fields = after_metadata
        .as_ref()
        .map(|metadata| metadata.deprecated_fields.clone())
        .unwrap_or_default();
    let new_required_assumptions = after_metadata
        .as_ref()
        .map(|metadata| metadata.required_assumptions.clone())
        .unwrap_or_default();
    let coverage_exactness_boundaries = after_metadata
        .as_ref()
        .map(|metadata| metadata.coverage_exactness_boundaries.clone())
        .unwrap_or_default();

    let summary = summarize_checks(&checks);

    SchemaCompatibilityCheckReportV0 {
        schema_version: SCHEMA_COMPATIBILITY_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        checker_id: "archsig-b9-schema-compatibility-checker-v0".to_string(),
        compatibility_policy_ref: catalog.compatibility_policy.policy_version.clone(),
        before: artifact_ref(
            before_path,
            before_schema,
            before_entry,
            before_metadata.is_some(),
        ),
        after: artifact_ref(
            after_path,
            after_schema,
            after_entry,
            after_metadata.is_some(),
        ),
        summary,
        checks,
        field_mappings,
        deprecated_fields,
        new_required_assumptions,
        coverage_exactness_boundaries,
        non_conclusions,
    }
}

fn schema_version(value: &Value) -> Option<&str> {
    value.get("schemaVersion").and_then(Value::as_str)
}

fn catalog_entry<'a>(
    catalog: &'a SchemaVersionCatalogV0,
    schema_version: &str,
) -> Option<&'a SchemaVersionCatalogEntryV0> {
    catalog
        .artifacts
        .iter()
        .find(|artifact| artifact.schema_version_name == schema_version)
}

fn schema_compatibility_metadata(value: &Value) -> Option<SchemaArtifactCompatibilityV0> {
    value
        .get("schemaCompatibility")
        .and_then(|metadata| serde_json::from_value(metadata.clone()).ok())
}

fn artifact_ref(
    path: &str,
    schema_version: Option<&str>,
    entry: Option<&SchemaVersionCatalogEntryV0>,
    has_schema_compatibility_metadata: bool,
) -> SchemaCompatibilityArtifactRefV0 {
    SchemaCompatibilityArtifactRefV0 {
        path: path.to_string(),
        artifact_id: entry.map(|entry| entry.artifact_id.clone()),
        schema_version_name: schema_version.map(str::to_string),
        catalog_status: entry
            .map(|entry| entry.status.clone())
            .unwrap_or_else(|| "unknown".to_string()),
        has_schema_compatibility_metadata,
    }
}

fn check_known_schema_version(
    id: &str,
    side: &str,
    schema_version: Option<&str>,
    entry: Option<&SchemaVersionCatalogEntryV0>,
) -> SchemaCompatibilityCheckV0 {
    match (schema_version, entry) {
        (Some(version), Some(entry)) => check(
            id,
            "schema_version",
            "pass",
            "compatible",
            format!(
                "{side} schemaVersion `{version}` is cataloged as `{}`",
                entry.artifact_id
            ),
            None,
            None,
        ),
        (Some(version), None) => check(
            id,
            "schema_version",
            "fail",
            "fail",
            format!("{side} schemaVersion `{version}` is not present in the B9 catalog"),
            Some("add a catalog entry or provide an explicit compatibility policy".to_string()),
            Some("unknown schemaVersion is not evidence of semantic preservation".to_string()),
        ),
        (None, _) => check(
            id,
            "schema_version",
            "fail",
            "fail",
            format!("{side} artifact does not declare schemaVersion"),
            Some("declare schemaVersion before running migration checks".to_string()),
            Some("missing schemaVersion is not evidence of extractor completeness".to_string()),
        ),
    }
}

fn check_schema_version_delta(
    before_schema: Option<&str>,
    after_schema: Option<&str>,
    after_metadata: Option<&SchemaArtifactCompatibilityV0>,
) -> SchemaCompatibilityCheckV0 {
    if before_schema == after_schema {
        return check(
            "schema-version-delta",
            "field_mapping",
            "pass",
            "compatible",
            "schemaVersion is unchanged".to_string(),
            None,
            Some("unchanged schemaVersion does not prove semantic preservation".to_string()),
        );
    }

    if after_metadata
        .map(|metadata| !metadata.field_mappings.is_empty())
        .unwrap_or(false)
    {
        check(
            "schema-version-delta",
            "field_mapping",
            "requiresMigration",
            "migrationRequired",
            "schemaVersion changed and explicit field mappings are present".to_string(),
            Some("review the declared field mappings before accepting the migration".to_string()),
            Some("field mapping does not prove semantic preservation".to_string()),
        )
    } else {
        check(
            "schema-version-delta",
            "field_mapping",
            "requiresMigration",
            "migrationRequired",
            "schemaVersion changed without explicit field mappings".to_string(),
            Some("add schemaCompatibility.fieldMappings for renamed, removed, split, or merged fields".to_string()),
            Some("renamed fields do not discharge new required assumptions".to_string()),
        )
    }
}

fn check_schema_compatibility_metadata_parse(
    id: &str,
    side: &str,
    parse_failed: bool,
) -> SchemaCompatibilityCheckV0 {
    if parse_failed {
        check(
            id,
            "coverage_exactness_boundary",
            "fail",
            "fail",
            format!("{side} schemaCompatibility metadata is malformed"),
            Some("make schemaCompatibility match SchemaArtifactCompatibilityV0".to_string()),
            Some("malformed compatibility metadata is not a migration proof".to_string()),
        )
    } else {
        check(
            id,
            "coverage_exactness_boundary",
            "pass",
            "compatible",
            format!("{side} schemaCompatibility metadata is parseable or absent"),
            None,
            None,
        )
    }
}

fn check_metadata_presence(
    before_schema: Option<&str>,
    after_schema: Option<&str>,
    after_entry: Option<&SchemaVersionCatalogEntryV0>,
    after_metadata: Option<&SchemaArtifactCompatibilityV0>,
) -> SchemaCompatibilityCheckV0 {
    if after_metadata.is_some() {
        return check(
            "schema-compatibility-metadata-present",
            "coverage_exactness_boundary",
            "pass",
            "compatible",
            "after artifact carries schemaCompatibility metadata".to_string(),
            None,
            None,
        );
    }

    let same_schema = before_schema == after_schema;
    let artifact = after_entry
        .map(|entry| entry.artifact_id.as_str())
        .unwrap_or("unknown artifact");
    if same_schema {
        check(
            "schema-compatibility-metadata-present",
            "coverage_exactness_boundary",
            "pass",
            "warning",
            format!("{artifact} has no schemaCompatibility metadata; accepted as backward-compatible input"),
            Some("new B9 AIR / Feature Extension Report outputs should emit schemaCompatibility metadata".to_string()),
            Some("legacy metadata absence is not measured-zero evidence".to_string()),
        )
    } else {
        check(
            "schema-compatibility-metadata-present",
            "coverage_exactness_boundary",
            "requiresMigration",
            "migrationRequired",
            format!("{artifact} changes schema boundary without schemaCompatibility metadata"),
            Some("add field mapping, required assumptions, coverage / exactness boundary, and non-conclusions".to_string()),
            Some("schema migration without metadata is not semantic preservation".to_string()),
        )
    }
}

fn check_metadata_completeness(
    metadata: &SchemaArtifactCompatibilityV0,
    policy: &SchemaCompatibilityPolicyV0,
) -> Vec<SchemaCompatibilityCheckV0> {
    vec![
        nonempty_check(
            "field-mappings-explicit",
            "field_mapping",
            !metadata.field_mappings.is_empty(),
            "field mappings are explicit",
            "schemaCompatibility.fieldMappings is empty",
            "declare stable, renamed, removed, split, or merged field mappings",
            "field mapping does not prove semantic preservation",
        ),
        nonempty_check(
            "required-assumptions-surfaced",
            "new_required_assumptions",
            !metadata.required_assumptions.is_empty(),
            "new required assumptions are surfaced",
            "schemaCompatibility.requiredAssumptions is empty",
            "surface new theorem, coverage, projection, exactness, or review assumptions",
            "new assumptions are not discharged by field names alone",
        ),
        nonempty_check(
            "coverage-exactness-boundaries-present",
            "coverage_exactness_boundary",
            !metadata.coverage_exactness_boundaries.is_empty(),
            "coverage / exactness boundaries are present",
            "schemaCompatibility.coverageExactnessBoundaries is empty",
            "record measurement boundaries, coverage assumptions, and exactness assumptions",
            "coverage gaps are not measured-zero evidence",
        ),
        nonempty_check(
            "non-conclusions-present",
            "non_conclusions",
            !metadata.non_conclusions.is_empty() && !policy.non_conclusions.is_empty(),
            "non-conclusions are present",
            "schemaCompatibility.nonConclusions is empty",
            "preserve or strengthen non-conclusion guardrails",
            "compatibility pass is not a Lean theorem package",
        ),
    ]
}

fn check_formal_claim_promotion_boundary(
    metadata: &SchemaArtifactCompatibilityV0,
) -> Vec<SchemaCompatibilityCheckV0> {
    let non_conclusions = metadata
        .non_conclusions
        .iter()
        .map(|value| value.to_ascii_lowercase())
        .collect::<Vec<_>>();
    let has_lean_theorem_boundary = non_conclusions
        .iter()
        .any(|value| value.contains("lean theorem") || value.contains("formal claim"));
    let has_semantic_boundary = non_conclusions
        .iter()
        .any(|value| value.contains("semantic preservation"));
    let has_extractor_boundary = non_conclusions
        .iter()
        .any(|value| value.contains("extractor completeness"));
    let assumption_fallbacks_block_claims =
        metadata.required_assumptions.iter().all(|assumption| {
            let fallback = assumption.fallback_when_missing.to_ascii_lowercase();
            fallback.contains("undischarged")
                || fallback.contains("missing")
                || fallback.contains("do not infer")
                || fallback.contains("formal claim")
        });

    vec![
        boundary_check(
            "semantic-preservation-non-conclusion-preserved",
            "non_conclusions",
            has_semantic_boundary,
            "semantic preservation is kept as a non-conclusion",
            "schemaCompatibility.nonConclusions does not mention semantic preservation",
            "preserve the semantic-preservation non-conclusion",
            "schema compatibility does not prove semantic preservation",
        ),
        boundary_check(
            "extractor-completeness-non-conclusion-preserved",
            "non_conclusions",
            has_extractor_boundary,
            "extractor completeness is kept as a non-conclusion",
            "schemaCompatibility.nonConclusions does not mention extractor completeness",
            "preserve the extractor-completeness non-conclusion",
            "schema compatibility does not prove extractor completeness",
        ),
        boundary_check(
            "formal-claim-promotion-blocked",
            "non_conclusions",
            has_lean_theorem_boundary,
            "formal claim promotion is blocked by non-conclusion metadata",
            "schemaCompatibility.nonConclusions does not block Lean theorem / formal claim promotion",
            "add a non-conclusion that compatibility pass does not promote tooling evidence to a Lean theorem claim",
            "compatibility pass does not promote tooling evidence to a Lean theorem claim",
        ),
        boundary_check(
            "required-assumptions-do-not-discharge-formal-claims",
            "new_required_assumptions",
            assumption_fallbacks_block_claims,
            "missing assumptions remain missing or undischarged",
            "a required assumption fallback could discharge a formal claim implicitly",
            "make fallbackWhenMissing report missing / undischarged assumptions without inferring formal claims",
            "new required assumptions are not discharged by migration",
        ),
    ]
}

fn check_deprecated_fields(
    metadata: &SchemaArtifactCompatibilityV0,
) -> Vec<SchemaCompatibilityCheckV0> {
    if metadata.deprecated_fields.is_empty() {
        return vec![check(
            "deprecated-fields-declare-reader-behavior",
            "deprecated_fields",
            "pass",
            "compatible",
            "no deprecated fields are declared".to_string(),
            None,
            None,
        )];
    }

    metadata
        .deprecated_fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            let valid = !field.field.is_empty()
                && !field.removal_phase.is_empty()
                && (field.replacement.as_ref().is_some_and(|value| !value.is_empty())
                    || !field.reader_behavior.is_empty());
            if valid {
                check(
                    &format!("deprecated-field-{index}-reader-behavior"),
                    "deprecated_fields",
                    "pass",
                    "compatible",
                    format!("deprecated field `{}` declares replacement or reader behavior", field.field),
                    None,
                    Some("deprecated field support does not prove semantic preservation".to_string()),
                )
            } else {
                check(
                    &format!("deprecated-field-{index}-reader-behavior"),
                    "deprecated_fields",
                    "fail",
                    "fail",
                    format!("deprecated field `{}` is missing replacement, removal phase, or reader behavior", field.field),
                    Some("declare replacement or reader behavior and removal phase for deprecated fields".to_string()),
                    Some("deprecated field compatibility is not semantic preservation".to_string()),
                )
            }
        })
        .collect()
}

fn check_preserved_metadata(
    before: &SchemaArtifactCompatibilityV0,
    after: &SchemaArtifactCompatibilityV0,
) -> Vec<SchemaCompatibilityCheckV0> {
    let before_non_conclusions: BTreeSet<_> = before.non_conclusions.iter().cloned().collect();
    let after_non_conclusions: BTreeSet<_> = after.non_conclusions.iter().cloned().collect();
    let missing_non_conclusions = before_non_conclusions
        .difference(&after_non_conclusions)
        .cloned()
        .collect::<Vec<_>>();
    let before_boundaries: BTreeSet<_> = before
        .coverage_exactness_boundaries
        .iter()
        .map(boundary_key)
        .collect();
    let after_boundaries: BTreeSet<_> = after
        .coverage_exactness_boundaries
        .iter()
        .map(boundary_key)
        .collect();
    let missing_boundaries = before_boundaries
        .difference(&after_boundaries)
        .cloned()
        .collect::<Vec<_>>();

    vec![
        if missing_non_conclusions.is_empty() {
            check(
                "non-conclusions-preserved",
                "non_conclusions",
                "pass",
                "compatible",
                "before non-conclusions are preserved or strengthened".to_string(),
                None,
                Some("preserved non-conclusions do not prove architecture lawfulness".to_string()),
            )
        } else {
            check(
                "non-conclusions-preserved",
                "non_conclusions",
                "blockedFormalClaimPromotion",
                "blockedFormalClaimPromotion",
                format!(
                    "after artifact dropped non-conclusions: {}",
                    missing_non_conclusions.join(", ")
                ),
                Some(
                    "restore dropped non-conclusions or replace them with stricter guardrails"
                        .to_string(),
                ),
                Some("dropped non-conclusions can over-promote tooling evidence".to_string()),
            )
        },
        if missing_boundaries.is_empty() {
            check(
                "coverage-exactness-boundaries-preserved",
                "coverage_exactness_boundary",
                "pass",
                "compatible",
                "before coverage / exactness boundaries are preserved".to_string(),
                None,
                Some(
                    "preserved coverage metadata does not imply extractor completeness".to_string(),
                ),
            )
        } else {
            check(
                "coverage-exactness-boundaries-preserved",
                "coverage_exactness_boundary",
                "requiresMigration",
                "migrationRequired",
                format!(
                    "after artifact dropped coverage / exactness boundaries: {}",
                    missing_boundaries.join(", ")
                ),
                Some(
                    "restore dropped boundary metadata or add an explicit migration note"
                        .to_string(),
                ),
                Some("missing coverage is not measured zero".to_string()),
            )
        },
    ]
}

fn nonempty_check(
    id: &str,
    dimension: &str,
    is_present: bool,
    pass_message: &str,
    missing_message: &str,
    required_action: &str,
    non_conclusion: &str,
) -> SchemaCompatibilityCheckV0 {
    if is_present {
        check(
            id,
            dimension,
            "pass",
            "compatible",
            pass_message.to_string(),
            None,
            Some(non_conclusion.to_string()),
        )
    } else {
        check(
            id,
            dimension,
            "requiresMigration",
            "migrationRequired",
            missing_message.to_string(),
            Some(required_action.to_string()),
            Some(non_conclusion.to_string()),
        )
    }
}

fn boundary_check(
    id: &str,
    dimension: &str,
    valid: bool,
    pass_message: &str,
    missing_message: &str,
    required_action: &str,
    non_conclusion: &str,
) -> SchemaCompatibilityCheckV0 {
    if valid {
        check(
            id,
            dimension,
            "pass",
            "compatible",
            pass_message.to_string(),
            None,
            Some(non_conclusion.to_string()),
        )
    } else {
        check(
            id,
            dimension,
            "blockedFormalClaimPromotion",
            "blockedFormalClaimPromotion",
            missing_message.to_string(),
            Some(required_action.to_string()),
            Some(non_conclusion.to_string()),
        )
    }
}

fn check(
    id: &str,
    dimension: &str,
    result: &str,
    severity: &str,
    message: String,
    required_action: Option<String>,
    non_conclusion: Option<String>,
) -> SchemaCompatibilityCheckV0 {
    SchemaCompatibilityCheckV0 {
        id: id.to_string(),
        dimension: dimension.to_string(),
        result: result.to_string(),
        severity: severity.to_string(),
        message,
        required_action,
        non_conclusion,
    }
}

fn boundary_key(boundary: &SchemaCoverageExactnessBoundaryV0) -> String {
    format!(
        "{}:{}",
        boundary.axis_or_layer, boundary.measurement_boundary
    )
}

fn merged_non_conclusions(
    catalog: &SchemaVersionCatalogV0,
    after_metadata: Option<&SchemaArtifactCompatibilityV0>,
) -> Vec<String> {
    let mut non_conclusions = BTreeSet::new();
    non_conclusions.extend(catalog.non_conclusions.iter().cloned());
    non_conclusions.extend(catalog.compatibility_policy.non_conclusions.iter().cloned());
    if let Some(metadata) = after_metadata {
        non_conclusions.extend(metadata.non_conclusions.iter().cloned());
    }
    non_conclusions.into_iter().collect()
}

fn summarize_checks(checks: &[SchemaCompatibilityCheckV0]) -> SchemaCompatibilityCheckSummaryV0 {
    let compatible_diff_count = checks
        .iter()
        .filter(|check| check.severity == "compatible")
        .count();
    let migration_required_count = checks
        .iter()
        .filter(|check| check.severity == "migrationRequired")
        .count();
    let blocked_formal_claim_promotion_count = checks
        .iter()
        .filter(|check| check.severity == "blockedFormalClaimPromotion")
        .count();
    let warning_count = checks
        .iter()
        .filter(|check| check.severity == "warning")
        .count();

    let result = if checks.iter().any(|check| check.severity == "fail") {
        "fail"
    } else if blocked_formal_claim_promotion_count > 0 {
        "blockedFormalClaimPromotion"
    } else if migration_required_count > 0 {
        "requiresMigration"
    } else {
        "pass"
    };

    SchemaCompatibilityCheckSummaryV0 {
        result: result.to_string(),
        compatible_diff_count,
        migration_required_count,
        blocked_formal_claim_promotion_count,
        warning_count,
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::static_schema_version_catalog;

    #[test]
    fn unchanged_cataloged_artifact_without_metadata_is_backward_compatible() {
        let catalog = static_schema_version_catalog();
        let artifact = json!({"schemaVersion": "archsig-sig0-v0"});
        let report = build_schema_compatibility_check_report(
            &artifact,
            "before.json",
            &artifact,
            "after.json",
            &catalog,
        );

        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.warning_count, 1);
        assert!(
            report
                .non_conclusions
                .iter()
                .any(|item| item.contains("semantic"))
        );
    }

    #[test]
    fn missing_formal_claim_guardrail_blocks_report() {
        let catalog = static_schema_version_catalog();
        let before = json!({
            "schemaVersion": "aat-air-v0",
            "schemaCompatibility": {
                "artifactId": "air",
                "schemaVersionName": "aat-air-v0",
                "compatibilityPolicyRef": "b9-compatibility-policy-v0",
                "fieldMappings": [{"sourceField": "claims[].nonConclusions", "targetField": "claims[].nonConclusions", "mappingKind": "stable", "requiredReview": "preserve guardrails"}],
                "deprecatedFields": [],
                "requiredAssumptions": [{"assumptionId": "a", "appliesTo": "air", "requiredFor": "schema compatibility review", "fallbackWhenMissing": "report as undischarged; do not infer a formal claim"}],
                "coverageExactnessBoundaries": [{"axisOrLayer": "static", "measurementBoundary": "bounded", "coverageAssumptions": ["scope"], "exactnessAssumptions": ["exact"]}],
                "nonConclusions": ["schema compatibility metadata does not prove semantic preservation", "schema compatibility metadata does not imply extractor completeness", "compatibility pass does not promote tooling evidence to a Lean theorem claim"]
            }
        });
        let mut after = before.clone();
        after["schemaCompatibility"]["nonConclusions"] =
            json!(["schema compatibility metadata does not prove semantic preservation"]);

        let report = build_schema_compatibility_check_report(
            &before,
            "before.json",
            &after,
            "after.json",
            &catalog,
        );

        assert_eq!(report.summary.result, "blockedFormalClaimPromotion");
        assert!(report.checks.iter().any(|check| {
            check.id == "formal-claim-promotion-blocked"
                && check.result == "blockedFormalClaimPromotion"
        }));
    }
}
