use crate::{
    AIR_SCHEMA_VERSION, ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
    CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION,
    DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
    FEATURE_EXTENSION_REPORT_SCHEMA_VERSION, OBSTRUCTION_WITNESS_SCHEMA_VERSION,
    REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION, SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION,
    SCHEMA_VERSION, SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
    SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0, SchemaVersionCatalogEntryV0,
    SchemaVersionCatalogV0,
};

pub fn static_schema_version_catalog() -> SchemaVersionCatalogV0 {
    let catalog_version = "b10-schema-catalog-v0";
    SchemaVersionCatalogV0 {
        schema_version: SCHEMA_VERSION_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-b9-b10-schema-version-catalog".to_string(),
        catalog_version: catalog_version.to_string(),
        phase: "B9 Schema standardization and compatibility / B10 operational feedback".to_string(),
        artifacts: vec![
            artifact(
                "signature-artifact",
                "Architecture Signature artifact",
                SCHEMA_VERSION,
                "extractor-output",
                "B0-B8",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#4-architecture-signature-artifact-layer",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec![],
                compatibility_boundary(
                    "Map component/relation/signature fields by stable camelCase names; new axes must be added with metricStatus boundary metadata.",
                    vec![],
                    vec![
                        "New required axes must declare measuredZero/measuredNonzero/unmeasured/outOfScope semantics.",
                    ],
                    vec![
                        "metricStatus is the compatibility boundary for coverage and exactness of Sig0 axes.",
                    ],
                ),
            ),
            artifact(
                "air",
                "Architecture Intermediate Representation",
                AIR_SCHEMA_VERSION,
                "intermediate-representation",
                "B0-B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#31-air-v0-schema",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec!["#608", "#609"],
                compatibility_boundary(
                    "Map ids, relation refs, evidence refs, claims, coverage layers, and theorem-package refs explicitly; never infer a formal claim from renamed fields.",
                    vec![],
                    vec![
                        "New required theorem, coverage, projection, or exactness assumptions must be listed in claims or coverage layers.",
                    ],
                    vec![
                        "AIR coverage layers and claim classifications are the exactness boundary for report generation.",
                    ],
                ),
            ),
            artifact(
                "feature-extension-report",
                "Feature Extension Report",
                FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
                "review-output",
                "B1-B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#5-feature-extension-report",
                    "docs/design/archsig_tooling_index.md",
                ],
                vec!["#608", "#609"],
                compatibility_boundary(
                    "Map review summary, witness, theorem precondition, coverage gap, repair suggestion, and non-conclusion fields separately.",
                    vec![],
                    vec![
                        "New required review assumptions must appear in discharged/undischarged assumptions or theorem precondition checks.",
                    ],
                    vec![
                        "Coverage gaps, runtime summary, semantic summary, and non-conclusions delimit report exactness.",
                    ],
                ),
            ),
            artifact(
                "obstruction-witness",
                "Obstruction Witness",
                OBSTRUCTION_WITNESS_SCHEMA_VERSION,
                "embedded-witness",
                "B1-B9",
                "implemented",
                vec!["docs/aat_v2_tooling_design.md#6-obstruction-witness-schema"],
                vec!["#608", "#610"],
                compatibility_boundary(
                    "Map witness id, layer, kind, extension role, classification, evidence, theorem refs, claim classification, measurement boundary, and non-conclusions independently.",
                    vec![],
                    vec![
                        "New witness kinds must declare layer, evidence requirements, measurement boundary, and non-conclusions.",
                    ],
                    vec![
                        "Witness measurement boundary and claim classification distinguish measured evidence from formal theorem claims.",
                    ],
                ),
            ),
            artifact(
                "architecture-drift-ledger",
                "Architecture Drift Ledger",
                ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
                "batch-history-output",
                "B1-B9",
                "implemented",
                vec!["docs/aat_v2_tooling_design.md#51-architecture-drift-ledger"],
                vec!["#608", "#610"],
                compatibility_boundary(
                    "Map stable grouping keys, aggregation window, source, metric, status, suppression, repair, witness, claim, and non-conclusion fields separately.",
                    vec![],
                    vec![
                        "New batch metrics must declare grouping key, aggregation window, measurement boundary, and evidence refs.",
                    ],
                    vec![
                        "Ledger status and suppression metadata are operational state, not formal proof state.",
                    ],
                ),
            ),
            artifact(
                "detectable-values-reported-axes-catalog",
                "Detectable values / reported axes catalog",
                DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
                "axis-catalog",
                "B9",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#41-detectable-values--reported-axes",
                    "docs/design/schema_version_catalog.md#detectable-values--reported-axes-catalog",
                ],
                vec!["#608"],
                compatibility_boundary(
                    "Map axis id, layer, value type, measurement boundary, evidence requirements, theorem refs, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New reported axes must declare whether unmeasured differs from measured zero.",
                    ],
                    vec![
                        "Axis coverage and exactness metadata delimit what a zero or nonzero value can support.",
                    ],
                ),
            ),
            artifact(
                "report-outcome-daily-ledger",
                "Report outcome daily ledger",
                REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION,
                "operational-feedback-output",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#report-outcome-daily-ledger-metadata",
                ],
                vec!["#620"],
                compatibility_boundary(
                    "Map aggregation window, source report refs, retention policy, outcome metric summaries, missing/private/unmeasured boundaries, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New daily batch metrics must preserve source report refs, retention policy, and missing/private/unmeasured boundary counts.",
                    ],
                    vec![
                        "Missing, private, unavailable, and unmeasured outcome data delimit the operational feedback exactness boundary.",
                    ],
                ),
            ),
            artifact(
                "calibration-review-record",
                "Calibration review record",
                CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION,
                "operational-feedback-input",
                "B10",
                "implemented",
                vec![
                    "docs/aat_v2_tooling_design.md#phase-b10-operational-feedback-loop",
                    "docs/design/schema_version_catalog.md#calibration-review-record-metadata",
                ],
                vec!["#621", "#622"],
                compatibility_boundary(
                    "Map report finding refs, witness refs, reviewer decision, outcome refs, confidence, missing evidence, calibration input, and non-conclusions separately.",
                    vec![],
                    vec![
                        "New calibration fields must preserve missing / private evidence boundaries and formal-claim non-conclusions.",
                    ],
                    vec![
                        "Reviewer decision, confidence, missing evidence, and calibration input delimit empirical policy tuning exactness.",
                    ],
                ),
            ),
        ],
        compatibility_policy: compatibility_policy(catalog_version),
        non_conclusions: vec![
            "schema migration is not a semantic-preservation theorem".to_string(),
            "catalog membership does not imply extractor completeness".to_string(),
            "compatibility pass does not imply architecture lawfulness".to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

fn artifact(
    artifact_id: &str,
    artifact_name: &str,
    schema_version_name: &str,
    artifact_role: &str,
    owner_phase: &str,
    status: &str,
    primary_docs: Vec<&str>,
    downstream_issues: Vec<&str>,
    compatibility_boundary: SchemaCompatibilityBoundaryV0,
) -> SchemaVersionCatalogEntryV0 {
    SchemaVersionCatalogEntryV0 {
        artifact_id: artifact_id.to_string(),
        artifact_name: artifact_name.to_string(),
        schema_version_name: schema_version_name.to_string(),
        artifact_role: artifact_role.to_string(),
        owner_phase: owner_phase.to_string(),
        status: status.to_string(),
        primary_docs: primary_docs.into_iter().map(str::to_string).collect(),
        downstream_issues: downstream_issues.into_iter().map(str::to_string).collect(),
        compatibility_boundary,
    }
}

fn compatibility_boundary(
    field_mapping_policy: &str,
    deprecated_fields: Vec<&str>,
    new_required_assumptions: Vec<&str>,
    coverage_exactness_boundary: Vec<&str>,
) -> SchemaCompatibilityBoundaryV0 {
    SchemaCompatibilityBoundaryV0 {
        field_mapping_policy: field_mapping_policy.to_string(),
        deprecated_fields: deprecated_fields.into_iter().map(str::to_string).collect(),
        new_required_assumptions: new_required_assumptions
            .into_iter()
            .map(str::to_string)
            .collect(),
        coverage_exactness_boundary: coverage_exactness_boundary
            .into_iter()
            .map(str::to_string)
            .collect(),
        non_conclusions: vec![
            "field mapping does not prove semantic preservation".to_string(),
            "missing coverage is not measured zero".to_string(),
            "renamed fields do not discharge new required assumptions".to_string(),
        ],
    }
}

fn compatibility_policy(catalog_version: &str) -> SchemaCompatibilityPolicyV0 {
    SchemaCompatibilityPolicyV0 {
        schema_version: SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION.to_string(),
        policy_id: "archsig-b9-schema-compatibility-policy".to_string(),
        policy_version: "b9-compatibility-policy-v0".to_string(),
        applies_to_catalog_version: catalog_version.to_string(),
        dimensions: vec![
            dimension(
                "field_mapping",
                vec![
                    "sourceField",
                    "targetField",
                    "mappingKind",
                    "requiredReview",
                ],
                "A checker may validate declared field mappings, but it must not infer semantic equivalence.",
            ),
            dimension(
                "deprecated_fields",
                vec!["field", "replacement", "removalPhase", "readerBehavior"],
                "Deprecated fields remain compatibility metadata until removal; migration must preserve explicit reader behavior.",
            ),
            dimension(
                "new_required_assumptions",
                vec![
                    "assumptionId",
                    "appliesTo",
                    "requiredFor",
                    "fallbackWhenMissing",
                ],
                "New assumptions must be reported as missing or undischarged unless explicit evidence is present.",
            ),
            dimension(
                "non_conclusions",
                vec!["nonConclusion", "appliesTo", "reason"],
                "Non-conclusions are mandatory guardrails and cannot be dropped by migration.",
            ),
            dimension(
                "coverage_exactness_boundary",
                vec![
                    "axisOrLayer",
                    "measurementBoundary",
                    "coverageAssumptions",
                    "exactnessAssumptions",
                ],
                "Coverage and exactness metadata delimit what any reported value can support.",
            ),
        ],
        required_checks: vec![
            "known schemaVersion in catalog".to_string(),
            "field mapping entries are explicit for renamed or removed fields".to_string(),
            "deprecated fields declare replacement or removal behavior".to_string(),
            "new required assumptions are surfaced as missing until discharged".to_string(),
            "non-conclusions are preserved or strengthened".to_string(),
            "coverage and exactness metadata are not dropped".to_string(),
        ],
        non_conclusions: vec![
            "compatibility policy is not a proof of semantic preservation".to_string(),
            "compatibility policy is not evidence of extractor completeness".to_string(),
            "compatibility policy is not a Lean theorem package".to_string(),
        ],
    }
}

fn dimension(
    dimension: &str,
    required_metadata: Vec<&str>,
    checker_boundary: &str,
) -> SchemaCompatibilityDimensionV0 {
    SchemaCompatibilityDimensionV0 {
        dimension: dimension.to_string(),
        required_metadata: required_metadata.into_iter().map(str::to_string).collect(),
        checker_boundary: checker_boundary.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn static_catalog_records_b9_schema_versions_and_boundaries() {
        let catalog = static_schema_version_catalog();
        assert_eq!(
            catalog.schema_version,
            SCHEMA_VERSION_CATALOG_SCHEMA_VERSION
        );
        assert_eq!(
            catalog.compatibility_policy.schema_version,
            SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION
        );
        assert!(
            catalog
                .non_conclusions
                .contains(&"schema migration is not a semantic-preservation theorem".to_string())
        );

        let versions: BTreeSet<_> = catalog
            .artifacts
            .iter()
            .map(|artifact| artifact.schema_version_name.as_str())
            .collect();
        for expected in [
            SCHEMA_VERSION,
            AIR_SCHEMA_VERSION,
            FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
            OBSTRUCTION_WITNESS_SCHEMA_VERSION,
            ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
            DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
            CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION,
        ] {
            assert!(
                versions.contains(expected),
                "missing schema version {expected}"
            );
        }

        for artifact in &catalog.artifacts {
            assert!(
                !artifact
                    .compatibility_boundary
                    .field_mapping_policy
                    .is_empty()
            );
            assert!(!artifact.compatibility_boundary.non_conclusions.is_empty());
            assert!(
                artifact
                    .compatibility_boundary
                    .non_conclusions
                    .iter()
                    .any(|non_conclusion| non_conclusion.contains("semantic preservation"))
            );
        }
    }

    #[test]
    fn canonical_fixture_matches_static_catalog() {
        let fixture: SchemaVersionCatalogV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/schema_version_catalog.json"
        ))
        .expect("schema version catalog fixture parses");
        assert_eq!(fixture, static_schema_version_catalog());
    }
}
