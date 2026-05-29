use crate::{
    ARCHMAP_SCHEMA_VERSION, ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION, LAW_POLICY_SCHEMA_VERSION,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
    SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0, SchemaVersionCatalogEntryV0,
    SchemaVersionCatalogV0,
};

pub fn static_schema_version_catalog() -> SchemaVersionCatalogV0 {
    SchemaVersionCatalogV0 {
        schema_version: SCHEMA_VERSION_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-llm-atom-schema-version-catalog".to_string(),
        catalog_version: "llm-atom-archmap-v0".to_string(),
        phase: "LLM Atom ArchMap primary workflow".to_string(),
        artifacts: vec![
            artifact(
                "archmap",
                "LLM-native ArchMap Atom observation artifact",
                ARCHMAP_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/atom_handoff.md",
                ],
                "ArchMap records source-grounded atomObservations, moleculeObservations, semanticObservations, observationGaps, projectionInfo, concernHints, provenance, and nonConclusions without selecting laws or constructing obstruction circuits.",
                vec![
                    "ArchMap does not prove architecture lawfulness, obstruction existence, zero curvature, or certified atom truth.",
                    "ArchMap concern hints are review cues until ArchSig combines them with a selected LawPolicy.",
                ],
            ),
            artifact(
                "archmap-validation-report",
                "ArchMap validation report",
                ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                "ArchMap validation checks source refs, claim boundaries, projection separation, atom observation summaries, and responsibility boundaries without promoting observations to formal truth.",
                vec![
                    "Validation pass does not imply semantic correctness, architecture lawfulness, source completeness, zero curvature, or Lean theorem discharge.",
                    "Validation diagnostics are bounded tool checks, not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "law-policy",
                "Selected LawPolicy artifact",
                LAW_POLICY_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/README.md",
                ],
                "LawPolicy owns selected laws, witness rules, molecule patterns, obstruction definitions, signature axis definitions, exactness assumptions, coverage requirements, excluded readings, and non-conclusions separately from ArchMap observations.",
                vec![
                    "LawPolicy is selected analysis policy, not AAT itself, architecture lawfulness, atom truth, or Lean theorem discharge.",
                    "Adding a law family must preserve missing coverage as distinct from measured zero.",
                ],
            ),
            artifact(
                "law-policy-validation-report",
                "LawPolicy validation report",
                LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                "LawPolicy validation checks schema support, identity, id uniqueness, law/witness/axis references, coverage, exactness, and non-conclusion guardrails.",
                vec![
                    "Validation pass does not imply architecture lawfulness, certified atom truth, zero curvature, or Lean theorem discharge.",
                    "Policy validation is not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "archsig-analysis-packet",
                "ArchSig AAT analysis packet",
                ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec![
                    "docs/tool/archsig_analysis_packet.md",
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                ],
                "ArchSig analysis packet owns law-relative molecule readings, obstruction circuits, signature axes, flatness reading, static/runtime/semantic split, repair operation candidates, evidence boundary, LLM interpretation notes, excluded readings, and non-conclusions.",
                vec![
                    "Analysis packet is not a Lean theorem proof, global architecture truth, extractor completeness proof, quality score, or automatic safe repair.",
                    "Analysis packet compatibility is a JSON contract, not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "archsig-analysis-packet-validation-report",
                "ArchSig analysis packet validation report",
                ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
                "primary",
                "LLM Atom ArchMap",
                vec!["docs/tool/archsig_analysis_packet.md"],
                "Validation checks identity, ArchMap and LawPolicy refs, law-relative obstruction links, signature and flatness boundaries, repair candidate guardrails, LLM interpretation surface, and non-conclusions without computing the analysis engine.",
                vec![
                    "Validation pass does not imply architecture lawfulness, source completeness, flatness proof, or repair safety.",
                    "Validation report compatibility is not a semantic-preservation theorem.",
                ],
            ),
        ],
        compatibility_policy: SchemaCompatibilityPolicyV0 {
            schema_version: SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION.to_string(),
            policy_id: "archsig-llm-atom-schema-compatibility-policy".to_string(),
            policy_version: "llm-atom-archmap-v0".to_string(),
            applies_to_catalog_version: "llm-atom-archmap-v0".to_string(),
            dimensions: vec![
                compatibility_dimension(
                    "schema-version",
                    vec!["schemaVersion"],
                    "schemaVersion must match one of the current LLM Atom ArchMap artifacts.",
                ),
                compatibility_dimension(
                    "claim-boundary",
                    vec!["nonConclusions", "evidenceBoundary"],
                    "Claim boundaries must remain explicit and must not promote observations to formal proof.",
                ),
            ],
            required_checks: vec![
                "Run archsig schema-catalog and compare against the canonical fixture.".to_string(),
                "Run the LLM-native workflow and FieldSig handoff checks.".to_string(),
            ],
            non_conclusions: vec![
                "schema catalog compatibility is not a semantic-preservation theorem".to_string(),
                "schema catalog compatibility is not evidence of extractor completeness".to_string(),
                "schema catalog compatibility is not a Lean theorem package".to_string(),
            ],
        },
        non_conclusions: vec![
            "schema migration is not a semantic-preservation theorem".to_string(),
            "schema catalog does not retain legacy AIR, Sig0, PR review, or governance surfaces as current ArchSig contracts".to_string(),
            "FieldSig-owned forecast and governance artifacts are intentionally outside this ArchSig catalog".to_string(),
        ],
    }
}

fn artifact(
    artifact_id: &str,
    artifact_name: &str,
    schema_version_name: &str,
    artifact_role: &str,
    owner_phase: &str,
    docs: Vec<&str>,
    field_mapping_policy: &str,
    non_conclusions: Vec<&str>,
) -> SchemaVersionCatalogEntryV0 {
    SchemaVersionCatalogEntryV0 {
        artifact_id: artifact_id.to_string(),
        artifact_name: artifact_name.to_string(),
        schema_version_name: schema_version_name.to_string(),
        artifact_role: artifact_role.to_string(),
        owner_phase: owner_phase.to_string(),
        status: "implemented".to_string(),
        primary_docs: docs.into_iter().map(str::to_string).collect(),
        downstream_issues: vec![],
        compatibility_boundary: SchemaCompatibilityBoundaryV0 {
            field_mapping_policy: field_mapping_policy.to_string(),
            deprecated_fields: vec![],
            new_required_assumptions: vec![
                "Required fields, observation families, law refs, or analysis axes change."
                    .to_string(),
                "Evidence boundaries or non-conclusions are removed or weakened.".to_string(),
            ],
            coverage_exactness_boundary: vec![
                "Coverage and exactness are artifact-local and do not imply semantic completeness."
                    .to_string(),
            ],
            non_conclusions: non_conclusions.into_iter().map(str::to_string).collect(),
        },
    }
}

fn compatibility_dimension(
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
    fn static_catalog_records_primary_llm_atom_artifacts_only() {
        let catalog = static_schema_version_catalog();
        assert_eq!(
            catalog.schema_version,
            SCHEMA_VERSION_CATALOG_SCHEMA_VERSION
        );
        assert_eq!(
            catalog.compatibility_policy.schema_version,
            SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION
        );

        let ids: BTreeSet<_> = catalog
            .artifacts
            .iter()
            .map(|artifact| artifact.artifact_id.as_str())
            .collect();
        assert_eq!(
            ids,
            BTreeSet::from([
                "archmap",
                "archmap-validation-report",
                "law-policy",
                "law-policy-validation-report",
                "archsig-analysis-packet",
                "archsig-analysis-packet-validation-report",
            ])
        );
        for legacy in [
            "signature-artifact",
            "air",
            "feature-extension-report",
            "theorem-precondition-check-report",
            "architecture-policy",
            "law-violation-report",
            "organization-policy",
            "policy-decision",
            "pr-comment-summary",
            "baseline-suppression",
            "aat-observable-bundle",
            "report-artifact-retention-manifest",
        ] {
            assert!(
                !ids.contains(legacy),
                "legacy artifact {legacy} remains current"
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
