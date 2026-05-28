use crate::{
    AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION, AIR_SCHEMA_VERSION,
    ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION, ARCHITECTURE_POLICY_SCHEMA_VERSION,
    ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
    DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
    FEATURE_EXTENSION_REPORT_SCHEMA_VERSION, LAW_POLICY_SCHEMA_VERSION,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, LAW_VIOLATION_REPORT_SCHEMA_VERSION,
    OBSTRUCTION_WITNESS_SCHEMA_VERSION, PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
    SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION, SCHEMA_VERSION,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
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
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec![],
                compatibility_boundary(
                    "Map component/relation/signature fields by stable camelCase names; adapter coverageBoundary, unsupportedConstructs, missingEvidence, and nonConclusions must remain explicit.",
                    vec![],
                    vec![
                        "New required axes must declare measuredZero/measuredNonzero/unmeasured/outOfScope semantics.",
                        "New adapter evidence must preserve coverage and missing-evidence boundaries.",
                    ],
                    vec![
                        "metricStatus is the compatibility boundary for coverage and exactness of Sig0 axes.",
                        "Sig0 is bounded adapter evidence, not the ArchSig primary review surface or extractor completeness proof.",
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
                "archmap",
                "LLM-native ArchMap Atom observation artifact",
                ARCHMAP_SCHEMA_VERSION,
                "atom-observation-input",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/atom_handoff.md",
                ],
                vec!["#1329"],
                compatibility_boundary(
                    "ArchMap records source-grounded atomObservations, moleculeObservations, semanticObservations, observationGaps, projectionInfo, concernHints, provenance, and nonConclusions without selecting laws or constructing obstruction circuits.",
                    vec![],
                    vec![
                        "New observation families must cite source refs, keep evidence boundaries explicit, and avoid law-relative conclusions.",
                        "Concern hints must remain review cues until ArchSig combines ArchMap with a selected LawPolicy.",
                    ],
                    vec![
                        "ArchMap does not prove architecture lawfulness, output obstruction circuits, prove zero curvature, certify universal atom truth, or replace Lean theorem discharge.",
                    ],
                ),
            ),
            artifact(
                "archmap-validation-report",
                "ArchMap Validation Report",
                ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/atom_handoff.md",
                ],
                vec!["#1329"],
                compatibility_boundary(
                    "Keep source inventory checks, source ref checks, claim boundary checks, semantic coverage checks, projection-separation checks, formal promotion guardrail checks, derived projection diagnostics, atomic observation summary, and responsibility checks separate.",
                    vec![],
                    vec![
                        "New checks must report whether they fail, warn, or pass without promoting observed atoms to universal atom truth.",
                        "Atomic observation checks must distinguish atom observations, molecule observations, semantic observations, concern hints, and observation gaps.",
                    ],
                    vec![
                        "Validation pass does not imply semantic correctness, completeness, architecture lawfulness, obstruction existence, certified atom truth, zero curvature, or SFT forecast correctness.",
                    ],
                ),
            ),
            artifact(
                "law-policy",
                "LLM-native selected LawPolicy artifact",
                LAW_POLICY_SCHEMA_VERSION,
                "selected-law-universe-policy",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/README.md",
                ],
                vec!["#1330"],
                compatibility_boundary(
                    "LawPolicy owns selected laws, witness rules, molecule patterns, obstruction definitions, signature axis definitions, exactness assumptions, coverage requirements, excluded readings, and non-conclusions separately from ArchMap observations.",
                    vec![],
                    vec![
                        "New law families must declare witness rules, required zero axes, coverage requirements, and exactness assumptions.",
                        "New signature axes must keep missing coverage distinct from measured zero.",
                    ],
                    vec![
                        "LawPolicy is selected analysis policy, not AAT itself, architecture lawfulness, atom truth, or Lean theorem discharge.",
                    ],
                ),
            ),
            artifact(
                "law-policy-validation-report",
                "LLM-native LawPolicy validation report",
                LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                vec!["#1330"],
                compatibility_boundary(
                    "Validation reports schema support, identity, id uniqueness, law/witness/axis references, coverage, exactness, and non-conclusion guardrails without proving lawfulness.",
                    vec![],
                    vec![
                        "New checks must fail or warn without promoting policy validation to theorem evidence.",
                    ],
                    vec![
                        "Validation pass does not imply architecture lawfulness, certified atom truth, zero curvature, or Lean theorem discharge.",
                    ],
                ),
            ),
            artifact(
                "archsig-analysis-packet",
                "LLM-native ArchSig AAT analysis packet",
                ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
                "analysis-output",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/README.md",
                ],
                vec!["#1331"],
                compatibility_boundary(
                    "ArchSig analysis packet owns law-relative molecule readings, obstruction circuits, signature axes, flatness reading, static/runtime/semantic split, repair operation candidates, evidence boundary, LLM interpretation notes, excluded readings, and non-conclusions.",
                    vec![],
                    vec![
                        "New packet readings must keep ArchMap refs and selected LawPolicy refs explicit.",
                        "New repair candidates must retain preserved invariants, preconditions, transfer risks, evidence boundary, and non-conclusions.",
                    ],
                    vec![
                        "Analysis packet is not a Lean theorem proof, global architecture truth, extractor completeness proof, quality score, or automatic safe repair.",
                    ],
                ),
            ),
            artifact(
                "archsig-analysis-packet-validation-report",
                "LLM-native ArchSig analysis packet validation report",
                ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "LLM-native ArchMap / ArchSig",
                "implemented",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                vec!["#1331"],
                compatibility_boundary(
                    "Validation checks identity, ArchMap and LawPolicy refs, law-relative obstruction links, signature and flatness boundaries, repair candidate guardrails, LLM interpretation surface, and non-conclusions without computing the analysis engine.",
                    vec![],
                    vec![
                        "New checks must fail or warn without promoting packet validation to theorem evidence.",
                    ],
                    vec![
                        "Validation pass does not imply architecture lawfulness, source completeness, flatness proof, or repair safety.",
                    ],
                ),
            ),
            artifact(
                "architecture-policy",
                "Architecture policy artifact",
                ARCHITECTURE_POLICY_SCHEMA_VERSION,
                "law-aware-review-policy",
                "ArchMap law-aware review",
                "implemented",
                vec![
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec!["#1162"],
                compatibility_boundary(
                    "Map adopted laws, layer selectors, dependency rules, exceptions, and SRP taxonomy explicitly; do not infer policy from repository shape.",
                    vec![],
                    vec![
                        "New law families must declare deterministic versus LLM-review enforcement boundary.",
                    ],
                    vec![
                        "Architecture policy is review evidence, not a Lean theorem or architecture lawfulness proof.",
                    ],
                ),
            ),
            artifact(
                "architecture-policy-validation-report",
                "Architecture policy validation report",
                ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
                "validation-output",
                "ArchMap law-aware review",
                "implemented",
                vec!["tools/archsig/docs/commands.md"],
                vec!["#1162"],
                compatibility_boundary(
                    "Keep identity, adopted law, layer selector, dependency rule, SRP evidence, and non-conclusion checks separate.",
                    vec![],
                    vec!["New checks must distinguish fail, warn, and unmeasured policy evidence."],
                    vec![
                        "Validation pass does not imply architecture lawfulness or SRP violation.",
                    ],
                ),
            ),
            artifact(
                "law-violation-report",
                "Law violation report",
                LAW_VIOLATION_REPORT_SCHEMA_VERSION,
                "review-output",
                "ArchMap law-aware review",
                "implemented",
                vec![
                    "tools/archsig/docs/commands.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                ],
                vec!["#1164", "#1165"],
                compatibility_boundary(
                    "Map deterministic Layered findings, allowed exceptions, SRP cues, unmeasured selectors, review actions, and non-conclusions explicitly.",
                    vec![],
                    vec![
                        "New law findings must preserve evidence refs and policy refs before review classification.",
                    ],
                    vec![
                        "Layered findings are selected-universe tooling evidence and SRP cues are not tool-only violations.",
                    ],
                ),
            ),
            artifact(
                "archmap-generation-protocol",
                "ArchMap generation protocol",
                "archmap-generation-protocol-v0",
                "external-agent-protocol",
                "ArchMap v2",
                "implemented",
                vec![
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec!["#1139"],
                compatibility_boundary(
                    "Map source inventory refs, prompt pack refs, model provenance, required workflow, and private / unavailable generation boundary explicitly.",
                    vec![],
                    vec![
                        "New generation workflow fields must preserve model provenance and validation boundary.",
                    ],
                    vec![
                        "Generation protocol does not execute the model or prove the generated ArchMap correct.",
                    ],
                ),
            ),
            artifact(
                "pr-quality-analysis",
                "PR Quality Analysis report",
                PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
                "review-output",
                "PRD v3",
                "implemented",
                vec![
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec!["#1153"],
                compatibility_boundary(
                    "Map ArchMap, AIR, theorem-check, feature-report, and policy-decision refs to reviewer-facing cues and missing evidence without automatic merge approval.",
                    vec![],
                    vec![
                        "New cue kinds must declare evidence boundary and avoid merge-decision or architecture-lawfulness claims.",
                    ],
                    vec![
                        "PR quality analysis is review evidence, not merge approval or a global architecture ranking.",
                    ],
                ),
            ),
            artifact(
                "aat-observable-bundle",
                "AAT Observable Bundle",
                AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION,
                "aat-observable-review-bundle",
                "AAT observable bridge",
                "implemented",
                vec![
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/artifacts-and-boundaries.md",
                    "tools/archsig/docs/commands.md",
                ],
                vec![
                    "#1166", "#1167", "#1168", "#1169", "#1170", "#1171", "#1172", "#1173",
                    "#1174", "#1175", "#1176", "#1177", "#1178", "#1179",
                ],
                compatibility_boundary(
                    "Map AAT concepts, source refs, selected universe, witness refs, operation candidates, theorem boundaries, review actions, and responsibility splits without promoting tooling evidence to proof.",
                    vec![],
                    vec![
                        "New AAT concept mappings must declare expressibility, retention, reviewability, measurement status, responsibility, and non-conclusions.",
                        "New measured axes must keep measuredZero, measuredNonzero, unmeasured, outOfScope, private, unavailable, unsupported, and dynamic boundaries distinct.",
                    ],
                    vec![
                        "AAT Observable Bundle is a review artifact bundle, not AAT itself, extractor completeness, global lawfulness proof, or merge approval.",
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
            LAW_POLICY_SCHEMA_VERSION,
            LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
            ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
            ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
            FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
            OBSTRUCTION_WITNESS_SCHEMA_VERSION,
            ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
            DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION,
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
