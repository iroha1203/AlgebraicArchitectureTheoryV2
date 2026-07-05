use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHITECTURE_DISTANCE_V1_SCHEMA, ARCHMAP_V1_SCHEMA,
    ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA, ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
    ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION, LAW_POLICY_V1_SCHEMA, MEASUREMENT_PROFILE_V1_SCHEMA,
    NORMALIZED_ARCHMAP_V1_SCHEMA, SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
    SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0, SchemaVersionCatalogEntryV0,
    SchemaVersionCatalogV0, TYPED_EVALUATOR_RESULTS_V1_SCHEMA,
};

pub fn static_schema_version_catalog() -> SchemaVersionCatalogV0 {
    SchemaVersionCatalogV0 {
        schema_version: SCHEMA_VERSION_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-llm-atom-schema-version-catalog".to_string(),
        catalog_version: "llm-atom-archmap/v0.5.0".to_string(),
        phase: "LLM Atom ArchMap primary workflow".to_string(),
        artifacts: vec![
            artifact(
                "archmap-current",
                "ArchMap current input artifact",
                ARCHMAP_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec![
                    "archsig-contract:archmap-minimal-observation",
                    "archsig-contract:v0.4.0-ag-measurement",
                ],
                "ArchMap v0.5.0 records source-grounded architecture observations. Structural-shape inputs contain sources, atoms, and molecules for the typed evaluator path; finite-poset-site-shape inputs contain sources, subject/axis-decorated atoms, contexts, and covers for AG measurement. Both shapes reject legacy v0 root fields, unknown atom kinds or predicates, and unresolved source refs before analysis.",
                vec![
                    "ArchMap validation does not run the evaluator or measurement pipeline.",
                    "ArchMap validation does not prove architecture lawfulness, source completeness, U-adequacy, exactness, Lean theorem discharge, or global semantic truth.",
                    "Shape selection is command-local; schema equality does not by itself promote structural input to finite-poset-site input.",
                ],
            ),
            artifact(
                "aat-atom-vocabulary/v0.5.0",
                "AAT atom vocabulary v1",
                AAT_ATOM_VOCABULARY_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.4.0-improvement"],
                "AAT atom vocabulary v1 is an artifact-side projection of allowed ArchMap atom kind tokens with provenance refs back to the AAT doctrine. ArchMap v2 validation enforces the compiled-in fixed AAT canonical doctrine before checking atoms[].kind membership.",
                vec![
                    "Vocabulary lint checks token membership only; it does not prove source extraction soundness or semantic correctness.",
                    "The linter does not decide whether a new atom kind should be added to the doctrine.",
                ],
            ),
            artifact(
                "law-policy/v0.5.0",
                "LawPolicy v1 selector artifact",
                LAW_POLICY_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "LawPolicy v1 selects policy packs or explicit law/evaluator pairs with registry-owned basis, scope, and severity. It rejects unknown packs, unknown evaluators, unresolved basis refs, and DSL-style witness rules before analysis.",
                vec![
                    "LawPolicy v1 selects evaluators; it does not define witness predicates, axis valuation, obstruction definitions, or Lean proofs.",
                    "LawPolicy v1 validation does not run the v1 evaluator pipeline.",
                ],
            ),
            artifact(
                "measurement-profile/v0.5.0",
                "MeasurementProfile v1 AG evaluator selector",
                MEASUREMENT_PROFILE_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.4.0-ag-measurement"],
                "MeasurementProfile v1 declares selected site, cover, coefficient, EffCoeff procedure, witness family, resolution selector, Dom/Zero/NonZero/Cert predicates, and five-valued verdict discipline.",
                vec![
                    "MeasurementProfile selects a bounded measurement regime; it does not prove adequacy or theorem hypotheses.",
                    "Profile absence for AG evaluators is a validation error, not an unmeasured zero result.",
                ],
            ),
            artifact(
                "law-evaluator-registry/v0.5.0",
                "Law evaluator registry v1",
                "law-evaluator-registry/v0.5.0",
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "Law evaluator registry v1 owns evaluator manifests, policy pack expansion, basis refs, missing blocker rules, pass / violation criteria, typed result schema refs, distance contribution, and output refs. LawPolicy v1 selects entries from this registry.",
                vec![
                    "Evaluator registry manifest is an ArchSig computation contract, not a Lean theorem proof.",
                    "LawPolicy v1 cannot override witness rules, axis rules, distance formula, pass criteria, or violation criteria.",
                ],
            ),
            artifact(
                "normalized-archmap-current",
                "Normalized ArchMap current computation artifact",
                NORMALIZED_ARCHMAP_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec![
                    "archsig-contract:archmap-minimal-observation",
                    "archsig-contract:v0.4.0-ag-measurement",
                ],
                "Normalized ArchMap v0.5.0 is generated by the ArchSig normalizer without rereading the source repository. Structural-shape output records normalized AtomKind / Axis / predicate bindings, valence template refs, molecule memberships, and generated molecule candidate status; finite-poset-site-shape output records deterministic context, cover, and selected-site presentation under the fixed AAT canonical doctrine fingerprint.",
                vec![
                    "Normalized ArchMap is deterministic tooling input for evaluators or measurements, not a Lean proof object.",
                    "Generated molecule candidate status is not an obstruction, holonomy, risk, or lawfulness conclusion.",
                    "Finite-poset-site normalization does not prove source extraction soundness.",
                ],
            ),
            artifact(
                "typed-evaluator-results/v0.5.0",
                "Typed evaluator results v1",
                TYPED_EVALUATOR_RESULTS_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "Typed evaluator results v1 records evaluator status, support atom refs, support molecule refs, basis refs, detail refs, and bounded conclusions computed from Normalized ArchMap v1 and LawPolicy v1.",
                vec![
                    "Typed evaluator results do not read label-only, memo-only, removed-field-only, or schema-only evidence as measured support.",
                    "Blocked, unknown, and unmeasured results are not measured zero.",
                ],
            ),
            artifact(
                "archsig-architecture-distance/v0.5.0",
                "Architecture distance v1 computation artifact",
                ARCHITECTURE_DISTANCE_V1_SCHEMA,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec!["archsig-contract:tool-boundary"],
                "Architecture distance v1 records measured atom, configuration, signature, operation, primary curvature geometry readings, primary homotopy filling geometry readings, primary representation metric readings, and distanceInsights computed from Normalized ArchMap v1, TypedEvaluatorResults v1, raw v1 packet distance rows, and the selected LawPolicy distanceProfileRef.",
                vec![
                    "Architecture distance is a diagnostic ArchSig artifact, not a Lean theorem proof.",
                    "Typed evaluator violation counts are not substituted for architecture distance.",
                    "Blocked or unmeasured distance readings are not measured zero.",
                ],
            ),
            artifact(
                "archsig-measurement-packet/v0.5.0",
                "ArchSig measurement packet v1",
                ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.4.0-ag-measurement"],
                "ArchSig measurement packet v1 carries profile, structuralVerdict with optional dependsOnAssumptions refs, computedInvariants, analyticReadings, assumptions, boundaryStatements, and legacy-compatible nonConclusions as the AG Definition 11.1-aligned output contract.",
                vec![
                    "Structural verdicts are limited to measured_zero, measured_nonzero, unmeasured, unknown, and not_computed.",
                    "dependsOnAssumptions records row-level refs into the packet assumption ledger; violated assumptions only normalize dependent measured rows to not_computed.",
                    "Analytic readings do not generate structural verdicts unless a certified evaluator explicitly emits one.",
                    "BoundaryStatements are typed scoped qualifiers; nonConclusions remains a string compatibility view.",
                    "Theorem-candidate readings are analytic-only.",
                ],
            ),
            artifact(
                "archsig-boundary-statement/v0.5.0",
                "ArchSig BoundaryStatement v1",
                ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.4.0-improvement"],
                "BoundaryStatement v1 is the typed scoped qualifier contract for measurement packet boundaries. It records id, kind, scopeRefs, reason, and text while preserving nonConclusions as a compatibility view.",
                vec![
                    "Boundary statements qualify selected packet rows; they do not prove source extraction soundness, semantic correctness, or Lean theorem discharge.",
                    "Boundary kinds keep blocked, unmeasured, not-applicable, and violated-assumption states distinct from measured_zero.",
                ],
            ),
            artifact(
                "archsig-analysis-packet/v0.5.0",
                "ArchSig v1 typed evaluator analysis packet",
                ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
                "primary",
                "FieldSig handoff / raw evidence store",
                vec![
                    "archsig-contract:archmap-minimal-observation",
                    "archsig-contract:analysis-packet",
                    "archsig-contract:llm-native-e2e",
                ],
                "ArchSig v1 analysis packet is emitted only in raw mode and is the current FieldSig handoff contract. It carries typed evaluator results, architecture distance, generated packet refs, spectrum, homotopy, structural reading surface, bounded conclusions, detail refs, and non-conclusions.",
                vec![
                    "ArchSig v1 packet is bounded current structural state, not forecast truth, a Lean proof, global architecture truth, or automatic repair safety.",
                    "FieldSig reads v1 packet refs as SFT input coordinates and owns PR / diff / change-vector evolution analysis.",
                ],
            ),
            artifact(
                "archsig-run-manifest/v0.5.0",
                "ArchSig analyze run manifest",
                ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec![
                    "archsig-contract:output-report",
                    "archsig-contract:command-guide",
                ],
                "Run manifest records the analyze command name, input artifact paths, output mode, generated and omitted artifact lists, validation report paths, optional raw artifact paths, and validation result summary for one ArchSig analyze run.",
                vec![
                    "Run manifest is artifact navigation metadata, not source completeness proof, architecture lawfulness, or Lean theorem discharge.",
                    "Generated and omitted artifact lists describe this run only; omitted raw artifacts can be regenerated with explicit raw retention.",
                ],
            ),
            artifact(
                "archsig-atom-viewer-data/v0.5.0",
                "ArchSig viewer bounded projection data",
                ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec![
                    "archsig-contract:output-report",
                    "archsig-contract:command-guide",
                ],
                "Viewer projection data records source artifact refs, bounded layout settings, atom nodes, molecule groups, selected law-axis overlays, analysis overlays, report pane sections, omitted detail counts, truncation policy, and non-conclusions for browser visualization without embedding the raw analysis packet.",
                vec![
                    "Viewer data is a bounded visual projection, not a replacement for explicit ArchSig evidence lookup.",
                    "3D layout distance is not an AAT theorem metric, semantic equivalence, or causal relation.",
                    "Viewer data must not treat raw packet detail as browser input.",
                ],
            ),
        ],
        compatibility_policy: SchemaCompatibilityPolicyV0 {
            schema_version: SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION.to_string(),
            policy_id: "archsig-llm-atom-schema-compatibility-policy".to_string(),
            policy_version: "llm-atom-archmap/v0.5.0".to_string(),
            applies_to_catalog_version: "llm-atom-archmap/v0.5.0".to_string(),
            dimensions: vec![
                compatibility_dimension(
                    "schema-version",
                    vec!["schema"],
                    "schema must match one of the current LLM Atom ArchMap artifacts.",
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
            "schema catalog does not retain pre-Atom scan, projection, report, or PR-review surfaces as current ArchSig contracts".to_string(),
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
            ids.len(),
            catalog.artifacts.len(),
            "schema catalog artifact IDs must be unique"
        );
        let schema_names: BTreeSet<_> = catalog
            .artifacts
            .iter()
            .map(|artifact| artifact.schema_version_name.as_str())
            .collect();
        assert_eq!(
            schema_names.len(),
            catalog.artifacts.len(),
            "schema catalog schema names must be unique"
        );
        assert_eq!(
            ids,
            BTreeSet::from([
                "archmap-current",
                "aat-atom-vocabulary/v0.5.0",
                "law-policy/v0.5.0",
                "law-evaluator-registry/v0.5.0",
                "measurement-profile/v0.5.0",
                "normalized-archmap-current",
                "typed-evaluator-results/v0.5.0",
                "archsig-architecture-distance/v0.5.0",
                "archsig-measurement-packet/v0.5.0",
                "archsig-boundary-statement/v0.5.0",
                "archsig-analysis-packet/v0.5.0",
                "archsig-run-manifest/v0.5.0",
                "archsig-atom-viewer-data/v0.5.0",
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
            "../tests/fixtures/ag_measurement/schema_version_catalog.json"
        ))
        .expect("schema version catalog fixture parses");
        assert_eq!(fixture, static_schema_version_catalog());
    }
}
