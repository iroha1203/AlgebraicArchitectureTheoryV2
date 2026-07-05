use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA,
    ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA, ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
    ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, ARCHMAP_V2_SCHEMA, ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
    ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION, ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA,
    ARCHSIG_COMPARISON_REPORT_V1_SCHEMA, ARCHSIG_GATE_POLICY_V1_SCHEMA,
    ARCHSIG_GATE_REPORT_V1_SCHEMA, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_REPAIR_PLAN_V1_SCHEMA, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION, LAW_POLICY_V1_SCHEMA,
    MEASUREMENT_PROFILE_V1_SCHEMA, NORMALIZED_ARCHMAP_V2_SCHEMA,
    SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION, SCHEMA_VERSION_CATALOG_SCHEMA_VERSION,
    SchemaCompatibilityBoundaryV0, SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0,
    SchemaVersionCatalogEntryV0, SchemaVersionCatalogV0,
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
                ARCHMAP_V2_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec![
                    "archsig-contract:archmap-minimal-observation",
                    "archsig-contract:v0.4.0-ag-measurement",
                ],
                "ArchMap v0.5.0 records source-grounded architecture observations. Finite-poset-site inputs contain sources, subject/axis-decorated atoms, contexts, and covers for AG measurement. They reject legacy v0 root fields, unknown atom kinds or predicates, and unresolved source refs before analysis.",
                vec![
                    "ArchMap validation does not run the evaluator or measurement pipeline.",
                    "ArchMap validation does not prove architecture lawfulness, source completeness, U-adequacy, exactness, Lean theorem discharge, or global semantic truth.",
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
                "archmap-scope-manifest/v0.5.0",
                "ArchMap authoring scope manifest",
                ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.0 ArchMap authoring",
                vec!["archsig-contract:v0.5.0-prd5-archmap-skill"],
                "Scope manifest v0.5.0 records the selected authoring scope, repository revision, deterministic worklist, content hashes, exclusions, and author-supplied evidence files before reading begins.",
                vec![
                    "Scope manifest records the selected scope only; it does not assert source extraction completeness.",
                    "Scope manifest does not generate atoms or decide semantic meaning.",
                ],
            ),
            artifact(
                "archmap-candidate-packet/v0.5.0",
                "ArchMap authoring candidate packet",
                ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.0 ArchMap authoring",
                vec!["archsig-contract:v0.5.0-prd5-archmap-skill"],
                "Candidate packet v0.5.0 records one reading pass chunk: reviewed sources, candidate observations, survey rows, unavailable notes, and self-review gates.",
                vec![
                    "Candidate packets are not final ArchMap artifacts.",
                    "Candidate packets do not adjudicate pass disagreement or automate semantic adoption.",
                ],
            ),
            artifact(
                "archmap-extraction-consistency/v0.5.0",
                "ArchMap authoring extraction consistency report",
                ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.0 ArchMap authoring",
                vec!["archsig-contract:v0.5.0-prd5-archmap-skill"],
                "Extraction consistency v0.5.0 records atom-match-key comparison between reading passes, unmatched queues, matchRate, context differences, and integrator adjudications.",
                vec![
                    "matchRate is a record, not a verdict.",
                    "Unmatched rows are rereading queues, not evidence that a candidate is wrong.",
                ],
            ),
            artifact(
                "archmap-coverage-ledger/v0.5.0",
                "ArchMap authoring coverage ledger",
                ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.0 ArchMap authoring",
                vec!["archsig-contract:v0.5.0-prd5-archmap-skill"],
                "Coverage ledger v0.5.0 records selected-scope survey rows and the fixed claim boundary for authoring provenance.",
                vec![
                    "Coverage ledger rows record authoring survey state; they do not assert extraction completeness.",
                    "Coverage ledger is not read by analyze.",
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
                "archsig-repair-plan/v0.5.0",
                "ArchSig RepairPlan v1 SAGA supplied input artifact",
                ARCHSIG_REPAIR_PLAN_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.0 SAGA Stage 1",
                vec!["archsig-contract:v0.5.0-prd4-lawpolicy-saga"],
                "RepairPlan v1 supplies the checked SAGA descent input side: residual refs, finite complex, primitive restriction differences, semantic projection, faithfulness regime, and F2-additive coefficient.",
                vec![
                    "RepairPlan validation checks supplied premises before use; it does not compute boundary membership or global coherence.",
                    "RepairPlan input cannot supply generated conclusion tokens such as glues, verdict, h1Zero, or globalCoherent.",
                    "Enumeration completeness is recorded as an author assumption, not mechanically verified.",
                ],
            ),
            artifact(
                "law-evaluator-registry/v0.5.0",
                "Law evaluator registry v1",
                "law-evaluator-registry/v0.5.0",
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "Law evaluator registry v1 owns evaluator manifests, policy pack expansion, basis refs, missing blocker rules, pass / violation criteria, and output refs. LawPolicy v1 selects entries from this registry.",
                vec![
                    "Evaluator registry manifest is an ArchSig computation contract, not a Lean theorem proof.",
                    "LawPolicy v1 cannot override witness rules, axis rules, distance formula, pass criteria, or violation criteria.",
                ],
            ),
            artifact(
                "normalized-archmap-current",
                "Normalized ArchMap current computation artifact",
                NORMALIZED_ARCHMAP_V2_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec![
                    "archsig-contract:archmap-minimal-observation",
                    "archsig-contract:v0.4.0-ag-measurement",
                ],
                "Normalized ArchMap v0.5.0 is generated by the ArchSig normalizer without rereading the source repository. Finite-poset-site output records deterministic context, cover, and selected-site presentation under the fixed AAT canonical doctrine fingerprint.",
                vec![
                    "Normalized ArchMap is deterministic tooling input for evaluators or measurements, not a Lean proof object.",
                    "Finite-poset-site normalization does not prove source extraction soundness.",
                ],
            ),
            artifact(
                "archsig-measurement-packet/v0.5.0",
                "ArchSig measurement packet v1",
                ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.4.0-ag-measurement"],
                "ArchSig measurement packet v1 carries profile, structuralVerdict with optional dependsOnAssumptions refs, computedInvariants, analyticReadings, assumptions, boundaryStatements, and legacy-compatible nonConclusions as the AG Definition 11.1-aligned output contract. Registered PRD-4 conclusionCode values include REPAIR_GLUES_WITHIN_SELECTED_COMPLEX, MEASURED_NONGLUING_RESIDUAL, COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION, and REPAIR_TARGETS_IDENTIFIED.",
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
                "archsig-gate-policy/v0.5.0",
                "ArchSig gate policy v1",
                ARCHSIG_GATE_POLICY_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:v0.5.0-prd2-artifact-ci"],
                "Gate policy v1 records institutional verdict-to-action mappings for absolute and introduced-by-change rules. Absolute rules must map measured_zero, measured_nonzero, unmeasured, unknown, not_computed, and violated_assumption_dependency; introduced-by-change rules must map new, cleared, preexisting, removed, and other.",
                vec![
                    "Gate policy is authored institutional judgment, not a measurement packet verdict.",
                    "Non-terminal measurement states and removed / other transitions cannot be mapped to plain pass.",
                    "Gate policy does not introduce analytic thresholds or class transport.",
                ],
            ),
            artifact(
                "archsig-gate-report/v0.5.0",
                "ArchSig gate report v1",
                ARCHSIG_GATE_REPORT_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:v0.5.0-prd2-artifact-ci"],
                "Gate report v1 records PASS_WITHIN_GATE_POLICY, BLOCKED_BY_GATE_POLICY, or NOT_EVALUABLE together with ruleOutcomes[].appliedMapping rows that preserve original measurement verdict vocabulary.",
                vec![
                    "Gate report does not mutate measurement verdicts.",
                    "Gate report does not infer improvement, repair, class identity, or transport between runs.",
                    "Not evaluable is neither pass nor block.",
                ],
            ),
            artifact(
                "archmap-diff/v0.5.0",
                "ArchSig deterministic normalized ArchMap diff",
                ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:v0.5.0-prd2-artifact-ci"],
                "ArchMap diff v1 records deterministic added, removed, and modified sources, atoms, contexts, and covers computed from two normalized-archmap/v0.5.0 artifacts.",
                vec![
                    "ArchMap diff is a computed record artifact, not supplied observation evidence.",
                    "Diff entries are mechanical JSON differences and do not assign causality to verdict changes.",
                ],
            ),
            artifact(
                "archsig-comparison-report/v0.5.0",
                "ArchSig comparison report v1",
                ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:v0.5.0-prd2-artifact-ci"],
                "Comparison report v1 records identical, verdict-row, or not-comparable run comparison together with record-level verdict transitions and archmap-diff intersections. Registered conclusionCode values are NO_NEW_MEASURED_OBSTRUCTION_RECORDED, MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE, MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE, and RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA.",
                vec![
                    "Comparison report does not implement class transport, obstruction identity transport, repair causality, or semantic equivalence.",
                    "Comparison report conclusion codes are record-level names only.",
                    "Cover or context changes are boundary data and map to other_transition for gate policy evaluation.",
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
                "Run manifest records the analyze command name, deterministic runId, toolVersion, input digests, mode, conclusion code, generated artifact list, artifact links, validation report paths, and validation result summary for one ArchSig analyze run.",
                vec![
                    "Run manifest is artifact navigation metadata, not source completeness proof, architecture lawfulness, or Lean theorem discharge.",
                    "Generated artifact lists describe this run only and do not imply any unlisted artifact was produced.",
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
                "archmap-scope-manifest/v0.5.0",
                "archmap-candidate-packet/v0.5.0",
                "archmap-extraction-consistency/v0.5.0",
                "archmap-coverage-ledger/v0.5.0",
                "law-policy/v0.5.0",
                "law-evaluator-registry/v0.5.0",
                "measurement-profile/v0.5.0",
                "archsig-repair-plan/v0.5.0",
                "normalized-archmap-current",
                "archsig-measurement-packet/v0.5.0",
                "archsig-boundary-statement/v0.5.0",
                "archsig-gate-policy/v0.5.0",
                "archsig-gate-report/v0.5.0",
                "archmap-diff/v0.5.0",
                "archsig-comparison-report/v0.5.0",
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
