use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA,
    ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA, ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
    ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, ARCHMAP_V2_SCHEMA, ARCHSIG_ANALYSIS_CONCLUSION_CODES,
    ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA, ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
    ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA, ARCHSIG_COMPARISON_CONCLUSION_CODES,
    ARCHSIG_COMPARISON_REPORT_V1_SCHEMA, ARCHSIG_GATE_POLICY_V1_SCHEMA,
    ARCHSIG_GATE_REPORT_DECISIONS, ARCHSIG_GATE_REPORT_V1_SCHEMA,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ARCHSIG_POLICY_BUNDLE_V1_SCHEMA,
    ARCHSIG_REPAIR_PLAN_V1_SCHEMA, ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
    ARCHSIG_SAGA_CONCLUSION_CODES, LAW_EQUATION_SURFACE_V1_SCHEMA, LAW_POLICY_V1_SCHEMA,
    LAW_SURFACE_BINDING_VOCABULARY_SCHEMA, MEASUREMENT_PROFILE_V1_SCHEMA,
    NORMALIZED_ARCHMAP_V2_SCHEMA, SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION,
    SCHEMA_VERSION_CATALOG_SCHEMA_VERSION, SchemaCompatibilityBoundaryV0,
    SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0, SchemaVersionCatalogEntryV0,
    SchemaVersionCatalogV0,
};

pub fn static_schema_version_catalog() -> SchemaVersionCatalogV0 {
    SchemaVersionCatalogV0 {
        schema_version: SCHEMA_VERSION_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-llm-atom-schema-version-catalog".to_string(),
        catalog_version: "llm-atom-archmap/v0.5.1".to_string(),
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
                    "archsig-contract:v0.5.1-ag-measurement",
                ],
                "ArchMap v0.5.1 records source-grounded architecture observations. Finite-poset-site inputs contain sources, subject/axis-decorated atoms, contexts, and covers for AG measurement. They reject legacy v0 root fields, unknown atom kinds or predicates, and unresolved source refs before analysis.",
                vec![
                    "ArchMap validation does not run the evaluator or measurement pipeline.",
                    "ArchMap validation does not prove architecture lawfulness, source completeness, U-adequacy, exactness, Lean theorem discharge, or global semantic truth.",
                    ],
            ),
            artifact(
                "aat-atom-vocabulary/v0.5.1",
                "AAT atom vocabulary v0.5.1",
                AAT_ATOM_VOCABULARY_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.5.1-improvement"],
                "AAT atom vocabulary v0.5.1 is an artifact-side projection of allowed ArchMap atom kind tokens with provenance refs back to the AAT doctrine. ArchMap v2 validation enforces the compiled-in fixed AAT canonical doctrine before checking atoms[].kind membership.",
                vec![
                    "Vocabulary lint checks token membership only; it does not prove source extraction soundness or semantic correctness.",
                    "The linter does not decide whether a new atom kind should be added to the doctrine.",
                ],
            ),
            artifact(
                "archmap-scope-manifest/v0.5.1",
                "ArchMap authoring scope manifest",
                ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.1 ArchMap authoring",
                vec!["archsig-contract:archmap-authoring-v0.5.1"],
                "Scope manifest v0.5.1 records the selected authoring scope, repository revision, deterministic worklist, content hashes, exclusions, and author-supplied evidence files before reading begins.",
                vec![
                    "Scope manifest records the selected scope only; it does not assert source extraction completeness.",
                    "Scope manifest does not generate atoms or decide semantic meaning.",
                ],
            ),
            artifact(
                "archmap-candidate-packet/v0.5.1",
                "ArchMap authoring candidate packet",
                ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.1 ArchMap authoring",
                vec!["archsig-contract:archmap-authoring-v0.5.1"],
                "Candidate packet v0.5.1 records one reading pass chunk: reviewed sources, candidate observations, survey rows, unavailable notes, and self-review gates.",
                vec![
                    "Candidate packets are not final ArchMap artifacts.",
                    "Candidate packets do not adjudicate pass disagreement or automate semantic adoption.",
                ],
            ),
            artifact(
                "archmap-extraction-consistency/v0.5.1",
                "ArchMap authoring extraction consistency report",
                ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.1 ArchMap authoring",
                vec!["archsig-contract:archmap-authoring-v0.5.1"],
                "Extraction consistency v0.5.1 records atom-match-key comparison between reading passes, unmatched queues, matchRate, context differences, and integrator adjudications.",
                vec![
                    "matchRate is a record, not a verdict.",
                    "Unmatched rows are rereading queues, not evidence that a candidate is wrong.",
                ],
            ),
            artifact(
                "archmap-coverage-ledger/v0.5.1",
                "ArchMap authoring coverage ledger",
                ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA,
                "authoring",
                "ArchSig v0.5.1 ArchMap authoring",
                vec!["archsig-contract:archmap-authoring-v0.5.1"],
                "Coverage ledger v0.5.1 records selected-scope survey rows and the fixed claim boundary for authoring provenance.",
                vec![
                    "Coverage ledger rows record authoring survey state; they do not assert extraction completeness.",
                    "Coverage ledger is not read by analyze.",
                ],
            ),
            artifact(
                "aat-atom-vocabulary-binding/v0.5.1",
                "AAT atom binding vocabulary manifest v0.5.1",
                LAW_SURFACE_BINDING_VOCABULARY_SCHEMA,
                "authoring",
                "ArchSig v0.5.1 LawPolicy Stage 2",
                vec!["archsig-contract:v0.5.1-law-equation-surface"],
                "The AAT atom binding vocabulary manifest fixes the supported Stage 2 axis/predicate pairs shared by ArchMap authoring and law-equation-surface validation.",
                vec![
                    "The manifest does not add evaluator conclusions or compute measurements.",
                    "Pairs outside the registered Stage 2 axis/predicate vocabulary are not accepted by this stage.",
                ],
            ),
            artifact(
                "law-equation-surface/v0.5.1",
                "Law equation surface v0.5.1 author declaration",
                LAW_EQUATION_SURFACE_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 LawPolicy Stage 2",
                vec!["archsig-contract:v0.5.1-law-equation-surface"],
                "Law equation surface v0.5.1 records the authoring input contract for law identifiers, condition types, witness bindings, and closed-equational forbidden support generators. This stage's standalone command validates the declaration contract.",
                vec![
                    "The surface does not supply verdicts, certificates, boundary membership, or global coherence conclusions.",
                    "Stage 3 reservation fields are rejected when written.",
                ],
            ),
            artifact(
                "law-policy/v0.5.1",
                "LawPolicy v0.5.1 selector artifact",
                LAW_POLICY_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "LawPolicy v0.5.1 selects explicit law/evaluator pairs with registry-owned basis, scope, and severity. Retired policy pack selectors, unknown evaluators, unresolved basis refs, and DSL-style witness rules are rejected before analysis.",
                vec![
                    "LawPolicy v0.5.1 selects evaluators; it does not define witness predicates, axis valuation, obstruction definitions, or Lean proofs.",
                    "LawPolicy validation does not run the evaluator pipeline.",
                ],
            ),
            artifact(
                "archsig-policy-bundle/v0.5.1",
                "ArchSig policy bundle v0.5.1",
                ARCHSIG_POLICY_BUNDLE_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 LawPolicy Stage 2",
                vec!["archsig-contract:v0.5.1-law-equation-surface"],
                "Policy bundle v0.5.1 fixes LawPolicy, law-equation-surface, and MeasurementProfile references together with canonical JSON SHA-256 component fingerprints for one analyze run.",
                vec![
                    "The bundle records component identity; it does not add evaluator conclusions or prove semantic equivalence.",
                    "Fingerprint mismatch is a validation failure before measurement.",
                ],
            ),
            artifact(
                "measurement-profile/v0.5.1",
                "MeasurementProfile v0.5.1 AG evaluator selector",
                MEASUREMENT_PROFILE_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.5.1-ag-measurement"],
                "MeasurementProfile v0.5.1 declares selected site, cover, coefficient, EffCoeff procedure, resolution selector, Dom/Zero/NonZero/Cert predicates, and five-valued verdict discipline. Witness variables are supplied by the referenced law-equation-surface.",
                vec![
                    "MeasurementProfile selects a bounded measurement regime; it does not prove adequacy or theorem hypotheses.",
                    "Profile absence for AG evaluators is a validation error, not an unmeasured zero result.",
                ],
            ),
            artifact(
                "archsig-repair-plan/v0.5.1",
                "ArchSig RepairPlan v0.5.1 SAGA supplied input artifact",
                ARCHSIG_REPAIR_PLAN_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 SAGA Stage 1",
                vec!["archsig-contract:saga-stage1-v0.5.1"],
                    "RepairPlan v0.5.1 supplies the checked SAGA descent input side: residual refs, finite complex, primitive restriction differences, semantic projection, faithfulness regime, and F2-additive coefficient.",
                vec![
                    "RepairPlan validation checks supplied premises before use; it does not compute boundary membership or global coherence.",
                    "RepairPlan input cannot supply generated conclusion tokens such as glues, verdict, h1Zero, or globalCoherent.",
                    "Enumeration completeness is recorded as an author assumption, not mechanically verified.",
                ],
            ),
            artifact(
                "law-evaluator-registry/v0.5.1",
                "Law evaluator registry v0.5.1",
                "law-evaluator-registry/v0.5.1",
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["archsig-contract:archmap-minimal-observation"],
                "Law evaluator registry v0.5.1 owns evaluator manifests, basis refs, missing blocker rules, pass / violation criteria, and output refs. LawPolicy v0.5.1 selects entries from this registry.",
                vec![
                    "Evaluator registry manifest is an ArchSig computation contract, not a Lean theorem proof.",
                    "LawPolicy v0.5.1 cannot override witness rules, axis rules, distance formula, pass criteria, or violation criteria.",
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
                    "archsig-contract:v0.5.1-ag-measurement",
                ],
                "Normalized ArchMap v0.5.1 is generated by the ArchSig normalizer without rereading the source repository. Finite-poset-site output records deterministic context, cover, and selected-site presentation under the fixed AAT canonical doctrine fingerprint.",
                vec![
                    "Normalized ArchMap is deterministic tooling input for evaluators or measurements, not a Lean proof object.",
                    "Finite-poset-site normalization does not prove source extraction soundness.",
                ],
            ),
            artifact(
                "archsig-measurement-packet/v0.5.1",
                "ArchSig measurement packet v0.5.1",
                ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.5.1-ag-measurement"],
                &format!(
                    "ArchSig measurement packet v0.5.1 carries profile, structuralVerdict with optional dependsOnAssumptions refs, computedInvariants, analyticReadings, assumptions, boundaryStatements, and legacy-compatible nonConclusions as the AG Definition 11.1-aligned output contract. Registered SAGA conclusionCode values include {}.",
                    registry_sentence(&ARCHSIG_SAGA_CONCLUSION_CODES),
                ),
                vec![
                    "Structural verdicts are limited to measured_zero, measured_nonzero, unmeasured, unknown, and not_computed.",
                    "dependsOnAssumptions records row-level refs into the packet assumption ledger; violated assumptions only normalize dependent measured rows to not_computed.",
                    "Analytic readings do not generate structural verdicts unless a certified evaluator explicitly emits one.",
                    "BoundaryStatements are typed scoped qualifiers; nonConclusions remains a string compatibility view.",
                    "Theorem-candidate readings are analytic-only.",
                ],
            ),
            artifact(
                "archsig-boundary-statement/v0.5.1",
                "ArchSig BoundaryStatement v0.5.1",
                ARCHSIG_BOUNDARY_STATEMENT_V1_SCHEMA,
                "primary",
                "ArchSig v0.5.1 Algebraic Geometry Measurement",
                vec!["archsig-contract:v0.5.1-improvement"],
                "BoundaryStatement v0.5.1 is the typed scoped qualifier contract for measurement packet boundaries. It records id, kind, scopeRefs, reason, and text while preserving nonConclusions as a compatibility view.",
                vec![
                    "Boundary statements qualify selected packet rows; they do not prove source extraction soundness, semantic correctness, or Lean theorem discharge.",
                    "Boundary kinds keep blocked, unmeasured, not-applicable, and violated-assumption states distinct from measured_zero.",
                ],
            ),
            artifact(
                "archsig-gate-policy/v0.5.1",
                "ArchSig gate policy v0.5.1",
                ARCHSIG_GATE_POLICY_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:artifact-ci-v0.5.1"],
                "Gate policy v0.5.1 records institutional verdict-to-action mappings for absolute and introduced-by-change rules. Absolute rules must map measured_zero, measured_nonzero, unmeasured, unknown, not_computed, and violated_assumption_dependency; introduced-by-change rules must map new, cleared, preexisting, removed, and other.",
                vec![
                    "Gate policy is authored institutional judgment, not a measurement packet verdict.",
                    "Non-terminal measurement states and removed / other transitions cannot be mapped to plain pass.",
                    "Gate policy does not introduce analytic thresholds or class transport.",
                ],
            ),
            artifact(
                "archsig-gate-report/v0.5.1",
                "ArchSig gate report v0.5.1",
                ARCHSIG_GATE_REPORT_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:artifact-ci-v0.5.1"],
                &format!(
                    "Gate report v0.5.1 records {} together with ruleOutcomes[].appliedMapping rows that preserve original measurement verdict vocabulary.",
                    registry_sentence(&ARCHSIG_GATE_REPORT_DECISIONS),
                ),
                vec![
                    "Gate report does not mutate measurement verdicts.",
                    "Gate report does not infer improvement, repair, class identity, or transport between runs.",
                    "Not evaluable is neither pass nor block.",
                ],
            ),
            artifact(
                "archmap-diff/v0.5.1",
                "ArchSig deterministic normalized ArchMap diff",
                ARCHSIG_ARCHMAP_DIFF_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:artifact-ci-v0.5.1"],
                "ArchMap diff v0.5.1 records deterministic added, removed, and modified sources, atoms, contexts, and covers computed from two normalized-archmap/v0.5.1 artifacts.",
                vec![
                    "ArchMap diff is a computed record artifact, not supplied observation evidence.",
                    "Diff entries are mechanical JSON differences and do not assign causality to verdict changes.",
                ],
            ),
            artifact(
                "archsig-comparison-report/v0.5.1",
                "ArchSig comparison report v0.5.1",
                ARCHSIG_COMPARISON_REPORT_V1_SCHEMA,
                "primary",
                "ArchSig Output / CI workflow",
                vec!["archsig-contract:artifact-ci-v0.5.1"],
                &format!(
                    "Comparison report v0.5.1 records identical, verdict-row, or not-comparable run comparison together with record-level verdict transitions and archmap-diff intersections. Registered conclusionCode values are {}.",
                    registry_sentence(&ARCHSIG_COMPARISON_CONCLUSION_CODES),
                ),
                vec![
                    "Comparison report does not implement class transport, obstruction identity transport, repair causality, or semantic equivalence.",
                    "Comparison report conclusion codes are record-level names only.",
                    "Cover or context changes are boundary data and map to other_transition for gate policy evaluation.",
                ],
            ),
            artifact(
                "archsig-run-manifest/v0.5.1",
                "ArchSig analyze run manifest",
                ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec![
                    "archsig-contract:output-report",
                    "archsig-contract:command-guide",
                ],
                &format!(
                    "Run manifest records the analyze command name, deterministic runId, toolVersion, input digests, mode, conclusion code, generated artifact list, artifact links, validation report paths, and validation result summary for one ArchSig analyze run. Registered analyze conclusionCode values are {}.",
                    registry_sentence(&ARCHSIG_ANALYSIS_CONCLUSION_CODES),
                ),
                vec![
                    "Run manifest is artifact navigation metadata, not source completeness proof, architecture lawfulness, or Lean theorem discharge.",
                    "Generated artifact lists describe this run only and do not imply any unlisted artifact was produced.",
                ],
            ),
            artifact(
                "archsig-atom-viewer-data/v0.5.1",
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
            policy_version: "llm-atom-archmap/v0.5.1".to_string(),
            applies_to_catalog_version: "llm-atom-archmap/v0.5.1".to_string(),
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

fn registry_sentence(values: &[&str]) -> String {
    match values {
        [] => String::new(),
        [only] => (*only).to_string(),
        [first, second] => format!("{first} and {second}"),
        _ => {
            let mut items = values.to_vec();
            let last = items.pop().unwrap_or_default();
            format!("{}, and {}", items.join(", "), last)
        }
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
                "aat-atom-vocabulary/v0.5.1",
                "archmap-scope-manifest/v0.5.1",
                "archmap-candidate-packet/v0.5.1",
                "archmap-extraction-consistency/v0.5.1",
                "archmap-coverage-ledger/v0.5.1",
                "aat-atom-vocabulary-binding/v0.5.1",
                "law-equation-surface/v0.5.1",
                "law-policy/v0.5.1",
                "archsig-policy-bundle/v0.5.1",
                "law-evaluator-registry/v0.5.1",
                "measurement-profile/v0.5.1",
                "archsig-repair-plan/v0.5.1",
                "normalized-archmap-current",
                "archsig-measurement-packet/v0.5.1",
                "archsig-boundary-statement/v0.5.1",
                "archsig-gate-policy/v0.5.1",
                "archsig-gate-report/v0.5.1",
                "archmap-diff/v0.5.1",
                "archsig-comparison-report/v0.5.1",
                "archsig-run-manifest/v0.5.1",
                "archsig-atom-viewer-data/v0.5.1",
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
