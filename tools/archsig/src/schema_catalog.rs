use crate::{
    ARCHITECTURE_DISTANCE_V1_SCHEMA, ARCHMAP_SCHEMA_VERSION, ARCHMAP_V1_SCHEMA, ARCHMAP_V2_SCHEMA,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA, ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
    ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION, ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
    ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION, LAW_POLICY_SCHEMA_VERSION, LAW_POLICY_V1_SCHEMA,
    LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION, MEASUREMENT_PROFILE_V1_SCHEMA,
    NORMALIZED_ARCHMAP_V1_SCHEMA, NORMALIZED_ARCHMAP_V2_SCHEMA,
    SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION, SCHEMA_VERSION_CATALOG_SCHEMA_VERSION,
    SchemaCompatibilityBoundaryV0, SchemaCompatibilityDimensionV0, SchemaCompatibilityPolicyV0,
    SchemaVersionCatalogEntryV0, SchemaVersionCatalogV0, TYPED_EVALUATOR_RESULTS_V1_SCHEMA,
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
                "Legacy ArchMap v0 observation artifact",
                ARCHMAP_SCHEMA_VERSION,
                "legacy",
                "Historical ArchMap v0",
                vec![
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/atom_handoff.md",
                ],
                "Legacy ArchMap v0 recorded atomObservations, moleculeObservations, semanticObservations, observationGaps, projectionInfo, operationSquareEvidence, concernHints, provenance, and nonConclusions. It is not a current runtime input.",
                vec![
                    "ArchMap does not prove architecture lawfulness, obstruction existence, zero curvature, or certified atom truth.",
                    "ArchMap concern hints are review cues until ArchSig combines them with a selected LawPolicy.",
                ],
            ),
            artifact(
                "archmap-validation-report",
                "Legacy ArchMap v0 validation report",
                ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
                "legacy",
                "Historical ArchMap v0",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                "ArchMap validation checks source refs, claim boundaries, projection separation, atom observation summaries, and responsibility boundaries without promoting observations to formal truth.",
                vec![
                    "Validation pass does not imply semantic correctness, architecture lawfulness, source completeness, zero curvature, or Lean theorem discharge.",
                    "Validation diagnostics are bounded tool checks, not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "archmap-v1",
                "ArchMap v1 Atom input artifact",
                ARCHMAP_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["docs/tool/archmap_minimal_observation_contract_prd.md"],
                "ArchMap v1 records sources, atoms, and molecules as the primary input contract. It rejects legacy v0 root fields, unknown atom kinds, unknown predicates, and unresolved source refs before analysis.",
                vec![
                    "ArchMap v1 validation does not run the v1 evaluator pipeline.",
                    "ArchMap v1 validation does not prove architecture lawfulness, source completeness, Lean theorem discharge, or global semantic truth.",
                ],
            ),
            artifact(
                "archmap-v2",
                "ArchMap v2 finite poset site artifact",
                ARCHMAP_V2_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md"],
                "ArchMap v2 records sources, subject/axis-decorated atoms, finite context posets, covers, and extractionDoctrineRef. Molecules are not a primary v2 field.",
                vec![
                    "ArchMap v2 validation does not prove source extraction soundness, U-adequacy, exactness, Lean theorem discharge, or architecture lawfulness.",
                    "Contexts and covers are observation structure; measurement choices live in MeasurementProfile.",
                ],
            ),
            artifact(
                "law-policy",
                "Legacy LawPolicy v0 interpretation profile artifact",
                LAW_POLICY_SCHEMA_VERSION,
                "legacy",
                "Historical LawPolicy v0",
                vec![
                    "docs/tool/archsig_aat_analysis_engine_prd.md",
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                    "docs/tool/README.md",
                ],
                "The legacy law-policy-v0 JSON contract selected laws, witness rules, molecule patterns, obstruction definitions, signature axes, measurement policy, optional spectrum measurement profile, optional homotopy measurement profile, exactness assumptions, coverage requirements, excluded readings, and non-conclusions. It is not a current runtime input.",
                vec![
                    "Interpretation profile is selected analysis policy, not AAT itself, architecture lawfulness, atom truth, or Lean theorem discharge.",
                    "Adding a law family must preserve missing coverage as distinct from measured zero.",
                    "Changing a spectrum measurement profile changes a measurement recipe, not the selected law universe.",
                    "Changing a homotopy measurement profile changes a path / filler / loop measurement recipe, not the selected law universe.",
                ],
            ),
            artifact(
                "law-policy-v1",
                "LawPolicy v1 selector artifact",
                LAW_POLICY_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["docs/tool/archmap_minimal_observation_contract_prd.md"],
                "LawPolicy v1 selects policy packs or explicit law/evaluator pairs with registry-owned basis, scope, and severity. It rejects unknown packs, unknown evaluators, unresolved basis refs, and DSL-style witness rules before analysis.",
                vec![
                    "LawPolicy v1 selects evaluators; it does not define witness predicates, axis valuation, obstruction definitions, or Lean proofs.",
                    "LawPolicy v1 validation does not run the v1 evaluator pipeline.",
                ],
            ),
            artifact(
                "measurement-profile-v1",
                "MeasurementProfile v1 AG evaluator selector",
                MEASUREMENT_PROFILE_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md"],
                "MeasurementProfile v1 declares selected site, cover, coefficient, EffCoeff procedure, witness family, resolution selector, Dom/Zero/NonZero/Cert predicates, and five-valued verdict discipline.",
                vec![
                    "MeasurementProfile selects a bounded measurement regime; it does not prove adequacy or theorem hypotheses.",
                    "Profile absence for AG evaluators is a validation error, not an unmeasured zero result.",
                ],
            ),
            artifact(
                "law-evaluator-registry-v1",
                "Law evaluator registry v1",
                "law-evaluator-registry/v1",
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["docs/tool/archmap_minimal_observation_contract_prd.md"],
                "Law evaluator registry v1 owns evaluator manifests, policy pack expansion, basis refs, missing blocker rules, pass / violation criteria, typed result schema refs, distance contribution, and output refs. LawPolicy v1 selects entries from this registry.",
                vec![
                    "Evaluator registry manifest is an ArchSig computation contract, not a Lean theorem proof.",
                    "LawPolicy v1 cannot override witness rules, axis rules, distance formula, pass criteria, or violation criteria.",
                ],
            ),
            artifact(
                "law-policy-validation-report",
                "Legacy LawPolicy v0 validation report",
                LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
                "legacy",
                "Historical LawPolicy v0",
                vec!["docs/tool/llm_native_archmap_archsig_prd.md"],
                "LawPolicy validation checks schema support, identity, id uniqueness, law/witness/axis references, measurement policy, optional spectrum measurement profile refs, optional homotopy path / filler / loop measurement profile refs, coverage, exactness, and non-conclusion guardrails.",
                vec![
                    "Validation pass does not imply architecture lawfulness, certified atom truth, zero curvature, or Lean theorem discharge.",
                    "Policy validation is not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "normalized-archmap-v1",
                "Normalized ArchMap v1 computation artifact",
                NORMALIZED_ARCHMAP_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["docs/tool/archmap_minimal_observation_contract_prd.md"],
                "Normalized ArchMap v1 is generated by the ArchSig normalizer from ArchMap v1 without rereading the source repository. It records normalized AtomKind / Axis / predicate bindings, valence template refs, molecule memberships, and generated molecule candidate status.",
                vec![
                    "Normalized ArchMap v1 is deterministic tooling input for evaluators, not a Lean proof object.",
                    "Generated molecule candidate status is not an obstruction, holonomy, risk, or lawfulness conclusion.",
                ],
            ),
            artifact(
                "normalized-archmap-v2",
                "Normalized ArchMap v2 finite poset site artifact",
                NORMALIZED_ARCHMAP_V2_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md"],
                "Normalized ArchMap v2 is the deterministic finite-poset-site presentation produced from ArchMap v2 under a declared extraction doctrine fingerprint.",
                vec![
                    "Normalized ArchMap v2 does not prove source extraction soundness.",
                    "A8 determinism is relative to the declared extraction doctrine fingerprint.",
                ],
            ),
            artifact(
                "typed-evaluator-results-v1",
                "Typed evaluator results v1",
                TYPED_EVALUATOR_RESULTS_V1_SCHEMA,
                "primary",
                "ArchMap Atom-to-AAT contract",
                vec!["docs/tool/archmap_minimal_observation_contract_prd.md"],
                "Typed evaluator results v1 records evaluator status, support atom refs, support molecule refs, basis refs, detail refs, and bounded conclusions computed from Normalized ArchMap v1 and LawPolicy v1.",
                vec![
                    "Typed evaluator results do not read label-only, memo-only, removed-field-only, or schema-only evidence as measured support.",
                    "Blocked, unknown, and unmeasured results are not measured zero.",
                ],
            ),
            artifact(
                "architecture-distance-v1",
                "Architecture distance v1 computation artifact",
                ARCHITECTURE_DISTANCE_V1_SCHEMA,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec!["docs/tool/README.md"],
                "Architecture distance v1 records measured atom, configuration, signature, operation, primary curvature geometry readings, primary homotopy filling geometry readings, primary representation metric readings, and distanceInsights computed from Normalized ArchMap v1, TypedEvaluatorResults v1, raw v1 packet distance rows, and the selected LawPolicy distanceProfileRef.",
                vec![
                    "Architecture distance is a diagnostic ArchSig artifact, not a Lean theorem proof.",
                    "Typed evaluator violation counts are not substituted for architecture distance.",
                    "Blocked or unmeasured distance readings are not measured zero.",
                ],
            ),
            artifact(
                "archsig-measurement-packet-v1",
                "ArchSig measurement packet v1",
                ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA,
                "primary",
                "ArchSig v0.4.0 Algebraic Geometry Measurement",
                vec!["docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md"],
                "ArchSig measurement packet v1 carries profile, structuralVerdict, computedInvariants, analyticReadings, assumptions, and nonConclusions as the AG Definition 11.1-aligned output contract.",
                vec![
                    "Structural verdicts are limited to measured_zero, measured_nonzero, unmeasured, unknown, and not_computed.",
                    "Analytic readings do not generate structural verdicts unless a certified evaluator explicitly emits one.",
                    "Theorem-candidate readings are analytic-only.",
                ],
            ),
            artifact(
                "archsig-analysis-packet",
                "Legacy ArchSig v0 AAT analysis packet",
                ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
                "legacy",
                "Historical ArchSig v0 packet",
                vec![
                    "docs/tool/archsig_aat_analysis_engine_prd.md",
                    "docs/tool/archsig_analysis_packet.md",
                    "docs/tool/llm_native_archmap_archsig_prd.md",
                ],
                "ArchSig analysis packet owns AAT concept surfaces, architecture state, design pressure, change impact, architecture object projections, invariant family readings, LawUniverse reading, molecule readings, Part IV distance foundation with DistanceValue / DistanceProfile / DiagnosticScope provenance gates, Part IV Atom distance readings, Part IV selected configuration hypergraph distance readings with typed hyperedges / shortest paths / context overlap / gap blockers, Part IV signature distance readings with rho_i / safe-region margin / drift / axis partitions, Part IV operation distance readings with operation cost / target decrease / protected-axis movement / side-effect blockers, Part IV obstruction measure and curvature mass readings with witness-backed Omega_U / curv_mass_U / transport blockers, Part IV homotopy distance readings with filling cost / observation-gap lower bound / selected Dehn-style area blockers, obstruction circuits, signature axes, analytic representations, coupling/cohesion readings, spectral analysis readings, spectral mode readings, spectral drilldown readings, curvature support readings, curvature transfer readings, ArchitectureSpectrumReport, transfer bridge readings with edge source refs, review focus, and cut recommendations, Atom support / axis restriction readings, Atom compatibility readings, LawUniverse coverage readings, feature extension formula readings, operation calculus law readings, path signature trajectory readings, homotopy / operation-order sensitivity readings, diagram fillability readings, axis-forgetting / projection reflection loss readings, signature trajectory homotopy refutation readings, bridge split obstruction transfer readings, homotopy complex summaries, path pair candidates, loop candidates, filler candidate readings, architectural hole readings, homotopy holonomy readings, Stokes-style readings, ArchitectureHomotopyReport, representation strength readings, local curvature diagram readings, three-layer flatness readings, observation projection readings, state transition algebra readings, operation/invariant Galois readings, split readiness readings, structural reading review surface, current-state/evolution boundary, design principle readings, operation deltas, path/homotopy/diagram readings, bounded judgements, LLM interpretation packet, evidence boundary, excluded readings, and non-conclusions.",
                vec![
                    "Analysis packet is not a Lean theorem proof, global architecture truth, extractor completeness proof, quality score, or automatic safe repair.",
                    "Analysis packet compatibility is a JSON contract, not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "archsig-analysis-packet-v1",
                "ArchSig v1 typed evaluator analysis packet",
                ARCHSIG_ANALYSIS_PACKET_V1_SCHEMA,
                "primary",
                "FieldSig handoff / raw evidence store",
                vec![
                    "docs/tool/archmap_minimal_observation_contract_prd.md",
                    "docs/tool/archsig_analysis_packet.md",
                    "docs/tool/llm_native_e2e_workflow.md",
                ],
                "ArchSig v1 analysis packet is emitted only in raw mode and is the current FieldSig handoff contract. It carries typed evaluator results, architecture distance, generated packet refs, spectrum, homotopy, structural reading surface, bounded conclusions, detail refs, and non-conclusions.",
                vec![
                    "ArchSig v1 packet is bounded current structural state, not forecast truth, a Lean proof, global architecture truth, or automatic repair safety.",
                    "FieldSig reads v1 packet refs as SFT input coordinates and owns PR / diff / change-vector evolution analysis.",
                ],
            ),
            artifact(
                "archsig-analysis-packet-validation-report",
                "Legacy ArchSig v0 analysis packet validation report",
                ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION,
                "legacy",
                "Historical ArchSig v0 packet",
                vec!["docs/tool/archsig_analysis_packet.md"],
                "Validation separates JSON surface checks from measurement-depth and proxy-regression checks. It checks identity, ArchMap and LawPolicy refs, Part IV distance foundation profile / diagnostic scope / DistanceValue status and provenance gates, Part IV Atom distance component basis / semantic-anchor blockers / viewer-distance separation, Part IV selected configuration hypergraph typed edges / shortest-path basis / context basis / observation-gap blockers, Part IV signature distance rho_i basis / safe-region margin / drift / axis partitions, Part IV operation cost / target decrease / protected-axis movement / side-effect blockers, Part IV obstruction measure / curvature mass / curvature transport distance refs and missing-witness blockers, Part IV homotopy distance / filling cost / observation-gap lower-bound refs and missing-filler blockers, spectral analysis readings, spectral mode readings, spectral drilldown readings, curvature support readings, curvature transfer readings, ArchitectureSpectrumReport, transfer bridge readings, bridge edge source refs / review focus / cut recommendations, v0.3.0 measurement expansion readings including reverse-import projection / trajectory / bridge-transfer readings, homotopy complex / path pair / loop candidate surfaces, filler candidate and architectural hole surfaces, homotopy holonomy and Stokes-style surfaces, ArchitectureHomotopyReport, AAT structural state readings, structural reading review surface, current-state/evolution boundary, law-relative obstruction links, signature and flatness boundaries, repair candidate guardrails, evaluator input refs, distance value provenance, witness rule alignment, coverage blockers, hard-coded fixture marker rejection, LLM interpretation surface, and non-conclusions without recomputing the full analysis engine.",
                vec![
                    "Validation pass does not imply architecture lawfulness, source completeness, flatness proof, or repair safety.",
                    "Validation report compatibility is not a semantic-preservation theorem.",
                ],
            ),
            artifact(
                "archsig-run-manifest",
                "ArchSig analyze run manifest",
                ARCHSIG_RUN_MANIFEST_SCHEMA_VERSION,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec![
                    "docs/tool/archsig_output_report_prd.md",
                    "tools/archsig/docs/commands.md",
                ],
                "Run manifest records the analyze command name, input artifact paths, output mode, generated and omitted artifact lists, validation report paths, optional raw artifact paths, and validation result summary for one ArchSig analyze run.",
                vec![
                    "Run manifest is artifact navigation metadata, not source completeness proof, architecture lawfulness, or Lean theorem discharge.",
                    "Generated and omitted artifact lists describe this run only; omitted raw artifacts can be regenerated with explicit raw retention.",
                ],
            ),
            artifact(
                "archsig-atom-viewer-data",
                "ArchSig Atom Viewer bounded projection data",
                ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION,
                "primary",
                "ArchSig Output / Viewer workflow",
                vec![
                    "docs/tool/archsig_output_report_prd.md",
                    "tools/archsig/docs/commands.md",
                ],
                "Atom Viewer data records source artifact refs, bounded layout settings, atom nodes, molecule groups, selected law-axis overlays, analysis overlays, report pane sections, omitted detail counts, truncation policy, and non-conclusions for browser visualization without embedding the raw analysis packet.",
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
            ids,
            BTreeSet::from([
                "archmap",
                "archmap-validation-report",
                "archmap-v1",
                "archmap-v2",
                "law-policy",
                "law-policy-validation-report",
                "law-policy-v1",
                "law-evaluator-registry-v1",
                "measurement-profile-v1",
                "normalized-archmap-v1",
                "normalized-archmap-v2",
                "typed-evaluator-results-v1",
                "architecture-distance-v1",
                "archsig-measurement-packet-v1",
                "archsig-analysis-packet",
                "archsig-analysis-packet-v1",
                "archsig-analysis-packet-validation-report",
                "archsig-run-manifest",
                "archsig-atom-viewer-data",
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
