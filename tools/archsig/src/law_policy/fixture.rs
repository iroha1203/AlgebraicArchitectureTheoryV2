use super::constants::{
    REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS, REQUIRED_NON_CONCLUSIONS,
    REQUIRED_PART4_DISTANCE_PROFILE_NON_CONCLUSIONS, REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS,
};
use super::helpers::strings;
use crate::{
    LAW_POLICY_SCHEMA_VERSION, LawPolicyAxisDefinitionV0, LawPolicyCoverageRequirementV0,
    LawPolicyDocumentV0, LawPolicyHomotopyFillerRuleV0, LawPolicyHomotopyLoopMeasurementPolicyV0,
    LawPolicyHomotopyMeasurementProfileV0, LawPolicyHomotopyPathDiscoveryRuleV0,
    LawPolicyMeasurementPolicyV0, LawPolicyMoleculePatternV0,
    LawPolicyObstructionCircuitDefinitionV0, LawPolicyPart4DistanceProfileV0,
    LawPolicyPart4DistanceWeightV0, LawPolicyPart4OperationCostV0, LawPolicyReadingBoundaryV0,
    LawPolicySelectedLawV0, LawPolicySignatureAxisDefinitionV0, LawPolicySpectrumDistanceKindV0,
    LawPolicySpectrumMeasurementProfileV0, LawPolicyWitnessRuleV0,
};

pub fn static_law_policy() -> LawPolicyDocumentV0 {
    LawPolicyDocumentV0 {
        schema_version: LAW_POLICY_SCHEMA_VERSION.to_string(),
        law_policy_id: "llm-native-aat-law-policy-fixture".to_string(),
        policy_version: "v0".to_string(),
        scope: "LLM-native ArchMap observation analysis fixture".to_string(),
        archmap_schema_ref: "archmap-observation-map-v0".to_string(),
        selected_laws: vec![
            selected_law(
                "law:layer-respecting",
                "dependency-direction",
                "Dependencies must respect the selected layer order.",
                &["relation", "boundaryAuthority"],
                &["witness:layer-violation"],
                &["axis:layer-violation"],
            ),
            selected_law(
                "law:semantic-contract-alignment",
                "semantic-contract",
                "Semantic observations and contract observations must agree on the selected operation meaning.",
                &["contractSpecification", "semanticInterpretation"],
                &["witness:semantic-contract-mismatch"],
                &["axis:semantic-inconsistency"],
            ),
        ],
        required_zero_axes: vec![
            axis(
                "axis:layer-violation",
                "dependency-direction",
                "nat",
                "zero means no required layer violation witness was constructed under this policy",
                "computedFromObservedAtoms",
                &[
                    "observed relation atoms",
                    "observed boundary membership atoms",
                ],
            ),
            axis(
                "axis:semantic-inconsistency",
                "semantic-contract",
                "nat",
                "zero means no required semantic contract mismatch witness was constructed under this policy",
                "computedFromObservedAtoms",
                &["observed semantic atoms", "observed contract atoms"],
            ),
        ],
        optional_axes: vec![axis(
            "axis:observation-gap",
            "coverage",
            "nat",
            "zero means no policy-required observation gap was reported",
            "coverageBoundary",
            &["observation gap records"],
        )],
        witness_rules: vec![
            witness_rule(
                "witness:layer-violation",
                "law:layer-respecting",
                "forbidden-dependency-direction",
                &["relation", "boundaryAuthority"],
                &["molecule:layered-component"],
            ),
            witness_rule(
                "witness:semantic-contract-mismatch",
                "law:semantic-contract-alignment",
                "semantic-contract-noncommutation",
                &["contractSpecification", "semanticInterpretation"],
                &["molecule:operation-contract"],
            ),
        ],
        molecule_patterns: vec![
            molecule_pattern(
                "molecule:layered-component",
                "layered component",
                &["existence", "boundaryAuthority"],
                &["relation"],
            ),
            molecule_pattern(
                "molecule:operation-contract",
                "operation contract",
                &["capability", "contractSpecification"],
                &["semanticInterpretation", "effect"],
            ),
        ],
        obstruction_circuit_definitions: vec![
            obstruction_definition(
                "obstruction:layer-violation",
                "law:layer-respecting",
                "witness:layer-violation",
                "BoundaryLeakCircuit",
                &["axis:layer-violation"],
            ),
            obstruction_definition(
                "obstruction:semantic-contract-mismatch",
                "law:semantic-contract-alignment",
                "witness:semantic-contract-mismatch",
                "SemanticMismatchCircuit",
                &["axis:semantic-inconsistency"],
            ),
        ],
        signature_axis_definitions: vec![
            signature_axis(
                "sig-axis:layer-violation",
                "law:layer-respecting",
                "axis:layer-violation",
                "count constructed BoundaryLeakCircuit witnesses",
            ),
            signature_axis(
                "sig-axis:semantic-inconsistency",
                "law:semantic-contract-alignment",
                "axis:semantic-inconsistency",
                "count constructed SemanticMismatchCircuit witnesses",
            ),
        ],
        measurement_policy: LawPolicyMeasurementPolicyV0 {
            policy_id: "measurement-policy:monodromy-boundary-holonomy".to_string(),
            selected_axis_refs: vec![
                "axis:layer-violation".to_string(),
                "axis:semantic-inconsistency".to_string(),
            ],
            distance_kind: "weighted-axis-l1".to_string(),
            weight_policy:
                "unit weights until repo-specific calibration is declared in a future policy"
                    .to_string(),
            coverage_policy:
                "measure only selected axes with declared coverage; missing coverage remains blocked, not zero"
                    .to_string(),
            arch_map_store_ref_kinds: vec![
                "archmap-delta".to_string(),
                "archmap-commit".to_string(),
                "archmap-snapshot".to_string(),
                "archmap-index".to_string(),
            ],
            measurement_boundary:
                "monodromy and boundary holonomy readings are finite ArchMapStore telemetry over selected axes, not theorem proofs"
                    .to_string(),
            exactness_assumption_refs: vec![
                "selected LawPolicy exactness assumptions".to_string(),
                "ArchMapStore compaction boundary".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        part4_distance_profile: Some(LawPolicyPart4DistanceProfileV0 {
            profile_id: "part4-distance-profile:llm-native-aat-law-policy-fixture".to_string(),
            atom_weights: vec![
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "atom.fiber".to_string(),
                    weight: 1,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "atom.carrier".to_string(),
                    weight: 1,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "atom.valence".to_string(),
                    weight: 1,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "atom.semanticAnchor".to_string(),
                    weight: 1,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
            ],
            signature_weights: vec![
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "sig-axis:layer-violation".to_string(),
                    weight: 1,
                    source_ref: "law:layer-respecting".to_string(),
                },
                LawPolicyPart4DistanceWeightV0 {
                    axis_ref: "sig-axis:semantic-inconsistency".to_string(),
                    weight: 1,
                    source_ref: "law:semantic-contract-alignment".to_string(),
                },
            ],
            operation_costs: vec![
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "rename".to_string(),
                    cost: 1,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "move".to_string(),
                    cost: 2,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "extract".to_string(),
                    cost: 3,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "evidence-enrichment".to_string(),
                    cost: 3,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "introduce-port".to_string(),
                    cost: 4,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "split-module".to_string(),
                    cost: 5,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "change-contract".to_string(),
                    cost: 8,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "semantic-rewrite".to_string(),
                    cost: 13,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "repair-boundaryleakcircuit".to_string(),
                    cost: 13,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "repair-semanticmismatchcircuit".to_string(),
                    cost: 13,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
                LawPolicyPart4OperationCostV0 {
                    operation_kind: "runtime-protocol-shift".to_string(),
                    cost: 21,
                    source_ref:
                        "aat-theory:distance-extension-design"
                            .to_string(),
                },
            ],
            aggregation_policy:
                "aggregate measured axes only; propagate unmeasured, unavailable, incomparable, and blocked status separately"
                    .to_string(),
            unmeasured_policy:
                "unmeasured is not zero and cannot contribute numeric zero to total measured distance"
                    .to_string(),
            law_overlay_policy:
                "law-relative distance is an overlay over ArchMap Atom observations, not an Atom generator"
                    .to_string(),
            coverage_requirement_refs: vec![
                "coverage:layer-atoms".to_string(),
                "coverage:semantic-contract-atoms".to_string(),
            ],
            evidence_boundary:
                "Part IV distances are measured from selected ArchMap evidence under this LawPolicy profile"
                    .to_string(),
            calibration_refs: Vec::new(),
            non_conclusions: strings(&REQUIRED_PART4_DISTANCE_PROFILE_NON_CONCLUSIONS),
        }),
        spectrum_measurement_profile: Some(LawPolicySpectrumMeasurementProfileV0 {
            profile_id: "spectrum-profile:curvature-transfer-default".to_string(),
            reading_boundary: reading_boundary(
                "boundedMeasuredWithProxyTransfer",
                &[
                    "coverage:layer-atoms",
                    "coverage:semantic-contract-atoms",
                    "selected LawPolicy exactness assumptions",
                ],
                &[
                    "source-backed witness support",
                    "selected axis preservation",
                    "witness completeness for measured rows",
                ],
                &[
                    "coverage:layer-atoms",
                    "coverage:semantic-contract-atoms",
                ],
                "zero spectrum reflects only selected measured witness rows with declared coverage; transfer recurrence remains bounded review telemetry",
            ),
            selected_axis_refs: vec![
                "axis:layer-violation".to_string(),
                "axis:semantic-inconsistency".to_string(),
            ],
            measured_witness_rule_refs: vec![
                "witness:layer-violation".to_string(),
                "witness:semantic-contract-mismatch".to_string(),
            ],
            distance_kinds: vec![
                LawPolicySpectrumDistanceKindV0 {
                    axis_ref: "axis:layer-violation".to_string(),
                    distance_kind: "boolean-mismatch".to_string(),
                },
                LawPolicySpectrumDistanceKindV0 {
                    axis_ref: "axis:semantic-inconsistency".to_string(),
                    distance_kind: "semantic-witness-mismatch-count".to_string(),
                },
            ],
            weight_policy: "unit weights until repo-specific calibration is declared".to_string(),
            support_projection_rule:
                "project witness support to observed Atom refs and selected axis ids".to_string(),
            transfer_edge_rule:
                "construct transfer edges only from measured witness support overlap under selected axes"
                    .to_string(),
            clustering_ranking_options: vec![
                "rank top curvature modes by weighted measured curvature".to_string(),
                "rank recurrent modes only inside the selected measured support x axis state space"
                    .to_string(),
            ],
            report_focus_options: vec![
                "surface top modes with witness refs, source refs, coverage gaps, and non-conclusions"
                    .to_string(),
            ],
            coverage_requirement_refs: vec![
                "coverage:layer-atoms".to_string(),
                "coverage:semantic-contract-atoms".to_string(),
            ],
            coverage_boundary:
                "missing coverage blocks spectrum zero reflection and remains a report gap".to_string(),
            exactness_assumption_refs: vec![
                "selected LawPolicy exactness assumptions".to_string(),
            ],
            measurement_boundary:
                "curvature-transfer spectrum readings are bounded ArchSig diagnostics, not theorem discharge"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS),
        }),
        homotopy_measurement_profile: Some(LawPolicyHomotopyMeasurementProfileV0 {
            profile_id: "homotopy-profile:bounded-stokes-default".to_string(),
            reading_boundary: reading_boundary(
                "boundedMeasuredWithCandidatePaths",
                &[
                    "coverage:layer-atoms",
                    "coverage:semantic-contract-atoms",
                    "selected path and filler evidence is supplied",
                ],
                &[
                    "selected continuation traces preserve declared axes",
                    "positive monodromy is backed by source, test, runtime, or policy evidence",
                ],
                &[
                    "coverage:layer-atoms",
                    "coverage:semantic-contract-atoms",
                ],
                "homotopy zero reflects only measured path pairs and fillers inside the selected coverage universe; unresolved paths stay coverage gaps",
            ),
            selected_axis_refs: vec![
                "axis:layer-violation".to_string(),
                "axis:semantic-inconsistency".to_string(),
            ],
            path_discovery_rules: vec![
                LawPolicyHomotopyPathDiscoveryRuleV0 {
                    rule_id: "path-rule:interface-implementation".to_string(),
                    path_source_kind: "interface-implementation-path".to_string(),
                    endpoint_policy:
                        "compare candidate paths only when endpoints are supported by observed Atom refs"
                            .to_string(),
                    candidate_source:
                        "LLM-discovered candidates must cite source refs or remain unresolved"
                            .to_string(),
                    evidence_boundary:
                        "candidate paths are bounded review cues derived from ArchMap evidence and selected LawPolicy"
                            .to_string(),
                    non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
                },
                LawPolicyHomotopyPathDiscoveryRuleV0 {
                    rule_id: "path-rule:cache-repository".to_string(),
                    path_source_kind: "cache-repository-path".to_string(),
                    endpoint_policy:
                        "compare cache and repository paths only under declared semantic and state axes"
                            .to_string(),
                    candidate_source:
                        "repository evidence, runtime notes, tests, or explicit user intent".to_string(),
                    evidence_boundary:
                        "absence of a candidate path is not proof that no architectural loop exists"
                            .to_string(),
                    non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
                },
            ],
            filler_rules: vec![
                LawPolicyHomotopyFillerRuleV0 {
                    rule_id: "filler-rule:contract-or-test".to_string(),
                    filler_kind: "contract-or-test-filler".to_string(),
                    required_source_ref_kinds: vec![
                        "doc-section".to_string(),
                        "test".to_string(),
                        "runtime-trace".to_string(),
                    ],
                    missing_filler_behavior:
                        "report architectural hole and missing filler evidence; do not promote to violation"
                            .to_string(),
                    evidence_boundary:
                        "filler evidence is bounded to supplied source refs, tests, runtime evidence, or user-confirmed policy"
                            .to_string(),
                    non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
                },
                LawPolicyHomotopyFillerRuleV0 {
                    rule_id: "filler-rule:authority-or-idempotency".to_string(),
                    filler_kind: "authority-or-idempotency-filler".to_string(),
                    required_source_ref_kinds: vec![
                        "policy".to_string(),
                        "test".to_string(),
                        "runtime-trace".to_string(),
                    ],
                    missing_filler_behavior:
                        "keep missing authority or idempotency evidence as an unfilled loop boundary"
                            .to_string(),
                    evidence_boundary:
                        "filler absence blocks Stokes-style local-curvature conclusions".to_string(),
                    non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
                },
            ],
            loop_measurement_policy: LawPolicyHomotopyLoopMeasurementPolicyV0 {
                policy_id: "loop-policy:selected-axis-holonomy".to_string(),
                loop_candidate_sources: vec![
                    "LLM-discovered candidate".to_string(),
                    "LawPolicy-required candidate".to_string(),
                    "ArchMap-supplied candidate".to_string(),
                    "source-confirmed candidate".to_string(),
                    "unresolved needsReview candidate".to_string(),
                ],
                filled_loop_reading:
                    "filled loops may localize nonzero holonomy to measured local curvature cells"
                        .to_string(),
                unfilled_loop_reading:
                    "unfilled loops are architectural holes and missing evidence surfaces".to_string(),
                holonomy_distance_kind: "selected-axis-continuation-distance".to_string(),
                local_curvature_reading_boundary:
                    "local curvature is read only for measured fillings, not for unfilled loops"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
            },
            continuation_policy:
                "compare selected continuation traces only on axes declared in this profile"
                    .to_string(),
            distance_policy:
                "bounded distance over selected semantic, state, effect, authority, and runtime axes"
                    .to_string(),
            coverage_requirement_refs: vec![
                "coverage:layer-atoms".to_string(),
                "coverage:semantic-contract-atoms".to_string(),
            ],
            coverage_boundary:
                "missing path or filler evidence blocks zero and Stokes-style readings".to_string(),
            exactness_assumption_refs: vec![
                "selected LawPolicy exactness assumptions".to_string(),
            ],
            measurement_boundary:
                "homotopy / holonomy readings are bounded ArchSig diagnostics, not theorem discharge"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS),
        }),
        exactness_assumptions: vec![
            "the selected witness rules cover only policy-declared laws".to_string(),
            "zero readings are exact only for observed atoms and declared coverage requirements"
                .to_string(),
        ],
        coverage_requirements: vec![
            coverage_requirement(
                "coverage:layer-atoms",
                &["law:layer-respecting"],
                &["existence", "relation", "boundaryAuthority"],
                &["file", "symbol"],
            ),
            coverage_requirement(
                "coverage:semantic-contract-atoms",
                &["law:semantic-contract-alignment"],
                &[
                    "capability",
                    "contractSpecification",
                    "semanticInterpretation",
                ],
                &["file", "doc-section", "test"],
            ),
        ],
        excluded_readings: vec![
            "global architecture truth".to_string(),
            "Lean theorem discharge".to_string(),
            "SFT forecast correctness".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}
fn selected_law(
    law_id: &str,
    law_family: &str,
    description: &str,
    applies_to_atom_families: &[&str],
    required_witness_refs: &[&str],
    required_axis_refs: &[&str],
) -> LawPolicySelectedLawV0 {
    LawPolicySelectedLawV0 {
        law_id: law_id.to_string(),
        law_family: law_family.to_string(),
        description: description.to_string(),
        enforcement_boundary: "ArchSig computes witnesses from observed Atom records; this policy does not prove lawfulness".to_string(),
        applies_to_atom_families: strings(applies_to_atom_families),
        required_witness_refs: strings(required_witness_refs),
        required_axis_refs: strings(required_axis_refs),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn axis(
    axis_id: &str,
    axis_family: &str,
    value_type: &str,
    zero_reading: &str,
    measurement_boundary: &str,
    evidence_requirements: &[&str],
) -> LawPolicyAxisDefinitionV0 {
    LawPolicyAxisDefinitionV0 {
        axis_id: axis_id.to_string(),
        axis_family: axis_family.to_string(),
        value_type: value_type.to_string(),
        zero_reading: zero_reading.to_string(),
        measurement_boundary: measurement_boundary.to_string(),
        evidence_requirements: strings(evidence_requirements),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn reading_boundary(
    reading_strength: &str,
    zero_reflection_assumptions: &[&str],
    obstruction_reflection_assumptions: &[&str],
    coverage_requirement_refs: &[&str],
    witness_completeness_boundary: &str,
) -> LawPolicyReadingBoundaryV0 {
    LawPolicyReadingBoundaryV0 {
        reading_strength: reading_strength.to_string(),
        zero_reflection_assumptions: strings(zero_reflection_assumptions),
        obstruction_reflection_assumptions: strings(obstruction_reflection_assumptions),
        coverage_requirement_refs: strings(coverage_requirement_refs),
        witness_completeness_boundary: witness_completeness_boundary.to_string(),
    }
}

fn witness_rule(
    witness_rule_id: &str,
    law_ref: &str,
    witness_kind: &str,
    required_atom_families: &[&str],
    molecule_pattern_refs: &[&str],
) -> LawPolicyWitnessRuleV0 {
    LawPolicyWitnessRuleV0 {
        witness_rule_id: witness_rule_id.to_string(),
        law_ref: law_ref.to_string(),
        witness_kind: witness_kind.to_string(),
        atom_observation_refs: Vec::new(),
        required_atom_families: strings(required_atom_families),
        molecule_pattern_refs: strings(molecule_pattern_refs),
        evidence_boundary: "construct only from observed ArchMap Atom observations; concern hints are not obstruction circuits".to_string(),
        missing_evidence_behavior: "report observation gap; do not infer measured zero".to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn molecule_pattern(
    molecule_pattern_id: &str,
    role_name: &str,
    required_atom_families: &[&str],
    optional_atom_families: &[&str],
) -> LawPolicyMoleculePatternV0 {
    LawPolicyMoleculePatternV0 {
        molecule_pattern_id: molecule_pattern_id.to_string(),
        role_name: role_name.to_string(),
        required_atom_families: strings(required_atom_families),
        optional_atom_families: strings(optional_atom_families),
        interpretation_boundary:
            "molecule pattern is role interpretation over atoms, not a primitive atom".to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn obstruction_definition(
    obstruction_circuit_id: &str,
    law_ref: &str,
    witness_rule_ref: &str,
    circuit_kind: &str,
    signature_axis_refs: &[&str],
) -> LawPolicyObstructionCircuitDefinitionV0 {
    LawPolicyObstructionCircuitDefinitionV0 {
        obstruction_circuit_id: obstruction_circuit_id.to_string(),
        law_ref: law_ref.to_string(),
        witness_rule_ref: witness_rule_ref.to_string(),
        circuit_kind: circuit_kind.to_string(),
        minimality_reading: "minimality is evaluated within the selected observed Atom configuration and witness rule".to_string(),
        evidence_boundary: "law-relative ArchSig witness, not ArchMap observation and not Lean theorem discharge".to_string(),
        signature_axis_refs: strings(signature_axis_refs),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn signature_axis(
    signature_axis_id: &str,
    law_ref: &str,
    axis_ref: &str,
    valuation_rule: &str,
) -> LawPolicySignatureAxisDefinitionV0 {
    LawPolicySignatureAxisDefinitionV0 {
        signature_axis_id: signature_axis_id.to_string(),
        law_ref: law_ref.to_string(),
        axis_ref: axis_ref.to_string(),
        valuation_rule: valuation_rule.to_string(),
        value_type: "nat".to_string(),
        zero_reading: "zero means no matching required witness was constructed under declared coverage and exactness assumptions".to_string(),
        coverage_boundary: "coverage gaps remain observation gaps, not measured zero".to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn coverage_requirement(
    coverage_requirement_id: &str,
    applies_to_law_refs: &[&str],
    required_atom_families: &[&str],
    required_source_ref_kinds: &[&str],
) -> LawPolicyCoverageRequirementV0 {
    LawPolicyCoverageRequirementV0 {
        coverage_requirement_id: coverage_requirement_id.to_string(),
        applies_to_law_refs: strings(applies_to_law_refs),
        required_atom_families: strings(required_atom_families),
        required_source_ref_kinds: strings(required_source_ref_kinds),
        missing_coverage_behavior: "report observation gap and block signature-zero reflection"
            .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}
