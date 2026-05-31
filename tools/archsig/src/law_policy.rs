use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    LAW_POLICY_SCHEMA_VERSION, LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
    LawPolicyAxisDefinitionV0, LawPolicyCoverageRequirementV0, LawPolicyDocumentV0,
    LawPolicyHomotopyFillerRuleV0, LawPolicyHomotopyLoopMeasurementPolicyV0,
    LawPolicyHomotopyMeasurementProfileV0, LawPolicyHomotopyPathDiscoveryRuleV0,
    LawPolicyMeasurementPolicyV0, LawPolicyMoleculePatternV0,
    LawPolicyObstructionCircuitDefinitionV0, LawPolicyReadingBoundaryV0, LawPolicySelectedLawV0,
    LawPolicySignatureAxisDefinitionV0, LawPolicySpectrumDistanceKindV0,
    LawPolicySpectrumMeasurementProfileV0, LawPolicyValidationInputV0, LawPolicyValidationReportV0,
    LawPolicyValidationSummaryV0, LawPolicyWitnessRuleV0, ValidationCheck, ValidationExample,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "law policy is selected analysis policy, not AAT itself",
    "law policy validation does not prove architecture lawfulness",
    "law policy validation does not certify atom truth",
    "missing coverage is not measured zero",
    "signature zero requires ArchSig analysis with declared coverage and exactness assumptions",
];

const REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS: [&str; 4] = [
    "spectrum measurement profile is a measurement recipe, not a law universe",
    "profile differences are not law universe differences",
    "unmeasured axes are not zero",
    "spectrum zero requires coverage, exactness, and zero-reflection assumptions",
];

const REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS: [&str; 5] = [
    "homotopy measurement profile is a measurement recipe, not a law universe",
    "candidate paths and loops are review cues, not path truth",
    "unfilled loops are architectural holes, not automatic violations",
    "missing filler evidence is not measured zero",
    "nonzero holonomy does not prove future incidents or repair unsafety",
];

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

pub fn validate_law_policy_report(
    policy: &LawPolicyDocumentV0,
    input_path: &str,
) -> LawPolicyValidationReportV0 {
    let checks = vec![
        check_schema_version(policy),
        check_identity(policy),
        check_ids_unique(policy),
        check_law_refs(policy),
        check_axis_refs(policy),
        check_witness_and_obstruction_boundaries(policy),
        check_coverage_and_exactness(policy),
        check_measurement_policy(policy),
        check_spectrum_measurement_profile(policy),
        check_homotopy_measurement_profile(policy),
        check_non_conclusions(policy),
    ];
    let summary = LawPolicyValidationSummaryV0 {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        selected_law_count: policy.selected_laws.len(),
        required_zero_axis_count: policy.required_zero_axes.len(),
        witness_rule_count: policy.witness_rules.len(),
        obstruction_circuit_definition_count: policy.obstruction_circuit_definitions.len(),
        signature_axis_definition_count: policy.signature_axis_definitions.len(),
        coverage_requirement_count: policy.coverage_requirements.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    LawPolicyValidationReportV0 {
        schema_version: LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: LawPolicyValidationInputV0 {
            schema_version: policy.schema_version.clone(),
            path: input_path.to_string(),
            law_policy_id: policy.law_policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            archmap_schema_ref: policy.archmap_schema_ref.clone(),
        },
        policy: policy.clone(),
        summary,
        checks,
    }
}

fn check_measurement_policy(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let required_store_kinds = BTreeSet::from([
        "archmap-delta",
        "archmap-commit",
        "archmap-snapshot",
        "archmap-index",
    ]);
    let present_store_kinds = policy
        .measurement_policy
        .arch_map_store_ref_kinds
        .iter()
        .map(|kind| kind.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "measurementPolicy.policyId",
        &policy.measurement_policy.policy_id,
    );
    if policy.measurement_policy.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &policy.measurement_policy.policy_id,
            "selectedAxisRefs",
            "measurement policy must select axes for monodromy and boundary holonomy readings",
        ));
    }
    for axis_ref in &policy.measurement_policy.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &policy.measurement_policy.policy_id,
                axis_ref,
                "measurement policy selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    for required_kind in required_store_kinds {
        if !present_store_kinds.contains(required_kind) {
            examples.push(generic_validation_example(
                &policy.measurement_policy.policy_id,
                required_kind,
                "measurement policy must declare every ArchMapStore ref kind",
            ));
        }
    }
    push_blank(
        &mut examples,
        "measurementPolicy.distanceKind",
        &policy.measurement_policy.distance_kind,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.weightPolicy",
        &policy.measurement_policy.weight_policy,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.coveragePolicy",
        &policy.measurement_policy.coverage_policy,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.measurementBoundary",
        &policy.measurement_policy.measurement_boundary,
    );
    if policy.measurement_policy.non_conclusions.is_empty()
        || has_blank(&policy.measurement_policy.non_conclusions)
    {
        examples.push(generic_validation_example(
            &policy.measurement_policy.policy_id,
            "nonConclusions",
            "measurement policy must keep non-conclusions explicit",
        ));
    }

    check_from_examples(
        "law-policy-monodromy-measurement-policy",
        "LawPolicy declares selected axes, distance, weight, coverage, and ArchMapStore ref kinds for monodromy readings",
        examples,
        "fail",
    )
}

fn check_spectrum_measurement_profile(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let Some(profile) = &policy.spectrum_measurement_profile else {
        return validation_check(
            "law-policy-spectrum-measurement-profile",
            "optional spectrum measurement profile is absent; LawPolicy remains valid without ACTS readings",
            "pass",
        );
    };

    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let coverage_ids = set(policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.as_str()));
    let present_non_conclusions = profile
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.profileId",
        &profile.profile_id,
    );
    if profile.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "selectedAxisRefs",
            "spectrum profile must select axes for curvature support readings",
        ));
    }
    for axis_ref in &profile.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                axis_ref,
                "spectrum profile selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    if profile.measured_witness_rule_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "measuredWitnessRuleRefs",
            "spectrum profile must declare measured witness rule refs",
        ));
    }
    for witness_ref in &profile.measured_witness_rule_refs {
        if !witness_ids.contains(witness_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                witness_ref,
                "spectrum profile measuredWitnessRuleRefs must reference known witness rules",
            ));
        }
    }
    if profile.distance_kinds.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "distanceKinds",
            "spectrum profile must declare at least one axis distance kind",
        ));
    }
    for distance in &profile.distance_kinds {
        if !axis_ids.contains(distance.axis_ref.as_str())
            && !signature_axis_ids.contains(distance.axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &distance.axis_ref,
                "spectrum distanceKinds[].axisRef must reference known axes or signature axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("spectrum distance kind for {}", distance.axis_ref),
            &distance.distance_kind,
        );
    }
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.weightPolicy",
        &profile.weight_policy,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.supportProjectionRule",
        &profile.support_projection_rule,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.transferEdgeRule",
        &profile.transfer_edge_rule,
    );
    if profile.coverage_requirement_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "coverageRequirementRefs",
            "spectrum profile must reference coverage requirements",
        ));
    }
    for coverage_ref in &profile.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                coverage_ref,
                "spectrum profile coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    validate_reading_boundary(
        &mut examples,
        &profile.profile_id,
        "spectrumMeasurementProfile.readingBoundary",
        &profile.reading_boundary,
        &coverage_ids,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.coverageBoundary",
        &profile.coverage_boundary,
    );
    if profile.exactness_assumption_refs.is_empty() || has_blank(&profile.exactness_assumption_refs)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "exactnessAssumptionRefs",
            "spectrum profile must record exactness assumption refs",
        ));
    }
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.measurementBoundary",
        &profile.measurement_boundary,
    );
    if profile.non_conclusions.is_empty() || has_blank(&profile.non_conclusions) {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "nonConclusions",
            "spectrum profile must keep non-conclusions explicit",
        ));
    }
    for required in REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS {
        if !present_non_conclusions.contains(required) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required,
                "missing required spectrum profile non-conclusion",
            ));
        }
    }

    check_from_examples(
        "law-policy-spectrum-measurement-profile",
        "LawPolicy keeps spectrum measurement recipes separate from the selected law universe",
        examples,
        "fail",
    )
}

fn check_homotopy_measurement_profile(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let Some(profile) = &policy.homotopy_measurement_profile else {
        return validation_check(
            "law-policy-homotopy-measurement-profile",
            "optional homotopy measurement profile is absent; LawPolicy remains valid without homotopy readings",
            "pass",
        );
    };

    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let coverage_ids = set(policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.as_str()));
    let present_non_conclusions = profile
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.profileId",
        &profile.profile_id,
    );
    if profile.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "selectedAxisRefs",
            "homotopy profile must select axes for continuation and holonomy readings",
        ));
    }
    for axis_ref in &profile.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                axis_ref,
                "homotopy profile selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    if profile.path_discovery_rules.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "pathDiscoveryRules",
            "homotopy profile must declare path discovery rules",
        ));
    }
    for rule in &profile.path_discovery_rules {
        push_blank(&mut examples, "pathDiscoveryRules[].ruleId", &rule.rule_id);
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].pathSourceKind", rule.rule_id),
            &rule.path_source_kind,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].endpointPolicy", rule.rule_id),
            &rule.endpoint_policy,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].candidateSource", rule.rule_id),
            &rule.candidate_source,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].evidenceBoundary", rule.rule_id),
            &rule.evidence_boundary,
        );
        if rule.non_conclusions.is_empty() || has_blank(&rule.non_conclusions) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy path discovery rules must keep non-conclusions explicit",
            ));
        }
    }
    if profile.filler_rules.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "fillerRules",
            "homotopy profile must declare filler rules",
        ));
    }
    for rule in &profile.filler_rules {
        push_blank(&mut examples, "fillerRules[].ruleId", &rule.rule_id);
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].fillerKind", rule.rule_id),
            &rule.filler_kind,
        );
        if rule.required_source_ref_kinds.is_empty() || has_blank(&rule.required_source_ref_kinds) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy filler rules must declare required source ref kinds",
            ));
        }
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].missingFillerBehavior", rule.rule_id),
            &rule.missing_filler_behavior,
        );
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].evidenceBoundary", rule.rule_id),
            &rule.evidence_boundary,
        );
        if rule.non_conclusions.is_empty() || has_blank(&rule.non_conclusions) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy filler rules must keep non-conclusions explicit",
            ));
        }
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.loopMeasurementPolicy.policyId",
        &profile.loop_measurement_policy.policy_id,
    );
    if profile
        .loop_measurement_policy
        .loop_candidate_sources
        .is_empty()
        || has_blank(&profile.loop_measurement_policy.loop_candidate_sources)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "loopMeasurementPolicy.loopCandidateSources",
            "homotopy loop measurement policy must declare candidate sources",
        ));
    }
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.filledLoopReading",
        &profile.loop_measurement_policy.filled_loop_reading,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.unfilledLoopReading",
        &profile.loop_measurement_policy.unfilled_loop_reading,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.holonomyDistanceKind",
        &profile.loop_measurement_policy.holonomy_distance_kind,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.localCurvatureReadingBoundary",
        &profile
            .loop_measurement_policy
            .local_curvature_reading_boundary,
    );
    if profile.loop_measurement_policy.non_conclusions.is_empty()
        || has_blank(&profile.loop_measurement_policy.non_conclusions)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "loopMeasurementPolicy.nonConclusions",
            "homotopy loop measurement policy must keep non-conclusions explicit",
        ));
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.continuationPolicy",
        &profile.continuation_policy,
    );
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.distancePolicy",
        &profile.distance_policy,
    );
    if profile.coverage_requirement_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "coverageRequirementRefs",
            "homotopy profile must reference coverage requirements",
        ));
    }
    for coverage_ref in &profile.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                coverage_ref,
                "homotopy profile coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    validate_reading_boundary(
        &mut examples,
        &profile.profile_id,
        "homotopyMeasurementProfile.readingBoundary",
        &profile.reading_boundary,
        &coverage_ids,
    );
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.coverageBoundary",
        &profile.coverage_boundary,
    );
    if profile.exactness_assumption_refs.is_empty() || has_blank(&profile.exactness_assumption_refs)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "exactnessAssumptionRefs",
            "homotopy profile must record exactness assumption refs",
        ));
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.measurementBoundary",
        &profile.measurement_boundary,
    );
    if profile.non_conclusions.is_empty() || has_blank(&profile.non_conclusions) {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "nonConclusions",
            "homotopy profile must keep non-conclusions explicit",
        ));
    }
    for required in REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS {
        if !present_non_conclusions.contains(required) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required,
                "missing required homotopy profile non-conclusion",
            ));
        }
    }

    check_from_examples(
        "law-policy-homotopy-measurement-profile",
        "LawPolicy keeps homotopy path, filler, loop, coverage, and non-conclusion recipes separate from the selected law universe",
        examples,
        "fail",
    )
}

fn check_schema_version(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut check = validation_check(
        "law-policy-schema-version-supported",
        "law policy schema version is supported",
        if policy.schema_version == LAW_POLICY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported law policy schemaVersion: {}",
            policy.schema_version
        ));
    }
    check
}

fn check_identity(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "lawPolicyId", &policy.law_policy_id);
    push_blank(&mut examples, "policyVersion", &policy.policy_version);
    push_blank(&mut examples, "scope", &policy.scope);
    push_blank(
        &mut examples,
        "archMapSchemaRef",
        &policy.archmap_schema_ref,
    );
    check_from_examples(
        "law-policy-identity-recorded",
        "law policy identity, scope, and target ArchMap schema are recorded",
        examples,
        "fail",
    )
}

fn check_ids_unique(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "selectedLaws[].lawId",
        duplicates(policy.selected_laws.iter().map(|law| law.law_id.as_str())),
    ));
    examples.extend(duplicate_examples(
        "requiredZeroAxes[].axisId",
        duplicates(
            policy
                .required_zero_axes
                .iter()
                .map(|axis| axis.axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "optionalAxes[].axisId",
        duplicates(
            policy
                .optional_axes
                .iter()
                .map(|axis| axis.axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "witnessRules[].witnessRuleId",
        duplicates(
            policy
                .witness_rules
                .iter()
                .map(|rule| rule.witness_rule_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "moleculePatterns[].moleculePatternId",
        duplicates(
            policy
                .molecule_patterns
                .iter()
                .map(|pattern| pattern.molecule_pattern_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "obstructionCircuitDefinitions[].obstructionCircuitId",
        duplicates(
            policy
                .obstruction_circuit_definitions
                .iter()
                .map(|definition| definition.obstruction_circuit_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "signatureAxisDefinitions[].signatureAxisId",
        duplicates(
            policy
                .signature_axis_definitions
                .iter()
                .map(|definition| definition.signature_axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "coverageRequirements[].coverageRequirementId",
        duplicates(
            policy
                .coverage_requirements
                .iter()
                .map(|requirement| requirement.coverage_requirement_id.as_str()),
        ),
    ));
    check_from_examples(
        "law-policy-ids-unique",
        "law policy ids are unique within each definition family",
        examples,
        "fail",
    )
}

fn check_law_refs(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let law_ids = set(policy.selected_laws.iter().map(|law| law.law_id.as_str()));
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let mut examples = Vec::new();

    for law in &policy.selected_laws {
        if law.required_witness_refs.is_empty() {
            examples.push(generic_validation_example(
                &law.law_id,
                "requiredWitnessRefs",
                "selected law must declare witness rules",
            ));
        }
        if law.required_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &law.law_id,
                "requiredAxisRefs",
                "selected law must declare required signature axes",
            ));
        }
        for witness_ref in &law.required_witness_refs {
            if !witness_ids.contains(witness_ref.as_str()) {
                examples.push(generic_validation_example(
                    &law.law_id,
                    witness_ref,
                    "selected law references an unknown witness rule",
                ));
            }
        }
        for axis_ref in &law.required_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &law.law_id,
                    axis_ref,
                    "selected law references an unknown required or optional axis",
                ));
            }
        }
    }

    for rule in &policy.witness_rules {
        if !law_ids.contains(rule.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                &rule.law_ref,
                "witness rule references an unknown selected law",
            ));
        }
    }
    for definition in &policy.obstruction_circuit_definitions {
        if !law_ids.contains(definition.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                &definition.law_ref,
                "obstruction circuit definition references an unknown selected law",
            ));
        }
    }
    for axis in &policy.signature_axis_definitions {
        if !law_ids.contains(axis.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                &axis.law_ref,
                "signature axis definition references an unknown selected law",
            ));
        }
    }

    check_from_examples(
        "law-policy-law-refs-resolve",
        "selected laws, witness rules, obstruction definitions, and signature axes cross-reference each other",
        examples,
        "fail",
    )
}

fn check_axis_refs(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    for definition in &policy.signature_axis_definitions {
        if !axis_ids.contains(definition.axis_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.signature_axis_id,
                &definition.axis_ref,
                "signature axis definition references an unknown axis",
            ));
        }
    }
    for definition in &policy.obstruction_circuit_definitions {
        if definition.signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                "signatureAxisRefs",
                "obstruction circuit definition should declare affected signature axes",
            ));
        }
        for axis_ref in &definition.signature_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &definition.obstruction_circuit_id,
                    axis_ref,
                    "obstruction circuit definition references an unknown axis",
                ));
            }
        }
    }
    check_from_examples(
        "law-policy-axis-refs-resolve",
        "required and optional axes are referenced explicitly by signature and obstruction definitions",
        examples,
        "fail",
    )
}

fn check_witness_and_obstruction_boundaries(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let molecule_pattern_ids = set(policy
        .molecule_patterns
        .iter()
        .map(|pattern| pattern.molecule_pattern_id.as_str()));
    let mut examples = Vec::new();

    for rule in &policy.witness_rules {
        if rule.evidence_boundary.trim().is_empty() {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                "evidenceBoundary",
                "witness rule must declare evidence boundary",
            ));
        }
        if rule.required_atom_families.is_empty() && rule.molecule_pattern_refs.is_empty() {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                "requiredAtomFamilies",
                "witness rule must declare atom families or molecule pattern refs",
            ));
        }
        for pattern_ref in &rule.molecule_pattern_refs {
            if !molecule_pattern_ids.contains(pattern_ref.as_str()) {
                examples.push(generic_validation_example(
                    &rule.witness_rule_id,
                    pattern_ref,
                    "witness rule references an unknown molecule pattern",
                ));
            }
        }
    }

    for definition in &policy.obstruction_circuit_definitions {
        if !witness_ids.contains(definition.witness_rule_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                &definition.witness_rule_ref,
                "obstruction circuit definition references an unknown witness rule",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} minimalityReading", definition.obstruction_circuit_id),
            &definition.minimality_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", definition.obstruction_circuit_id),
            &definition.evidence_boundary,
        );
    }

    check_from_examples(
        "law-policy-witness-and-obstruction-boundaries",
        "witness and obstruction definitions declare evidence, minimality, and molecule boundaries",
        examples,
        "fail",
    )
}

fn check_coverage_and_exactness(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let law_ids = set(policy.selected_laws.iter().map(|law| law.law_id.as_str()));
    let mut examples = Vec::new();
    if policy.exactness_assumptions.is_empty() || has_blank(&policy.exactness_assumptions) {
        examples.push(generic_validation_example(
            &policy.law_policy_id,
            "exactnessAssumptions",
            "law policy must declare exactness assumptions",
        ));
    }
    if policy.coverage_requirements.is_empty() {
        examples.push(generic_validation_example(
            &policy.law_policy_id,
            "coverageRequirements",
            "law policy must declare coverage requirements",
        ));
    }
    for requirement in &policy.coverage_requirements {
        if requirement.applies_to_law_refs.is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "appliesToLawRefs",
                "coverage requirement must declare selected laws",
            ));
        }
        for law_ref in &requirement.applies_to_law_refs {
            if !law_ids.contains(law_ref.as_str()) {
                examples.push(generic_validation_example(
                    &requirement.coverage_requirement_id,
                    law_ref,
                    "coverage requirement references an unknown selected law",
                ));
            }
        }
        if requirement.required_atom_families.is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "requiredAtomFamilies",
                "coverage requirement must declare atom families",
            ));
        }
        if requirement.missing_coverage_behavior.trim().is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "missingCoverageBehavior",
                "coverage requirement must state missing coverage behavior",
            ));
        }
    }
    check_from_examples(
        "law-policy-coverage-and-exactness-declared",
        "coverage requirements and exactness assumptions are declared",
        examples,
        "fail",
    )
}

fn check_non_conclusions(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let present = policy
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let examples = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !present.contains(**required))
        .map(|required| {
            generic_validation_example(
                &policy.law_policy_id,
                required,
                "missing required law policy non-conclusion",
            )
        })
        .collect();
    check_from_examples(
        "law-policy-non-conclusion-boundary",
        "law policy keeps theory, lawfulness, atom truth, coverage, and signature-zero boundaries explicit",
        examples,
        "fail",
    )
}

fn validate_reading_boundary(
    examples: &mut Vec<ValidationExample>,
    subject: &str,
    field: &str,
    boundary: &LawPolicyReadingBoundaryV0,
    coverage_ids: &BTreeSet<&str>,
) {
    push_blank(
        examples,
        &format!("{field}.readingStrength"),
        &boundary.reading_strength,
    );
    if boundary.zero_reflection_assumptions.is_empty()
        || has_blank(&boundary.zero_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.zeroReflectionAssumptions"),
            "reading boundary must declare zero-reflection assumptions",
        ));
    }
    if boundary.obstruction_reflection_assumptions.is_empty()
        || has_blank(&boundary.obstruction_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.obstructionReflectionAssumptions"),
            "reading boundary must declare obstruction-reflection assumptions",
        ));
    }
    if boundary.coverage_requirement_refs.is_empty()
        || has_blank(&boundary.coverage_requirement_refs)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.coverageRequirementRefs"),
            "reading boundary must reference coverage requirements",
        ));
    }
    for coverage_ref in &boundary.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                subject,
                coverage_ref,
                "reading boundary coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    push_blank(
        examples,
        &format!("{field}.witnessCompletenessBoundary"),
        &boundary.witness_completeness_boundary,
    );
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

fn check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<ValidationExample>,
    failure_result: &str,
) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if examples.is_empty() {
            "pass"
        } else {
            failure_result
        },
    );
    check.count = Some(examples.len());
    check.examples = examples;
    check
}

fn duplicate_examples(field: &str, duplicates: Vec<String>) -> Vec<ValidationExample> {
    duplicates
        .into_iter()
        .map(|id| generic_validation_example(field, &id, "duplicate id"))
        .collect()
}

fn push_blank(examples: &mut Vec<ValidationExample>, field: &str, value: &str) {
    if value.trim().is_empty() {
        examples.push(generic_validation_example(
            field,
            value,
            "field must be non-empty",
        ));
    }
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn set<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_law_policy_validates() {
        let policy = static_law_policy();
        let report = validate_law_policy_report(&policy, "static-law-policy.json");
        assert_eq!(
            report.schema_version,
            LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.selected_law_count, 2);
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-non-conclusion-boundary" && check.result == "pass"
        }));
    }

    #[test]
    fn missing_law_policy_non_conclusion_fails() {
        let mut policy = static_law_policy();
        policy.non_conclusions.clear();
        let report = validate_law_policy_report(&policy, "bad-law-policy.json");
        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-non-conclusion-boundary" && check.result == "fail"
        }));
    }

    #[test]
    fn unknown_witness_ref_fails() {
        let mut policy = static_law_policy();
        policy.selected_laws[0]
            .required_witness_refs
            .push("witness:missing".to_string());
        let report = validate_law_policy_report(&policy, "bad-law-policy.json");
        assert_eq!(report.summary.result, "fail");
        assert!(
            report.checks.iter().any(|check| {
                check.id == "law-policy-law-refs-resolve" && check.result == "fail"
            })
        );
    }

    #[test]
    fn duplicate_law_policy_ids_fail() {
        let mut policy = static_law_policy();
        policy.selected_laws[1].law_id = policy.selected_laws[0].law_id.clone();
        policy.witness_rules[1].witness_rule_id = policy.witness_rules[0].witness_rule_id.clone();
        policy.coverage_requirements[1].coverage_requirement_id = policy.coverage_requirements[0]
            .coverage_requirement_id
            .clone();

        let report = validate_law_policy_report(&policy, "bad-law-policy.json");

        assert_eq!(report.summary.result, "fail");
        let id_check = report
            .checks
            .iter()
            .find(|check| check.id == "law-policy-ids-unique")
            .expect("ids uniqueness check is emitted");
        assert_eq!(id_check.result, "fail");
        assert!(
            id_check
                .examples
                .iter()
                .any(|example| example.source.as_deref() == Some("selectedLaws[].lawId"))
        );
        assert!(
            id_check
                .examples
                .iter()
                .any(|example| example.source.as_deref() == Some("witnessRules[].witnessRuleId"))
        );
        assert!(id_check.examples.iter().any(|example| {
            example.source.as_deref() == Some("coverageRequirements[].coverageRequirementId")
        }));
    }

    #[test]
    fn invalid_measurement_policy_fails() {
        let mut policy = static_law_policy();
        policy.measurement_policy.selected_axis_refs = vec!["axis:missing".to_string()];
        policy.measurement_policy.arch_map_store_ref_kinds = vec!["archmap-delta".to_string()];

        let report = validate_law_policy_report(&policy, "bad-law-policy.json");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-monodromy-measurement-policy" && check.result == "fail"
        }));
    }

    #[test]
    fn invalid_spectrum_measurement_profile_fails() {
        let mut policy = static_law_policy();
        let profile = policy
            .spectrum_measurement_profile
            .as_mut()
            .expect("fixture declares a spectrum profile");
        profile.selected_axis_refs = vec!["axis:missing".to_string()];
        profile.measured_witness_rule_refs = vec!["witness:missing".to_string()];
        profile.coverage_requirement_refs.clear();
        profile.non_conclusions.clear();

        let report = validate_law_policy_report(&policy, "bad-law-policy.json");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-spectrum-measurement-profile" && check.result == "fail"
        }));
    }

    #[test]
    fn absent_spectrum_measurement_profile_is_valid() {
        let mut policy = static_law_policy();
        policy.spectrum_measurement_profile = None;

        let report = validate_law_policy_report(&policy, "law-policy-without-spectrum.json");

        assert_eq!(report.summary.result, "pass");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-spectrum-measurement-profile" && check.result == "pass"
        }));
    }

    #[test]
    fn invalid_homotopy_measurement_profile_fails() {
        let mut policy = static_law_policy();
        let profile = policy
            .homotopy_measurement_profile
            .as_mut()
            .expect("fixture declares a homotopy profile");
        profile.selected_axis_refs = vec!["axis:missing".to_string()];
        profile.path_discovery_rules.clear();
        profile.filler_rules.clear();
        profile.coverage_requirement_refs = vec!["coverage:missing".to_string()];
        profile.non_conclusions.clear();

        let report = validate_law_policy_report(&policy, "bad-law-policy.json");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-homotopy-measurement-profile" && check.result == "fail"
        }));
    }

    #[test]
    fn absent_homotopy_measurement_profile_is_valid() {
        let mut policy = static_law_policy();
        policy.homotopy_measurement_profile = None;

        let report = validate_law_policy_report(&policy, "law-policy-without-homotopy.json");

        assert_eq!(report.summary.result, "pass");
        assert!(report.checks.iter().any(|check| {
            check.id == "law-policy-homotopy-measurement-profile" && check.result == "pass"
        }));
    }

    #[test]
    fn unknown_top_level_law_policy_field_is_rejected() {
        let mut value = serde_json::to_value(static_law_policy()).expect("policy serializes");
        value["unexpectedField"] = serde_json::json!("unknown");

        let error = serde_json::from_value::<LawPolicyDocumentV0>(value)
            .expect_err("unknown top-level fields must be rejected");

        assert!(error.to_string().contains("unknown field"));
    }

    #[test]
    fn canonical_fixture_matches_static_law_policy() {
        let fixture: LawPolicyDocumentV0 =
            serde_json::from_str(include_str!("../tests/fixtures/minimal/law_policy.json"))
                .expect("law policy fixture parses");
        assert_eq!(fixture, static_law_policy());
    }
}
