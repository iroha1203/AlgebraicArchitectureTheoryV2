use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION, ArchMapConcernHintV0,
    ArchMapDocumentV0, ArchMapMoleculeObservationV0, ArchMapSemanticObservationV0,
    ArchMapSourceRef, ArchSigAatConceptSurfaceV0, ArchSigAnalysisArtifactRefV0,
    ArchSigAnalysisPacketV0, ArchSigAnalysisPacketValidationInputV0,
    ArchSigAnalysisPacketValidationReportV0, ArchSigAnalysisPacketValidationSummaryV0,
    ArchSigAnalyticRepresentationV0, ArchSigArchitectureObjectProjectionV0,
    ArchSigArchitectureStateV0, ArchSigAtomCompatibilityConflictV0,
    ArchSigAtomCompatibilityReadingV0, ArchSigAtomConfigurationSummaryV0,
    ArchSigAtomSupportAxisReadingV0, ArchSigAxisExcursionV0, ArchSigAxisRestrictionCountV0,
    ArchSigBoundaryPreparationRankV0, ArchSigBoundedJudgementV0, ArchSigBridgeAtomFamilyReadingV0,
    ArchSigBridgeEdgeBreakdownV0, ArchSigChangeImpactReadingV0, ArchSigCouplingCohesionReadingV0,
    ArchSigCoverageStatusV0, ArchSigCurrentStateEvolutionBoundaryV0,
    ArchSigDesignPressureReadingV0, ArchSigDesignPrincipleReadingV0,
    ArchSigDiagramFillabilityReadingV0, ArchSigDominantAtomFamilyCompositionV0,
    ArchSigEvolutionRiskRankingV0, ArchSigFeatureExtensionAxisSummaryV0,
    ArchSigFeatureExtensionFormulaReadingV0, ArchSigFlatnessReadingV0,
    ArchSigHighOverlapMoleculePairV0, ArchSigHomotopyOrderSensitivityReadingV0,
    ArchSigInvariantFamilyReadingV0, ArchSigLawUniverseCoverageReadingV0,
    ArchSigLawUniverseReadingV0, ArchSigLayerSplitV0, ArchSigLlmInterpretationPacketV0,
    ArchSigLocalCurvatureDiagramReadingV0, ArchSigMoleculeReadingV0,
    ArchSigObservationProjectionReadingV0, ArchSigObstructionCircuitV0,
    ArchSigOperationCalculusLawReadingV0, ArchSigOperationDeltaReadingV0,
    ArchSigOperationInvariantGaloisReadingV0, ArchSigPathHomotopyDiagramReadingV0,
    ArchSigPathSignatureTrajectoryReadingV0, ArchSigRepairAxisDeltaReadingV0,
    ArchSigRepairOperationCandidateV0, ArchSigRepairTransferRiskRankV0,
    ArchSigRepresentationStrengthReadingV0, ArchSigSignatureAxisReadingV0,
    ArchSigSpectralAnalysisReadingV0, ArchSigSpectralDominantComponentV0,
    ArchSigSpectralDrilldownReadingV0, ArchSigSpectralMatrixShapeV0,
    ArchSigSpectralModeComponentV0, ArchSigSpectralModeReadingV0, ArchSigSpectralValueV0,
    ArchSigSplitReadinessReadingV0, ArchSigStateTransitionAlgebraReadingV0,
    ArchSigStructuralReadingReviewSurfaceV0, ArchSigSubjectFamilySpreadV0,
    ArchSigThreeLayerFlatnessReadingV0, ArchSigTransferBridgeReadingV0,
    ArchSigTransferMatrixEntryV0, ArchSigWorkflowAtomFamilyCountV0,
    ArchSigWorkflowRiskAxisReadingV0, ArchSigWorkflowRiskReadingV0, LAW_POLICY_SCHEMA_VERSION,
    LawPolicyDocumentV0, LawPolicyObstructionCircuitDefinitionV0,
    LawPolicySignatureAxisDefinitionV0, LawPolicyWitnessRuleV0, ValidationCheck, ValidationExample,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 7] = [
    "ArchSig analysis packet is not a Lean theorem proof",
    "ArchSig analysis packet is not global architecture truth",
    "ArchSig analysis packet does not prove source extraction completeness",
    "signature axes are law-policy-relative, not universal quality scores",
    "flatness reading is blocked by coverage gaps and exactness assumptions",
    "repair operation candidates are not automatic safe refactorings",
    "ArchSig reads current architecture state and does not replace FieldSig evolution analysis",
];

#[cfg(test)]
fn static_archsig_analysis_packet() -> ArchSigAnalysisPacketV0 {
    let archmap: ArchMapDocumentV0 =
        serde_json::from_str(include_str!("../tests/fixtures/minimal/archmap.json"))
            .expect("static ArchMap fixture parses");
    let law_policy: LawPolicyDocumentV0 =
        serde_json::from_str(include_str!("../tests/fixtures/minimal/law_policy.json"))
            .expect("static LawPolicy fixture parses");
    build_archsig_analysis_packet(
        &archmap,
        &law_policy,
        Some("tools/archsig/tests/fixtures/minimal/archmap.json"),
        Some("tools/archsig/tests/fixtures/minimal/law_policy.json"),
    )
}

pub fn build_archsig_analysis_packet(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    archmap_path: Option<&str>,
    law_policy_path: Option<&str>,
) -> ArchSigAnalysisPacketV0 {
    let interpretation_profile_ref = artifact_ref(
        &law_policy.law_policy_id,
        "interpretation-profile",
        &law_policy.schema_version,
        law_policy_path,
    );
    let molecule_readings = build_molecule_readings(archmap, law_policy);
    let obstruction_circuits = build_obstruction_circuits(archmap, law_policy, &molecule_readings);
    let signature_axes = build_signature_axes(archmap, law_policy, &obstruction_circuits);
    let flatness_reading = build_flatness_reading(archmap, law_policy, &signature_axes);
    let repair_operation_candidates =
        build_repair_candidates(archmap, &obstruction_circuits, &signature_axes);
    let architecture_object_projections = build_architecture_object_projections(archmap);
    let invariant_family_readings =
        build_invariant_family_readings(archmap, law_policy, &obstruction_circuits);
    let law_universe_reading = build_law_universe_reading(law_policy);
    let analytic_representations =
        build_analytic_representations(archmap, &signature_axes, &obstruction_circuits);
    let coupling_cohesion_readings = build_coupling_cohesion_readings(archmap);
    let workflow_risk_readings = build_workflow_risk_readings(archmap);
    let design_principle_readings = build_design_principle_readings(
        archmap,
        &invariant_family_readings,
        &obstruction_circuits,
        &repair_operation_candidates,
    );
    let operation_deltas =
        build_operation_deltas(archmap, &repair_operation_candidates, &signature_axes);
    let spectral_analysis_readings = build_spectral_analysis_readings(
        archmap,
        &workflow_risk_readings,
        &obstruction_circuits,
        &signature_axes,
        &operation_deltas,
    );
    let spectral_mode_readings = build_spectral_mode_readings(&spectral_analysis_readings);
    let spectral_drilldown_readings = build_spectral_drilldown_readings(
        archmap,
        &spectral_mode_readings,
        &workflow_risk_readings,
        &obstruction_circuits,
        &signature_axes,
        &operation_deltas,
    );
    let transfer_bridge_readings = build_transfer_bridge_readings(
        archmap,
        &spectral_mode_readings,
        &spectral_drilldown_readings,
        &workflow_risk_readings,
    );
    let atom_support_axis_readings = build_atom_support_axis_readings(archmap, &molecule_readings);
    let atom_compatibility_readings = build_atom_compatibility_readings(archmap);
    let law_universe_coverage_readings =
        build_law_universe_coverage_readings(archmap, law_policy, &signature_axes);
    let path_homotopy_diagram_readings =
        build_path_homotopy_diagram_readings(archmap, &molecule_readings, &obstruction_circuits);
    let layer_split = build_layer_split(archmap);
    let representation_strength_readings = build_representation_strength_readings(
        archmap,
        &analytic_representations,
        &spectral_analysis_readings,
        &flatness_reading,
    );
    let local_curvature_diagram_readings =
        build_local_curvature_diagram_readings(archmap, &obstruction_circuits);
    let three_layer_flatness_readings =
        build_three_layer_flatness_readings(archmap, &layer_split, &signature_axes);
    let observation_projection_readings = build_observation_projection_readings(archmap);
    let state_transition_algebra_readings =
        build_state_transition_algebra_readings(archmap, &obstruction_circuits);
    let operation_invariant_galois_readings = build_operation_invariant_galois_readings(
        &invariant_family_readings,
        &repair_operation_candidates,
    );
    let split_readiness_readings = build_split_readiness_readings(
        &molecule_readings,
        &obstruction_circuits,
        &transfer_bridge_readings,
    );
    let feature_extension_formula_readings = build_feature_extension_formula_readings(
        archmap,
        &obstruction_circuits,
        &repair_operation_candidates,
        &split_readiness_readings,
    );
    let operation_calculus_law_readings =
        build_operation_calculus_law_readings(&repair_operation_candidates, &operation_deltas);
    let path_signature_trajectory_readings =
        build_path_signature_trajectory_readings(&operation_deltas, &signature_axes);
    let homotopy_order_sensitivity_readings = build_homotopy_order_sensitivity_readings(
        &path_homotopy_diagram_readings,
        &operation_deltas,
        &repair_operation_candidates,
    );
    let diagram_fillability_readings = build_diagram_fillability_readings(
        &local_curvature_diagram_readings,
        &feature_extension_formula_readings,
    );
    let structural_reading_review_surface = build_structural_reading_review_surface(
        &representation_strength_readings,
        &local_curvature_diagram_readings,
        &three_layer_flatness_readings,
        &observation_projection_readings,
        &state_transition_algebra_readings,
        &operation_invariant_galois_readings,
        &split_readiness_readings,
        &atom_support_axis_readings,
        &atom_compatibility_readings,
        &law_universe_coverage_readings,
        &feature_extension_formula_readings,
        &operation_calculus_law_readings,
        &path_signature_trajectory_readings,
        &homotopy_order_sensitivity_readings,
        &diagram_fillability_readings,
    );
    let current_state_evolution_boundary =
        build_current_state_evolution_boundary(archmap, law_policy);
    let bounded_judgements = build_bounded_judgements(
        archmap,
        &obstruction_circuits,
        &signature_axes,
        &design_principle_readings,
    );
    let architecture_state =
        build_architecture_state(archmap, &signature_axes, &invariant_family_readings);
    let design_pressure = build_design_pressure(archmap, &obstruction_circuits, &signature_axes);
    let change_impact = build_change_impact(
        &repair_operation_candidates,
        &operation_deltas,
        &signature_axes,
    );
    let aat_concept_surfaces = build_aat_concept_surfaces(
        archmap,
        law_policy,
        &obstruction_circuits,
        &signature_axes,
        &repair_operation_candidates,
        &analytic_representations,
    );
    let llm_interpretation_packet = build_llm_interpretation_packet(
        archmap,
        &architecture_state,
        &design_pressure,
        &signature_axes,
        &analytic_representations,
        &workflow_risk_readings,
        &spectral_analysis_readings,
        &spectral_mode_readings,
        &spectral_drilldown_readings,
        &transfer_bridge_readings,
        &atom_support_axis_readings,
        &atom_compatibility_readings,
        &law_universe_coverage_readings,
        &feature_extension_formula_readings,
        &operation_calculus_law_readings,
        &path_signature_trajectory_readings,
        &homotopy_order_sensitivity_readings,
        &diagram_fillability_readings,
        &representation_strength_readings,
        &local_curvature_diagram_readings,
        &three_layer_flatness_readings,
        &observation_projection_readings,
        &state_transition_algebra_readings,
        &operation_invariant_galois_readings,
        &split_readiness_readings,
        &structural_reading_review_surface,
        &current_state_evolution_boundary,
        &repair_operation_candidates,
        &bounded_judgements,
    );

    ArchSigAnalysisPacketV0 {
        schema_version: ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION.to_string(),
        analysis_id: format!(
            "archsig-analysis:{}:{}",
            archmap.map_id, law_policy.law_policy_id
        ),
        generated_at: archmap.generated_at.clone(),
        arch_map_ref: artifact_ref(
            &archmap.map_id,
            "archmap",
            &archmap.schema_version,
            archmap_path,
        ),
        interpretation_profile_ref,
        selected_law_policy_ref: artifact_ref(
            &law_policy.law_policy_id,
            "law-policy",
            &law_policy.schema_version,
            law_policy_path,
        ),
        architecture_state,
        design_pressure,
        change_impact,
        aat_concept_surfaces,
        atom_configuration_summary: build_atom_configuration_summary(archmap),
        architecture_object_projections,
        invariant_family_readings,
        law_universe_reading,
        molecule_readings,
        obstruction_circuits,
        signature_axes,
        analytic_representations,
        coupling_cohesion_readings,
        workflow_risk_readings,
        spectral_analysis_readings,
        spectral_mode_readings,
        spectral_drilldown_readings,
        transfer_bridge_readings,
        atom_support_axis_readings,
        atom_compatibility_readings,
        law_universe_coverage_readings,
        feature_extension_formula_readings,
        operation_calculus_law_readings,
        path_signature_trajectory_readings,
        homotopy_order_sensitivity_readings,
        diagram_fillability_readings,
        representation_strength_readings,
        local_curvature_diagram_readings,
        three_layer_flatness_readings,
        observation_projection_readings,
        state_transition_algebra_readings,
        operation_invariant_galois_readings,
        split_readiness_readings,
        structural_reading_review_surface,
        current_state_evolution_boundary,
        design_principle_readings,
        flatness_reading,
        static_runtime_semantic_layer_split: layer_split,
        repair_operation_candidates,
        operation_deltas,
        path_homotopy_diagram_readings,
        bounded_judgements,
        llm_interpretation_packet,
        evidence_boundary: format!(
            "computed from ArchMap {} and selected interpretation profile {}; concernHints are auxiliary cues only",
            archmap.map_id, law_policy.law_policy_id
        ),
        interpretation_notes_for_llm: vec![
            "Lead with selected LawPolicy scope and evidence gaps.".to_string(),
            "Explain nonzero signature axes as law-relative ArchSig outputs.".to_string(),
            "Do not describe concernHints as obstruction circuits.".to_string(),
        ],
        excluded_readings: vec![
            "single architecture quality score".to_string(),
            "global architecture lawfulness".to_string(),
            "automatic repair safety".to_string(),
            "concern hint promoted without LawPolicy witness rule".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_atom_configuration_summary(
    archmap: &ArchMapDocumentV0,
) -> ArchSigAtomConfigurationSummaryV0 {
    let mut source_refs = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_observation_id.clone())
        .chain(
            archmap
                .observation_gaps
                .iter()
                .map(|gap| gap.gap_id.clone()),
        )
        .collect::<Vec<_>>();
    source_refs.sort();
    source_refs.dedup();

    ArchSigAtomConfigurationSummaryV0 {
        atom_observation_count: archmap.atom_observations.len(),
        molecule_observation_count: archmap.molecule_observations.len(),
        semantic_observation_count: archmap.semantic_observations.len(),
        observation_gap_count: archmap.observation_gaps.len(),
        concern_hint_count: archmap.concern_hints.len(),
        configuration_boundary:
            "counts are read from one bounded ArchMap, not complete architecture enumeration"
                .to_string(),
        coverage_summary: coverage_summary(archmap),
        source_refs,
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_molecule_readings(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
) -> Vec<ArchSigMoleculeReadingV0> {
    archmap
        .molecule_observations
        .iter()
        .map(|molecule| {
            let law_refs =
                selected_laws_for_atom_refs(law_policy, archmap, &molecule.atom_observation_refs);
            ArchSigMoleculeReadingV0 {
                molecule_reading_id: format!(
                    "molecule-reading:{}",
                    stable_id(&molecule.molecule_observation_id)
                ),
                molecule_observation_ref: molecule.molecule_observation_id.clone(),
                law_refs,
                atom_observation_refs: molecule.atom_observation_refs.clone(),
                reading: format!(
                    "{} is read as a {} molecule under selected LawPolicy",
                    molecule.molecule_observation_id, molecule.molecule_family
                ),
                evidence_summary: format!(
                    "molecule uses {} atom observation refs and {} source refs",
                    molecule.atom_observation_refs.len(),
                    molecule.source_refs.len()
                ),
                evidence_boundary:
                    "law-relative molecule reading over ArchMap observations; not a primitive atom"
                        .to_string(),
                source_refs: molecule.source_refs.iter().map(source_ref_label).collect(),
                interpretation_notes_for_llm: vec![
                    "Explain molecule readings as grouped observed atoms before discussing laws."
                        .to_string(),
                ],
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_obstruction_circuits(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    molecule_readings: &[ArchSigMoleculeReadingV0],
) -> Vec<ArchSigObstructionCircuitV0> {
    law_policy
        .obstruction_circuit_definitions
        .iter()
        .filter_map(|definition| {
            let witness_rule = law_policy
                .witness_rules
                .iter()
                .find(|rule| rule.witness_rule_id == definition.witness_rule_ref)?;
            let atom_refs = matching_atom_refs_for_witness(archmap, witness_rule);
            let molecule_refs = molecule_readings
                .iter()
                .filter(|reading| reading.law_refs.contains(&definition.law_ref))
                .map(|reading| reading.molecule_reading_id.clone())
                .collect::<Vec<_>>();
            let concern_refs = archmap
                .concern_hints
                .iter()
                .filter(|hint| concern_supports_witness(hint.concern_family.as_str(), witness_rule))
                .map(|hint| hint.concern_hint_id.clone())
                .collect::<Vec<_>>();

            if !witness_constructible(witness_rule, &atom_refs, &molecule_refs, &concern_refs) {
                return None;
            }

            Some(obstruction_circuit(
                definition,
                witness_rule,
                atom_refs,
                molecule_refs,
                concern_refs,
                archmap,
                law_policy,
            ))
        })
        .collect()
}

fn build_signature_axes(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigSignatureAxisReadingV0> {
    law_policy
        .signature_axis_definitions
        .iter()
        .map(|definition| {
            let value = obstruction_circuits
                .iter()
                .filter(|circuit| {
                    circuit
                        .signature_axis_refs
                        .contains(&definition.signature_axis_id)
                })
                .count() as i64;
            let coverage_status = if archmap.observation_gaps.is_empty() {
                "covered-for-selected-atoms"
            } else {
                "coverage-gap-preserved"
            };
            let mut source_refs = obstruction_circuits
                .iter()
                .filter(|circuit| {
                    circuit
                        .signature_axis_refs
                        .contains(&definition.signature_axis_id)
                })
                .flat_map(|circuit| circuit.atom_observation_refs.clone())
                .collect::<Vec<_>>();
            if source_refs.is_empty() {
                source_refs = archmap
                    .atom_observations
                    .iter()
                    .filter(|atom| {
                        law_policy
                            .selected_laws
                            .iter()
                            .filter(|law| law.law_id == definition.law_ref)
                            .any(|law| {
                                law.applies_to_atom_families
                                    .iter()
                                    .any(|family| family_matches(&atom.atom_family, family))
                            })
                    })
                    .map(|atom| atom.atom_observation_id.clone())
                    .collect();
            }
            if source_refs.is_empty() {
                source_refs.push(format!(
                    "{}: no direct source refs under selected coverage",
                    definition.signature_axis_id
                ));
            }
            ArchSigSignatureAxisReadingV0 {
                signature_axis_id: definition.signature_axis_id.clone(),
                law_ref: definition.law_ref.clone(),
                axis_ref: definition.axis_ref.clone(),
                value_type: definition.value_type.clone(),
                value,
                zero_reading: if value == 0 {
                    format!(
                        "zero means no {} witness was constructed under declared coverage",
                        definition.axis_ref
                    )
                } else {
                    format!(
                        "nonzero means {} witness count is present under selected LawPolicy",
                        definition.axis_ref
                    )
                },
                coverage_status: coverage_status.to_string(),
                exactness_assumptions: law_policy.exactness_assumptions.clone(),
                evidence_summary: format!(
                    "{} obstruction circuit(s) contribute to {}",
                    value, definition.signature_axis_id
                ),
                source_refs,
                missing_evidence: signature_axis_missing_evidence(archmap, law_policy, definition),
                excluded_readings: signature_axis_excluded_readings(law_policy, definition),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_flatness_reading(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> ArchSigFlatnessReadingV0 {
    let zero_signature_axis_refs = signature_axes
        .iter()
        .filter(|axis| axis.value == 0)
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<Vec<_>>();
    let nonzero_signature_axis_refs = signature_axes
        .iter()
        .filter(|axis| axis.value != 0)
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<Vec<_>>();
    let blocked_by_coverage_gaps = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let status = if !nonzero_signature_axis_refs.is_empty() {
        "nonflatUnderSelectedPolicy"
    } else if !blocked_by_coverage_gaps.is_empty() {
        "flatForConstructedWitnessesButCoverageGapBlocked"
    } else {
        "flatUnderSelectedPolicy"
    };
    ArchSigFlatnessReadingV0 {
        reading_id: format!("flatness:{}", law_policy.law_policy_id),
        selected_law_policy_ref: law_policy.law_policy_id.clone(),
        status: status.to_string(),
        zero_signature_axis_refs,
        nonzero_signature_axis_refs,
        blocked_by_coverage_gaps,
        evidence_boundary:
            "flatness is relative to selected signature axes, coverage gaps, and exactness assumptions"
                .to_string(),
        interpretation_notes_for_llm: vec![
            "Do not turn zero signature axes into global lawfulness claims.".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_layer_split(archmap: &ArchMapDocumentV0) -> ArchSigLayerSplitV0 {
    ArchSigLayerSplitV0 {
        static_observation_refs: archmap
            .atom_observations
            .iter()
            .filter(|atom| matches!(atom.atom_family.as_str(), "existence" | "relation"))
            .map(|atom| atom.atom_observation_id.clone())
            .collect(),
        runtime_observation_refs: archmap
            .observation_gaps
            .iter()
            .filter(|gap| gap.gap_kind.to_ascii_lowercase().contains("runtime"))
            .map(|gap| gap.gap_id.clone())
            .collect(),
        semantic_observation_refs: archmap
            .atom_observations
            .iter()
            .filter(|atom| atom.atom_family.to_ascii_lowercase().contains("contract"))
            .map(|atom| atom.atom_observation_id.clone())
            .chain(
                archmap
                    .semantic_observations
                    .iter()
                    .map(|semantic| semantic.semantic_observation_id.clone()),
            )
            .collect(),
        split_boundary:
            "runtime gaps are preserved separately and are not interpreted as measured zero"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_architecture_state(
    archmap: &ArchMapDocumentV0,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    invariant_readings: &[ArchSigInvariantFamilyReadingV0],
) -> ArchSigArchitectureStateV0 {
    ArchSigArchitectureStateV0 {
        state_id: format!("architecture-state:{}", stable_id(&archmap.architecture_id)),
        reading: format!(
            "{} is represented as {} atom observations, {} molecules, {} semantic observations, and {} preserved observation gaps",
            archmap.architecture_id,
            archmap.atom_observations.len(),
            archmap.molecule_observations.len(),
            archmap.semantic_observations.len(),
            archmap.observation_gaps.len()
        ),
        atom_family_refs: unique_strings(
            archmap
                .atom_observations
                .iter()
                .map(|atom| atom.atom_family.clone()),
        ),
        molecule_refs: archmap
            .molecule_observations
            .iter()
            .map(|molecule| molecule.molecule_observation_id.clone())
            .collect(),
        workflow_refs: archmap
            .semantic_observations
            .iter()
            .map(|semantic| semantic.semantic_observation_id.clone())
            .collect(),
        boundary_refs: archmap
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.clone())
            .collect(),
        invariant_refs: invariant_readings
            .iter()
            .map(|reading| reading.invariant_id.clone())
            .collect(),
        signature_axis_refs: signature_axes
            .iter()
            .map(|axis| axis.signature_axis_id.clone())
            .collect(),
        coverage_boundary:
            "state is an ArchMap-relative architecture state, not a complete source reconstruction"
                .to_string(),
        recommended_next_action:
            "review nonzero axes, stressed principles, and preserved observation gaps before planning repair"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_design_pressure(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigDesignPressureReadingV0> {
    let obstruction_refs = obstruction_circuits
        .iter()
        .map(|circuit| circuit.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let signature_axis_refs = signature_axes
        .iter()
        .filter(|axis| axis.value != 0)
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<Vec<_>>();
    vec![ArchSigDesignPressureReadingV0 {
        pressure_id: "design-pressure:selected-atom-configuration".to_string(),
        status: if obstruction_refs.is_empty() {
            "needsReview"
        } else {
            "actionable"
        }
        .to_string(),
        reading: format!(
            "{} selected obstruction circuit(s) and {} coverage gap(s) define the current pressure surface",
            obstruction_refs.len(),
            archmap.observation_gaps.len()
        ),
        atom_configuration_refs: archmap
            .atom_observations
            .iter()
            .map(|atom| atom.atom_observation_id.clone())
            .collect(),
        obstruction_refs,
        signature_axis_refs,
        coverage_boundary:
            "pressure is relative to the observed finite Atom configuration and selected profile"
                .to_string(),
        recommended_next_action:
            "use bounded judgements to decide whether to inspect source refs, add evidence, or plan repair"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_change_impact(
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> ArchSigChangeImpactReadingV0 {
    ArchSigChangeImpactReadingV0 {
        impact_id: "change-impact:selected-repair-operations".to_string(),
        operation_scope: "repair, extension, migration, and refactor operations over observed ArchMap atoms".to_string(),
        signature_delta_summary: operation_deltas
            .iter()
            .flat_map(|delta| delta.signature_delta.clone())
            .collect(),
        affected_boundaries: signature_axes
            .iter()
            .map(|axis| format!("{}: {}", axis.signature_axis_id, axis.coverage_status))
            .collect(),
        complexity_transfer_notes: repair_candidates
            .iter()
            .flat_map(|candidate| candidate.transfer_risks.clone())
            .collect(),
        coverage_boundary:
            "impact is a pre-change operation reading; it is not evidence that a future patch is safe"
                .to_string(),
        recommended_next_action:
            "compare operation deltas before and after the patch and keep transferred obstruction notes"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_aat_concept_surfaces(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    analytic_representations: &[ArchSigAnalyticRepresentationV0],
) -> Vec<ArchSigAatConceptSurfaceV0> {
    let concept_specs = [
        (
            "Atom",
            archmap.atom_observations.len(),
            all_atom_refs(archmap),
        ),
        (
            "Configuration",
            archmap.atom_observations.len() + archmap.molecule_observations.len(),
            all_atom_refs(archmap),
        ),
        (
            "ArchitectureObject",
            archmap.projection_info.len().max(1),
            archmap
                .projection_info
                .iter()
                .map(|projection| projection.projection_id.clone())
                .collect(),
        ),
        (
            "Invariant",
            law_policy.selected_laws.len(),
            law_policy
                .selected_laws
                .iter()
                .map(|law| law.law_id.clone())
                .collect(),
        ),
        (
            "LawUniverse",
            law_policy.selected_laws.len(),
            law_policy
                .selected_laws
                .iter()
                .map(|law| law.law_id.clone())
                .collect(),
        ),
        (
            "ObstructionCircuit",
            obstruction_circuits.len(),
            obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect(),
        ),
        (
            "ArchitectureSignature",
            signature_axes.len(),
            signature_axes
                .iter()
                .map(|axis| axis.signature_axis_id.clone())
                .collect(),
        ),
        (
            "Operation",
            repair_candidates.len(),
            repair_candidates
                .iter()
                .map(|candidate| candidate.repair_operation_candidate_id.clone())
                .collect(),
        ),
        (
            "Path",
            archmap.molecule_observations.len().max(1),
            archmap
                .molecule_observations
                .iter()
                .map(|molecule| molecule.molecule_observation_id.clone())
                .collect(),
        ),
        (
            "Homotopy",
            archmap.semantic_observations.len().max(1),
            archmap
                .semantic_observations
                .iter()
                .map(|semantic| semantic.semantic_observation_id.clone())
                .collect(),
        ),
        (
            "Diagram",
            obstruction_circuits.len().max(1),
            obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect(),
        ),
        (
            "AnalyticRepresentation",
            analytic_representations.len(),
            analytic_representations
                .iter()
                .map(|representation| representation.representation_id.clone())
                .collect(),
        ),
    ];

    concept_specs
        .into_iter()
        .map(|(concept, count, evidence_refs)| ArchSigAatConceptSurfaceV0 {
            concept: concept.to_string(),
            status: if count == 0 {
                "unmeasured"
            } else {
                "observedOrRepresented"
            }
            .to_string(),
            reading: format!("{concept} is represented with {count} bounded packet record(s)"),
            evidence_refs,
            coverage_boundary:
                "concept surface records packet expressiveness, not theorem proof or extraction completeness"
                    .to_string(),
            exactness_boundary:
                "exactness is relative to ArchMap coverage and selected interpretation profile"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        })
        .collect()
}

fn build_architecture_object_projections(
    archmap: &ArchMapDocumentV0,
) -> Vec<ArchSigArchitectureObjectProjectionV0> {
    if archmap.projection_info.is_empty() {
        return vec![ArchSigArchitectureObjectProjectionV0 {
            projection_id: "architecture-object:default-observed-configuration".to_string(),
            projection_family: "observedAtomConfiguration".to_string(),
            atom_refs: all_atom_refs(archmap),
            molecule_refs: archmap
                .molecule_observations
                .iter()
                .map(|molecule| molecule.molecule_observation_id.clone())
                .collect(),
            semantic_refs: archmap
                .semantic_observations
                .iter()
                .map(|semantic| semantic.semantic_observation_id.clone())
                .collect(),
            reading:
                "default architecture object projection formed from observed atoms, molecules, and semantic records"
                    .to_string(),
            projection_boundary: "synthetic projection used because ArchMap provided no explicit projectionInfo".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }];
    }

    archmap
        .projection_info
        .iter()
        .map(|projection| ArchSigArchitectureObjectProjectionV0 {
            projection_id: projection.projection_id.clone(),
            projection_family: projection.projection_family.clone(),
            atom_refs: archmap
                .atom_observations
                .iter()
                .filter(|atom| atom.projection_refs.contains(&projection.projection_id))
                .map(|atom| atom.atom_observation_id.clone())
                .collect(),
            molecule_refs: vec![],
            semantic_refs: vec![projection.source_observation_ref.clone()],
            reading: projection.reading.clone(),
            projection_boundary: projection.projection_boundary.clone(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        })
        .collect()
}

fn build_invariant_family_readings(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigInvariantFamilyReadingV0> {
    law_policy
        .selected_laws
        .iter()
        .map(|law| {
            let obstruction_refs = obstruction_circuits
                .iter()
                .filter(|circuit| circuit.law_ref == law.law_id)
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect::<Vec<_>>();
            ArchSigInvariantFamilyReadingV0 {
                invariant_id: format!("invariant:{}", stable_id(&law.law_id)),
                invariant_family: law.law_family.clone(),
                status: if obstruction_refs.is_empty() {
                    "preservedForConstructedWitnesses"
                } else {
                    "stressed"
                }
                .to_string(),
                law_refs: vec![law.law_id.clone()],
                atom_refs: archmap
                    .atom_observations
                    .iter()
                    .filter(|atom| {
                        law.applies_to_atom_families
                            .iter()
                            .any(|family| family_matches(&atom.atom_family, family))
                    })
                    .map(|atom| atom.atom_observation_id.clone())
                    .collect(),
                obstruction_refs,
                reading: format!(
                    "{} is read as an invariant family selected by the interpretation profile",
                    law.description
                ),
                evidence_boundary: law.enforcement_boundary.clone(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_law_universe_reading(law_policy: &LawPolicyDocumentV0) -> ArchSigLawUniverseReadingV0 {
    ArchSigLawUniverseReadingV0 {
        law_universe_id: format!("law-universe:{}", stable_id(&law_policy.law_policy_id)),
        profile_ref: law_policy.law_policy_id.clone(),
        selected_law_refs: law_policy
            .selected_laws
            .iter()
            .map(|law| law.law_id.clone())
            .collect(),
        witness_rule_refs: law_policy
            .witness_rules
            .iter()
            .map(|rule| rule.witness_rule_id.clone())
            .collect(),
        signature_axis_refs: law_policy
            .signature_axis_definitions
            .iter()
            .map(|axis| axis.signature_axis_id.clone())
            .collect(),
        exactness_assumptions: law_policy.exactness_assumptions.clone(),
        coverage_requirements: law_policy
            .coverage_requirements
            .iter()
            .map(|requirement| requirement.coverage_requirement_id.clone())
            .collect(),
        reading:
            "LawPolicy is interpreted as an analysis profile selecting a bounded LawUniverse, witnesses, axes, coverage, and exactness assumptions"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_analytic_representations(
    archmap: &ArchMapDocumentV0,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigAnalyticRepresentationV0> {
    let relation_count = archmap
        .atom_observations
        .iter()
        .filter(|atom| atom.atom_family.to_ascii_lowercase().contains("relation"))
        .count();
    let node_count = unique_strings(
        archmap
            .atom_observations
            .iter()
            .flat_map(|atom| atom.object_refs.clone()),
    )
    .len()
    .max(archmap.atom_observations.len());
    let reachable_cone_size = node_count + relation_count;
    let walk_count = relation_count + archmap.molecule_observations.len();
    let propagation_depth = if relation_count == 0 { 0 } else { 1 };
    let nilpotence_boundary = if archmap.observation_gaps.is_empty() {
        "candidateNilpotentForSelectedStaticGraph"
    } else {
        "blockedByCoverageGap"
    };
    let spectral_proxy = if node_count == 0 {
        "unavailable".to_string()
    } else {
        format!("{:.3}", relation_count as f64 / node_count as f64)
    };
    vec![
        analytic_representation(
            "analytic:weighted-adjacency",
            "weightedAdjacencyMatrix",
            "measured",
            "matrixShape",
            &format!("{node_count}x{node_count}; edgeCount={relation_count}"),
            all_atom_refs(archmap),
            signature_axes,
            "selected relation atoms induce a bounded weighted adjacency representation",
        ),
        analytic_representation(
            "analytic:reachable-cone-size",
            "reachableConeSize",
            "measured",
            "nat",
            &reachable_cone_size.to_string(),
            all_atom_refs(archmap),
            signature_axes,
            "reachable cone is a bounded graph proxy over observed object refs and relation atoms",
        ),
        analytic_representation(
            "analytic:walk-count",
            "walkCount",
            "measured",
            "nat",
            &walk_count.to_string(),
            all_atom_refs(archmap),
            signature_axes,
            "walk count is a bounded proxy from observed relation atoms and molecule paths",
        ),
        analytic_representation(
            "analytic:nilpotence-boundary",
            "nilpotenceBoundary",
            "needsReview",
            "boundaryStatus",
            nilpotence_boundary,
            all_atom_refs(archmap),
            signature_axes,
            "nilpotence is represented as a boundary condition, not folded into Decomposable or global acyclicity",
        ),
        analytic_representation(
            "analytic:selected-subgraph-spectrum",
            "selectedSubgraphSpectrum",
            "measured",
            "vector",
            &format!("[{spectral_proxy}]"),
            all_atom_refs(archmap),
            signature_axes,
            "selected subgraph spectrum records the bounded spectrum vector for the observed relation subgraph",
        ),
        analytic_representation(
            "analytic:propagation-depth",
            "propagationDepth",
            "measured",
            "nat",
            &propagation_depth.to_string(),
            all_atom_refs(archmap),
            signature_axes,
            "propagation depth is computed over observed relation atoms only",
        ),
        analytic_representation(
            "analytic:spectral-radius-proxy",
            "spectralRadius",
            if spectral_proxy == "unavailable" {
                "unavailable"
            } else {
                "measured"
            },
            "float",
            &spectral_proxy,
            all_atom_refs(archmap),
            signature_axes,
            "spectral radius is represented as a bounded proxy until full matrix extraction is supplied",
        ),
        analytic_representation(
            "analytic:curvature-valuation",
            "curvatureValuation",
            "measured",
            "nat",
            &obstruction_circuits.len().to_string(),
            obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect(),
            signature_axes,
            "curvature valuation counts constructed obstruction circuits under the selected profile",
        ),
        analytic_representation(
            "analytic:state-algebra-boundary",
            "stateAlgebra",
            if archmap
                .observation_gaps
                .iter()
                .any(|gap| gap.gap_kind.to_ascii_lowercase().contains("runtime"))
            {
                "unmeasured"
            } else {
                "needsReview"
            },
            "boundaryStatus",
            "state/effect algebra requires explicit state transition and runtime/effect atoms",
            all_atom_refs(archmap),
            signature_axes,
            "state algebra is preserved as a first-class analytic boundary even when state evidence is unavailable",
        ),
        analytic_representation(
            "analytic:zero-reflecting-aggregate-boundary",
            "zeroReflectingAggregateBoundary",
            "needsReview",
            "boundaryStatus",
            if archmap.observation_gaps.is_empty() {
                "candidateForSelectedCoverage"
            } else {
                "blockedByObservationGaps"
            },
            archmap
                .observation_gaps
                .iter()
                .map(|gap| gap.gap_id.clone())
                .collect(),
            signature_axes,
            "zero-reflecting aggregate boundary says when zero axes may and may not be read as absence",
        ),
    ]
}

fn analytic_representation(
    representation_id: &str,
    representation_family: &str,
    status: &str,
    value_type: &str,
    value: &str,
    graph_scope_refs: Vec<String>,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    reading: &str,
) -> ArchSigAnalyticRepresentationV0 {
    ArchSigAnalyticRepresentationV0 {
        representation_id: representation_id.to_string(),
        representation_family: representation_family.to_string(),
        status: status.to_string(),
        value_type: value_type.to_string(),
        value: value.to_string(),
        graph_scope_refs,
        axis_refs: signature_axes
            .iter()
            .map(|axis| axis.signature_axis_id.clone())
            .collect(),
        reading: reading.to_string(),
        coverage_boundary:
            "analytic value is relative to selected graph / matrix representation and is not a quality score"
                .to_string(),
        zero_reflecting_boundary:
            "zero reflects only the selected representation when coverage and exactness assumptions hold"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_coupling_cohesion_readings(
    archmap: &ArchMapDocumentV0,
) -> Vec<ArchSigCouplingCohesionReadingV0> {
    let relation_refs = archmap
        .atom_observations
        .iter()
        .filter(|atom| atom.atom_family.to_ascii_lowercase().contains("relation"))
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    let contract_refs = archmap
        .atom_observations
        .iter()
        .filter(|atom| atom.atom_family.to_ascii_lowercase().contains("contract"))
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    let semantic_refs = archmap
        .semantic_observations
        .iter()
        .map(|semantic| semantic.semantic_observation_id.clone())
        .collect::<Vec<_>>();
    let gap_refs = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();

    vec![
        coupling_reading(
            "coupling:static-dependency",
            "staticDependencyCoupling",
            relation_refs.len(),
            relation_refs,
            vec![],
            "static relation atoms show direct source-level coupling",
        ),
        coupling_reading(
            "cohesion:semantic-contract",
            "contractCohesion",
            contract_refs.len() + semantic_refs.len(),
            contract_refs.into_iter().chain(semantic_refs).collect(),
            vec![],
            "contract and semantic observations give a semantic cohesion reading",
        ),
        coupling_reading(
            "coupling:state-effect",
            "stateEffectCoupling",
            gap_refs.len(),
            gap_refs.clone(),
            gap_refs,
            "state/effect coupling remains stressed when runtime or effect evidence is unavailable",
        ),
        coupling_reading(
            "coupling:authority-trust",
            "authorityTrustCoupling",
            archmap
                .atom_observations
                .iter()
                .filter(|atom| {
                    let family = atom.atom_family.to_ascii_lowercase();
                    family.contains("authority") || family.contains("trust")
                })
                .count(),
            all_atom_refs(archmap),
            archmap
                .observation_gaps
                .iter()
                .map(|gap| gap.gap_id.clone())
                .collect(),
            "authority and trust coupling are unmeasured unless ArchMap records explicit authority/trust atoms",
        ),
    ]
}

fn coupling_reading(
    reading_id: &str,
    axis: &str,
    value: usize,
    supporting_refs: Vec<String>,
    stressed_refs: Vec<String>,
    reading: &str,
) -> ArchSigCouplingCohesionReadingV0 {
    ArchSigCouplingCohesionReadingV0 {
        reading_id: reading_id.to_string(),
        axis: axis.to_string(),
        status: if value == 0 {
            "unmeasured"
        } else if stressed_refs.is_empty() {
            "actionable"
        } else {
            "needsReview"
        }
        .to_string(),
        value_type: "boundedCount".to_string(),
        value: value.to_string(),
        supporting_refs,
        stressed_refs,
        reading: reading.to_string(),
        coverage_boundary:
            "coupling/cohesion is semantic ArchMap-relative evidence, not import-count truth"
                .to_string(),
        recommended_next_action:
            "inspect supporting refs and add missing state/effect/authority evidence before treating zero as absence"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_workflow_risk_readings(archmap: &ArchMapDocumentV0) -> Vec<ArchSigWorkflowRiskReadingV0> {
    let atom_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let mut readings = archmap
        .molecule_observations
        .iter()
        .map(|molecule| {
            let molecule_atoms = molecule
                .atom_observation_refs
                .iter()
                .filter_map(|atom_ref| atom_by_id.get(atom_ref.as_str()).copied())
                .collect::<Vec<_>>();
            let semantic_refs = archmap
                .semantic_observations
                .iter()
                .filter(|semantic| {
                    semantic
                        .molecule_observation_refs
                        .contains(&molecule.molecule_observation_id)
                })
                .map(|semantic| semantic.semantic_observation_id.clone())
                .collect::<Vec<_>>();
            let concerns = archmap
                .concern_hints
                .iter()
                .filter(|concern| {
                    concern
                        .molecule_observation_refs
                        .contains(&molecule.molecule_observation_id)
                })
                .collect::<Vec<_>>();
            let concern_refs = concerns
                .iter()
                .map(|concern| concern.concern_hint_id.clone())
                .collect::<Vec<_>>();
            let family_counts = workflow_atom_family_counts(&molecule_atoms);
            let workflow_blob = workflow_text_blob(molecule, &molecule_atoms, archmap, &concerns);
            let mut top_axes = workflow_risk_axis_readings(
                &family_counts,
                &workflow_blob,
                archmap,
                &concerns,
            );
            top_axes.sort_by(|left, right| right.score.cmp(&left.score).then(left.axis.cmp(&right.axis)));
            let risk_score = top_axes.iter().map(|axis| axis.score).sum::<i64>();
            let coverage_gap_refs = top_axes
                .iter()
                .flat_map(|axis| axis.coverage_gap_refs.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let review_focus = top_axes
                .iter()
                .take(3)
                .map(|axis| workflow_review_focus(axis.axis.as_str()))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            ArchSigWorkflowRiskReadingV0 {
                workflow_risk_id: format!(
                    "workflow-risk:{}",
                    stable_id(&molecule.molecule_observation_id)
                ),
                molecule_observation_ref: molecule.molecule_observation_id.clone(),
                molecule_family: molecule.molecule_family.clone(),
                role_name: molecule.role_name.clone(),
                status: workflow_risk_status(risk_score, &coverage_gap_refs).to_string(),
                risk_score,
                risk_tier: workflow_risk_tier(risk_score).to_string(),
                atom_count: molecule_atoms.len(),
                atom_family_counts: family_counts
                    .iter()
                    .map(|(atom_family, count)| ArchSigWorkflowAtomFamilyCountV0 {
                        atom_family: atom_family.clone(),
                        count: *count,
                    })
                    .collect(),
                semantic_refs,
                concern_refs,
                top_axes,
                review_focus,
                coverage_gap_refs,
                evidence_boundary:
                    "workflow risk is a molecule-local ArchMap reading for review prioritization, not a quality score or proof"
                        .to_string(),
                recommended_next_action:
                    "review the top axes, source refs, concern hints, and coverage gaps before planning repair"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect::<Vec<_>>();
    readings.sort_by(|left, right| {
        right
            .risk_score
            .cmp(&left.risk_score)
            .then(left.workflow_risk_id.cmp(&right.workflow_risk_id))
    });
    readings
}

fn workflow_atom_family_counts(
    atoms: &[&crate::ArchMapAtomObservationV0],
) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for atom in atoms {
        *counts.entry(atom.atom_family.clone()).or_insert(0) += 1;
    }
    counts
}

fn workflow_text_blob(
    molecule: &ArchMapMoleculeObservationV0,
    atoms: &[&crate::ArchMapAtomObservationV0],
    archmap: &ArchMapDocumentV0,
    concerns: &[&ArchMapConcernHintV0],
) -> String {
    let mut parts = vec![
        molecule.molecule_observation_id.clone(),
        molecule.molecule_family.clone(),
        molecule.role_name.clone(),
        molecule.evidence_boundary.clone(),
    ];
    parts.extend(atoms.iter().map(|atom| atom.predicate.clone()));
    parts.extend(atoms.iter().map(|atom| atom.subject_ref.clone()));
    parts.extend(
        archmap
            .semantic_observations
            .iter()
            .filter(|semantic| {
                semantic
                    .molecule_observation_refs
                    .contains(&molecule.molecule_observation_id)
            })
            .map(workflow_semantic_text),
    );
    parts.extend(concerns.iter().map(|concern| {
        format!(
            "{} {} {}",
            concern.concern_hint_id, concern.concern_family, concern.subject_ref
        )
    }));
    parts.join(" ").to_ascii_lowercase()
}

fn workflow_semantic_text(semantic: &ArchMapSemanticObservationV0) -> String {
    format!(
        "{} {} {} {}",
        semantic.semantic_observation_id,
        semantic.semantic_family,
        semantic.subject_ref,
        semantic.predicate
    )
}

fn workflow_risk_axis_readings(
    family_counts: &BTreeMap<String, usize>,
    workflow_blob: &str,
    archmap: &ArchMapDocumentV0,
    concerns: &[&ArchMapConcernHintV0],
) -> Vec<ArchSigWorkflowRiskAxisReadingV0> {
    workflow_axis_specs()
        .into_iter()
        .filter_map(|spec| {
            let family_score = spec
                .family_weights
                .iter()
                .map(|(family, weight)| {
                    family_counts.get(*family).copied().unwrap_or_default() as i64 * *weight
                })
                .sum::<i64>();
            let keyword_hits = matching_keywords(workflow_blob, spec.keywords);
            let concern_refs = concerns
                .iter()
                .filter(|concern| {
                    let text = format!(
                        "{} {} {}",
                        concern.concern_hint_id, concern.concern_family, concern.subject_ref
                    )
                    .to_ascii_lowercase();
                    !matching_keywords(&text, spec.concern_keywords).is_empty()
                })
                .map(|concern| concern.concern_hint_id.clone())
                .collect::<Vec<_>>();
            let coverage_gap_refs = workflow_axis_gap_refs(archmap, spec.gap_keywords);
            let score = family_score
                + keyword_hits.len() as i64 * 2
                + concern_refs.len() as i64 * 3
                + coverage_gap_refs.len().min(3) as i64;
            if score == 0 {
                return None;
            }
            Some(ArchSigWorkflowRiskAxisReadingV0 {
                axis: spec.axis.to_string(),
                status: if coverage_gap_refs.is_empty() {
                    "actionable"
                } else {
                    "needsReview"
                }
                .to_string(),
                score,
                family_score,
                keyword_hits,
                concern_refs,
                coverage_gap_refs,
                reading: spec.reading.to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            })
        })
        .collect()
}

struct WorkflowAxisSpec {
    axis: &'static str,
    family_weights: &'static [(&'static str, i64)],
    keywords: &'static [&'static str],
    concern_keywords: &'static [&'static str],
    gap_keywords: &'static [&'static str],
    reading: &'static str,
}

fn workflow_axis_specs() -> Vec<WorkflowAxisSpec> {
    vec![
        WorkflowAxisSpec {
            axis: "authorityTrustBoundary",
            family_weights: &[
                ("authority", 3),
                ("trust", 3),
                ("contractSpecification", 1),
                ("effect", 1),
            ],
            keywords: &[
                "admin",
                "auth",
                "jwt",
                "token",
                "session",
                "permission",
                "role",
                "trust",
                "provider",
                "external",
            ],
            concern_keywords: &["permission", "trust", "provider"],
            gap_keywords: &["permission", "route", "provider", "runtime"],
            reading: "authority labels, trust handoffs, provider output, and boundary checks concentrate in this workflow",
        },
        WorkflowAxisSpec {
            axis: "stateEffectReconciliation",
            family_weights: &[
                ("state", 3),
                ("effect", 3),
                ("contractSpecification", 1),
                ("semantic", 1),
            ],
            keywords: &[
                "job",
                "event",
                "status",
                "retry",
                "processing",
                "external",
                "effect",
                "commit",
                "delete",
                "purge",
                "upload",
            ],
            concern_keywords: &["commit", "recovery", "retry"],
            gap_keywords: &["runtime", "provider", "test"],
            reading: "durable state, external effects, retry, and status-finalization pressure concentrate in this workflow",
        },
        WorkflowAxisSpec {
            axis: "sourceBackedDomainCohesion",
            family_weights: &[
                ("state", 2),
                ("semantic", 3),
                ("contractSpecification", 2),
                ("relation", 2),
            ],
            keywords: &[
                "source", "voc", "insight", "solution", "persona", "market", "domain", "artifact",
                "context",
            ],
            concern_keywords: &[],
            gap_keywords: &["model", "semantic", "test"],
            reading: "source-backed domain identity, relation, and contract cohesion concentrate in this workflow",
        },
        WorkflowAxisSpec {
            axis: "llmOutputMediation",
            family_weights: &[
                ("trust", 3),
                ("semantic", 3),
                ("contractSpecification", 2),
                ("effect", 2),
                ("capability", 1),
            ],
            keywords: &[
                "llm",
                "ai",
                "agent",
                "prompt",
                "generation",
                "provider",
                "openai",
                "tool",
                "transcription",
            ],
            concern_keywords: &["provider", "trust"],
            gap_keywords: &["provider", "runtime", "test"],
            reading: "prompt/context validation, LLM/provider output, filtering, and persistence gates concentrate in this workflow",
        },
        WorkflowAxisSpec {
            axis: "permissionCoverage",
            family_weights: &[
                ("authority", 4),
                ("relation", 2),
                ("contractSpecification", 2),
                ("trust", 1),
            ],
            keywords: &[
                "route",
                "api",
                "admin",
                "workspace",
                "permission",
                "role",
                "tenant",
                "session",
                "jwt",
            ],
            concern_keywords: &["permission"],
            gap_keywords: &["permission", "route"],
            reading: "route/session/admin authority coverage concentrates in this workflow",
        },
    ]
}

fn matching_keywords(text: &str, keywords: &[&str]) -> Vec<String> {
    keywords
        .iter()
        .filter(|keyword| text.contains(**keyword))
        .map(|keyword| keyword.to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn workflow_axis_gap_refs(archmap: &ArchMapDocumentV0, gap_keywords: &[&str]) -> Vec<String> {
    archmap
        .observation_gaps
        .iter()
        .filter(|gap| {
            let text = format!(
                "{} {} {} {} {}",
                gap.gap_id,
                gap.gap_kind,
                gap.subject_ref,
                gap.reason,
                gap.expected_atom_families.join(" ")
            )
            .to_ascii_lowercase();
            !matching_keywords(&text, gap_keywords).is_empty()
        })
        .map(|gap| gap.gap_id.clone())
        .collect()
}

fn workflow_review_focus(axis: &str) -> String {
    match axis {
        "authorityTrustBoundary" => {
            "authority label, trust handoff, provider output, and boundary checks".to_string()
        }
        "stateEffectReconciliation" => {
            "retry / duplicate / partial failure / status finalization".to_string()
        }
        "sourceBackedDomainCohesion" => {
            "Source-backed domain identity, relations, and contract cohesion".to_string()
        }
        "llmOutputMediation" => {
            "prompt/context validation, LLM output filtering, persistence gate".to_string()
        }
        "permissionCoverage" => {
            "route-by-route permission dependency and tenant/workspace scope".to_string()
        }
        _ => "inspect source refs and coverage boundaries".to_string(),
    }
}

fn workflow_risk_status(risk_score: i64, coverage_gap_refs: &[String]) -> &'static str {
    if risk_score == 0 {
        "nonConclusion"
    } else if !coverage_gap_refs.is_empty() {
        "needsReview"
    } else {
        "actionable"
    }
}

fn workflow_risk_tier(risk_score: i64) -> &'static str {
    if risk_score >= 90 {
        "high"
    } else if risk_score >= 45 {
        "medium"
    } else if risk_score > 0 {
        "low"
    } else {
        "unmeasured"
    }
}

fn build_spectral_analysis_readings(
    archmap: &ArchMapDocumentV0,
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
) -> Vec<ArchSigSpectralAnalysisReadingV0> {
    vec![
        workflow_risk_axis_pressure_spectrum(workflow_risk_readings),
        molecule_atom_overlap_spectrum(archmap),
        obstruction_axis_curvature_spectrum(obstruction_circuits, signature_axes),
        operation_signature_delta_spectrum(operation_deltas, signature_axes),
    ]
}

fn workflow_risk_axis_pressure_spectrum(
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
) -> ArchSigSpectralAnalysisReadingV0 {
    let axes = workflow_risk_readings
        .iter()
        .flat_map(|reading| reading.top_axes.iter().map(|axis| axis.axis.as_str()))
        .collect::<BTreeSet<_>>();
    let nonzero_entry_count = workflow_risk_readings
        .iter()
        .map(|reading| reading.top_axes.len())
        .sum::<usize>();
    let max_row = workflow_risk_readings
        .iter()
        .map(|reading| reading.risk_score)
        .max()
        .unwrap_or_default();
    let mut axis_scores = BTreeMap::<String, i64>::new();
    let mut squared_sum = 0_f64;
    for axis in workflow_risk_readings
        .iter()
        .flat_map(|reading| reading.top_axes.iter())
    {
        *axis_scores.entry(axis.axis.clone()).or_default() += axis.score;
        squared_sum += (axis.score as f64).powi(2);
    }
    let max_col = axis_scores.values().copied().max().unwrap_or_default();
    let mut dominant_components = Vec::new();
    if let Some(workflow) = workflow_risk_readings.iter().max_by(|left, right| {
        left.risk_score
            .cmp(&right.risk_score)
            .then(left.workflow_risk_id.cmp(&right.workflow_risk_id))
    }) {
        dominant_components.push(spectral_component(
            &workflow.molecule_observation_ref,
            "workflow",
            workflow.risk_score.to_string(),
            "dominant row pressure in the workflow-by-axis matrix",
        ));
    }
    if let Some((axis, score)) = axis_scores
        .iter()
        .max_by(|left, right| left.1.cmp(right.1).then(left.0.cmp(right.0)))
    {
        dominant_components.push(spectral_component(
            axis,
            "workflowRiskAxis",
            score.to_string(),
            "dominant column pressure accumulated across workflows",
        ));
    }

    spectral_reading(
        "spectral:workflow-risk-axis-pressure",
        "workflowRiskAxisPressureMatrix",
        spectral_status(
            nonzero_entry_count,
            workflow_risk_readings
                .iter()
                .any(|reading| !reading.coverage_gap_refs.is_empty()),
        ),
        spectral_shape(
            "workflowRiskReadings",
            "workflowRiskAxes",
            workflow_risk_readings.len(),
            axes.len(),
            nonzero_entry_count,
        ),
        "entry(i,j) is the workflow risk axis score for workflow i and risk axis j",
        vec![
            spectral_value(
                "maxRowSum",
                max_row,
                "largest molecule-local review pressure",
            ),
            spectral_value("maxColumnSum", max_col, "largest accumulated axis pressure"),
            spectral_float_value(
                "frobeniusNorm",
                squared_sum.sqrt(),
                "global pressure magnitude of the observed finite matrix",
            ),
            spectral_float_value(
                "spectralRadiusUpperBound",
                spectral_upper_bound(max_row, max_col),
                "nonnegative-matrix upper bound, not an exact eigen theorem",
            ),
        ],
        dominant_components,
        workflow_risk_readings
            .iter()
            .map(|reading| reading.workflow_risk_id.clone())
            .collect(),
        "workflow risk pressure is concentrated by rows and axes; use the dominant row and column before treating local risk as isolated",
        "coverage gaps on workflow axes block measured-zero interpretation for absent entries",
        "zero entries mean no observed risk-axis evidence under current ArchMap and heuristics, not absence of architectural pressure",
        "review the dominant workflow row, dominant axis column, and coverage gaps before selecting repair operations",
    )
}

fn molecule_atom_overlap_spectrum(archmap: &ArchMapDocumentV0) -> ArchSigSpectralAnalysisReadingV0 {
    let atom_family_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom.atom_family.as_str()))
        .collect::<BTreeMap<_, _>>();
    let molecule_atoms = archmap
        .molecule_observations
        .iter()
        .map(|molecule| {
            let atom_refs = molecule
                .atom_observation_refs
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            let family_counts = molecule
                .atom_observation_refs
                .iter()
                .filter_map(|atom_ref| atom_family_by_id.get(atom_ref.as_str()).copied())
                .fold(BTreeMap::<String, usize>::new(), |mut counts, family| {
                    *counts.entry(family.to_string()).or_default() += 1;
                    counts
                });
            (
                molecule.molecule_observation_id.clone(),
                atom_refs,
                family_counts,
            )
        })
        .collect::<Vec<_>>();

    let mut row_sums = BTreeMap::<String, i64>::new();
    let mut nonzero_entry_count = 0_usize;
    let mut squared_sum = 0_f64;
    for (left_id, left_atoms, left_families) in &molecule_atoms {
        for (right_id, right_atoms, right_families) in &molecule_atoms {
            let exact_overlap = left_atoms.intersection(right_atoms).count() as i64;
            let family_overlap = left_families
                .iter()
                .map(|(family, left_count)| {
                    right_families
                        .get(family)
                        .map(|right_count| (*left_count).min(*right_count))
                        .unwrap_or_default()
                })
                .sum::<usize>() as i64;
            let weight = if left_id == right_id {
                family_overlap.max(exact_overlap)
            } else {
                exact_overlap * 2 + family_overlap
            };
            if weight > 0 {
                nonzero_entry_count += 1;
                squared_sum += (weight as f64).powi(2);
                *row_sums.entry(left_id.clone()).or_default() += weight;
            }
        }
    }
    let max_row = row_sums.values().copied().max().unwrap_or_default();
    let dominant_components = row_sums
        .iter()
        .max_by(|left, right| left.1.cmp(right.1).then(left.0.cmp(right.0)))
        .map(|(molecule_ref, value)| {
            vec![spectral_component(
                molecule_ref,
                "molecule",
                value.to_string(),
                "dominant molecule by atom/family overlap mass",
            )]
        })
        .unwrap_or_default();

    spectral_reading(
        "spectral:molecule-atom-overlap-coupling",
        "moleculeAtomOverlapCouplingMatrix",
        spectral_status(nonzero_entry_count, !archmap.observation_gaps.is_empty()),
        spectral_shape(
            "moleculeObservations",
            "moleculeObservations",
            molecule_atoms.len(),
            molecule_atoms.len(),
            nonzero_entry_count,
        ),
        "entry(i,j) is exact atom overlap weighted with atom-family overlap; the diagonal records molecule atom-family mass",
        vec![
            spectral_value(
                "maxRowSum",
                max_row,
                "largest observed molecule overlap mass",
            ),
            spectral_float_value(
                "frobeniusNorm",
                squared_sum.sqrt(),
                "observed overlap magnitude of the molecule coupling matrix",
            ),
            spectral_float_value(
                "spectralRadiusUpperBound",
                max_row as f64,
                "Gershgorin-style row-sum upper bound for this nonnegative matrix",
            ),
        ],
        dominant_components,
        archmap
            .molecule_observations
            .iter()
            .map(|molecule| molecule.molecule_observation_id.clone())
            .collect(),
        "molecules sharing atom refs or atom families form an overlap coupling surface that is invisible to import-only static analysis",
        "missing atom families and observation gaps can make overlap coupling appear smaller than the source architecture actually is",
        "zero off-diagonal overlap means no shared observed atom/family evidence, not guaranteed independence",
        "inspect the dominant molecule and any high-overlap neighbors before splitting or moving responsibilities",
    )
}

fn obstruction_axis_curvature_spectrum(
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> ArchSigSpectralAnalysisReadingV0 {
    let axis_ids = signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut axis_scores = BTreeMap::<String, i64>::new();
    let mut max_row = 0_i64;
    let mut squared_sum = 0_f64;
    let mut nonzero_entry_count = 0_usize;
    for circuit in obstruction_circuits {
        let row_sum = circuit
            .signature_axis_refs
            .iter()
            .filter(|axis_ref| axis_ids.contains(axis_ref.as_str()))
            .map(|axis_ref| {
                *axis_scores.entry(axis_ref.clone()).or_default() += 1;
                squared_sum += 1_f64;
                nonzero_entry_count += 1;
                1_i64
            })
            .sum::<i64>();
        max_row = max_row.max(row_sum);
    }
    let max_col = axis_scores.values().copied().max().unwrap_or_default();
    let mut dominant_components = Vec::new();
    if let Some(circuit) = obstruction_circuits.iter().max_by(|left, right| {
        left.signature_axis_refs
            .len()
            .cmp(&right.signature_axis_refs.len())
            .then(
                left.obstruction_circuit_id
                    .cmp(&right.obstruction_circuit_id),
            )
    }) {
        dominant_components.push(spectral_component(
            &circuit.obstruction_circuit_id,
            "obstructionCircuit",
            circuit.signature_axis_refs.len().to_string(),
            "dominant obstruction row by connected signature axes",
        ));
    }
    if let Some((axis_ref, value)) = axis_scores
        .iter()
        .max_by(|left, right| left.1.cmp(right.1).then(left.0.cmp(right.0)))
    {
        dominant_components.push(spectral_component(
            axis_ref,
            "signatureAxis",
            value.to_string(),
            "dominant curvature column across obstruction circuits",
        ));
    }

    spectral_reading(
        "spectral:obstruction-axis-curvature",
        "obstructionAxisCurvatureMatrix",
        spectral_status(nonzero_entry_count, false),
        spectral_shape(
            "obstructionCircuits",
            "signatureAxes",
            obstruction_circuits.len(),
            signature_axes.len(),
            nonzero_entry_count,
        ),
        "entry(i,j) is 1 when obstruction circuit i contributes to signature axis j",
        vec![
            spectral_value(
                "maxRowSum",
                max_row,
                "widest obstruction-to-axis curvature row",
            ),
            spectral_value("maxColumnSum", max_col, "most repeated obstruction axis"),
            spectral_float_value(
                "frobeniusNorm",
                squared_sum.sqrt(),
                "curvature incidence magnitude over constructed obstruction circuits",
            ),
            spectral_float_value(
                "spectralRadiusUpperBound",
                spectral_upper_bound(max_row, max_col),
                "incidence-matrix upper bound, not a global flatness proof",
            ),
        ],
        dominant_components,
        obstruction_circuits
            .iter()
            .map(|circuit| circuit.obstruction_circuit_id.clone())
            .collect(),
        "obstruction circuits distribute curvature onto signature axes; repeated columns indicate axes where local failures accumulate",
        "only constructed obstruction circuits are represented; concern hints that lack witness rules remain outside this matrix",
        "zero incidence means no constructed obstruction-to-axis edge, not proof of zero curvature",
        "review the dominant obstruction row and repeated axis column before treating a signature axis as local",
    )
}

fn operation_signature_delta_spectrum(
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> ArchSigSpectralAnalysisReadingV0 {
    let axis_ids = signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut axis_scores = BTreeMap::<String, i64>::new();
    let mut max_row = 0_i64;
    let mut squared_sum = 0_f64;
    let mut nonzero_entry_count = 0_usize;
    for delta in operation_deltas {
        let mentioned_axes = delta
            .signature_delta
            .iter()
            .flat_map(|entry| {
                axis_ids
                    .iter()
                    .filter(|axis_id| entry.contains(**axis_id))
                    .map(|axis_id| (*axis_id).to_string())
                    .collect::<Vec<_>>()
            })
            .chain(delta.decreased_axes.iter().cloned())
            .collect::<BTreeSet<_>>();
        let row_sum = mentioned_axes
            .iter()
            .filter(|axis_ref| axis_ids.contains(axis_ref.as_str()))
            .map(|axis_ref| {
                *axis_scores.entry(axis_ref.clone()).or_default() += 1;
                squared_sum += 1_f64;
                nonzero_entry_count += 1;
                1_i64
            })
            .sum::<i64>();
        max_row = max_row.max(row_sum);
    }
    let max_col = axis_scores.values().copied().max().unwrap_or_default();
    let mut dominant_components = Vec::new();
    if let Some(delta) = operation_deltas.iter().max_by(|left, right| {
        left.decreased_axes
            .len()
            .cmp(&right.decreased_axes.len())
            .then(left.operation_delta_id.cmp(&right.operation_delta_id))
    }) {
        dominant_components.push(spectral_component(
            &delta.operation_delta_id,
            "operationDelta",
            delta.decreased_axes.len().to_string(),
            "dominant operation row by declared decreased axes",
        ));
    }
    if let Some((axis_ref, value)) = axis_scores
        .iter()
        .max_by(|left, right| left.1.cmp(right.1).then(left.0.cmp(right.0)))
    {
        dominant_components.push(spectral_component(
            axis_ref,
            "signatureAxis",
            value.to_string(),
            "dominant signature axis touched by operation deltas",
        ));
    }

    spectral_reading(
        "spectral:operation-signature-delta",
        "operationSignatureDeltaMatrix",
        spectral_status(nonzero_entry_count, false),
        spectral_shape(
            "operationDeltas",
            "signatureAxes",
            operation_deltas.len(),
            signature_axes.len(),
            nonzero_entry_count,
        ),
        "entry(i,j) is 1 when operation delta i declares or mentions a change to signature axis j",
        vec![
            spectral_value(
                "maxRowSum",
                max_row,
                "widest operation-to-signature delta row",
            ),
            spectral_value(
                "maxColumnSum",
                max_col,
                "signature axis touched by most operations",
            ),
            spectral_float_value(
                "frobeniusNorm",
                squared_sum.sqrt(),
                "operation delta incidence magnitude",
            ),
            spectral_float_value(
                "spectralRadiusUpperBound",
                spectral_upper_bound(max_row, max_col),
                "operation-transition upper bound, not repair correctness",
            ),
        ],
        dominant_components,
        operation_deltas
            .iter()
            .map(|delta| delta.operation_delta_id.clone())
            .collect(),
        "operation deltas show which signature axes would move together under candidate repairs or evidence enrichment",
        "candidate operations are bounded review artifacts; absent delta entries are not proof that an operation preserves an axis",
        "zero delta incidence means no declared or text-mentioned axis movement under current candidates, not repair safety",
        "review the dominant operation row and repeated axis column before converting a repair candidate into code changes",
    )
}

fn spectral_reading(
    spectral_reading_id: &str,
    representation_family: &str,
    status: &str,
    matrix_shape: ArchSigSpectralMatrixShapeV0,
    entry_rule: &str,
    values: Vec<ArchSigSpectralValueV0>,
    dominant_components: Vec<ArchSigSpectralDominantComponentV0>,
    support_refs: Vec<String>,
    reading: &str,
    coverage_boundary: &str,
    zero_reflecting_boundary: &str,
    recommended_next_action: &str,
) -> ArchSigSpectralAnalysisReadingV0 {
    ArchSigSpectralAnalysisReadingV0 {
        spectral_reading_id: spectral_reading_id.to_string(),
        representation_family: representation_family.to_string(),
        status: status.to_string(),
        matrix_shape,
        entry_rule: entry_rule.to_string(),
        value_type: "boundedSpectralProxy".to_string(),
        values,
        dominant_components,
        support_refs,
        reading: reading.to_string(),
        coverage_boundary: coverage_boundary.to_string(),
        zero_reflecting_boundary: zero_reflecting_boundary.to_string(),
        recommended_next_action: recommended_next_action.to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn spectral_shape(
    row_domain: &str,
    column_domain: &str,
    row_count: usize,
    column_count: usize,
    nonzero_entry_count: usize,
) -> ArchSigSpectralMatrixShapeV0 {
    ArchSigSpectralMatrixShapeV0 {
        row_domain: row_domain.to_string(),
        column_domain: column_domain.to_string(),
        row_count,
        column_count,
        nonzero_entry_count,
    }
}

fn spectral_value(name: &str, value: i64, interpretation: &str) -> ArchSigSpectralValueV0 {
    ArchSigSpectralValueV0 {
        name: name.to_string(),
        value: value.to_string(),
        interpretation: interpretation.to_string(),
    }
}

fn spectral_float_value(name: &str, value: f64, interpretation: &str) -> ArchSigSpectralValueV0 {
    ArchSigSpectralValueV0 {
        name: name.to_string(),
        value: format!("{value:.3}"),
        interpretation: interpretation.to_string(),
    }
}

fn spectral_component(
    component_ref: &str,
    component_kind: &str,
    value: String,
    reading: &str,
) -> ArchSigSpectralDominantComponentV0 {
    ArchSigSpectralDominantComponentV0 {
        component_ref: component_ref.to_string(),
        component_kind: component_kind.to_string(),
        value,
        reading: reading.to_string(),
    }
}

fn spectral_status(nonzero_entry_count: usize, has_coverage_gap: bool) -> &'static str {
    if nonzero_entry_count == 0 {
        "nonConclusion"
    } else if has_coverage_gap {
        "needsReview"
    } else {
        "actionable"
    }
}

fn spectral_upper_bound(max_row: i64, max_col: i64) -> f64 {
    ((max_row.max(0) as f64) * (max_col.max(0) as f64)).sqrt()
}

fn build_spectral_mode_readings(
    spectral_analysis_readings: &[ArchSigSpectralAnalysisReadingV0],
) -> Vec<ArchSigSpectralModeReadingV0> {
    spectral_analysis_readings
        .iter()
        .map(spectral_mode_reading)
        .collect()
}

fn spectral_mode_reading(
    spectral_reading: &ArchSigSpectralAnalysisReadingV0,
) -> ArchSigSpectralModeReadingV0 {
    let max_row = spectral_value_by_name(spectral_reading, "maxRowSum");
    let max_col = spectral_value_by_name(spectral_reading, "maxColumnSum");
    let frobenius = spectral_value_by_name(spectral_reading, "frobeniusNorm");
    let dominant = if max_row > 0.0 { max_row } else { max_col };
    let dominant_norm = dominant.min(frobenius);
    let residual = (frobenius.powi(2) - dominant_norm.powi(2)).max(0.0).sqrt();
    let gap_proxy = dominant_norm - residual;
    let localization = if frobenius > 0.0 {
        (dominant_norm / frobenius).min(1.0)
    } else {
        0.0
    };
    let density = spectral_matrix_density(&spectral_reading.matrix_shape);
    let mode_kind = spectral_mode_kind(
        &spectral_reading.representation_family,
        localization,
        density,
    );
    let mode_components = spectral_reading
        .dominant_components
        .iter()
        .enumerate()
        .map(|(index, component)| ArchSigSpectralModeComponentV0 {
            component_ref: component.component_ref.clone(),
            component_kind: component.component_kind.clone(),
            weight: component.value.clone(),
            role: if index == 0 {
                "primaryDominantComponent"
            } else {
                "coupledDominantComponent"
            }
            .to_string(),
            reading: component.reading.clone(),
        })
        .collect::<Vec<_>>();

    ArchSigSpectralModeReadingV0 {
        spectral_mode_id: format!(
            "spectral-mode:{}",
            stable_id(&spectral_reading.spectral_reading_id)
        ),
        source_spectral_reading_ref: spectral_reading.spectral_reading_id.clone(),
        representation_family: spectral_reading.representation_family.clone(),
        status: spectral_mode_status(spectral_reading, localization, density).to_string(),
        mode_kind: mode_kind.to_string(),
        mode_components,
        spectral_gap_proxy: spectral_float_value(
            "dominantResidualGapProxy",
            gap_proxy,
            "dominant component magnitude minus residual Frobenius mass; bounded proxy, not an eigenvalue gap theorem",
        ),
        localization_index: spectral_float_value(
            "dominantFrobeniusLocalization",
            localization,
            "dominant component magnitude divided by Frobenius norm; higher means pressure is more localized",
        ),
        matrix_density: spectral_float_value(
            "nonzeroMatrixDensity",
            density,
            "nonzero entries divided by finite matrix capacity; higher means more distributed coupling",
        ),
        decomposability_reading: spectral_decomposability_reading(localization, density).to_string(),
        repair_perturbation_reading: spectral_repair_perturbation_reading(
            spectral_reading,
            localization,
            density,
        ),
        evidence_boundary:
            "spectral mode is a bounded proxy computed from ArchSig finite representation summaries, not an exact eigenvector theorem"
                .to_string(),
        recommended_next_action: spectral_mode_next_action(
            &spectral_reading.representation_family,
            localization,
            density,
        ),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn spectral_value_by_name(reading: &ArchSigSpectralAnalysisReadingV0, name: &str) -> f64 {
    reading
        .values
        .iter()
        .find(|value| value.name == name)
        .and_then(|value| value.value.parse::<f64>().ok())
        .unwrap_or_default()
}

fn spectral_matrix_density(shape: &ArchSigSpectralMatrixShapeV0) -> f64 {
    let capacity = shape.row_count.saturating_mul(shape.column_count);
    if capacity == 0 {
        0.0
    } else {
        shape.nonzero_entry_count as f64 / capacity as f64
    }
}

fn spectral_mode_kind(
    representation_family: &str,
    localization: f64,
    density: f64,
) -> &'static str {
    match representation_family {
        "workflowRiskAxisPressureMatrix" if density >= 0.65 => "distributedPressureMode",
        "workflowRiskAxisPressureMatrix" if localization >= 0.55 => "localizedPressureMode",
        "workflowRiskAxisPressureMatrix" => "distributedPressureMode",
        "moleculeAtomOverlapCouplingMatrix" if density >= 0.65 => "delocalizedCouplingMode",
        "moleculeAtomOverlapCouplingMatrix" => "localizedCouplingMode",
        "obstructionAxisCurvatureMatrix" => "curvatureMode",
        "operationSignatureDeltaMatrix" if density >= 0.65 => "broadPerturbationMode",
        "operationSignatureDeltaMatrix" => "localizedPerturbationMode",
        _ => "boundedSpectralMode",
    }
}

fn spectral_mode_status(
    spectral_reading: &ArchSigSpectralAnalysisReadingV0,
    localization: f64,
    density: f64,
) -> &'static str {
    if spectral_reading.matrix_shape.nonzero_entry_count == 0 {
        "nonConclusion"
    } else if spectral_reading.status == "needsReview" || density >= 0.65 || localization < 0.35 {
        "needsReview"
    } else {
        "actionable"
    }
}

fn spectral_decomposability_reading(localization: f64, density: f64) -> &'static str {
    if density <= 0.35 && localization >= 0.55 {
        "mode is relatively localized; decomposition or targeted repair may be reviewable as a local operation"
    } else if density >= 0.65 || localization < 0.35 {
        "mode is delocalized or dense; treat the concern as architecture-wide coupling before attempting local repair"
    } else {
        "mode is mixed; local repair may work, but review nearby coupled components and transferred axes"
    }
}

fn spectral_repair_perturbation_reading(
    spectral_reading: &ArchSigSpectralAnalysisReadingV0,
    localization: f64,
    density: f64,
) -> String {
    if spectral_reading.representation_family == "operationSignatureDeltaMatrix" {
        if density >= 0.65 {
            "candidate operations touch many signature axes; repair is likely to move complexity across axes"
                .to_string()
        } else if localization >= 0.55 {
            "candidate operations have a dominant perturbation mode; review the leading operation before broad refactoring"
                .to_string()
        } else {
            "candidate operations have no strongly localized perturbation mode; require human review before code changes"
                .to_string()
        }
    } else {
        "not an operation transition matrix; use this mode to choose review focus before evaluating repair perturbations"
            .to_string()
    }
}

fn spectral_mode_next_action(
    representation_family: &str,
    localization: f64,
    density: f64,
) -> String {
    match representation_family {
        "workflowRiskAxisPressureMatrix" => {
            if localization >= 0.55 {
                "start review from the dominant workflow and dominant risk axis, then verify coverage gaps"
            } else {
                "treat review as a cross-workflow pressure mode and compare top workflows before assigning local ownership"
            }
        }
        "moleculeAtomOverlapCouplingMatrix" => {
            if density >= 0.65 {
                "map shared atom families across the dense molecule cluster before splitting boundaries"
            } else {
                "inspect the dominant molecule overlap and decide whether the boundary is semantic or accidental"
            }
        }
        "obstructionAxisCurvatureMatrix" => {
            "review whether repeated obstruction-axis curvature is local, transferred, or a law-policy coverage gap"
        }
        "operationSignatureDeltaMatrix" => {
            "compare the perturbation mode against candidate repair preconditions before changing code"
        }
        _ => "review dominant components and evidence boundaries before drawing architectural conclusions",
    }
    .to_string()
}

fn build_spectral_drilldown_readings(
    archmap: &ArchMapDocumentV0,
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
) -> Vec<ArchSigSpectralDrilldownReadingV0> {
    let dominant_atom_family_composition =
        build_dominant_atom_family_composition(archmap, spectral_mode_readings);
    let high_overlap_molecule_pairs = build_high_overlap_molecule_pairs(archmap);
    let repair_axis_delta_readings =
        build_repair_axis_delta_readings(obstruction_circuits, signature_axes, operation_deltas);
    let has_transfer_risk = repair_axis_delta_readings
        .iter()
        .any(|reading| !reading.negative_delta_axes.is_empty());
    let status = if dominant_atom_family_composition.is_empty()
        && high_overlap_molecule_pairs.is_empty()
        && repair_axis_delta_readings.is_empty()
    {
        "nonConclusion"
    } else if !high_overlap_molecule_pairs.is_empty()
        || has_transfer_risk
        || workflow_risk_readings
            .iter()
            .any(|reading| reading.status == "needsReview")
    {
        "needsReview"
    } else {
        "actionable"
    };

    vec![ArchSigSpectralDrilldownReadingV0 {
        drilldown_id: format!("spectral-drilldown:{}", stable_id(&archmap.map_id)),
        status: status.to_string(),
        source_spectral_mode_refs: spectral_mode_readings
            .iter()
            .map(|reading| reading.spectral_mode_id.clone())
            .collect(),
        dominant_atom_family_composition,
        high_overlap_molecule_pairs,
        repair_axis_delta_readings,
        reading:
            "spectral drilldown explains dominant modes with atom-family composition, molecule overlap pairs, and repair axis deltas"
                .to_string(),
        evidence_boundary:
            "drilldown is derived from ArchMap atom/molecule observations and ArchSig spectral summaries; it is not exact eigendecomposition or repair correctness"
                .to_string(),
        recommended_next_action:
            "review dominant atom families, high-overlap molecule pairs, and positive/negative repair delta axes before changing boundaries"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_dominant_atom_family_composition(
    archmap: &ArchMapDocumentV0,
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
) -> Vec<ArchSigDominantAtomFamilyCompositionV0> {
    let molecule_by_id = archmap
        .molecule_observations
        .iter()
        .map(|molecule| (molecule.molecule_observation_id.as_str(), molecule))
        .collect::<BTreeMap<_, _>>();
    let atom_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let mut composition = Vec::new();
    let mut seen_composition = BTreeSet::<(String, String)>::new();
    for component in spectral_mode_readings
        .iter()
        .flat_map(|mode| mode.mode_components.iter())
    {
        if component.component_kind != "workflow" && component.component_kind != "molecule" {
            continue;
        }
        let Some(molecule) = molecule_by_id.get(component.component_ref.as_str()) else {
            continue;
        };
        let mut refs_by_family = BTreeMap::<String, Vec<String>>::new();
        for atom_ref in &molecule.atom_observation_refs {
            if let Some(atom) = atom_by_id.get(atom_ref.as_str()) {
                refs_by_family
                    .entry(atom.atom_family.clone())
                    .or_default()
                    .push(atom.atom_observation_id.clone());
            }
        }
        for (atom_family, mut atom_refs) in refs_by_family {
            if !seen_composition.insert((component.component_ref.clone(), atom_family.clone())) {
                continue;
            }
            atom_refs.sort();
            composition.push(ArchSigDominantAtomFamilyCompositionV0 {
                source_component_ref: component.component_ref.clone(),
                source_component_kind: component.component_kind.clone(),
                atom_family: atom_family.clone(),
                count: atom_refs.len(),
                atom_observation_refs: atom_refs,
                reading: format!(
                    "{} contributes {} observed {} atom(s) to the dominant spectral mode",
                    component.component_ref,
                    molecule
                        .atom_observation_refs
                        .iter()
                        .filter(|atom_ref| {
                            atom_by_id
                                .get(atom_ref.as_str())
                                .is_some_and(|atom| atom.atom_family == atom_family)
                        })
                        .count(),
                    atom_family
                ),
            });
        }
    }
    composition.sort_by(|left, right| {
        right
            .count
            .cmp(&left.count)
            .then(left.source_component_ref.cmp(&right.source_component_ref))
            .then(left.atom_family.cmp(&right.atom_family))
    });
    composition
}

fn build_high_overlap_molecule_pairs(
    archmap: &ArchMapDocumentV0,
) -> Vec<ArchSigHighOverlapMoleculePairV0> {
    let atom_family_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom.atom_family.as_str()))
        .collect::<BTreeMap<_, _>>();
    let molecule_atoms = archmap
        .molecule_observations
        .iter()
        .map(|molecule| {
            let atom_refs = molecule
                .atom_observation_refs
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            let family_counts = molecule
                .atom_observation_refs
                .iter()
                .filter_map(|atom_ref| atom_family_by_id.get(atom_ref.as_str()).copied())
                .fold(BTreeMap::<String, usize>::new(), |mut counts, family| {
                    *counts.entry(family.to_string()).or_default() += 1;
                    counts
                });
            (
                molecule.molecule_observation_id.clone(),
                atom_refs,
                family_counts,
            )
        })
        .collect::<Vec<_>>();
    let mut pairs = Vec::new();
    for left_index in 0..molecule_atoms.len() {
        for right_index in (left_index + 1)..molecule_atoms.len() {
            let (left_id, left_atoms, left_families) = &molecule_atoms[left_index];
            let (right_id, right_atoms, right_families) = &molecule_atoms[right_index];
            let shared_atom_refs = left_atoms
                .intersection(right_atoms)
                .cloned()
                .collect::<Vec<_>>();
            let shared_atom_families = left_families
                .iter()
                .filter_map(|(family, left_count)| {
                    right_families
                        .get(family)
                        .map(|right_count| (family.clone(), (*left_count).min(*right_count)))
                })
                .collect::<Vec<_>>();
            let family_overlap = shared_atom_families
                .iter()
                .map(|(_, count)| *count)
                .sum::<usize>() as i64;
            let overlap_score = shared_atom_refs.len() as i64 * 3 + family_overlap;
            if overlap_score == 0 {
                continue;
            }
            let mut shared_families = shared_atom_families
                .into_iter()
                .map(|(family, _)| family)
                .collect::<Vec<_>>();
            shared_families.sort();
            pairs.push(ArchSigHighOverlapMoleculePairV0 {
                pair_id: format!(
                    "overlap-pair:{}:{}",
                    stable_id(left_id),
                    stable_id(right_id)
                ),
                left_molecule_ref: left_id.clone(),
                right_molecule_ref: right_id.clone(),
                overlap_score,
                shared_atom_families: shared_families,
                shared_atom_refs,
                boundary_advice: overlap_boundary_advice(left_id, right_id),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            });
        }
    }
    pairs.sort_by(|left, right| {
        right
            .overlap_score
            .cmp(&left.overlap_score)
            .then(left.left_molecule_ref.cmp(&right.left_molecule_ref))
            .then(left.right_molecule_ref.cmp(&right.right_molecule_ref))
    });
    pairs.truncate(12);
    pairs
}

fn overlap_boundary_advice(left_id: &str, right_id: &str) -> String {
    format!(
        "review shared atom families before splitting or merging {left_id} and {right_id}; overlap may indicate a semantic hub or leaked responsibility"
    )
}

fn build_repair_axis_delta_readings(
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
) -> Vec<ArchSigRepairAxisDeltaReadingV0> {
    let all_axes = signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<BTreeSet<_>>();
    let obstruction_axes = obstruction_circuits
        .iter()
        .map(|circuit| {
            (
                circuit.obstruction_circuit_id.as_str(),
                circuit
                    .signature_axis_refs
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    operation_deltas
        .iter()
        .map(|delta| {
            let positive_axes = delta
                .support_refs
                .iter()
                .filter_map(|support_ref| obstruction_axes.get(support_ref.as_str()))
                .flat_map(|axes| axes.iter().cloned())
                .collect::<BTreeSet<_>>();
            let mentioned_axes = delta
                .signature_delta
                .iter()
                .flat_map(|entry| {
                    all_axes
                        .iter()
                        .filter(|axis| entry.contains(axis.as_str()))
                        .cloned()
                        .collect::<Vec<_>>()
                })
                .chain(delta.decreased_axes.iter().cloned())
                .filter(|axis| all_axes.contains(axis))
                .collect::<BTreeSet<_>>();
            let positive_delta_axes = if positive_axes.is_empty() {
                delta
                    .decreased_axes
                    .iter()
                    .filter(|axis| all_axes.contains(*axis))
                    .cloned()
                    .collect::<BTreeSet<_>>()
            } else {
                positive_axes
            };
            let negative_delta_axes = mentioned_axes
                .difference(&positive_delta_axes)
                .cloned()
                .collect::<Vec<_>>();
            let neutral_or_unknown_axes = all_axes
                .difference(&mentioned_axes)
                .cloned()
                .collect::<Vec<_>>();
            let positive_delta_axes = positive_delta_axes.into_iter().collect::<Vec<_>>();
            ArchSigRepairAxisDeltaReadingV0 {
                operation_delta_ref: delta.operation_delta_id.clone(),
                operation_kind: delta.operation_kind.clone(),
                reading: repair_axis_delta_reading_text(
                    &positive_delta_axes,
                    &negative_delta_axes,
                    &neutral_or_unknown_axes,
                ),
                positive_delta_axes,
                negative_delta_axes,
                neutral_or_unknown_axes,
                transfer_risk_refs: delta.transferred_obstructions.clone(),
                evidence_boundary:
                    "positive axes come from target obstruction support; negative axes are touched but not target axes; neutral axes are unmentioned under current operation delta evidence"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn repair_axis_delta_reading_text(
    positive_delta_axes: &[String],
    negative_delta_axes: &[String],
    neutral_or_unknown_axes: &[String],
) -> String {
    if !negative_delta_axes.is_empty() {
        format!(
            "operation has {} target-positive axis/axes and {} transferred or side-effect axis/axes; review complexity movement before applying repair",
            positive_delta_axes.len(),
            negative_delta_axes.len()
        )
    } else if !positive_delta_axes.is_empty() && neutral_or_unknown_axes.is_empty() {
        "operation touches only target-positive axes under current evidence, but this is not repair correctness"
            .to_string()
    } else {
        "operation has bounded positive axes and leaves some axes neutral or unknown under current evidence"
            .to_string()
    }
}

fn build_transfer_bridge_readings(
    archmap: &ArchMapDocumentV0,
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    spectral_drilldown_readings: &[ArchSigSpectralDrilldownReadingV0],
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
) -> Vec<ArchSigTransferBridgeReadingV0> {
    let drilldown = spectral_drilldown_readings.first();
    let transfer_matrix_entries = drilldown
        .map(|reading| build_transfer_matrix_entries(&reading.repair_axis_delta_readings))
        .unwrap_or_default();
    let bridge_atom_families = drilldown
        .map(|reading| {
            build_bridge_atom_family_readings(
                archmap,
                spectral_mode_readings,
                workflow_risk_readings,
                &reading.high_overlap_molecule_pairs,
            )
        })
        .unwrap_or_default();
    let evolution_risk_ranking = drilldown
        .map(|reading| {
            build_evolution_risk_ranking(
                &reading.repair_axis_delta_readings,
                &reading.high_overlap_molecule_pairs,
            )
        })
        .unwrap_or_else(|| ArchSigEvolutionRiskRankingV0 {
            repair_transfer_risk_ranking: Vec::new(),
            boundary_preparation_ranking: Vec::new(),
            reading: "no spectral drilldown evidence is available for evolution risk ranking"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    let has_bridge_evidence = bridge_atom_families
        .iter()
        .any(|bridge| bridge.bridge_score > 0 || !bridge.intermediate_molecule_refs.is_empty());
    let status = if transfer_matrix_entries.is_empty() && !has_bridge_evidence {
        "nonConclusion"
    } else if !transfer_matrix_entries.is_empty()
        || bridge_atom_families
            .iter()
            .any(|bridge| bridge.review_risk == "high")
    {
        "needsReview"
    } else {
        "actionable"
    };

    vec![ArchSigTransferBridgeReadingV0 {
        transfer_bridge_id: format!("transfer-bridge:{}", stable_id(&archmap.map_id)),
        status: status.to_string(),
        transfer_matrix_entries,
        bridge_atom_families,
        evolution_risk_ranking,
        reading:
            "transfer bridge reading connects repair transfer axes, bridge atom families, and evolution risk ranking"
                .to_string(),
        evidence_boundary:
            "transfer bridge is derived from ArchMap atom/molecule overlap and ArchSig repair delta summaries; it is not a repair correctness theorem"
                .to_string(),
        recommended_next_action:
            "review bridge atom families and top transfer-risk repairs before applying local architecture changes"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_transfer_matrix_entries(
    repair_axis_delta_readings: &[ArchSigRepairAxisDeltaReadingV0],
) -> Vec<ArchSigTransferMatrixEntryV0> {
    repair_axis_delta_readings
        .iter()
        .flat_map(|delta| {
            delta
                .negative_delta_axes
                .iter()
                .map(|axis_ref| ArchSigTransferMatrixEntryV0 {
                    operation_delta_ref: delta.operation_delta_ref.clone(),
                    transferred_axis_ref: axis_ref.clone(),
                    transfer_weight: 1,
                    transfer_kind: "negativeAxisTransfer".to_string(),
                    reading: format!(
                        "{} may transfer complexity into {}",
                        delta.operation_delta_ref, axis_ref
                    ),
                })
        })
        .collect()
}

fn build_bridge_atom_family_readings(
    archmap: &ArchMapDocumentV0,
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
    high_overlap_pairs: &[ArchSigHighOverlapMoleculePairV0],
) -> Vec<ArchSigBridgeAtomFamilyReadingV0> {
    let source_hub = dominant_mode_component(
        spectral_mode_readings,
        "moleculeAtomOverlapCouplingMatrix",
        "molecule",
    );
    let target_hub = dominant_mode_component(
        spectral_mode_readings,
        "workflowRiskAxisPressureMatrix",
        "workflow",
    )
    .or_else(|| {
        workflow_risk_readings
            .first()
            .map(|reading| reading.molecule_observation_ref.clone())
    });
    let (Some(source_hub), Some(target_hub)) = (source_hub, target_hub) else {
        return Vec::new();
    };
    let Some(path) = bridge_path(&source_hub, &target_hub, high_overlap_pairs) else {
        return vec![ArchSigBridgeAtomFamilyReadingV0 {
            bridge_id: format!(
                "bridge:{}:{}",
                stable_id(&source_hub),
                stable_id(&target_hub)
            ),
            source_hub_molecule_ref: source_hub,
            target_hub_molecule_ref: target_hub,
            intermediate_molecule_refs: Vec::new(),
            bridge_atom_families: Vec::new(),
            bridge_score: 0,
            path_pair_refs: Vec::new(),
            edge_breakdowns: Vec::new(),
            shared_axis_refs: Vec::new(),
            review_risk: "nonConclusion".to_string(),
            recommended_boundary_preparation:
                "no observed overlap path connects the selected hubs under current ArchMap evidence"
                    .to_string(),
            evidence_boundary:
                "absence of a bridge path is not proof of architectural independence".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }];
    };

    let pair_by_endpoints = high_overlap_pairs
        .iter()
        .map(|pair| {
            (
                ordered_pair_key(&pair.left_molecule_ref, &pair.right_molecule_ref),
                pair,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut path_pair_refs = Vec::new();
    let mut edge_breakdowns = Vec::new();
    let mut bridge_atom_families = BTreeSet::new();
    let mut bridge_score = 0_i64;
    for edge in path.windows(2) {
        if let Some(pair) = pair_by_endpoints.get(&ordered_pair_key(&edge[0], &edge[1])) {
            path_pair_refs.push(pair.pair_id.clone());
            bridge_score += pair.overlap_score;
            bridge_atom_families.extend(pair.shared_atom_families.iter().cloned());
            edge_breakdowns.push(build_bridge_edge_breakdown(
                archmap, &edge[0], &edge[1], pair,
            ));
        }
    }
    let shared_axis_refs = shared_workflow_axes(&source_hub, &target_hub, workflow_risk_readings);
    let intermediate_molecule_refs = path
        .iter()
        .skip(1)
        .take(path.len().saturating_sub(2))
        .cloned()
        .collect::<Vec<_>>();
    let review_risk = if bridge_score >= 16 || path.len() <= 3 {
        "high"
    } else if bridge_score > 0 {
        "medium"
    } else {
        "nonConclusion"
    };

    vec![ArchSigBridgeAtomFamilyReadingV0 {
        bridge_id: format!(
            "bridge:{}:{}",
            stable_id(&source_hub),
            stable_id(&target_hub)
        ),
        source_hub_molecule_ref: source_hub.clone(),
        target_hub_molecule_ref: target_hub.clone(),
        intermediate_molecule_refs,
        bridge_atom_families: bridge_atom_families.into_iter().collect(),
        bridge_score,
        path_pair_refs,
        edge_breakdowns,
        shared_axis_refs,
        review_risk: review_risk.to_string(),
        recommended_boundary_preparation: format!(
            "review bridge atom families before assuming {source_hub} and {target_hub} are independent architecture hubs"
        ),
        evidence_boundary:
            "bridge path is computed from high-overlap molecule pairs and shared atom families, not from direct source dependency proof"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_bridge_edge_breakdown(
    archmap: &ArchMapDocumentV0,
    source_molecule_ref: &str,
    target_molecule_ref: &str,
    pair: &ArchSigHighOverlapMoleculePairV0,
) -> ArchSigBridgeEdgeBreakdownV0 {
    let atom_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let molecule_atom_refs = archmap
        .molecule_observations
        .iter()
        .map(|molecule| {
            (
                molecule.molecule_observation_id.as_str(),
                molecule.atom_observation_refs.as_slice(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let shared_family_set = pair
        .shared_atom_families
        .iter()
        .map(|family| family.as_str())
        .collect::<BTreeSet<_>>();
    let exact_shared_set = pair
        .shared_atom_refs
        .iter()
        .map(|atom_ref| atom_ref.as_str())
        .collect::<BTreeSet<_>>();
    let mut family_supporting_atom_refs = BTreeSet::new();
    for molecule_ref in [source_molecule_ref, target_molecule_ref] {
        for atom_ref in molecule_atom_refs
            .get(molecule_ref)
            .copied()
            .unwrap_or_default()
        {
            let Some(atom) = atom_by_id.get(atom_ref.as_str()) else {
                continue;
            };
            if shared_family_set.contains(atom.atom_family.as_str())
                || exact_shared_set.contains(atom.atom_observation_id.as_str())
            {
                family_supporting_atom_refs.insert(atom.atom_observation_id.clone());
            }
        }
    }
    let mut source_refs = BTreeSet::new();
    for atom_ref in family_supporting_atom_refs
        .iter()
        .chain(pair.shared_atom_refs.iter())
    {
        if let Some(atom) = atom_by_id.get(atom_ref.as_str()) {
            source_refs.extend(atom.source_refs.iter().map(source_ref_label));
        }
    }
    let family_supporting_atom_refs = family_supporting_atom_refs.into_iter().collect::<Vec<_>>();
    let source_refs = source_refs.into_iter().collect::<Vec<_>>();
    let dependency_kind = bridge_edge_dependency_kind(pair, &atom_by_id).to_string();
    let recommended_cut_kind =
        bridge_edge_cut_kind(source_molecule_ref, target_molecule_ref, pair).to_string();
    let dependency_reading = format!(
        "{} -> {} is read as {} through shared atom families {:?}",
        source_molecule_ref, target_molecule_ref, dependency_kind, pair.shared_atom_families
    );
    let cut_rationale = bridge_edge_cut_rationale(
        &recommended_cut_kind,
        source_molecule_ref,
        target_molecule_ref,
    );
    let source_ref_count = source_refs.len();
    let source_ref_rationale = format!(
        "sourceRefs collect ArchMap atom evidence supporting shared families {:?} across {} and {}; they bound the review evidence for this bridge edge",
        pair.shared_atom_families, source_molecule_ref, target_molecule_ref
    );
    let review_focus = bridge_edge_review_focus(
        source_molecule_ref,
        target_molecule_ref,
        &dependency_kind,
        &recommended_cut_kind,
        source_ref_count,
        &pair.shared_atom_families,
    );
    let llm_review_summary = format!(
        "Review {} -> {} by reading {} source refs, shared families {:?}, dependency kind {}, and cut recommendation {} before treating the molecules as independently changeable.",
        source_molecule_ref,
        target_molecule_ref,
        source_ref_count,
        pair.shared_atom_families,
        dependency_kind,
        recommended_cut_kind
    );

    ArchSigBridgeEdgeBreakdownV0 {
        edge_id: format!(
            "bridge-edge:{}:{}",
            stable_id(source_molecule_ref),
            stable_id(target_molecule_ref)
        ),
        source_molecule_ref: source_molecule_ref.to_string(),
        target_molecule_ref: target_molecule_ref.to_string(),
        pair_ref: pair.pair_id.clone(),
        overlap_score: pair.overlap_score,
        shared_atom_families: pair.shared_atom_families.clone(),
        shared_atom_refs: pair.shared_atom_refs.clone(),
        family_supporting_atom_refs,
        source_refs,
        source_ref_rationale,
        dependency_kind,
        dependency_reading,
        review_focus,
        recommended_cut_kind,
        cut_rationale,
        llm_review_summary,
        evidence_boundary:
            "edge source refs are derived from ArchMap atom observations in the two bridge molecules; classification is a review reading, not proof of runtime dependency"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn bridge_edge_review_focus(
    source_molecule_ref: &str,
    target_molecule_ref: &str,
    dependency_kind: &str,
    recommended_cut_kind: &str,
    source_ref_count: usize,
    shared_atom_families: &[String],
) -> Vec<String> {
    let mut focus = vec![
        format!(
            "read {source_ref_count} source refs before accepting the bridge {} -> {}",
            source_molecule_ref, target_molecule_ref
        ),
        format!(
            "check shared atom families {:?} to decide whether the edge is structural pressure or incidental overlap",
            shared_atom_families
        ),
        format!(
            "treat dependency kind {dependency_kind} as review classification, not runtime proof"
        ),
        format!(
            "evaluate whether recommended cut kind {recommended_cut_kind} preserves the relevant invariant families"
        ),
    ];
    match recommended_cut_kind {
        "policy" => focus.push(
            "check authority, permission, and contract decisions before moving this boundary"
                .to_string(),
        ),
        "transactionBoundary" => focus.push(
            "check state commit ownership, idempotency, ordering, and rollback semantics".to_string(),
        ),
        "antiCorruptionLayer" => focus.push(
            "check provider, AI, trust, and external-effect translation before admitting domain facts"
                .to_string(),
        ),
        _ => focus.push(
            "check interface contract, capability sharing, and hidden semantic coupling".to_string(),
        ),
    }
    focus
}

fn bridge_edge_dependency_kind(
    pair: &ArchSigHighOverlapMoleculePairV0,
    atom_by_id: &BTreeMap<&str, &crate::ArchMapAtomObservationV0>,
) -> &'static str {
    let exact_contract = pair.shared_atom_refs.iter().any(|atom_ref| {
        atom_by_id
            .get(atom_ref.as_str())
            .is_some_and(|atom| atom.atom_family == "contractSpecification")
    });
    let has_contract_family = pair
        .shared_atom_families
        .iter()
        .any(|family| family == "contractSpecification");
    if exact_contract {
        "explicitContract"
    } else if has_contract_family || !pair.shared_atom_refs.is_empty() {
        "mixedBoundary"
    } else {
        "implicitDependency"
    }
}

fn bridge_edge_cut_kind(
    source_molecule_ref: &str,
    target_molecule_ref: &str,
    pair: &ArchSigHighOverlapMoleculePairV0,
) -> &'static str {
    let joined = format!(
        "{} {} {}",
        source_molecule_ref,
        target_molecule_ref,
        pair.shared_atom_families.join(" ")
    )
    .to_ascii_lowercase();
    if joined.contains("tenant")
        || joined.contains("auth")
        || joined.contains("permission")
        || joined.contains("authority")
        || joined.contains("admin")
        || joined.contains("http")
    {
        "policy"
    } else if joined.contains("llm")
        || joined.contains("external")
        || joined.contains("salesforce")
        || joined.contains("integration")
        || joined.contains("provider")
        || joined.contains("trust")
    {
        "antiCorruptionLayer"
    } else if joined.contains("repository") || joined.contains("transaction") {
        "transactionBoundary"
    } else {
        "interface"
    }
}

fn bridge_edge_cut_rationale(
    recommended_cut_kind: &str,
    source_molecule_ref: &str,
    target_molecule_ref: &str,
) -> String {
    match recommended_cut_kind {
        "policy" => format!(
            "separate tenant/authority decisions from {} -> {} data and workflow access",
            source_molecule_ref, target_molecule_ref
        ),
        "transactionBoundary" => format!(
            "make state commit ownership explicit before crossing {} -> {}",
            source_molecule_ref, target_molecule_ref
        ),
        "antiCorruptionLayer" => format!(
            "translate provider/LLM/external effects before they become domain facts across {} -> {}",
            source_molecule_ref, target_molecule_ref
        ),
        _ => format!(
            "introduce an explicit interface contract before sharing capabilities across {} -> {}",
            source_molecule_ref, target_molecule_ref
        ),
    }
}

fn build_representation_strength_readings(
    archmap: &ArchMapDocumentV0,
    analytic_representations: &[ArchSigAnalyticRepresentationV0],
    spectral_analysis_readings: &[ArchSigSpectralAnalysisReadingV0],
    flatness_reading: &ArchSigFlatnessReadingV0,
) -> Vec<ArchSigRepresentationStrengthReadingV0> {
    let blockers = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let required_assumptions = flatness_reading
        .blocked_by_coverage_gaps
        .iter()
        .cloned()
        .chain(vec![
            "witness completeness for selected LawPolicy".to_string(),
            "signature axis exactness for selected readings".to_string(),
        ])
        .collect::<Vec<_>>();
    let blocked_reasons = if blockers.is_empty() {
        vec![
            "coverage and witness completeness are assumption-relative even without observed gaps"
                .to_string(),
        ]
    } else {
        blockers.clone()
    };

    analytic_representations
        .iter()
        .map(|representation| ArchSigRepresentationStrengthReadingV0 {
            reading_id: format!(
                "representation-strength:{}",
                stable_id(&representation.representation_id)
            ),
            source_reading_ref: representation.representation_id.clone(),
            representation_family: representation.representation_family.clone(),
            zero_preserving: if representation.status == "measured" {
                "supported".to_string()
            } else {
                "bounded".to_string()
            },
            zero_reflecting: if representation
                .zero_reflecting_boundary
                .to_ascii_lowercase()
                .contains("blocked")
                || !blockers.is_empty()
            {
                "blockedByCoverageGap".to_string()
            } else {
                "assumptionRelative".to_string()
            },
            obstruction_preserving: if representation.axis_refs.is_empty()
                && representation.graph_scope_refs.is_empty()
            {
                "weak".to_string()
            } else {
                "supported".to_string()
            },
            obstruction_reflecting: if blockers.is_empty() {
                "assumptionRelative".to_string()
            } else {
                "blockedByCoverageGap".to_string()
            },
            aggregate_zero_safety: "notAggregate".to_string(),
            cancellation_risk: "notApplicable".to_string(),
            required_assumptions: required_assumptions.clone(),
            blocked_by: blockers.clone(),
            blocked_reflection_or_preservation_reasons: blocked_reasons.clone(),
            reading: format!(
                "{} is a bounded analytic representation; use its zero/obstruction readings only with the recorded strength boundary",
                representation.representation_family
            ),
            evidence_boundary: representation.coverage_boundary.clone(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        })
        .chain(spectral_analysis_readings.iter().map(|reading| {
            ArchSigRepresentationStrengthReadingV0 {
                reading_id: format!(
                    "representation-strength:{}",
                    stable_id(&reading.spectral_reading_id)
                ),
                source_reading_ref: reading.spectral_reading_id.clone(),
                representation_family: reading.representation_family.clone(),
                zero_preserving: "boundedProxy".to_string(),
                zero_reflecting: if blockers.is_empty() {
                    "assumptionRelative".to_string()
                } else {
                    "blockedByCoverageGap".to_string()
                },
                obstruction_preserving: if reading.support_refs.is_empty() {
                    "weak".to_string()
                } else {
                    "supported".to_string()
                },
                obstruction_reflecting: "notAnEigenvalueTheorem".to_string(),
                aggregate_zero_safety: "proxyOnly".to_string(),
                cancellation_risk: "boundedProxyMayHideLocalComponents".to_string(),
                required_assumptions: required_assumptions.clone(),
                blocked_by: blockers.clone(),
                blocked_reflection_or_preservation_reasons: blocked_reasons.clone(),
                reading: format!(
                    "{} is a spectral proxy for review; it preserves selected pressure but does not reflect global architecture truth",
                    reading.representation_family
                ),
                evidence_boundary: reading.coverage_boundary.clone(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        }))
        .collect()
}

fn build_atom_support_axis_readings(
    archmap: &ArchMapDocumentV0,
    molecule_readings: &[ArchSigMoleculeReadingV0],
) -> Vec<ArchSigAtomSupportAxisReadingV0> {
    let atom_by_id = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let build_reading = |scope_ref: String, scope_kind: String, atom_refs: Vec<String>| {
        let atoms = atom_refs
            .iter()
            .filter_map(|atom_ref| atom_by_id.get(atom_ref.as_str()).copied())
            .collect::<Vec<_>>();
        let mut subject_map = BTreeMap::<String, Vec<String>>::new();
        let mut axis_map = BTreeMap::<String, Vec<String>>::new();
        let mut source_refs = BTreeSet::<String>::new();
        for atom in &atoms {
            subject_map
                .entry(atom.subject_ref.clone())
                .or_default()
                .push(atom.atom_family.clone());
            axis_map
                .entry(atom.atom_family.clone())
                .or_default()
                .push(atom.atom_observation_id.clone());
            for source_ref in &atom.source_refs {
                source_refs.insert(source_ref_label(source_ref));
            }
        }
        let mut subject_family_spread = subject_map
            .into_iter()
            .map(|(subject_ref, families)| {
                let unique = unique_strings(families.into_iter());
                ArchSigSubjectFamilySpreadV0 {
                    subject_ref,
                    atom_count: unique.len(),
                    atom_families: unique,
                }
            })
            .collect::<Vec<_>>();
        subject_family_spread.sort_by(|a, b| b.atom_count.cmp(&a.atom_count));
        let axis_restriction_counts = axis_map
            .into_iter()
            .map(|(axis, refs)| ArchSigAxisRestrictionCountV0 {
                axis,
                atom_count: refs.len(),
                atom_observation_refs: refs,
            })
            .collect::<Vec<_>>();
        let support_size = atoms
            .iter()
            .map(|atom| atom.subject_ref.clone())
            .collect::<BTreeSet<_>>()
            .len();
        let max_axis = axis_restriction_counts
            .iter()
            .map(|axis| axis.atom_count)
            .max()
            .unwrap_or(0);
        let axis_total = axis_restriction_counts
            .iter()
            .map(|axis| axis.atom_count)
            .sum::<usize>()
            .max(1);
        ArchSigAtomSupportAxisReadingV0 {
            reading_id: format!("atom-support-axis:{}", stable_id(&scope_ref)),
            scope_ref,
            scope_kind,
            support_size,
            subject_family_spread,
            axis_restriction_counts,
            axis_concentration: format!("maxAxisShare={}/{}", max_axis, axis_total),
            mixed_axis_molecule_pressure: if max_axis < axis_total {
                "mixedAxisPressurePresent".to_string()
            } else {
                "singleAxisDominant".to_string()
            },
            high_support_refs: atoms
                .iter()
                .take(12)
                .map(|atom| atom.atom_observation_id.clone())
                .collect(),
            source_refs: source_refs.into_iter().collect(),
            coverage_boundary:
                "support and axis restriction are computed from observed ArchMap atoms only"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }
    };

    let mut readings = vec![build_reading(
        archmap.map_id.clone(),
        "selectedSourceUniverse".to_string(),
        all_atom_refs(archmap),
    )];
    readings.extend(molecule_readings.iter().map(|molecule| {
        build_reading(
            molecule.molecule_observation_ref.clone(),
            "molecule".to_string(),
            molecule.atom_observation_refs.clone(),
        )
    }));
    readings
}

fn build_atom_compatibility_readings(
    archmap: &ArchMapDocumentV0,
) -> Vec<ArchSigAtomCompatibilityReadingV0> {
    let mut slots = BTreeMap::<String, Vec<&crate::ArchMapAtomObservationV0>>::new();
    for atom in &archmap.atom_observations {
        slots
            .entry(format!("{}::{}", atom.subject_ref, atom.predicate))
            .or_default()
            .push(atom);
    }
    let semantic_by_subject = archmap.semantic_observations.iter().fold(
        BTreeMap::<String, Vec<String>>::new(),
        |mut map, semantic| {
            map.entry(semantic.subject_ref.clone())
                .or_default()
                .push(semantic.semantic_observation_id.clone());
            map
        },
    );
    let conflicts = slots
        .into_iter()
        .filter_map(|(slot_ref, atoms)| {
            let families = atoms
                .iter()
                .map(|atom| atom.atom_family.clone())
                .collect::<BTreeSet<_>>();
            let statuses = atoms
                .iter()
                .map(|atom| atom.observation_status.clone())
                .collect::<BTreeSet<_>>();
            if atoms.len() < 2 || (families.len() <= 1 && statuses.len() <= 1) {
                return None;
            }
            let first = atoms[0];
            Some(ArchSigAtomCompatibilityConflictV0 {
                slot_ref,
                subject_ref: first.subject_ref.clone(),
                predicate: first.predicate.clone(),
                atom_observation_refs: atoms
                    .iter()
                    .map(|atom| atom.atom_observation_id.clone())
                    .collect(),
                semantic_observation_refs: semantic_by_subject
                    .get(&first.subject_ref)
                    .cloned()
                    .unwrap_or_default(),
                inconsistency_kind: if families.len() > 1 {
                    "familyDivergence".to_string()
                } else {
                    "statusDivergence".to_string()
                },
                reading: "same subject/predicate slot has divergent observed families or statuses"
                    .to_string(),
            })
        })
        .collect::<Vec<_>>();
    let conflicting_atom_observation_refs = conflicts
        .iter()
        .flat_map(|conflict| conflict.atom_observation_refs.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let conflicting_semantic_observation_refs = conflicts
        .iter()
        .flat_map(|conflict| conflict.semantic_observation_refs.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    vec![ArchSigAtomCompatibilityReadingV0 {
        reading_id: format!("atom-compatibility:{}", stable_id(&archmap.map_id)),
        status: if conflicts.is_empty() {
            "compatibleWithinObservedSlots".to_string()
        } else {
            "conflictNeedsReview".to_string()
        },
        same_slot_conflict_count: conflicts.len(),
        conflicts,
        conflicting_atom_observation_refs,
        conflicting_semantic_observation_refs,
        payload_inconsistency_kinds: vec![
            "familyDivergence".to_string(),
            "statusDivergence".to_string(),
            "semanticDivergence".to_string(),
        ],
        confidence_boundary: "compatibility is checked over observed subject/predicate slots only"
            .to_string(),
        uncertainty: archmap
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.clone())
            .collect(),
        evidence_boundary:
            "compatibility conflict is a review target, not proof of global semantic incorrectness"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_law_universe_coverage_readings(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigLawUniverseCoverageReadingV0> {
    let observed_families = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_family.as_str())
        .collect::<Vec<_>>();
    let gap_refs = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let coverage_status = |ref_id: String, required_families: &[String]| {
        let missing = required_families
            .iter()
            .filter(|family| {
                !observed_families
                    .iter()
                    .any(|observed| family_matches(observed, family))
            })
            .cloned()
            .collect::<Vec<_>>();
        ArchSigCoverageStatusV0 {
            ref_id,
            status: if missing.is_empty() {
                "coveredByObservedAtoms".to_string()
            } else {
                "blockedByCoverageGap".to_string()
            },
            evidence_refs: required_families.to_vec(),
            blocker_refs: missing
                .into_iter()
                .chain(gap_refs.iter().take(3).cloned())
                .collect(),
            reading: "coverage is selected-profile-relative and does not prove lawfulness"
                .to_string(),
        }
    };
    let required_law_coverage = law_policy
        .selected_laws
        .iter()
        .map(|law| coverage_status(law.law_id.clone(), &law.applies_to_atom_families))
        .collect::<Vec<_>>();
    let optional_law_coverage = law_policy
        .optional_axes
        .iter()
        .map(|axis| ArchSigCoverageStatusV0 {
            ref_id: axis.axis_id.clone(),
            status: "optionalAxis".to_string(),
            evidence_refs: axis.evidence_requirements.clone(),
            blocker_refs: Vec::new(),
            reading: "optional axis coverage is advisory".to_string(),
        })
        .collect::<Vec<_>>();
    let witness_family_coverage = law_policy
        .witness_rules
        .iter()
        .map(|rule| coverage_status(rule.witness_rule_id.clone(), &rule.required_atom_families))
        .collect::<Vec<_>>();
    let signature_axis_coverage = signature_axes
        .iter()
        .map(|axis| ArchSigCoverageStatusV0 {
            ref_id: axis.signature_axis_id.clone(),
            status: axis.coverage_status.clone(),
            evidence_refs: axis.source_refs.clone(),
            blocker_refs: axis.missing_evidence.clone(),
            reading: axis.evidence_summary.clone(),
        })
        .collect::<Vec<_>>();
    let exactness_assumption_status = law_policy
        .exactness_assumptions
        .iter()
        .map(|assumption| ArchSigCoverageStatusV0 {
            ref_id: assumption.clone(),
            status: if gap_refs.is_empty() {
                "assumptionRelative".to_string()
            } else {
                "blockedByCoverageGap".to_string()
            },
            evidence_refs: Vec::new(),
            blocker_refs: gap_refs.clone(),
            reading: "exactness assumption is not theorem discharge".to_string(),
        })
        .collect::<Vec<_>>();
    let unmeasured_required_law_count = required_law_coverage
        .iter()
        .filter(|coverage| coverage.status != "coveredByObservedAtoms")
        .count();
    vec![ArchSigLawUniverseCoverageReadingV0 {
        reading_id: format!(
            "law-universe-coverage:{}",
            stable_id(&law_policy.law_policy_id)
        ),
        law_universe_ref: law_policy.law_policy_id.clone(),
        required_law_coverage,
        optional_law_coverage,
        witness_family_coverage,
        signature_axis_coverage,
        exactness_assumption_status,
        unmeasured_required_law_count,
        blocked_witness_refs: law_policy
            .witness_rules
            .iter()
            .filter(|rule| !rule.missing_evidence_behavior.trim().is_empty())
            .map(|rule| rule.witness_rule_id.clone())
            .collect(),
        law_witness_axis_alignment: "selected laws, witness rules, and signature axes are compared by refs only; alignment is profile-relative".to_string(),
        coverage_boundary: "coverage measures selected profile visibility, not LawUniverse completeness".to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_local_curvature_diagram_readings(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigLocalCurvatureDiagramReadingV0> {
    let atom_sources = atom_source_refs_by_id(archmap);
    if obstruction_circuits.is_empty() {
        return vec![ArchSigLocalCurvatureDiagramReadingV0 {
            diagram_id: format!("local-curvature:{}:non-conclusion", stable_id(&archmap.map_id)),
            law_ref: "law:none-observed".to_string(),
            obstruction_ref: "obstruction:none-observed".to_string(),
            signature_axis_refs: Vec::new(),
            molecule_refs: archmap
                .molecule_observations
                .iter()
                .take(6)
                .map(|molecule| molecule.molecule_observation_id.clone())
                .collect(),
            lhs_path_refs: Vec::new(),
            rhs_path_refs: Vec::new(),
            curvature_value: 0,
            curvature_status: "nonConclusion".to_string(),
            diagram_reading:
                "no local curvature diagram is constructed because no obstruction circuit was observed under the selected LawPolicy"
                    .to_string(),
            filling_boundary:
                "absence of constructed curvature is not proof of global flatness".to_string(),
            source_refs: archmap
                .provenance
                .reviewed_refs
                .iter()
                .map(source_ref_label)
                .collect(),
            evidence_boundary:
                "local curvature placeholder records the selected evidence boundary only".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }];
    }
    obstruction_circuits
        .iter()
        .map(|obstruction| {
            let source_refs = obstruction
                .atom_observation_refs
                .iter()
                .flat_map(|atom_ref| atom_sources.get(atom_ref).cloned().unwrap_or_default())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let molecule_refs = obstruction
                .molecule_reading_refs
                .iter()
                .map(|reading_ref| reading_ref.trim_start_matches("molecule-reading:").to_string())
                .collect::<Vec<_>>();
            ArchSigLocalCurvatureDiagramReadingV0 {
                diagram_id: format!(
                    "local-curvature:{}",
                    stable_id(&obstruction.obstruction_circuit_id)
                ),
                law_ref: obstruction.law_ref.clone(),
                obstruction_ref: obstruction.obstruction_circuit_id.clone(),
                signature_axis_refs: obstruction.signature_axis_refs.clone(),
                molecule_refs: molecule_refs.clone(),
                lhs_path_refs: molecule_refs.iter().take(3).cloned().collect(),
                rhs_path_refs: vec![
                    format!("law-path:{}", stable_id(&obstruction.law_ref)),
                    format!("witness-path:{}", stable_id(&obstruction.witness_rule_ref)),
                ],
                curvature_value: obstruction.signature_axis_refs.len().max(1) as i64,
                curvature_status: "nonzero".to_string(),
                diagram_reading: format!(
                    "{} is read as local curvature for {}",
                    obstruction.obstruction_circuit_id, obstruction.law_ref
                ),
                filling_boundary:
                    "diagram filling is LawPolicy-relative and requires selected witness completeness"
                        .to_string(),
                source_refs,
                evidence_boundary: obstruction.evidence_boundary.clone(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_three_layer_flatness_readings(
    archmap: &ArchMapDocumentV0,
    layer_split: &ArchSigLayerSplitV0,
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigThreeLayerFlatnessReadingV0> {
    let nonzero_axes = signature_axes
        .iter()
        .filter(|axis| axis.value != 0)
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<Vec<_>>();
    let cross_layer_atom_refs = archmap
        .atom_observations
        .iter()
        .filter(|atom| {
            matches!(
                atom.atom_family.as_str(),
                "contractSpecification" | "state" | "effect" | "authority" | "trust" | "semantic"
            )
        })
        .take(24)
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    vec![ArchSigThreeLayerFlatnessReadingV0 {
        reading_id: format!("three-layer-flatness:{}", stable_id(&archmap.map_id)),
        static_status: if layer_split.static_observation_refs.is_empty() {
            "unmeasured".to_string()
        } else if nonzero_axes.is_empty() {
            "candidateFlat".to_string()
        } else {
            "needsReview".to_string()
        },
        runtime_status: if layer_split.runtime_observation_refs.is_empty()
            || archmap
                .observation_gaps
                .iter()
                .any(|gap| gap.gap_id.contains("runtime"))
        {
            "blockedByCoverageGap".to_string()
        } else {
            "needsReview".to_string()
        },
        semantic_status: if nonzero_axes.is_empty() {
            "candidateFlat".to_string()
        } else {
            "stressed".to_string()
        },
        static_observation_refs: layer_split.static_observation_refs.clone(),
        runtime_observation_refs: layer_split.runtime_observation_refs.clone(),
        semantic_observation_refs: layer_split.semantic_observation_refs.clone(),
        cross_layer_atom_refs,
        non_implication_reading:
            "static flatness does not imply runtime or semantic flatness; cross-layer atoms must be reviewed separately"
                .to_string(),
        evidence_boundary: layer_split.split_boundary.clone(),
        recommended_next_action:
            "review cross-layer contract/state/effect/authority atoms before treating layer separation as flatness"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_observation_projection_readings(
    archmap: &ArchMapDocumentV0,
) -> Vec<ArchSigObservationProjectionReadingV0> {
    let observed_atom_families = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_family.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let forgotten_coordinates = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let source_refs = archmap
        .provenance
        .reviewed_refs
        .iter()
        .map(source_ref_label)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut slots = BTreeMap::<String, Vec<String>>::new();
    let mut families_by_subject = BTreeMap::<String, BTreeSet<String>>::new();
    for atom in &archmap.atom_observations {
        slots
            .entry(format!("{}::{}", atom.subject_ref, atom.predicate))
            .or_default()
            .push(atom.atom_observation_id.clone());
        families_by_subject
            .entry(atom.subject_ref.clone())
            .or_default()
            .insert(atom.atom_family.clone());
    }
    let observation_collision_pairs = slots
        .into_iter()
        .filter(|(_, refs)| refs.len() > 1)
        .map(|(slot, refs)| format!("{} -> {}", slot, refs.join(",")))
        .collect::<Vec<_>>();
    let collapsed_atom_family_candidates = families_by_subject
        .into_iter()
        .filter(|(_, families)| families.len() > 1)
        .map(|(subject, families)| {
            format!(
                "{} -> {}",
                subject,
                families.into_iter().collect::<Vec<_>>().join(",")
            )
        })
        .collect::<Vec<_>>();
    let hidden_atom_family_hints = archmap
        .observation_gaps
        .iter()
        .map(|gap| format!("{}: {}", gap.gap_id, gap.reason))
        .collect::<Vec<_>>();
    let reconstruction_risk = if forgotten_coordinates.is_empty()
        && observation_collision_pairs.is_empty()
        && collapsed_atom_family_candidates.is_empty()
    {
        "boundedProjectionNoObservedCollision".to_string()
    } else {
        "reconstructionLossPresent".to_string()
    };
    vec![ArchSigObservationProjectionReadingV0 {
        reading_id: format!("observation-projection:{}", stable_id(&archmap.map_id)),
        observed_atom_family_count: observed_atom_families.len(),
        observed_atom_families,
        forgotten_coordinates: forgotten_coordinates.clone(),
        observation_collision_pairs,
        collapsed_atom_family_candidates,
        hidden_atom_family_hints,
        reconstruction_risk,
        coarse_projection_risks: vec![
            "coarse observation may merge distinct canonical atoms".to_string(),
            "unobserved source coordinates must not be read as absent atoms".to_string(),
            "LLM observation uncertainty is projection loss, not Atom non-uniqueness".to_string(),
        ],
        reconstruction_blockers: forgotten_coordinates,
        source_refs,
        reading:
            "ArchMap is treated as an observation projection of a canonical source-derived Atom family"
                .to_string(),
        evidence_boundary:
            "projection reading records lost coordinates and does not reconstruct the complete canonical Atom family"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_state_transition_algebra_readings(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigStateTransitionAlgebraReadingV0> {
    let family_refs = |family: &str| {
        archmap
            .atom_observations
            .iter()
            .filter(|atom| atom.atom_family == family)
            .take(40)
            .map(|atom| atom.atom_observation_id.clone())
            .collect::<Vec<_>>()
    };
    let state_atom_refs = family_refs("state");
    let effect_atom_refs = family_refs("effect");
    let runtime_atom_refs = archmap
        .atom_observations
        .iter()
        .filter(|atom| {
            atom.atom_family.to_ascii_lowercase().contains("runtime")
                || atom.predicate.to_ascii_lowercase().contains("retry")
                || atom.predicate.to_ascii_lowercase().contains("transaction")
                || atom.predicate.to_ascii_lowercase().contains("idempot")
        })
        .take(40)
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    let generator_refs = state_atom_refs
        .iter()
        .chain(effect_atom_refs.iter())
        .chain(runtime_atom_refs.iter())
        .take(48)
        .cloned()
        .collect::<Vec<_>>();
    let obstruction_refs = obstruction_circuits
        .iter()
        .filter(|obstruction| {
            let text = format!(
                "{} {} {}",
                obstruction.law_ref, obstruction.circuit_kind, obstruction.evidence_summary
            )
            .to_ascii_lowercase();
            text.contains("state")
                || text.contains("effect")
                || text.contains("replay")
                || text.contains("runtime")
                || text.contains("idempot")
        })
        .map(|obstruction| obstruction.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    vec![ArchSigStateTransitionAlgebraReadingV0 {
        reading_id: format!("state-transition-algebra:{}", stable_id(&archmap.map_id)),
        generator_refs,
        state_atom_refs,
        effect_atom_refs,
        runtime_atom_refs,
        required_relations: vec![
            "idempotency".to_string(),
            "replay safety".to_string(),
            "state/effect ordering".to_string(),
            "compensation or finalization".to_string(),
            "transaction boundary ownership".to_string(),
        ],
        unresolved_relations: archmap
            .observation_gaps
            .iter()
            .filter(|gap| {
                let text = format!("{} {}", gap.gap_id, gap.reason).to_ascii_lowercase();
                text.contains("runtime")
                    || text.contains("test")
                    || text.contains("model")
                    || text.contains("route")
            })
            .map(|gap| gap.gap_id.clone())
            .collect(),
        obstruction_refs,
        reading:
            "state/effect/runtime atoms generate a bounded state transition algebra reading"
                .to_string(),
        evidence_boundary:
            "transition algebra is derived from observed atoms only; runtime traces and tests remain required for reflecting laws"
                .to_string(),
        recommended_next_action:
            "verify idempotency, replay, ordering, and transaction ownership before claiming state/effect flatness"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_operation_invariant_galois_readings(
    invariant_readings: &[ArchSigInvariantFamilyReadingV0],
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
) -> Vec<ArchSigOperationInvariantGaloisReadingV0> {
    let invariant_family_refs = invariant_readings
        .iter()
        .map(|reading| reading.invariant_id.clone())
        .collect::<Vec<_>>();
    let operation_family_refs = repair_candidates
        .iter()
        .map(|candidate| candidate.repair_operation_candidate_id.clone())
        .collect::<Vec<_>>();
    let preserved_invariant_refs = invariant_readings
        .iter()
        .filter(|reading| reading.status != "stressed")
        .map(|reading| reading.invariant_id.clone())
        .collect::<Vec<_>>();
    let blocked_operation_refs = repair_candidates
        .iter()
        .filter(|candidate| {
            !candidate.missing_evidence.is_empty()
                || candidate
                    .preconditions
                    .iter()
                    .any(|precondition| precondition.contains("coverage gap"))
        })
        .map(|candidate| candidate.repair_operation_candidate_id.clone())
        .collect::<Vec<_>>();
    vec![ArchSigOperationInvariantGaloisReadingV0 {
        reading_id: "operation-invariant-galois:selected-law-policy".to_string(),
        invariant_family_refs,
        operation_family_refs,
        ops_of_invariants: repair_candidates
            .iter()
            .map(|candidate| {
                format!(
                    "{} is allowed only relative to preserved {:?}",
                    candidate.repair_operation_candidate_id, candidate.preserved_invariants
                )
            })
            .collect(),
        inv_of_operations: invariant_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} must be preserved by selected operation families ({})",
                    reading.invariant_id, reading.status
                )
            })
            .collect(),
        preserved_invariant_refs,
        blocked_operation_refs,
        reading:
            "operation families and invariant families form an AAT Galois-style review reading"
                .to_string(),
        evidence_boundary:
            "this reading classifies allowed operation families; it does not prove repair soundness"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_split_readiness_readings(
    molecule_readings: &[ArchSigMoleculeReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    transfer_bridge_readings: &[ArchSigTransferBridgeReadingV0],
) -> Vec<ArchSigSplitReadinessReadingV0> {
    let mut bridge_edges_by_molecule =
        BTreeMap::<String, Vec<&ArchSigBridgeEdgeBreakdownV0>>::new();
    for edge in transfer_bridge_readings
        .iter()
        .flat_map(|reading| reading.bridge_atom_families.iter())
        .flat_map(|bridge| bridge.edge_breakdowns.iter())
    {
        bridge_edges_by_molecule
            .entry(edge.source_molecule_ref.clone())
            .or_default()
            .push(edge);
        bridge_edges_by_molecule
            .entry(edge.target_molecule_ref.clone())
            .or_default()
            .push(edge);
    }
    molecule_readings
        .iter()
        .map(|molecule| {
            let obstruction_refs = obstruction_circuits
                .iter()
                .filter(|obstruction| {
                    obstruction
                        .molecule_reading_refs
                        .iter()
                        .any(|molecule_ref| molecule_ref == &molecule.molecule_reading_id)
                })
                .map(|obstruction| obstruction.obstruction_circuit_id.clone())
                .collect::<Vec<_>>();
            let bridge_edges = bridge_edges_by_molecule
                .get(&molecule.molecule_observation_ref)
                .cloned()
                .unwrap_or_default();
            let bridge_edge_refs = bridge_edges
                .iter()
                .map(|edge| edge.edge_id.clone())
                .collect::<Vec<_>>();
            let recommended_boundary_operation = bridge_edges
                .first()
                .map(|edge| edge.recommended_cut_kind.clone())
                .unwrap_or_else(|| "interface".to_string());
            let penalty =
                (obstruction_refs.len() as i64 * 8 + bridge_edge_refs.len() as i64 * 15).min(100);
            let readiness_score = 100 - penalty;
            let status = if !bridge_edge_refs.is_empty() {
                "needsBoundaryPreparation"
            } else if !obstruction_refs.is_empty() {
                "needsReview"
            } else {
                "candidateSplitReady"
            };
            ArchSigSplitReadinessReadingV0 {
                reading_id: format!(
                    "split-readiness:{}",
                    stable_id(&molecule.molecule_observation_ref)
                ),
                molecule_ref: molecule.molecule_observation_ref.clone(),
                status: status.to_string(),
                readiness_score,
                core_embedding_status: if molecule.atom_observation_refs.is_empty() {
                    "missingEvidence".to_string()
                } else {
                    "observed".to_string()
                },
                feature_view_section_status: if molecule
                    .interpretation_notes_for_llm
                    .iter()
                    .any(|note| note.to_ascii_lowercase().contains("semantic"))
                {
                    "observed".to_string()
                } else {
                    "needsSemanticView".to_string()
                },
                lifting_evidence_status: if bridge_edge_refs.is_empty() {
                    "notBlockedByObservedBridge".to_string()
                } else {
                    "blockedByBridgeEdge".to_string()
                },
                interaction_obstruction_refs: obstruction_refs,
                bridge_edge_refs,
                recommended_boundary_operation,
                reading: format!(
                    "{} has split readiness score {} under current ArchSig evidence",
                    molecule.molecule_observation_ref, readiness_score
                ),
                evidence_boundary:
                    "split readiness is a current-state architecture reading, not a feature-extension proof"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_feature_extension_formula_readings(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    split_readiness_readings: &[ArchSigSplitReadinessReadingV0],
) -> Vec<ArchSigFeatureExtensionFormulaReadingV0> {
    let obstruction_ids = obstruction_circuits
        .iter()
        .map(|obstruction| obstruction.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let feature_local = obstruction_circuits
        .iter()
        .filter(|obstruction| {
            let text = format!("{} {}", obstruction.law_ref, obstruction.evidence_summary)
                .to_ascii_lowercase();
            text.contains("feature") || text.contains("extension") || text.contains("semantic")
        })
        .map(|obstruction| obstruction.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let interaction = obstruction_circuits
        .iter()
        .filter(|obstruction| {
            let text = format!("{} {}", obstruction.law_ref, obstruction.evidence_summary)
                .to_ascii_lowercase();
            text.contains("interaction")
                || text.contains("bridge")
                || text.contains("runtime")
                || text.contains("effect")
        })
        .map(|obstruction| obstruction.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let lifting_failure_refs = split_readiness_readings
        .iter()
        .filter(|reading| reading.lifting_evidence_status != "observed")
        .map(|reading| reading.reading_id.clone())
        .collect::<Vec<_>>();
    let complexity_transfer_refs = repair_candidates
        .iter()
        .flat_map(|candidate| candidate.transfer_risks.clone())
        .collect::<Vec<_>>();
    let residual_coverage_gap_refs = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let filling_failure_refs = obstruction_circuits
        .iter()
        .filter(|obstruction| !obstruction.missing_evidence.is_empty())
        .map(|obstruction| obstruction.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let classification_summary = vec![
        extension_axis_summary("inheritedCoreObstruction", &obstruction_ids),
        extension_axis_summary("featureLocalObstruction", &feature_local),
        extension_axis_summary("interactionObstruction", &interaction),
        extension_axis_summary("liftingFailure", &lifting_failure_refs),
        extension_axis_summary("fillingFailure", &filling_failure_refs),
        extension_axis_summary("complexityTransfer", &complexity_transfer_refs),
        extension_axis_summary("residualCoverageGap", &residual_coverage_gap_refs),
    ];
    vec![ArchSigFeatureExtensionFormulaReadingV0 {
        reading_id: format!("feature-extension-formula:{}", stable_id(&archmap.map_id)),
        scope_ref: archmap.map_id.clone(),
        status: if obstruction_ids.is_empty() && residual_coverage_gap_refs.is_empty() {
            "needsReview".to_string()
        } else {
            "measured".to_string()
        },
        inherited_core_obstruction_refs: obstruction_ids,
        feature_local_obstruction_refs: feature_local,
        interaction_obstruction_refs: interaction,
        lifting_failure_refs,
        filling_failure_refs,
        complexity_transfer_refs,
        residual_coverage_gap_refs,
        classification_summary,
        evidence_boundary:
            "extension formula is computed over current ArchMap state, not an actual PR diff"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn extension_axis_summary(axis: &str, refs: &[String]) -> ArchSigFeatureExtensionAxisSummaryV0 {
    ArchSigFeatureExtensionAxisSummaryV0 {
        axis: axis.to_string(),
        status: if refs.is_empty() {
            "unmeasuredOrAbsent".to_string()
        } else {
            "observed".to_string()
        },
        refs: refs.to_vec(),
        reading: format!("{axis} is classified as a current-state extension coordinate"),
    }
}

fn build_operation_calculus_law_readings(
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
) -> Vec<ArchSigOperationCalculusLawReadingV0> {
    if repair_candidates.is_empty() {
        return vec![ArchSigOperationCalculusLawReadingV0 {
            reading_id: "operation-calculus-law:none-observed".to_string(),
            operation_ref: "repair-operation:none-observed".to_string(),
            operation_kind: "noneObserved".to_string(),
            composition_status: "unmeasured".to_string(),
            associativity_under_observation_status: "unmeasured".to_string(),
            refinement_abstraction_compatibility: "unmeasured".to_string(),
            replacement_equivalence: "unmeasured".to_string(),
            protection_idempotence: "notApplicable".to_string(),
            runtime_localization: "unmeasured".to_string(),
            migration_compatibility: "notApplicable".to_string(),
            reverse_involution: "unmeasured".to_string(),
            repair_monotonicity: "unmeasured".to_string(),
            synthesis_no_solution_boundary: "notASynthesisCertificate".to_string(),
            precondition_refs: Vec::new(),
            evidence_refs: Vec::new(),
            evidence_boundary:
                "no repair candidate was constructed; operation laws are not discharged by absence"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }];
    }
    let delta_by_kind = operation_deltas
        .iter()
        .map(|delta| (delta.operation_kind.as_str(), delta))
        .collect::<BTreeMap<_, _>>();
    repair_candidates
        .iter()
        .map(|candidate| {
            let delta = delta_by_kind
                .get(candidate.operation_kind.as_str())
                .copied();
            let transferred = delta
                .map(|delta| !delta.transferred_obstructions.is_empty())
                .unwrap_or(false);
            ArchSigOperationCalculusLawReadingV0 {
                reading_id: format!(
                    "operation-calculus-law:{}",
                    stable_id(&candidate.repair_operation_candidate_id)
                ),
                operation_ref: candidate.repair_operation_candidate_id.clone(),
                operation_kind: candidate.operation_kind.clone(),
                composition_status: "assumptionRelative".to_string(),
                associativity_under_observation_status: "selectedObservationOnly".to_string(),
                refinement_abstraction_compatibility: if candidate.missing_evidence.is_empty() {
                    "needsReview".to_string()
                } else {
                    "blockedByMissingEvidence".to_string()
                },
                replacement_equivalence: "unmeasured".to_string(),
                protection_idempotence: if candidate.operation_kind.contains("protection") {
                    "needsWitness".to_string()
                } else {
                    "notApplicable".to_string()
                },
                runtime_localization: if candidate
                    .preconditions
                    .iter()
                    .any(|precondition| precondition.to_ascii_lowercase().contains("runtime"))
                {
                    "blockedByCoverageGap".to_string()
                } else {
                    "unmeasured".to_string()
                },
                migration_compatibility: if candidate.operation_kind.contains("migrate") {
                    "needsWitness".to_string()
                } else {
                    "notApplicable".to_string()
                },
                reverse_involution: "unmeasured".to_string(),
                repair_monotonicity: if transferred {
                    "selectedAxisOnly".to_string()
                } else {
                    "candidateNonIncreasing".to_string()
                },
                synthesis_no_solution_boundary: "notASynthesisCertificate".to_string(),
                precondition_refs: candidate.preconditions.clone(),
                evidence_refs: candidate
                    .target_obstruction_refs
                    .iter()
                    .chain(candidate.preserved_invariants.iter())
                    .cloned()
                    .collect(),
                evidence_boundary: candidate.evidence_boundary.clone(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn build_path_signature_trajectory_readings(
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigPathSignatureTrajectoryReadingV0> {
    let mut readings = operation_deltas
        .iter()
        .map(|delta| {
            let non_monotone_axis_refs = delta
                .transferred_obstructions
                .iter()
                .chain(
                    delta
                        .signature_delta
                        .iter()
                        .filter(|value| value.contains("negative")),
                )
                .cloned()
                .collect::<Vec<_>>();
            ArchSigPathSignatureTrajectoryReadingV0 {
                reading_id: format!(
                    "path-signature-trajectory:{}",
                    stable_id(&delta.operation_delta_id)
                ),
                path_ref: delta.operation_delta_id.clone(),
                status: "candidateTrajectory".to_string(),
                endpoint_signature_delta: delta.signature_delta.clone(),
                max_axis_excursion: signature_axes
                    .iter()
                    .map(|axis| ArchSigAxisExcursionV0 {
                        axis_ref: axis.signature_axis_id.clone(),
                        max_value: axis.value.max(0),
                        evidence_refs: axis.source_refs.clone(),
                        reading:
                            "max excursion is a current-state proxy, not future trajectory proof"
                                .to_string(),
                    })
                    .collect(),
                non_monotone_axis_refs,
                path_cost_proxy: format!(
                    "support={} transferred={}",
                    delta.support_refs.len(),
                    delta.transferred_obstructions.len()
                ),
                preserved_invariant_trajectory: delta.invariant_preservation_claims.clone(),
                introduced_obstruction_trajectory: delta.transferred_obstructions.clone(),
                trajectory_coverage_boundary:
                    "trajectory is built from candidate operation deltas, not repository evolution"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect::<Vec<_>>();
    if readings.is_empty() {
        readings.push(ArchSigPathSignatureTrajectoryReadingV0 {
            reading_id: "path-signature-trajectory:none-observed".to_string(),
            path_ref: "operation-delta:none-observed".to_string(),
            status: "unmeasured".to_string(),
            endpoint_signature_delta: Vec::new(),
            max_axis_excursion: Vec::new(),
            non_monotone_axis_refs: Vec::new(),
            path_cost_proxy: "unmeasured".to_string(),
            preserved_invariant_trajectory: Vec::new(),
            introduced_obstruction_trajectory: Vec::new(),
            trajectory_coverage_boundary:
                "no operation deltas are available for trajectory measurement".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    }
    readings
}

fn build_homotopy_order_sensitivity_readings(
    path_homotopy_diagram_readings: &[ArchSigPathHomotopyDiagramReadingV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
) -> Vec<ArchSigHomotopyOrderSensitivityReadingV0> {
    let blockers = operation_deltas
        .iter()
        .flat_map(|delta| delta.transferred_obstructions.clone())
        .chain(
            repair_candidates
                .iter()
                .flat_map(|candidate| candidate.missing_evidence.clone()),
        )
        .collect::<Vec<_>>();
    vec![ArchSigHomotopyOrderSensitivityReadingV0 {
        reading_id: "homotopy-order-sensitivity:selected-operations".to_string(),
        status: if blockers.is_empty() {
            "needsReview".to_string()
        } else {
            "sensitive".to_string()
        },
        independent_square_candidate_refs: path_homotopy_diagram_readings
            .iter()
            .flat_map(|reading| reading.homotopy_refs.clone())
            .take(12)
            .collect(),
        same_contract_replacement_refs: operation_deltas
            .iter()
            .filter(|delta| {
                delta.operation_kind.contains("replace")
                    || delta.operation_kind.contains("substitut")
            })
            .map(|delta| delta.operation_delta_id.clone())
            .collect(),
        repair_filler_refs: repair_candidates
            .iter()
            .map(|candidate| candidate.repair_operation_candidate_id.clone())
            .collect(),
        operation_order_sensitivity: if blockers.is_empty() {
            "notComparableWithoutGenerators".to_string()
        } else {
            "blockedByTransferredObstructionOrMissingEvidence".to_string()
        },
        homotopy_blocker_refs: blockers,
        selected_observation_preservation_status:
            "selected observation only; same endpoint does not imply same trajectory".to_string(),
        evidence_boundary:
            "homotopy reading is generator-relative and does not prove operation commutativity"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn build_diagram_fillability_readings(
    local_curvature_readings: &[ArchSigLocalCurvatureDiagramReadingV0],
    feature_extension_formula_readings: &[ArchSigFeatureExtensionFormulaReadingV0],
) -> Vec<ArchSigDiagramFillabilityReadingV0> {
    let feature_refs = feature_extension_formula_readings
        .iter()
        .map(|reading| reading.reading_id.clone())
        .collect::<Vec<_>>();
    local_curvature_readings
        .iter()
        .map(|reading| ArchSigDiagramFillabilityReadingV0 {
            reading_id: format!("diagram-fillability:{}", stable_id(&reading.diagram_id)),
            diagram_ref: reading.diagram_id.clone(),
            diagram_family: "localCurvatureDiagram".to_string(),
            status: if reading.curvature_status == "nonConclusion" {
                "blocked".to_string()
            } else if reading.curvature_value == 0 {
                "candidateFillable".to_string()
            } else {
                "nonFillabilityWitnessed".to_string()
            },
            missing_filler_kind: if reading.curvature_value == 0 {
                "noneObserved".to_string()
            } else {
                "lawRelativeFiller".to_string()
            },
            filler_candidate_refs: reading
                .lhs_path_refs
                .iter()
                .chain(reading.rhs_path_refs.iter())
                .cloned()
                .collect(),
            non_fillability_witness_refs: if reading.curvature_value == 0 {
                Vec::new()
            } else {
                vec![reading.obstruction_ref.clone()]
            },
            filling_blocker_refs: if reading.filling_boundary.trim().is_empty() {
                Vec::new()
            } else {
                vec![reading.filling_boundary.clone()]
            },
            obstruction_refs: vec![reading.obstruction_ref.clone()],
            feature_extension_refs: feature_refs.clone(),
            evidence_boundary:
                "diagram fillability is selected-diagram-relative and not a theorem discharge"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        })
        .collect()
}

fn build_structural_reading_review_surface(
    representation_strength_readings: &[ArchSigRepresentationStrengthReadingV0],
    local_curvature_diagram_readings: &[ArchSigLocalCurvatureDiagramReadingV0],
    three_layer_flatness_readings: &[ArchSigThreeLayerFlatnessReadingV0],
    observation_projection_readings: &[ArchSigObservationProjectionReadingV0],
    state_transition_algebra_readings: &[ArchSigStateTransitionAlgebraReadingV0],
    operation_invariant_galois_readings: &[ArchSigOperationInvariantGaloisReadingV0],
    split_readiness_readings: &[ArchSigSplitReadinessReadingV0],
    atom_support_axis_readings: &[ArchSigAtomSupportAxisReadingV0],
    atom_compatibility_readings: &[ArchSigAtomCompatibilityReadingV0],
    law_universe_coverage_readings: &[ArchSigLawUniverseCoverageReadingV0],
    feature_extension_formula_readings: &[ArchSigFeatureExtensionFormulaReadingV0],
    operation_calculus_law_readings: &[ArchSigOperationCalculusLawReadingV0],
    path_signature_trajectory_readings: &[ArchSigPathSignatureTrajectoryReadingV0],
    homotopy_order_sensitivity_readings: &[ArchSigHomotopyOrderSensitivityReadingV0],
    diagram_fillability_readings: &[ArchSigDiagramFillabilityReadingV0],
) -> ArchSigStructuralReadingReviewSurfaceV0 {
    let blocked_representation_count = representation_strength_readings
        .iter()
        .filter(|reading| {
            reading.zero_reflecting == "blockedByCoverageGap"
                || reading.obstruction_reflecting == "blockedByCoverageGap"
        })
        .count();
    let curvature_count = local_curvature_diagram_readings
        .iter()
        .filter(|reading| reading.curvature_value > 0)
        .count();
    let blocked_operation_count = operation_invariant_galois_readings
        .iter()
        .map(|reading| reading.blocked_operation_refs.len())
        .sum::<usize>();
    let split_blocker_count = split_readiness_readings
        .iter()
        .filter(|reading| reading.status != "candidateSplitReady")
        .count();
    let atom_conflict_count = atom_compatibility_readings
        .iter()
        .map(|reading| reading.same_slot_conflict_count)
        .sum::<usize>();
    let unmeasured_law_count = law_universe_coverage_readings
        .iter()
        .map(|reading| reading.unmeasured_required_law_count)
        .sum::<usize>();
    let blocked_diagram_count = diagram_fillability_readings
        .iter()
        .filter(|reading| reading.status != "candidateFillable")
        .count();
    let mut connected_reading_refs = Vec::new();
    connected_reading_refs.extend(
        representation_strength_readings
            .iter()
            .take(6)
            .map(|reading| format!("representationStrength:{}", reading.representation_family)),
    );
    connected_reading_refs.extend(
        local_curvature_diagram_readings
            .iter()
            .map(|reading| reading.diagram_id.clone()),
    );
    connected_reading_refs.extend(
        three_layer_flatness_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        observation_projection_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        state_transition_algebra_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        operation_invariant_galois_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        split_readiness_readings
            .iter()
            .take(8)
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        atom_support_axis_readings
            .iter()
            .take(8)
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        atom_compatibility_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        law_universe_coverage_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        feature_extension_formula_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        operation_calculus_law_readings
            .iter()
            .take(8)
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        path_signature_trajectory_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        homotopy_order_sensitivity_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );
    connected_reading_refs.extend(
        diagram_fillability_readings
            .iter()
            .map(|reading| reading.reading_id.clone()),
    );

    let status = if curvature_count > 0
        || blocked_operation_count > 0
        || split_blocker_count > 0
        || atom_conflict_count > 0
        || unmeasured_law_count > 0
        || blocked_diagram_count > 0
    {
        "needsReview"
    } else if connected_reading_refs.is_empty() {
        "nonConclusion"
    } else {
        "actionable"
    };

    ArchSigStructuralReadingReviewSurfaceV0 {
        surface_id: "aat-structural-reading-review-surface".to_string(),
        status: status.to_string(),
        current_state_reading: format!(
            "ArchSig reads current architecture state across Atom support and compatibility, LawUniverse coverage, feature extension coordinates, operation calculus laws, path signature trajectory, homotopy order sensitivity, diagram fillability, representation strength, local curvature, three-layer flatness, observation projection, state transition algebra, operation-invariant constraints, and split readiness; blockedRepresentations={}, curvatures={}, blockedOperations={}, splitBlockers={}, atomConflicts={}, unmeasuredRequiredLaws={}, blockedDiagrams={}",
            blocked_representation_count,
            curvature_count,
            blocked_operation_count,
            split_blocker_count,
            atom_conflict_count,
            unmeasured_law_count,
            blocked_diagram_count
        ),
        connected_reading_refs,
        review_focus: vec![
            "read Atom support and compatibility before collapsing mixed state, effect, contract, authority, semantic, or runtime axes".to_string(),
            "read LawUniverse coverage and witness exactness before treating absence as measured zero".to_string(),
            "read feature extension, operation law, trajectory, homotopy, and diagram-fillability axes as current-state coordinates, not PR evolution claims".to_string(),
            "read representation-strength blockers before treating zero or obstruction absence as exact".to_string(),
            "read local-curvature diagrams as law-relative state pressure, not as generic lint failures".to_string(),
            "compare static, runtime, and semantic flatness before relying on source layout".to_string(),
            "treat observation projection gaps as lost coordinates that bound the reading".to_string(),
            "check state/effect algebra relations before approving local repairs".to_string(),
            "read split readiness and bridge edges before separating molecules".to_string(),
        ],
        evidence_boundary:
            "structural readings are computed from the current ArchMap and selected LawPolicy; they are review telemetry, not proof of global architecture truth"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_current_state_evolution_boundary(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
) -> ArchSigCurrentStateEvolutionBoundaryV0 {
    ArchSigCurrentStateEvolutionBoundaryV0 {
        boundary_id: "archsig-fieldsig-current-state-evolution-boundary".to_string(),
        archsig_current_state_scope: format!(
            "ArchSig computes current AAT structural state from ArchMap {} and LawPolicy {}; it reads atoms, molecules, laws, obstructions, bridge pressure, structural readings, and bounded review focus",
            archmap.map_id, law_policy.law_policy_id
        ),
        fieldsig_evolution_scope:
            "FieldSig consumes archsig-analysis-packet-v0 as bounded current AAT structural state and studies PR, diff, change-vector, forecast, governance, calibration, and operational evolution over that state"
                .to_string(),
        handoff_artifact_ref: "archsig-analysis-packet-v0".to_string(),
        forbidden_readings: vec![
            "ArchSig packet is not PR diff analysis".to_string(),
            "ArchSig packet is not forecast correctness or causal truth".to_string(),
            "raw ArchMap observations are not FieldSig forecast truth".to_string(),
            "FieldSig evolution readings must not be moved back into ArchMap".to_string(),
        ],
        evidence_boundary:
            "handoff preserves bounded current-state evidence; evolution claims remain downstream FieldSig readings"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn dominant_mode_component(
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    representation_family: &str,
    component_kind: &str,
) -> Option<String> {
    spectral_mode_readings
        .iter()
        .find(|reading| reading.representation_family == representation_family)
        .and_then(|reading| {
            reading
                .mode_components
                .iter()
                .find(|component| component.component_kind == component_kind)
        })
        .map(|component| component.component_ref.clone())
}

fn bridge_path(
    source: &str,
    target: &str,
    high_overlap_pairs: &[ArchSigHighOverlapMoleculePairV0],
) -> Option<Vec<String>> {
    if source == target {
        return Some(vec![source.to_string()]);
    }
    let mut adjacency = BTreeMap::<String, Vec<(String, i64)>>::new();
    for pair in high_overlap_pairs {
        adjacency
            .entry(pair.left_molecule_ref.clone())
            .or_default()
            .push((pair.right_molecule_ref.clone(), pair.overlap_score));
        adjacency
            .entry(pair.right_molecule_ref.clone())
            .or_default()
            .push((pair.left_molecule_ref.clone(), pair.overlap_score));
    }
    for neighbors in adjacency.values_mut() {
        neighbors.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
    }

    let mut queue = vec![vec![source.to_string()]];
    let mut visited = BTreeSet::from([source.to_string()]);
    while let Some(path) = queue.first().cloned() {
        queue.remove(0);
        let Some(current) = path.last() else {
            continue;
        };
        for (next, _) in adjacency.get(current).cloned().unwrap_or_default() {
            if !visited.insert(next.clone()) {
                continue;
            }
            let mut next_path = path.clone();
            next_path.push(next.clone());
            if next == target {
                return Some(next_path);
            }
            queue.push(next_path);
        }
    }
    None
}

fn ordered_pair_key(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

fn shared_workflow_axes(
    source_hub: &str,
    target_hub: &str,
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
) -> Vec<String> {
    let axes_by_molecule = workflow_risk_readings
        .iter()
        .map(|reading| {
            (
                reading.molecule_observation_ref.as_str(),
                reading
                    .top_axes
                    .iter()
                    .map(|axis| axis.axis.clone())
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let source_axes = axes_by_molecule.get(source_hub);
    let target_axes = axes_by_molecule.get(target_hub);
    match (source_axes, target_axes) {
        (Some(source_axes), Some(target_axes)) => source_axes
            .intersection(target_axes)
            .cloned()
            .collect::<Vec<_>>(),
        (Some(source_axes), None) => source_axes.iter().cloned().collect(),
        (None, Some(target_axes)) => target_axes.iter().cloned().collect(),
        (None, None) => Vec::new(),
    }
}

fn build_evolution_risk_ranking(
    repair_axis_delta_readings: &[ArchSigRepairAxisDeltaReadingV0],
    high_overlap_pairs: &[ArchSigHighOverlapMoleculePairV0],
) -> ArchSigEvolutionRiskRankingV0 {
    let mut repair_ranking = repair_axis_delta_readings
        .iter()
        .map(|delta| {
            let transfer_weight =
                delta.negative_delta_axes.len() as i64 + delta.transfer_risk_refs.len() as i64;
            (
                transfer_weight,
                delta.operation_delta_ref.clone(),
                delta.positive_delta_axes.len(),
                delta.negative_delta_axes.len(),
            )
        })
        .collect::<Vec<_>>();
    repair_ranking.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(&right.1)));
    let repair_transfer_risk_ranking = repair_ranking
        .into_iter()
        .enumerate()
        .map(
            |(index, (transfer_weight, operation_delta_ref, positive_count, transferred_count))| {
                ArchSigRepairTransferRiskRankV0 {
                    rank: index + 1,
                    operation_delta_ref: operation_delta_ref.clone(),
                    positive_axis_count: positive_count,
                    transferred_axis_count: transferred_count,
                    transfer_weight,
                    reading: format!(
                        "{operation_delta_ref} has {positive_count} target-positive axis/axes and {transferred_count} transferred axis/axes"
                    ),
                }
            },
        )
        .collect::<Vec<_>>();

    let mut boundary_pairs = high_overlap_pairs.to_vec();
    boundary_pairs.sort_by(|left, right| {
        right
            .overlap_score
            .cmp(&left.overlap_score)
            .then(left.left_molecule_ref.cmp(&right.left_molecule_ref))
            .then(left.right_molecule_ref.cmp(&right.right_molecule_ref))
    });
    let boundary_preparation_ranking = boundary_pairs
        .into_iter()
        .take(8)
        .enumerate()
        .map(|(index, pair)| ArchSigBoundaryPreparationRankV0 {
            rank: index + 1,
            pair_ref: pair.pair_id.clone(),
            left_molecule_ref: pair.left_molecule_ref.clone(),
            right_molecule_ref: pair.right_molecule_ref.clone(),
            overlap_score: pair.overlap_score,
            shared_atom_families: pair.shared_atom_families.clone(),
            reading: format!(
                "prepare boundary between {} and {} before repairs that touch shared {:?} atoms",
                pair.left_molecule_ref, pair.right_molecule_ref, pair.shared_atom_families
            ),
        })
        .collect();

    ArchSigEvolutionRiskRankingV0 {
        repair_transfer_risk_ranking,
        boundary_preparation_ranking,
        reading:
            "evolution risk ranks repairs by transfer-axis pressure and molecule pairs by boundary-preparation need"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_design_principle_readings(
    archmap: &ArchMapDocumentV0,
    invariant_readings: &[ArchSigInvariantFamilyReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
) -> Vec<ArchSigDesignPrincipleReadingV0> {
    let specs = [
        (
            "InformationHiding",
            "representation, state, effect, and provider details stay inside declared boundaries",
        ),
        (
            "Encapsulation",
            "state mutation, effect execution, and authority checks are owned by the selected boundary",
        ),
        (
            "SeparationOfConcerns",
            "semantic concern, state transition, effect, policy, and presentation remain unmixed",
        ),
        (
            "Substitutability",
            "replacement preserves contract, effect, state transition, and semantic reading",
        ),
        (
            "OpenClosedExtension",
            "feature extension preserves core invariants without new interaction obstruction",
        ),
        (
            "DependencyInversion",
            "abstract boundary semantics remain aligned with implementation obligations",
        ),
        (
            "RepresentationIndependence",
            "internal representation changes preserve selected observations and contracts",
        ),
        (
            "IdempotencyAndReplaySafety",
            "retry, replay, jobs, and external effects preserve selected state transition law",
        ),
        (
            "AuthorityAndTrustBoundary",
            "authority labels and trust handoffs survive operation paths",
        ),
    ];
    let gap_refs = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let obstruction_refs = obstruction_circuits
        .iter()
        .map(|circuit| circuit.obstruction_circuit_id.clone())
        .collect::<Vec<_>>();
    let invariant_refs = invariant_readings
        .iter()
        .map(|reading| reading.invariant_id.clone())
        .collect::<Vec<_>>();
    let operation_refs = repair_candidates
        .iter()
        .map(|candidate| candidate.repair_operation_candidate_id.clone())
        .collect::<Vec<_>>();
    specs
        .into_iter()
        .map(|(principle, reading)| {
            let status = principle_status(principle, archmap, obstruction_circuits);
            ArchSigDesignPrincipleReadingV0 {
                principle_id: format!("principle:{}", stable_id(principle)),
                principle: principle.to_string(),
                status: status.to_string(),
                aat_reading: format!("{principle} is read as invariant preservation / obstruction / operation preservation: {reading}"),
                invariant_refs: invariant_refs.clone(),
                obstruction_refs: obstruction_refs.clone(),
                operation_refs: operation_refs.clone(),
                evidence_refs: all_atom_refs(archmap),
                confidence: if status == "unmeasured" { "low" } else { "medium" }.to_string(),
                coverage_boundary:
                    "principle reading uses semantic ArchMap evidence and is not a slogan or static lint rule"
                        .to_string(),
                exactness_blockers: if gap_refs.is_empty() {
                    vec!["exactness remains selected-profile-relative".to_string()]
                } else {
                    gap_refs.clone()
                },
                recommended_next_action:
                    "turn stressed readings into source review questions or repair preconditions"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn principle_status(
    principle: &str,
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> &'static str {
    let lower = principle.to_ascii_lowercase();
    if lower.contains("idempotency")
        || lower.contains("authority")
        || lower.contains("representation")
    {
        if archmap.observation_gaps.is_empty() {
            "needsReview"
        } else {
            "unmeasured"
        }
    } else if obstruction_circuits.is_empty() {
        "preserved"
    } else {
        "stressed"
    }
}

fn build_operation_deltas(
    archmap: &ArchMapDocumentV0,
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigOperationDeltaReadingV0> {
    if repair_candidates.is_empty() {
        return vec![ArchSigOperationDeltaReadingV0 {
            operation_delta_id: "operation-delta:observe-before-repair".to_string(),
            operation_kind: "evidence-enrichment".to_string(),
            support_refs: all_atom_refs(archmap),
            preconditions: repair_preconditions(archmap),
            atom_transformations: vec![
                "add or refine ArchMap atom observations before claiming repair".to_string(),
            ],
            transition_relation:
                "ArchMap enrichment changes analysis coverage without changing source architecture"
                    .to_string(),
            invariant_preservation_claims: vec![
                "preserve all existing source-grounded atom observation refs".to_string(),
            ],
            obstruction_transport: vec![
                "no constructed obstruction is transported because no repair candidate exists"
                    .to_string(),
            ],
            signature_delta: signature_axes
                .iter()
                .map(|axis| format!("{} remains {}", axis.signature_axis_id, axis.value))
                .collect(),
            decreased_axes: vec![],
            transferred_obstructions: archmap
                .observation_gaps
                .iter()
                .map(|gap| gap.gap_id.clone())
                .collect(),
            excluded_readings: vec![
                "evidence enrichment is not a source-code repair".to_string(),
                "no automatic patch safety".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }];
    }

    repair_candidates
        .iter()
        .map(|candidate| ArchSigOperationDeltaReadingV0 {
            operation_delta_id: format!(
                "operation-delta:{}",
                stable_id(&candidate.repair_operation_candidate_id)
            ),
            operation_kind: candidate.operation_kind.clone(),
            support_refs: candidate.target_obstruction_refs.clone(),
            preconditions: candidate.preconditions.clone(),
            atom_transformations: vec![
                "split or enrich atoms that currently support the target obstruction".to_string(),
                "add observed compensation / authority / effect atoms only after source review"
                    .to_string(),
            ],
            transition_relation:
                "operation maps the current bounded Atom configuration to a candidate repaired configuration"
                    .to_string(),
            invariant_preservation_claims: candidate.preserved_invariants.clone(),
            obstruction_transport: candidate
                .target_obstruction_refs
                .iter()
                .map(|target| {
                    format!("{target} may decrease or move to a runtime/state/effect axis")
                })
                .collect(),
            signature_delta: candidate.expected_signature_axis_effects.clone(),
            decreased_axes: signature_axes
                .iter()
                .filter(|axis| axis.value != 0)
                .map(|axis| axis.signature_axis_id.clone())
                .collect(),
            transferred_obstructions: candidate.transfer_risks.clone(),
            excluded_readings: candidate.excluded_readings.clone(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        })
        .collect()
}

fn build_path_homotopy_diagram_readings(
    archmap: &ArchMapDocumentV0,
    molecule_readings: &[ArchSigMoleculeReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
) -> Vec<ArchSigPathHomotopyDiagramReadingV0> {
    vec![
        ArchSigPathHomotopyDiagramReadingV0 {
            reading_id: "path:semantic-operation-flow".to_string(),
            surface: "Path".to_string(),
            status: if archmap.semantic_observations.is_empty() {
                "unmeasured"
            } else {
                "observedOrRepresented"
            }
            .to_string(),
            path_refs: archmap
                .semantic_observations
                .iter()
                .map(|semantic| semantic.semantic_observation_id.clone())
                .collect(),
            homotopy_refs: molecule_readings
                .iter()
                .map(|reading| reading.molecule_reading_id.clone())
                .collect(),
            diagram_refs: obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect(),
            filling_boundary:
                "path reading is a source-grounded semantic workflow proxy, not a free-category proof"
                    .to_string(),
            reading: "semantic observations and molecules provide path candidates for review".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        ArchSigPathHomotopyDiagramReadingV0 {
            reading_id: "diagram:obstruction-filling".to_string(),
            surface: "Diagram".to_string(),
            status: if obstruction_circuits.is_empty() {
                "needsReview"
            } else {
                "actionable"
            }
            .to_string(),
            path_refs: all_atom_refs(archmap),
            homotopy_refs: molecule_readings
                .iter()
                .map(|reading| reading.molecule_reading_id.clone())
                .collect(),
            diagram_refs: obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.clone())
                .collect(),
            filling_boundary:
                "diagram filling is reported as obstruction / repair planning surface, not theorem discharge"
                    .to_string(),
            reading: "constructed obstruction circuits identify diagrams whose filling requires review or repair".to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
    ]
}

fn build_bounded_judgements(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    design_principles: &[ArchSigDesignPrincipleReadingV0],
) -> Vec<ArchSigBoundedJudgementV0> {
    let mut judgements = vec![ArchSigBoundedJudgementV0 {
        judgement_id: "judgement:architecture-state".to_string(),
        status: "actionable".to_string(),
        aat_concept: "ArchitectureObject".to_string(),
        reading: "observed atoms, molecules, semantic records, gaps, and signature axes define a bounded architecture state".to_string(),
        evidence_refs: all_atom_refs(archmap),
        confidence: "medium".to_string(),
        uncertainty: archmap
            .observation_gaps
            .iter()
            .map(|gap| gap.reason.clone())
            .collect(),
        coverage_boundary: "bounded to supplied ArchMap and selected interpretation profile".to_string(),
        exactness_boundary: "not global architecture truth and not Lean theorem proof".to_string(),
        recommended_next_action: "review nonzero axes and stressed principle readings first".to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }];

    for circuit in obstruction_circuits {
        judgements.push(ArchSigBoundedJudgementV0 {
            judgement_id: format!("judgement:{}", stable_id(&circuit.obstruction_circuit_id)),
            status: "actionable".to_string(),
            aat_concept: "ObstructionCircuit".to_string(),
            reading: circuit.evidence_summary.clone(),
            evidence_refs: circuit
                .atom_observation_refs
                .iter()
                .chain(circuit.molecule_reading_refs.iter())
                .chain(circuit.concern_hint_refs.iter())
                .cloned()
                .collect(),
            confidence: "medium".to_string(),
            uncertainty: circuit.missing_evidence.clone(),
            coverage_boundary: circuit.evidence_boundary.clone(),
            exactness_boundary: "witness is selected-profile-relative".to_string(),
            recommended_next_action: "inspect source refs and repair operation preconditions"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    }

    for axis in signature_axes {
        judgements.push(ArchSigBoundedJudgementV0 {
            judgement_id: format!("judgement:{}", stable_id(&axis.signature_axis_id)),
            status: if axis.value == 0 {
                "needsReview"
            } else {
                "actionable"
            }
            .to_string(),
            aat_concept: "ArchitectureSignature".to_string(),
            reading: axis.evidence_summary.clone(),
            evidence_refs: axis.source_refs.clone(),
            confidence: if axis.value == 0 { "low" } else { "medium" }.to_string(),
            uncertainty: axis.missing_evidence.clone(),
            coverage_boundary: axis.coverage_status.clone(),
            exactness_boundary: axis.exactness_assumptions.join("; "),
            recommended_next_action:
                "use zero axes only with exactness assumptions; review nonzero axes as design pressure"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    }

    for principle in design_principles {
        judgements.push(ArchSigBoundedJudgementV0 {
            judgement_id: format!("judgement:{}", stable_id(&principle.principle_id)),
            status: match principle.status.as_str() {
                "preserved" => "needsReview",
                "stressed" => "actionable",
                "unmeasured" => "blocked",
                _ => "needsReview",
            }
            .to_string(),
            aat_concept: "Invariant".to_string(),
            reading: principle.aat_reading.clone(),
            evidence_refs: principle.evidence_refs.clone(),
            confidence: principle.confidence.clone(),
            uncertainty: principle.exactness_blockers.clone(),
            coverage_boundary: principle.coverage_boundary.clone(),
            exactness_boundary: "design principle reading is not static lint and not theorem proof"
                .to_string(),
            recommended_next_action: principle.recommended_next_action.clone(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    }

    judgements
}

fn build_llm_interpretation_packet(
    archmap: &ArchMapDocumentV0,
    architecture_state: &ArchSigArchitectureStateV0,
    design_pressure: &[ArchSigDesignPressureReadingV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    analytic_representations: &[ArchSigAnalyticRepresentationV0],
    workflow_risk_readings: &[ArchSigWorkflowRiskReadingV0],
    spectral_analysis_readings: &[ArchSigSpectralAnalysisReadingV0],
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    spectral_drilldown_readings: &[ArchSigSpectralDrilldownReadingV0],
    transfer_bridge_readings: &[ArchSigTransferBridgeReadingV0],
    atom_support_axis_readings: &[ArchSigAtomSupportAxisReadingV0],
    atom_compatibility_readings: &[ArchSigAtomCompatibilityReadingV0],
    law_universe_coverage_readings: &[ArchSigLawUniverseCoverageReadingV0],
    feature_extension_formula_readings: &[ArchSigFeatureExtensionFormulaReadingV0],
    operation_calculus_law_readings: &[ArchSigOperationCalculusLawReadingV0],
    path_signature_trajectory_readings: &[ArchSigPathSignatureTrajectoryReadingV0],
    homotopy_order_sensitivity_readings: &[ArchSigHomotopyOrderSensitivityReadingV0],
    diagram_fillability_readings: &[ArchSigDiagramFillabilityReadingV0],
    representation_strength_readings: &[ArchSigRepresentationStrengthReadingV0],
    local_curvature_diagram_readings: &[ArchSigLocalCurvatureDiagramReadingV0],
    three_layer_flatness_readings: &[ArchSigThreeLayerFlatnessReadingV0],
    observation_projection_readings: &[ArchSigObservationProjectionReadingV0],
    state_transition_algebra_readings: &[ArchSigStateTransitionAlgebraReadingV0],
    operation_invariant_galois_readings: &[ArchSigOperationInvariantGaloisReadingV0],
    split_readiness_readings: &[ArchSigSplitReadinessReadingV0],
    structural_reading_review_surface: &ArchSigStructuralReadingReviewSurfaceV0,
    current_state_evolution_boundary: &ArchSigCurrentStateEvolutionBoundaryV0,
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    bounded_judgements: &[ArchSigBoundedJudgementV0],
) -> ArchSigLlmInterpretationPacketV0 {
    ArchSigLlmInterpretationPacketV0 {
        packet_id: format!("llm-interpretation:{}", stable_id(&archmap.map_id)),
        short_diagnosis: format!(
            "{} actionable judgement(s), {} design pressure reading(s), and {} observation gap(s) require review",
            bounded_judgements
                .iter()
                .filter(|judgement| judgement.status == "actionable")
                .count(),
            design_pressure.len(),
            archmap.observation_gaps.len()
        ),
        aat_concept_map: vec![
            "Atom -> Configuration -> ArchitectureObject".to_string(),
            "InvariantFamily -> LawUniverse -> ObstructionCircuit -> ArchitectureSignature"
                .to_string(),
            "Operation -> Path -> Homotopy -> Diagram -> AnalyticRepresentation".to_string(),
        ],
        observed_atoms_summary: architecture_state.atom_family_refs.clone(),
        obstruction_summary: design_pressure
            .iter()
            .flat_map(|pressure| pressure.obstruction_refs.clone())
            .collect(),
        signature_axes_summary: signature_axes
            .iter()
            .map(|axis| {
                format!(
                    "{}={} ({})",
                    axis.signature_axis_id, axis.value, axis.coverage_status
                )
            })
            .collect(),
        analytic_readings_summary: analytic_representations
            .iter()
            .map(|reading| {
                format!(
                    "{}={} ({})",
                    reading.representation_family, reading.value, reading.status
                )
            })
            .collect(),
        spectral_readings_summary: spectral_analysis_readings
            .iter()
            .map(|reading| {
                let upper_bound = reading
                    .values
                    .iter()
                    .find(|value| value.name == "spectralRadiusUpperBound")
                    .map(|value| value.value.as_str())
                    .unwrap_or("unmeasured");
                format!(
                    "{} upperBound={} shape={}x{} ({})",
                    reading.representation_family,
                    upper_bound,
                    reading.matrix_shape.row_count,
                    reading.matrix_shape.column_count,
                    reading.status
                )
            })
            .collect(),
        spectral_mode_summary: spectral_mode_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} {} gap={} localization={} density={} ({})",
                    reading.representation_family,
                    reading.mode_kind,
                    reading.spectral_gap_proxy.value,
                    reading.localization_index.value,
                    reading.matrix_density.value,
                    reading.status
                )
            })
            .collect(),
        spectral_drilldown_summary: spectral_drilldown_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} atomFamilies={} overlapPairs={} repairAxisDeltas={} ({})",
                    reading.drilldown_id,
                    reading.dominant_atom_family_composition.len(),
                    reading.high_overlap_molecule_pairs.len(),
                    reading.repair_axis_delta_readings.len(),
                    reading.status
                )
            })
            .collect(),
        transfer_bridge_summary: transfer_bridge_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} transfers={} bridges={} repairRanks={} boundaryRanks={} ({})",
                    reading.transfer_bridge_id,
                    reading.transfer_matrix_entries.len(),
                    reading.bridge_atom_families.len(),
                    reading
                        .evolution_risk_ranking
                        .repair_transfer_risk_ranking
                        .len(),
                    reading
                        .evolution_risk_ranking
                        .boundary_preparation_ranking
                        .len(),
                    reading.status
                )
            })
            .collect(),
        transfer_bridge_edge_summary: transfer_bridge_readings
            .iter()
            .flat_map(|reading| {
                reading.bridge_atom_families.iter().flat_map(|bridge| {
                    bridge.edge_breakdowns.iter().map(|edge| {
                        format!(
                            "{} {} -> {} pair={} kind={} cut={} sourceRefs={} focus={}",
                            edge.edge_id,
                            edge.source_molecule_ref,
                            edge.target_molecule_ref,
                            edge.pair_ref,
                            edge.dependency_kind,
                            edge.recommended_cut_kind,
                            edge.source_refs.len(),
                            edge.review_focus.len()
                        )
                    })
                })
            })
            .collect(),
        measurement_expansion_summary: vec![format!(
            "v0.3.0 measurement expansion reads {} Atom support axes, {} compatibility surfaces, {} LawUniverse coverage surfaces, {} feature-extension formulas, {} operation-law surfaces, {} path trajectories, {} homotopy/order surfaces, and {} diagram-fillability surfaces",
            atom_support_axis_readings.len(),
            atom_compatibility_readings.len(),
            law_universe_coverage_readings.len(),
            feature_extension_formula_readings.len(),
            operation_calculus_law_readings.len(),
            path_signature_trajectory_readings.len(),
            homotopy_order_sensitivity_readings.len(),
            diagram_fillability_readings.len()
        )],
        atom_support_axis_summary: atom_support_axis_readings
            .iter()
            .take(12)
            .map(|reading| {
                format!(
                    "{} support={} concentration={} pressure={}",
                    reading.scope_ref,
                    reading.support_size,
                    reading.axis_concentration,
                    reading.mixed_axis_molecule_pressure
                )
            })
            .collect(),
        atom_compatibility_summary: atom_compatibility_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} status={} sameSlotConflicts={} uncertainty={}",
                    reading.reading_id,
                    reading.status,
                    reading.same_slot_conflict_count,
                    reading.uncertainty.len()
                )
            })
            .collect(),
        law_universe_coverage_summary: law_universe_coverage_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} required={} unmeasured={} blockedWitnesses={}",
                    reading.law_universe_ref,
                    reading.required_law_coverage.len(),
                    reading.unmeasured_required_law_count,
                    reading.blocked_witness_refs.len()
                )
            })
            .collect(),
        feature_extension_formula_summary: feature_extension_formula_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} status={} inherited={} featureLocal={} interaction={} residualGaps={}",
                    reading.reading_id,
                    reading.status,
                    reading.inherited_core_obstruction_refs.len(),
                    reading.feature_local_obstruction_refs.len(),
                    reading.interaction_obstruction_refs.len(),
                    reading.residual_coverage_gap_refs.len()
                )
            })
            .collect(),
        operation_calculus_law_summary: operation_calculus_law_readings
            .iter()
            .take(12)
            .map(|reading| {
                format!(
                    "{} kind={} composition={} repairMonotonicity={} boundary={}",
                    reading.operation_ref,
                    reading.operation_kind,
                    reading.composition_status,
                    reading.repair_monotonicity,
                    reading.synthesis_no_solution_boundary
                )
            })
            .collect(),
        path_signature_trajectory_summary: path_signature_trajectory_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} status={} endpointDeltas={} nonMonotoneAxes={} cost={}",
                    reading.path_ref,
                    reading.status,
                    reading.endpoint_signature_delta.len(),
                    reading.non_monotone_axis_refs.len(),
                    reading.path_cost_proxy
                )
            })
            .collect(),
        homotopy_order_sensitivity_summary: homotopy_order_sensitivity_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} status={} orderSensitivity={} blockers={}",
                    reading.reading_id,
                    reading.status,
                    reading.operation_order_sensitivity,
                    reading.homotopy_blocker_refs.len()
                )
            })
            .collect(),
        diagram_fillability_summary: diagram_fillability_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} family={} status={} missingFiller={} blockers={}",
                    reading.diagram_ref,
                    reading.diagram_family,
                    reading.status,
                    reading.missing_filler_kind,
                    reading.filling_blocker_refs.len()
                )
            })
            .collect(),
        representation_strength_summary: representation_strength_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} zeroReflecting={} obstructionReflecting={} blockedBy={}",
                    reading.representation_family,
                    reading.zero_reflecting,
                    reading.obstruction_reflecting,
                    reading.blocked_by.len()
                )
            })
            .collect(),
        local_curvature_diagram_summary: local_curvature_diagram_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} law={} curvature={} axes={}",
                    reading.diagram_id,
                    reading.law_ref,
                    reading.curvature_value,
                    reading.signature_axis_refs.len()
                )
            })
            .collect(),
        three_layer_flatness_summary: three_layer_flatness_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} static={} runtime={} semantic={} crossLayerAtoms={}",
                    reading.reading_id,
                    reading.static_status,
                    reading.runtime_status,
                    reading.semantic_status,
                    reading.cross_layer_atom_refs.len()
                )
            })
            .collect(),
        observation_projection_summary: observation_projection_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} families={} forgotten={} blockers={}",
                    reading.reading_id,
                    reading.observed_atom_family_count,
                    reading.forgotten_coordinates.len(),
                    reading.reconstruction_blockers.len()
                )
            })
            .collect(),
        state_transition_algebra_summary: state_transition_algebra_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} generators={} unresolved={} obstructions={}",
                    reading.reading_id,
                    reading.generator_refs.len(),
                    reading.unresolved_relations.len(),
                    reading.obstruction_refs.len()
                )
            })
            .collect(),
        operation_invariant_galois_summary: operation_invariant_galois_readings
            .iter()
            .map(|reading| {
                format!(
                    "{} invariants={} operations={} blockedOps={}",
                    reading.reading_id,
                    reading.invariant_family_refs.len(),
                    reading.operation_family_refs.len(),
                    reading.blocked_operation_refs.len()
                )
            })
            .collect(),
        split_readiness_summary: split_readiness_readings
            .iter()
            .take(12)
            .map(|reading| {
                format!(
                    "{} status={} score={} boundaryOp={}",
                    reading.molecule_ref,
                    reading.status,
                    reading.readiness_score,
                    reading.recommended_boundary_operation
                )
            })
            .collect(),
        structural_reading_review_summary: vec![
            format!(
                "{} status={} refs={} focus={}",
                structural_reading_review_surface.surface_id,
                structural_reading_review_surface.status,
                structural_reading_review_surface
                    .connected_reading_refs
                    .len(),
                structural_reading_review_surface.review_focus.len()
            ),
            structural_reading_review_surface
                .current_state_reading
                .clone(),
        ],
        current_state_evolution_boundary_summary: vec![
            current_state_evolution_boundary
                .archsig_current_state_scope
                .clone(),
            current_state_evolution_boundary
                .fieldsig_evolution_scope
                .clone(),
            format!(
                "handoff={} forbiddenReadings={}",
                current_state_evolution_boundary.handoff_artifact_ref,
                current_state_evolution_boundary.forbidden_readings.len()
            ),
        ],
        repair_operation_summary: repair_candidates
            .iter()
            .map(|candidate| {
                format!(
                    "{} targets {:?}",
                    candidate.repair_operation_candidate_id, candidate.target_obstruction_refs
                )
            })
            .collect(),
        complexity_transfer_notes: repair_candidates
            .iter()
            .flat_map(|candidate| candidate.transfer_risks.clone())
            .chain(workflow_risk_readings.iter().take(5).map(|reading| {
                format!(
                    "{}: review {} ({})",
                    reading.molecule_observation_ref,
                    reading.risk_tier,
                    reading
                        .top_axes
                        .iter()
                        .take(3)
                        .map(|axis| axis.axis.clone())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }))
            .collect(),
        coverage_gaps_and_exactness_blockers: archmap_gap_missing_evidence(archmap),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        recommended_human_review_focus: bounded_judgements
            .iter()
            .filter(|judgement| judgement.status != "nonConclusion")
            .map(|judgement| {
                format!(
                    "{}: {}",
                    judgement.judgement_id, judgement.recommended_next_action
                )
            })
            .collect(),
    }
}

fn build_repair_candidates(
    archmap: &ArchMapDocumentV0,
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<ArchSigRepairOperationCandidateV0> {
    obstruction_circuits
        .iter()
        .map(|circuit| {
            let preserved_invariants = preserved_invariants_for_repair(signature_axes);
            ArchSigRepairOperationCandidateV0 {
            repair_operation_candidate_id: format!(
                "repair:{}",
                stable_id(&circuit.obstruction_circuit_id)
            ),
            operation_kind: format!("repair-{}", stable_id(&circuit.circuit_kind)),
            target_obstruction_refs: vec![circuit.obstruction_circuit_id.clone()],
            preserved_invariants,
            preconditions: repair_preconditions(archmap),
            expected_signature_axis_effects: circuit
                .signature_axis_refs
                .iter()
                .map(|axis| format!("decrease {axis} if the witness no longer constructs"))
                .collect(),
            transfer_risks: vec![
                "may transfer obstruction into runtime behavior, ownership, or idempotency boundary"
                    .to_string(),
            ],
            evidence_boundary:
                "repair candidate is derived from ArchSig packet evidence, not an automatic patch"
                    .to_string(),
            missing_evidence: repair_candidate_missing_evidence(archmap, circuit),
            excluded_readings: repair_candidate_excluded_readings(circuit),
            interpretation_notes_for_llm: vec![
                "Explain preconditions and transfer risks before implementation advice."
                    .to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

pub fn validate_archsig_analysis_packet_report(
    packet: &ArchSigAnalysisPacketV0,
    input_path: &str,
) -> ArchSigAnalysisPacketValidationReportV0 {
    let checks = vec![
        check_schema_version(packet),
        check_refs_and_identity(packet),
        check_north_star_aat_surfaces(packet),
        check_bounded_judgement_surface(packet),
        check_analytic_and_principle_surfaces(packet),
        check_workflow_risk_surface(packet),
        check_spectral_analysis_surface(packet),
        check_spectral_mode_surface(packet),
        check_spectral_drilldown_surface(packet),
        check_transfer_bridge_surface(packet),
        check_aat_structural_reading_surfaces(packet),
        check_current_state_evolution_boundary(packet),
        check_law_relative_analysis(packet),
        check_signature_and_flatness(packet),
        check_repair_candidates(packet),
        check_llm_interpretation_surface(packet),
        check_non_conclusions(packet),
    ];
    let summary = ArchSigAnalysisPacketValidationSummaryV0 {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        aat_concept_surface_count: packet.aat_concept_surfaces.len(),
        molecule_reading_count: packet.molecule_readings.len(),
        obstruction_circuit_count: packet.obstruction_circuits.len(),
        signature_axis_count: packet.signature_axes.len(),
        analytic_representation_count: packet.analytic_representations.len(),
        coupling_cohesion_reading_count: packet.coupling_cohesion_readings.len(),
        workflow_risk_reading_count: packet.workflow_risk_readings.len(),
        spectral_analysis_reading_count: packet.spectral_analysis_readings.len(),
        spectral_mode_reading_count: packet.spectral_mode_readings.len(),
        spectral_drilldown_reading_count: packet.spectral_drilldown_readings.len(),
        transfer_bridge_reading_count: packet.transfer_bridge_readings.len(),
        atom_support_axis_reading_count: packet.atom_support_axis_readings.len(),
        atom_compatibility_reading_count: packet.atom_compatibility_readings.len(),
        law_universe_coverage_reading_count: packet.law_universe_coverage_readings.len(),
        feature_extension_formula_reading_count: packet.feature_extension_formula_readings.len(),
        operation_calculus_law_reading_count: packet.operation_calculus_law_readings.len(),
        path_signature_trajectory_reading_count: packet.path_signature_trajectory_readings.len(),
        homotopy_order_sensitivity_reading_count: packet.homotopy_order_sensitivity_readings.len(),
        diagram_fillability_reading_count: packet.diagram_fillability_readings.len(),
        representation_strength_reading_count: packet.representation_strength_readings.len(),
        local_curvature_diagram_reading_count: packet.local_curvature_diagram_readings.len(),
        three_layer_flatness_reading_count: packet.three_layer_flatness_readings.len(),
        observation_projection_reading_count: packet.observation_projection_readings.len(),
        state_transition_algebra_reading_count: packet.state_transition_algebra_readings.len(),
        operation_invariant_galois_reading_count: packet.operation_invariant_galois_readings.len(),
        split_readiness_reading_count: packet.split_readiness_readings.len(),
        design_principle_reading_count: packet.design_principle_readings.len(),
        repair_operation_candidate_count: packet.repair_operation_candidates.len(),
        operation_delta_count: packet.operation_deltas.len(),
        bounded_judgement_count: packet.bounded_judgements.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArchSigAnalysisPacketValidationReportV0 {
        schema_version: ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ArchSigAnalysisPacketValidationInputV0 {
            schema_version: packet.schema_version.clone(),
            path: input_path.to_string(),
            analysis_id: packet.analysis_id.clone(),
            arch_map_ref: packet.arch_map_ref.artifact_id.clone(),
            selected_law_policy_ref: packet.selected_law_policy_ref.artifact_id.clone(),
        },
        packet: packet.clone(),
        summary,
        checks,
    }
}

fn check_schema_version(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut check = validation_check(
        "archsig-analysis-packet-schema-version-supported",
        "ArchSig analysis packet schema version is supported",
        if packet.schema_version == ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported ArchSig analysis packet schemaVersion: {}",
            packet.schema_version
        ));
    }
    check
}

fn check_refs_and_identity(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "analysisId", &packet.analysis_id);
    push_blank(&mut examples, "generatedAt", &packet.generated_at);
    push_blank(
        &mut examples,
        "archMapRef.artifactId",
        &packet.arch_map_ref.artifact_id,
    );
    push_blank(
        &mut examples,
        "interpretationProfileRef.artifactId",
        &packet.interpretation_profile_ref.artifact_id,
    );
    push_blank(
        &mut examples,
        "selectedLawPolicyRef.artifactId",
        &packet.selected_law_policy_ref.artifact_id,
    );
    if packet.arch_map_ref.schema_version != ARCHMAP_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "archMapRef.schemaVersion",
            &packet.arch_map_ref.schema_version,
            "analysis packet must reference the current ArchMap observation schema",
        ));
    }
    if packet.selected_law_policy_ref.schema_version != LAW_POLICY_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "selectedLawPolicyRef.schemaVersion",
            &packet.selected_law_policy_ref.schema_version,
            "analysis packet must reference a LawPolicy artifact",
        ));
    }
    check_from_examples(
        "archsig-analysis-packet-refs-and-identity",
        "analysis identity and ArchMap / LawPolicy references are recorded",
        examples,
        "fail",
    )
}

fn check_north_star_aat_surfaces(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let required_concepts = BTreeSet::from([
        "Atom",
        "Configuration",
        "ArchitectureObject",
        "Invariant",
        "LawUniverse",
        "ObstructionCircuit",
        "ArchitectureSignature",
        "Operation",
        "Path",
        "Homotopy",
        "Diagram",
        "AnalyticRepresentation",
    ]);
    let present = packet
        .aat_concept_surfaces
        .iter()
        .map(|surface| surface.concept.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = required_concepts
        .iter()
        .filter(|concept| !present.contains(**concept))
        .map(|concept| {
            generic_validation_example(
                "aatConceptSurfaces",
                concept,
                "North Star packet must represent every AAT concept surface",
            )
        })
        .collect::<Vec<_>>();

    if packet.architecture_object_projections.is_empty() {
        examples.push(generic_validation_example(
            "architectureObjectProjections",
            "empty",
            "packet must expose ArchitectureObject projection surface",
        ));
    }
    if packet.invariant_family_readings.is_empty() {
        examples.push(generic_validation_example(
            "invariantFamilyReadings",
            "empty",
            "packet must expose invariant family readings",
        ));
    }
    if packet.law_universe_reading.selected_law_refs.is_empty() {
        examples.push(generic_validation_example(
            "lawUniverseReading.selectedLawRefs",
            "empty",
            "packet must expose selected law universe/profile refs",
        ));
    }
    if packet.path_homotopy_diagram_readings.is_empty() {
        examples.push(generic_validation_example(
            "pathHomotopyDiagramReadings",
            "empty",
            "packet must expose path, homotopy, and diagram readings",
        ));
    }

    check_from_examples(
        "archsig-analysis-packet-north-star-aat-surfaces",
        "packet represents all AAT concept surfaces required by the North Star PRD",
        examples,
        "fail",
    )
}

fn check_bounded_judgement_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let allowed = BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let mut examples = Vec::new();
    if packet.bounded_judgements.is_empty() {
        examples.push(generic_validation_example(
            "boundedJudgements",
            "empty",
            "packet must provide bounded judgement records",
        ));
    }
    for judgement in &packet.bounded_judgements {
        if !allowed.contains(judgement.status.as_str()) {
            examples.push(generic_validation_example(
                &judgement.judgement_id,
                &judgement.status,
                "bounded judgement status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        if judgement.evidence_refs.is_empty() || has_blank(&judgement.evidence_refs) {
            examples.push(generic_validation_example(
                &judgement.judgement_id,
                "evidenceRefs",
                "bounded judgement must carry evidence refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", judgement.judgement_id),
            &judgement.coverage_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} exactnessBoundary", judgement.judgement_id),
            &judgement.exactness_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", judgement.judgement_id),
            &judgement.recommended_next_action,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-bounded-judgement-surface",
        "packet makes non-conclusion usable through bounded judgement records",
        examples,
        "fail",
    )
}

fn check_analytic_and_principle_surfaces(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let required_principles = BTreeSet::from([
        "InformationHiding",
        "Encapsulation",
        "SeparationOfConcerns",
        "Substitutability",
        "OpenClosedExtension",
        "DependencyInversion",
        "RepresentationIndependence",
        "IdempotencyAndReplaySafety",
        "AuthorityAndTrustBoundary",
    ]);
    let present_principles = packet
        .design_principle_readings
        .iter()
        .map(|reading| reading.principle.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = required_principles
        .iter()
        .filter(|principle| !present_principles.contains(**principle))
        .map(|principle| {
            generic_validation_example(
                "designPrincipleReadings",
                principle,
                "packet must expose static-hard design principles as AAT readings",
            )
        })
        .collect::<Vec<_>>();

    for required_axis in [
        "weightedAdjacencyMatrix",
        "walkCount",
        "reachableConeSize",
        "nilpotenceBoundary",
        "selectedSubgraphSpectrum",
        "propagationDepth",
        "spectralRadius",
        "curvatureValuation",
        "stateAlgebra",
        "zeroReflectingAggregateBoundary",
    ] {
        if !packet
            .analytic_representations
            .iter()
            .any(|reading| reading.representation_family == required_axis)
        {
            examples.push(generic_validation_example(
                "analyticRepresentations",
                required_axis,
                "packet must expose graph/matrix/spectrum/curvature analytic axes",
            ));
        }
    }
    for required_axis in [
        "staticDependencyCoupling",
        "contractCohesion",
        "stateEffectCoupling",
        "authorityTrustCoupling",
    ] {
        if !packet
            .coupling_cohesion_readings
            .iter()
            .any(|reading| reading.axis == required_axis)
        {
            examples.push(generic_validation_example(
                "couplingCohesionReadings",
                required_axis,
                "packet must expose semantic coupling/cohesion axes",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-analytic-and-principle-surfaces",
        "packet exposes analytic axes, semantic coupling/cohesion, and static-hard design principle readings",
        examples,
        "fail",
    )
}

fn check_workflow_risk_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let molecule_ids = set(packet
        .molecule_readings
        .iter()
        .map(|reading| reading.molecule_observation_ref.as_str()));
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let mut examples = Vec::new();
    if packet.workflow_risk_readings.is_empty() {
        examples.push(generic_validation_example(
            "workflowRiskReadings",
            "empty",
            "packet must expose workflow-local risk readings for review prioritization",
        ));
    }
    examples.extend(duplicate_examples(
        "workflowRiskReadings[].workflowRiskId",
        duplicates(
            packet
                .workflow_risk_readings
                .iter()
                .map(|reading| reading.workflow_risk_id.as_str()),
        ),
    ));
    for reading in &packet.workflow_risk_readings {
        if !molecule_ids.contains(reading.molecule_observation_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.workflow_risk_id,
                &reading.molecule_observation_ref,
                "workflow risk reading must reference an existing molecule reading",
            ));
        }
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.workflow_risk_id,
                &reading.status,
                "workflow risk status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        if reading.risk_score < 0 {
            examples.push(generic_validation_example(
                &reading.workflow_risk_id,
                &reading.risk_score.to_string(),
                "workflow risk score must be non-negative bounded ranking evidence",
            ));
        }
        if reading.top_axes.is_empty() {
            examples.push(generic_validation_example(
                &reading.workflow_risk_id,
                "topAxes",
                "workflow risk reading must carry at least one axis reading",
            ));
        }
        if reading.review_focus.is_empty() || has_blank(&reading.review_focus) {
            examples.push(generic_validation_example(
                &reading.workflow_risk_id,
                "reviewFocus",
                "workflow risk reading must provide review focus",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.workflow_risk_id),
            &reading.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.workflow_risk_id),
            &reading.recommended_next_action,
        );
        for axis in &reading.top_axes {
            push_blank(
                &mut examples,
                &format!("{} topAxes[].axis", reading.workflow_risk_id),
                &axis.axis,
            );
            if axis.score < 0 || axis.family_score < 0 {
                examples.push(generic_validation_example(
                    &reading.workflow_risk_id,
                    &axis.axis,
                    "workflow risk axis scores must be non-negative",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} topAxes[].reading", reading.workflow_risk_id),
                &axis.reading,
            );
        }
    }
    check_from_examples(
        "archsig-analysis-packet-workflow-risk-surface",
        "packet exposes workflow-local risk readings with review focus and bounded evidence boundaries",
        examples,
        "fail",
    )
}

fn check_spectral_analysis_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let required_families = BTreeSet::from([
        "workflowRiskAxisPressureMatrix",
        "moleculeAtomOverlapCouplingMatrix",
        "obstructionAxisCurvatureMatrix",
        "operationSignatureDeltaMatrix",
    ]);
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let present_families = packet
        .spectral_analysis_readings
        .iter()
        .map(|reading| reading.representation_family.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = required_families
        .iter()
        .filter(|family| !present_families.contains(**family))
        .map(|family| {
            generic_validation_example(
                "spectralAnalysisReadings",
                family,
                "packet must expose required AAT spectral analysis representation families",
            )
        })
        .collect::<Vec<_>>();
    if packet.spectral_analysis_readings.is_empty() {
        examples.push(generic_validation_example(
            "spectralAnalysisReadings",
            "empty",
            "packet must expose bounded spectral analysis readings",
        ));
    }
    examples.extend(duplicate_examples(
        "spectralAnalysisReadings[].spectralReadingId",
        duplicates(
            packet
                .spectral_analysis_readings
                .iter()
                .map(|reading| reading.spectral_reading_id.as_str()),
        ),
    ));
    for reading in &packet.spectral_analysis_readings {
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.spectral_reading_id,
                &reading.status,
                "spectral analysis status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} matrixShape.rowDomain", reading.spectral_reading_id),
            &reading.matrix_shape.row_domain,
        );
        push_blank(
            &mut examples,
            &format!("{} matrixShape.columnDomain", reading.spectral_reading_id),
            &reading.matrix_shape.column_domain,
        );
        push_blank(
            &mut examples,
            &format!("{} entryRule", reading.spectral_reading_id),
            &reading.entry_rule,
        );
        push_blank(
            &mut examples,
            &format!("{} reading", reading.spectral_reading_id),
            &reading.reading,
        );
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.spectral_reading_id),
            &reading.coverage_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} zeroReflectingBoundary", reading.spectral_reading_id),
            &reading.zero_reflecting_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.spectral_reading_id),
            &reading.recommended_next_action,
        );
        if reading.values.is_empty() {
            examples.push(generic_validation_example(
                &reading.spectral_reading_id,
                "values",
                "spectral analysis reading must carry bounded numeric values",
            ));
        }
        for value in &reading.values {
            push_blank(
                &mut examples,
                &format!("{} values[].name", reading.spectral_reading_id),
                &value.name,
            );
            push_blank(
                &mut examples,
                &format!("{} values[].value", reading.spectral_reading_id),
                &value.value,
            );
            push_blank(
                &mut examples,
                &format!("{} values[].interpretation", reading.spectral_reading_id),
                &value.interpretation,
            );
        }
        for component in &reading.dominant_components {
            push_blank(
                &mut examples,
                &format!(
                    "{} dominantComponents[].componentRef",
                    reading.spectral_reading_id
                ),
                &component.component_ref,
            );
            push_blank(
                &mut examples,
                &format!(
                    "{} dominantComponents[].reading",
                    reading.spectral_reading_id
                ),
                &component.reading,
            );
        }
    }
    check_from_examples(
        "archsig-analysis-packet-spectral-analysis-surface",
        "packet exposes AAT spectral readings as bounded finite-representation proxies",
        examples,
        "fail",
    )
}

fn check_spectral_mode_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let source_reading_ids = set(packet
        .spectral_analysis_readings
        .iter()
        .map(|reading| reading.spectral_reading_id.as_str()));
    let source_families = packet
        .spectral_analysis_readings
        .iter()
        .map(|reading| reading.representation_family.as_str())
        .collect::<BTreeSet<_>>();
    let mode_families = packet
        .spectral_mode_readings
        .iter()
        .map(|reading| reading.representation_family.as_str())
        .collect::<BTreeSet<_>>();
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let mut examples = source_families
        .iter()
        .filter(|family| !mode_families.contains(**family))
        .map(|family| {
            generic_validation_example(
                "spectralModeReadings",
                family,
                "packet must expose one spectral mode reading for each spectral analysis representation family",
            )
        })
        .collect::<Vec<_>>();
    if packet.spectral_mode_readings.is_empty() {
        examples.push(generic_validation_example(
            "spectralModeReadings",
            "empty",
            "packet must expose bounded spectral mode readings",
        ));
    }
    examples.extend(duplicate_examples(
        "spectralModeReadings[].spectralModeId",
        duplicates(
            packet
                .spectral_mode_readings
                .iter()
                .map(|reading| reading.spectral_mode_id.as_str()),
        ),
    ));
    for reading in &packet.spectral_mode_readings {
        if !source_reading_ids.contains(reading.source_spectral_reading_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.spectral_mode_id,
                &reading.source_spectral_reading_ref,
                "spectral mode reading must reference an existing spectral analysis reading",
            ));
        }
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.spectral_mode_id,
                &reading.status,
                "spectral mode status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} modeKind", reading.spectral_mode_id),
            &reading.mode_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} decomposabilityReading", reading.spectral_mode_id),
            &reading.decomposability_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} repairPerturbationReading", reading.spectral_mode_id),
            &reading.repair_perturbation_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.spectral_mode_id),
            &reading.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.spectral_mode_id),
            &reading.recommended_next_action,
        );
        for value in [
            &reading.spectral_gap_proxy,
            &reading.localization_index,
            &reading.matrix_density,
        ] {
            push_blank(
                &mut examples,
                &format!("{} modeValue.name", reading.spectral_mode_id),
                &value.name,
            );
            push_blank(
                &mut examples,
                &format!("{} modeValue.value", reading.spectral_mode_id),
                &value.value,
            );
            push_blank(
                &mut examples,
                &format!("{} modeValue.interpretation", reading.spectral_mode_id),
                &value.interpretation,
            );
        }
        if reading.mode_components.is_empty()
            && reading.status != "nonConclusion"
            && reading.representation_family != "obstructionAxisCurvatureMatrix"
        {
            examples.push(generic_validation_example(
                &reading.spectral_mode_id,
                "modeComponents",
                "spectral mode reading should expose dominant mode components unless the source representation is a non-conclusion",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-spectral-mode-surface",
        "packet exposes bounded spectral mode readings for localization, decomposability, and repair perturbation review",
        examples,
        "fail",
    )
}

fn check_spectral_drilldown_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mode_ids = set(packet
        .spectral_mode_readings
        .iter()
        .map(|reading| reading.spectral_mode_id.as_str()));
    let atom_ids = set(packet
        .molecule_readings
        .iter()
        .flat_map(|reading| reading.atom_observation_refs.iter().map(String::as_str)));
    let molecule_ids = set(packet
        .molecule_readings
        .iter()
        .map(|reading| reading.molecule_observation_ref.as_str()));
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let operation_ids = set(packet
        .operation_deltas
        .iter()
        .map(|delta| delta.operation_delta_id.as_str()));
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let mut examples = Vec::new();
    if packet.spectral_drilldown_readings.is_empty() {
        examples.push(generic_validation_example(
            "spectralDrilldownReadings",
            "empty",
            "packet must expose spectral drilldown readings for mode explanation",
        ));
    }
    examples.extend(duplicate_examples(
        "spectralDrilldownReadings[].drilldownId",
        duplicates(
            packet
                .spectral_drilldown_readings
                .iter()
                .map(|reading| reading.drilldown_id.as_str()),
        ),
    ));
    for reading in &packet.spectral_drilldown_readings {
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.drilldown_id,
                &reading.status,
                "spectral drilldown status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        if reading.source_spectral_mode_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.drilldown_id,
                "sourceSpectralModeRefs",
                "spectral drilldown must reference source spectral modes",
            ));
        }
        for mode_ref in &reading.source_spectral_mode_refs {
            if !mode_ids.contains(mode_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    mode_ref,
                    "spectral drilldown references an unknown spectral mode",
                ));
            }
        }
        if reading.dominant_atom_family_composition.is_empty() {
            examples.push(generic_validation_example(
                &reading.drilldown_id,
                "dominantAtomFamilyComposition",
                "spectral drilldown must explain dominant mode atom families",
            ));
        }
        for composition in &reading.dominant_atom_family_composition {
            push_blank(
                &mut examples,
                &format!("{} atomFamily", reading.drilldown_id),
                &composition.atom_family,
            );
            if composition.count == 0 || composition.atom_observation_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    &composition.atom_family,
                    "dominant atom family composition must carry positive atom evidence",
                ));
            }
            for atom_ref in &composition.atom_observation_refs {
                if !atom_ids.contains(atom_ref.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.drilldown_id,
                        atom_ref,
                        "dominant atom family composition references an unknown atom observation",
                    ));
                }
            }
            push_blank(
                &mut examples,
                &format!("{} composition.reading", reading.drilldown_id),
                &composition.reading,
            );
        }
        for pair in &reading.high_overlap_molecule_pairs {
            if pair.overlap_score <= 0 {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    &pair.pair_id,
                    "high-overlap molecule pair score must be positive",
                ));
            }
            if !molecule_ids.contains(pair.left_molecule_ref.as_str())
                || !molecule_ids.contains(pair.right_molecule_ref.as_str())
            {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    &pair.pair_id,
                    "high-overlap molecule pair must reference existing molecules",
                ));
            }
            if pair.shared_atom_families.is_empty() && pair.shared_atom_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    &pair.pair_id,
                    "high-overlap molecule pair must carry shared atom family or atom ref evidence",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} pair.boundaryAdvice", reading.drilldown_id),
                &pair.boundary_advice,
            );
        }
        if reading.repair_axis_delta_readings.is_empty() {
            examples.push(generic_validation_example(
                &reading.drilldown_id,
                "repairAxisDeltaReadings",
                "spectral drilldown must expose repair axis delta readings",
            ));
        }
        for delta in &reading.repair_axis_delta_readings {
            if !operation_ids.contains(delta.operation_delta_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.drilldown_id,
                    &delta.operation_delta_ref,
                    "repair axis delta reading references an unknown operation delta",
                ));
            }
            for axis_ref in delta
                .positive_delta_axes
                .iter()
                .chain(delta.negative_delta_axes.iter())
                .chain(delta.neutral_or_unknown_axes.iter())
            {
                if !axis_ids.contains(axis_ref.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.drilldown_id,
                        axis_ref,
                        "repair axis delta references an unknown signature axis",
                    ));
                }
            }
            push_blank(
                &mut examples,
                &format!("{} repairAxisDelta.reading", reading.drilldown_id),
                &delta.reading,
            );
            push_blank(
                &mut examples,
                &format!("{} repairAxisDelta.evidenceBoundary", reading.drilldown_id),
                &delta.evidence_boundary,
            );
        }
        push_blank(
            &mut examples,
            &format!("{} reading", reading.drilldown_id),
            &reading.reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.drilldown_id),
            &reading.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.drilldown_id),
            &reading.recommended_next_action,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-spectral-drilldown-surface",
        "packet explains spectral modes through atom families, overlap pairs, and repair axis deltas",
        examples,
        "fail",
    )
}

fn check_transfer_bridge_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let operation_ids = set(packet
        .operation_deltas
        .iter()
        .map(|delta| delta.operation_delta_id.as_str()));
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let molecule_ids = set(packet
        .molecule_readings
        .iter()
        .map(|reading| reading.molecule_observation_ref.as_str()));
    let pair_ids = packet
        .spectral_drilldown_readings
        .iter()
        .flat_map(|reading| {
            reading
                .high_overlap_molecule_pairs
                .iter()
                .map(|pair| pair.pair_id.as_str())
        })
        .collect::<BTreeSet<_>>();
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let allowed_dependency_kinds =
        BTreeSet::from(["explicitContract", "implicitDependency", "mixedBoundary"]);
    let allowed_cut_kinds = BTreeSet::from([
        "interface",
        "policy",
        "transactionBoundary",
        "antiCorruptionLayer",
    ]);
    let mut examples = Vec::new();
    if packet.transfer_bridge_readings.is_empty() {
        examples.push(generic_validation_example(
            "transferBridgeReadings",
            "empty",
            "packet must expose transfer bridge readings for evolution review",
        ));
    }
    examples.extend(duplicate_examples(
        "transferBridgeReadings[].transferBridgeId",
        duplicates(
            packet
                .transfer_bridge_readings
                .iter()
                .map(|reading| reading.transfer_bridge_id.as_str()),
        ),
    ));
    for reading in &packet.transfer_bridge_readings {
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.transfer_bridge_id,
                &reading.status,
                "transfer bridge status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        if reading.transfer_matrix_entries.is_empty() && reading.status != "nonConclusion" {
            examples.push(generic_validation_example(
                &reading.transfer_bridge_id,
                "transferMatrixEntries",
                "transfer bridge must expose repair operation x transferred axis matrix entries",
            ));
        }
        for entry in &reading.transfer_matrix_entries {
            if !operation_ids.contains(entry.operation_delta_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &entry.operation_delta_ref,
                    "transfer matrix entry references an unknown operation delta",
                ));
            }
            if !axis_ids.contains(entry.transferred_axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &entry.transferred_axis_ref,
                    "transfer matrix entry references an unknown transferred axis",
                ));
            }
            if entry.transfer_weight <= 0 {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &entry.transfer_weight.to_string(),
                    "transfer matrix entry must carry positive transfer weight",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} transferMatrixEntry.reading", reading.transfer_bridge_id),
                &entry.reading,
            );
        }
        if reading.bridge_atom_families.is_empty() {
            examples.push(generic_validation_example(
                &reading.transfer_bridge_id,
                "bridgeAtomFamilies",
                "transfer bridge must expose bridge atom family readings",
            ));
        }
        for bridge in &reading.bridge_atom_families {
            if !molecule_ids.contains(bridge.source_hub_molecule_ref.as_str())
                || !molecule_ids.contains(bridge.target_hub_molecule_ref.as_str())
            {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &bridge.bridge_id,
                    "bridge atom family reading must reference known hub molecules",
                ));
            }
            for molecule_ref in &bridge.intermediate_molecule_refs {
                if !molecule_ids.contains(molecule_ref.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        molecule_ref,
                        "bridge atom family reading references an unknown intermediate molecule",
                    ));
                }
            }
            if bridge.bridge_score < 0 {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &bridge.bridge_score.to_string(),
                    "bridge score must be non-negative",
                ));
            }
            if !bridge.path_pair_refs.is_empty() && bridge.edge_breakdowns.is_empty() {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &bridge.bridge_id,
                    "bridge atom family reading with path pairs must expose edge breakdowns",
                ));
            }
            for edge in &bridge.edge_breakdowns {
                if !molecule_ids.contains(edge.source_molecule_ref.as_str())
                    || !molecule_ids.contains(edge.target_molecule_ref.as_str())
                {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge breakdown must reference known source and target molecules",
                    ));
                }
                if !pair_ids.contains(edge.pair_ref.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.pair_ref,
                        "bridge edge breakdown must reference a high-overlap molecule pair",
                    ));
                }
                if edge.overlap_score <= 0 {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.overlap_score.to_string(),
                        "bridge edge breakdown must carry positive overlap score",
                    ));
                }
                if edge.shared_atom_families.is_empty() {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge breakdown must carry shared atom families",
                    ));
                }
                if edge.family_supporting_atom_refs.is_empty() {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge breakdown must carry family-supporting atom refs",
                    ));
                }
                if edge.source_refs.is_empty() {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge breakdown must carry source refs for review",
                    ));
                }
                if edge.review_focus.is_empty() {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge breakdown must carry reviewer focus items",
                    ));
                }
                if !edge
                    .review_focus
                    .iter()
                    .any(|focus| focus.to_ascii_lowercase().contains("source ref"))
                {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.edge_id,
                        "bridge edge review focus must connect the edge reading to source refs",
                    ));
                }
                push_blank(
                    &mut examples,
                    &format!(
                        "{} bridgeEdge.sourceRefRationale",
                        reading.transfer_bridge_id
                    ),
                    &edge.source_ref_rationale,
                );
                push_blank(
                    &mut examples,
                    &format!("{} bridgeEdge.llmReviewSummary", reading.transfer_bridge_id),
                    &edge.llm_review_summary,
                );
                if !allowed_dependency_kinds.contains(edge.dependency_kind.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.dependency_kind,
                        "bridge edge dependency kind must be explicitContract, implicitDependency, or mixedBoundary",
                    ));
                }
                if !allowed_cut_kinds.contains(edge.recommended_cut_kind.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.transfer_bridge_id,
                        &edge.recommended_cut_kind,
                        "bridge edge recommended cut kind must be interface, policy, transactionBoundary, or antiCorruptionLayer",
                    ));
                }
                push_blank(
                    &mut examples,
                    &format!(
                        "{} bridgeEdge.dependencyReading",
                        reading.transfer_bridge_id
                    ),
                    &edge.dependency_reading,
                );
                push_blank(
                    &mut examples,
                    &format!("{} bridgeEdge.cutRationale", reading.transfer_bridge_id),
                    &edge.cut_rationale,
                );
                push_blank(
                    &mut examples,
                    &format!("{} bridgeEdge.evidenceBoundary", reading.transfer_bridge_id),
                    &edge.evidence_boundary,
                );
            }
            push_blank(
                &mut examples,
                &format!("{} bridge.reviewRisk", reading.transfer_bridge_id),
                &bridge.review_risk,
            );
            push_blank(
                &mut examples,
                &format!(
                    "{} bridge.recommendedBoundaryPreparation",
                    reading.transfer_bridge_id
                ),
                &bridge.recommended_boundary_preparation,
            );
            push_blank(
                &mut examples,
                &format!("{} bridge.evidenceBoundary", reading.transfer_bridge_id),
                &bridge.evidence_boundary,
            );
        }
        if reading
            .evolution_risk_ranking
            .repair_transfer_risk_ranking
            .is_empty()
        {
            examples.push(generic_validation_example(
                &reading.transfer_bridge_id,
                "evolutionRiskRanking.repairTransferRiskRanking",
                "transfer bridge must rank repair transfer risk",
            ));
        }
        for rank in &reading.evolution_risk_ranking.repair_transfer_risk_ranking {
            if rank.rank == 0 || !operation_ids.contains(rank.operation_delta_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &rank.operation_delta_ref,
                    "repair transfer risk ranking must carry positive rank and known operation delta",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} repairTransferRisk.reading", reading.transfer_bridge_id),
                &rank.reading,
            );
        }
        for rank in &reading.evolution_risk_ranking.boundary_preparation_ranking {
            if rank.rank == 0
                || !molecule_ids.contains(rank.left_molecule_ref.as_str())
                || !molecule_ids.contains(rank.right_molecule_ref.as_str())
            {
                examples.push(generic_validation_example(
                    &reading.transfer_bridge_id,
                    &rank.pair_ref,
                    "boundary preparation ranking must carry positive rank and known molecules",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} boundaryPreparation.reading", reading.transfer_bridge_id),
                &rank.reading,
            );
        }
        push_blank(
            &mut examples,
            &format!("{} reading", reading.transfer_bridge_id),
            &reading.reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.transfer_bridge_id),
            &reading.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.transfer_bridge_id),
            &reading.recommended_next_action,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-transfer-bridge-surface",
        "packet exposes transfer matrix, bridge atom families, and evolution risk ranking",
        examples,
        "fail",
    )
}

fn check_aat_structural_reading_surfaces(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    if packet.representation_strength_readings.is_empty() {
        examples.push(generic_validation_example(
            "representationStrengthReadings",
            "empty",
            "packet must expose representation strength readings",
        ));
    }
    if packet.local_curvature_diagram_readings.is_empty() {
        examples.push(generic_validation_example(
            "localCurvatureDiagramReadings",
            "empty",
            "packet must expose local curvature diagram readings",
        ));
    }
    if packet.three_layer_flatness_readings.is_empty() {
        examples.push(generic_validation_example(
            "threeLayerFlatnessReadings",
            "empty",
            "packet must expose three-layer flatness readings",
        ));
    }
    if packet.observation_projection_readings.is_empty() {
        examples.push(generic_validation_example(
            "observationProjectionReadings",
            "empty",
            "packet must expose observation projection readings",
        ));
    }
    if packet.state_transition_algebra_readings.is_empty() {
        examples.push(generic_validation_example(
            "stateTransitionAlgebraReadings",
            "empty",
            "packet must expose state transition algebra readings",
        ));
    }
    if packet.operation_invariant_galois_readings.is_empty() {
        examples.push(generic_validation_example(
            "operationInvariantGaloisReadings",
            "empty",
            "packet must expose operation-invariant Galois readings",
        ));
    }
    if packet.split_readiness_readings.is_empty() {
        examples.push(generic_validation_example(
            "splitReadinessReadings",
            "empty",
            "packet must expose split readiness readings",
        ));
    }
    if packet.atom_support_axis_readings.is_empty() {
        examples.push(generic_validation_example(
            "atomSupportAxisReadings",
            "empty",
            "packet must expose Atom support / axis restriction readings",
        ));
    }
    if packet.atom_compatibility_readings.is_empty() {
        examples.push(generic_validation_example(
            "atomCompatibilityReadings",
            "empty",
            "packet must expose Atom compatibility readings",
        ));
    }
    if packet.law_universe_coverage_readings.is_empty() {
        examples.push(generic_validation_example(
            "lawUniverseCoverageReadings",
            "empty",
            "packet must expose LawUniverse coverage readings",
        ));
    }
    if packet.feature_extension_formula_readings.is_empty() {
        examples.push(generic_validation_example(
            "featureExtensionFormulaReadings",
            "empty",
            "packet must expose feature extension formula readings",
        ));
    }
    if packet.operation_calculus_law_readings.is_empty() {
        examples.push(generic_validation_example(
            "operationCalculusLawReadings",
            "empty",
            "packet must expose operation calculus law readings",
        ));
    }
    if packet.path_signature_trajectory_readings.is_empty() {
        examples.push(generic_validation_example(
            "pathSignatureTrajectoryReadings",
            "empty",
            "packet must expose path signature trajectory readings",
        ));
    }
    if packet.homotopy_order_sensitivity_readings.is_empty() {
        examples.push(generic_validation_example(
            "homotopyOrderSensitivityReadings",
            "empty",
            "packet must expose homotopy / operation-order sensitivity readings",
        ));
    }
    if packet.diagram_fillability_readings.is_empty() {
        examples.push(generic_validation_example(
            "diagramFillabilityReadings",
            "empty",
            "packet must expose diagram fillability readings",
        ));
    }

    for reading in &packet.representation_strength_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.source_reading_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} representationFamily", reading.reading_id),
            &reading.representation_family,
        );
        push_blank(
            &mut examples,
            &format!("{} zeroReflecting", reading.reading_id),
            &reading.zero_reflecting,
        );
        push_blank(
            &mut examples,
            &format!("{} zeroPreserving", reading.reading_id),
            &reading.zero_preserving,
        );
        push_blank(
            &mut examples,
            &format!("{} obstructionPreserving", reading.reading_id),
            &reading.obstruction_preserving,
        );
        push_blank(
            &mut examples,
            &format!("{} obstructionReflecting", reading.reading_id),
            &reading.obstruction_reflecting,
        );
        push_blank(
            &mut examples,
            &format!("{} aggregateZeroSafety", reading.reading_id),
            &reading.aggregate_zero_safety,
        );
        push_blank(
            &mut examples,
            &format!("{} cancellationRisk", reading.reading_id),
            &reading.cancellation_risk,
        );
        if reading.required_assumptions.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "requiredAssumptions",
                "representation strength must record required assumptions",
            ));
        }
        if reading
            .blocked_reflection_or_preservation_reasons
            .is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "blockedReflectionOrPreservationReasons",
                "representation strength must record reflection / preservation blockers",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.atom_support_axis_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.scope_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.scope_kind);
        if reading.axis_restriction_counts.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "axisRestrictionCounts",
                "Atom support reading must record axis restriction counts",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} axisConcentration", reading.reading_id),
            &reading.axis_concentration,
        );
        push_blank(
            &mut examples,
            &format!("{} mixedAxisMoleculePressure", reading.reading_id),
            &reading.mixed_axis_molecule_pressure,
        );
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
    }
    for reading in &packet.atom_compatibility_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        push_blank(
            &mut examples,
            &format!("{} confidenceBoundary", reading.reading_id),
            &reading.confidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
        if reading.payload_inconsistency_kinds.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "payloadInconsistencyKinds",
                "Atom compatibility reading must enumerate inconsistency kinds",
            ));
        }
    }
    for reading in &packet.law_universe_coverage_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.law_universe_ref,
        );
        if reading.required_law_coverage.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "requiredLawCoverage",
                "LawUniverse coverage must record required law coverage",
            ));
        }
        if reading.witness_family_coverage.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "witnessFamilyCoverage",
                "LawUniverse coverage must record witness family coverage",
            ));
        }
        if reading.signature_axis_coverage.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "signatureAxisCoverage",
                "LawUniverse coverage must record signature axis coverage",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} lawWitnessAxisAlignment", reading.reading_id),
            &reading.law_witness_axis_alignment,
        );
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
    }
    for reading in &packet.feature_extension_formula_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.scope_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        if reading.classification_summary.len() < 7 {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "classificationSummary",
                "feature extension formula must classify all required axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.operation_calculus_law_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.operation_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.operation_kind);
        for (field, value) in [
            ("compositionStatus", &reading.composition_status),
            (
                "associativityUnderObservationStatus",
                &reading.associativity_under_observation_status,
            ),
            (
                "refinementAbstractionCompatibility",
                &reading.refinement_abstraction_compatibility,
            ),
            ("replacementEquivalence", &reading.replacement_equivalence),
            ("protectionIdempotence", &reading.protection_idempotence),
            ("runtimeLocalization", &reading.runtime_localization),
            ("migrationCompatibility", &reading.migration_compatibility),
            ("reverseInvolution", &reading.reverse_involution),
            ("repairMonotonicity", &reading.repair_monotonicity),
            (
                "synthesisNoSolutionBoundary",
                &reading.synthesis_no_solution_boundary,
            ),
        ] {
            push_blank(
                &mut examples,
                &format!("{} {field}", reading.reading_id),
                value,
            );
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.path_signature_trajectory_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.path_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        push_blank(
            &mut examples,
            &format!("{} pathCostProxy", reading.reading_id),
            &reading.path_cost_proxy,
        );
        push_blank(
            &mut examples,
            &format!("{} trajectoryCoverageBoundary", reading.reading_id),
            &reading.trajectory_coverage_boundary,
        );
    }
    for reading in &packet.homotopy_order_sensitivity_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        push_blank(
            &mut examples,
            &format!("{} operationOrderSensitivity", reading.reading_id),
            &reading.operation_order_sensitivity,
        );
        push_blank(
            &mut examples,
            &format!(
                "{} selectedObservationPreservationStatus",
                reading.reading_id
            ),
            &reading.selected_observation_preservation_status,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.diagram_fillability_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.diagram_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.diagram_family);
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        push_blank(
            &mut examples,
            &format!("{} missingFillerKind", reading.reading_id),
            &reading.missing_filler_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.local_curvature_diagram_readings {
        push_blank(&mut examples, &reading.diagram_id, &reading.law_ref);
        push_blank(
            &mut examples,
            &format!("{} obstructionRef", reading.diagram_id),
            &reading.obstruction_ref,
        );
        if reading.curvature_status != "nonConclusion"
            && (reading.curvature_value <= 0 || reading.signature_axis_refs.is_empty())
        {
            examples.push(generic_validation_example(
                &reading.diagram_id,
                &reading.curvature_value.to_string(),
                "local curvature diagram must carry positive curvature and signature axis refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} diagramReading", reading.diagram_id),
            &reading.diagram_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} fillingBoundary", reading.diagram_id),
            &reading.filling_boundary,
        );
    }
    for reading in &packet.three_layer_flatness_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.static_status);
        push_blank(&mut examples, &reading.reading_id, &reading.runtime_status);
        push_blank(&mut examples, &reading.reading_id, &reading.semantic_status);
        push_blank(
            &mut examples,
            &format!("{} nonImplicationReading", reading.reading_id),
            &reading.non_implication_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.observation_projection_readings {
        if reading.observed_atom_families.is_empty() || reading.observed_atom_family_count == 0 {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "observedAtomFamilies",
                "observation projection must report observed atom families",
            ));
        }
        if reading.coarse_projection_risks.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "coarseProjectionRisks",
                "observation projection must record projection loss risks",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} reconstructionRisk", reading.reading_id),
            &reading.reconstruction_risk,
        );
        if reading.forgotten_coordinates.is_empty()
            && reading.observation_collision_pairs.is_empty()
            && reading.collapsed_atom_family_candidates.is_empty()
            && reading.hidden_atom_family_hints.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "observationProjectionExpansion",
                "observation projection must record collisions, collapsed candidates, hidden hints, or forgotten coordinates",
            ));
        }
        push_blank(&mut examples, &reading.reading_id, &reading.reading);
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.state_transition_algebra_readings {
        if reading.required_relations.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "requiredRelations",
                "state transition algebra must record required relations",
            ));
        }
        push_blank(&mut examples, &reading.reading_id, &reading.reading);
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.reading_id),
            &reading.recommended_next_action,
        );
    }
    for reading in &packet.operation_invariant_galois_readings {
        if reading.invariant_family_refs.is_empty() && reading.operation_family_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "invariant/operation refs",
                "operation-invariant Galois reading must carry invariant or operation family refs",
            ));
        }
        push_blank(&mut examples, &reading.reading_id, &reading.reading);
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.split_readiness_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.molecule_ref);
        push_blank(&mut examples, &reading.reading_id, &reading.status);
        if !(0..=100).contains(&reading.readiness_score) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.readiness_score.to_string(),
                "split readiness score must stay in 0..=100",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} recommendedBoundaryOperation", reading.reading_id),
            &reading.recommended_boundary_operation,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    let surface = &packet.structural_reading_review_surface;
    push_blank(
        &mut examples,
        &surface.surface_id,
        &surface.current_state_reading,
    );
    if surface.connected_reading_refs.is_empty() {
        examples.push(generic_validation_example(
            &surface.surface_id,
            "connectedReadingRefs",
            "structural reading review surface must connect the AAT reading families",
        ));
    }
    if surface.review_focus.len() < 4 {
        examples.push(generic_validation_example(
            &surface.surface_id,
            "reviewFocus",
            "structural reading review surface must expose a multi-axis review guide",
        ));
    }
    if !surface
        .current_state_reading
        .contains("current architecture state")
    {
        examples.push(generic_validation_example(
            &surface.surface_id,
            &surface.current_state_reading,
            "structural reading review surface must frame ArchSig as current-state telemetry",
        ));
    }
    push_blank(
        &mut examples,
        &format!("{} evidenceBoundary", surface.surface_id),
        &surface.evidence_boundary,
    );
    check_from_examples(
        "archsig-analysis-packet-aat-structural-readings",
        "packet exposes representation strength, curvature, layer flatness, projection, transition algebra, Galois, and split readiness readings",
        examples,
        "fail",
    )
}

fn check_current_state_evolution_boundary(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let boundary = &packet.current_state_evolution_boundary;
    let mut examples = Vec::new();
    push_blank(
        &mut examples,
        &boundary.boundary_id,
        &boundary.archsig_current_state_scope,
    );
    push_blank(
        &mut examples,
        &boundary.boundary_id,
        &boundary.fieldsig_evolution_scope,
    );
    if boundary.handoff_artifact_ref != ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            &boundary.boundary_id,
            &boundary.handoff_artifact_ref,
            "current-state/evolution boundary must preserve archsig-analysis-packet-v0 handoff",
        ));
    }
    if !boundary
        .archsig_current_state_scope
        .contains("current AAT structural state")
    {
        examples.push(generic_validation_example(
            &boundary.boundary_id,
            &boundary.archsig_current_state_scope,
            "ArchSig scope must be current AAT structural state",
        ));
    }
    if !boundary
        .fieldsig_evolution_scope
        .contains("PR, diff, change-vector")
    {
        examples.push(generic_validation_example(
            &boundary.boundary_id,
            &boundary.fieldsig_evolution_scope,
            "FieldSig scope must retain PR / diff / change-vector evolution",
        ));
    }
    for required in ["PR diff", "forecast correctness", "raw ArchMap"] {
        if !boundary
            .forbidden_readings
            .iter()
            .any(|reading| reading.contains(required))
        {
            examples.push(generic_validation_example(
                &boundary.boundary_id,
                required,
                "current-state/evolution boundary must retain forbidden readings",
            ));
        }
    }
    push_blank(
        &mut examples,
        &format!("{} evidenceBoundary", boundary.boundary_id),
        &boundary.evidence_boundary,
    );
    check_from_examples(
        "archsig-fieldsig-current-state-evolution-boundary",
        "packet preserves ArchSig current-state and FieldSig evolution responsibilities",
        examples,
        "fail",
    )
}

fn check_law_relative_analysis(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let molecule_ids = set(packet
        .molecule_readings
        .iter()
        .map(|reading| reading.molecule_reading_id.as_str()));
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "obstructionCircuits[].obstructionCircuitId",
        duplicates(
            packet
                .obstruction_circuits
                .iter()
                .map(|circuit| circuit.obstruction_circuit_id.as_str()),
        ),
    ));
    for circuit in &packet.obstruction_circuits {
        push_blank(
            &mut examples,
            &circuit.obstruction_circuit_id,
            &circuit.law_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} witnessRuleRef", circuit.obstruction_circuit_id),
            &circuit.witness_rule_ref,
        );
        if circuit.signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "signatureAxisRefs",
                "obstruction circuit must declare affected signature axes",
            ));
        }
        for axis_ref in &circuit.signature_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &circuit.obstruction_circuit_id,
                    axis_ref,
                    "obstruction circuit references an unknown signature axis",
                ));
            }
        }
        for molecule_ref in &circuit.molecule_reading_refs {
            if !molecule_ids.contains(molecule_ref.as_str()) {
                examples.push(generic_validation_example(
                    &circuit.obstruction_circuit_id,
                    molecule_ref,
                    "obstruction circuit references an unknown molecule reading",
                ));
            }
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", circuit.obstruction_circuit_id),
            &circuit.evidence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceSummary", circuit.obstruction_circuit_id),
            &circuit.evidence_summary,
        );
        if circuit.missing_evidence.is_empty() || has_blank(&circuit.missing_evidence) {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "missingEvidence",
                "obstruction circuit must carry child-level missing evidence boundary",
            ));
        }
        if circuit.excluded_readings.is_empty() || has_blank(&circuit.excluded_readings) {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "excludedReadings",
                "obstruction circuit must carry child-level excluded readings boundary",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-law-relative-obstructions",
        "obstruction circuits are LawPolicy-relative and cross-reference molecule and signature readings",
        examples,
        "fail",
    )
}

fn check_signature_and_flatness(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "signatureAxes[].signatureAxisId",
        duplicates(
            packet
                .signature_axes
                .iter()
                .map(|axis| axis.signature_axis_id.as_str()),
        ),
    ));
    for axis in &packet.signature_axes {
        push_blank(&mut examples, &axis.signature_axis_id, &axis.law_ref);
        push_blank(
            &mut examples,
            &format!("{} axisRef", axis.signature_axis_id),
            &axis.axis_ref,
        );
        if axis.exactness_assumptions.is_empty() || has_blank(&axis.exactness_assumptions) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "exactnessAssumptions",
                "signature axis must declare exactness assumptions",
            ));
        }
        if axis.coverage_status.trim().is_empty() {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "coverageStatus",
                "signature axis must keep coverage status explicit",
            ));
        }
        if axis.missing_evidence.is_empty() || has_blank(&axis.missing_evidence) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "missingEvidence",
                "signature axis must carry child-level missing evidence boundary",
            ));
        }
        if axis.excluded_readings.is_empty() || has_blank(&axis.excluded_readings) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "excludedReadings",
                "signature axis must carry child-level excluded readings boundary",
            ));
        }
    }
    for axis_ref in packet
        .flatness_reading
        .zero_signature_axis_refs
        .iter()
        .chain(packet.flatness_reading.nonzero_signature_axis_refs.iter())
    {
        if !axis_ids.contains(axis_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.flatness_reading.reading_id,
                axis_ref,
                "flatness reading references an unknown signature axis",
            ));
        }
    }
    push_blank(
        &mut examples,
        "flatnessReading.evidenceBoundary",
        &packet.flatness_reading.evidence_boundary,
    );
    check_from_examples(
        "archsig-analysis-packet-signature-and-flatness",
        "signature axes and flatness reading preserve coverage and exactness boundaries",
        examples,
        "fail",
    )
}

fn check_repair_candidates(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let obstruction_ids = set(packet
        .obstruction_circuits
        .iter()
        .map(|circuit| circuit.obstruction_circuit_id.as_str()));
    let mut examples = Vec::new();
    for repair in &packet.repair_operation_candidates {
        if repair.target_obstruction_refs.is_empty() {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "targetObstructionRefs",
                "repair operation candidate must name target obstructions",
            ));
        }
        for obstruction_ref in &repair.target_obstruction_refs {
            if !obstruction_ids.contains(obstruction_ref.as_str()) {
                examples.push(generic_validation_example(
                    &repair.repair_operation_candidate_id,
                    obstruction_ref,
                    "repair candidate references an unknown obstruction circuit",
                ));
            }
        }
        if repair.preserved_invariants.is_empty() || has_blank(&repair.preserved_invariants) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "preservedInvariants",
                "repair candidate must declare preserved invariants",
            ));
        }
        if repair.preconditions.is_empty() || has_blank(&repair.preconditions) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "preconditions",
                "repair candidate must declare preconditions",
            ));
        }
        if repair.transfer_risks.is_empty() || has_blank(&repair.transfer_risks) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "transferRisks",
                "repair candidate must retain transfer risks",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", repair.repair_operation_candidate_id),
            &repair.evidence_boundary,
        );
        if repair.missing_evidence.is_empty() || has_blank(&repair.missing_evidence) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "missingEvidence",
                "repair candidate must carry child-level missing evidence boundary",
            ));
        }
        if repair.excluded_readings.is_empty() || has_blank(&repair.excluded_readings) {
            examples.push(generic_validation_example(
                &repair.repair_operation_candidate_id,
                "excludedReadings",
                "repair candidate must carry child-level excluded readings boundary",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-repair-operation-boundary",
        "repair operation candidates preserve invariant, precondition, transfer risk, and evidence boundaries",
        examples,
        "fail",
    )
}

fn check_llm_interpretation_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "evidenceBoundary", &packet.evidence_boundary);
    if packet.interpretation_notes_for_llm.is_empty()
        || has_blank(&packet.interpretation_notes_for_llm)
    {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "interpretationNotesForLLM",
            "packet must retain LLM-facing interpretation notes",
        ));
    }
    if packet.excluded_readings.is_empty() || has_blank(&packet.excluded_readings) {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "excludedReadings",
            "packet must retain excluded readings",
        ));
    }
    if packet
        .llm_interpretation_packet
        .structural_reading_review_summary
        .is_empty()
    {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "llmInterpretationPacket.structuralReadingReviewSummary",
            "LLM interpretation packet must summarize structural reading review surface",
        ));
    }
    if packet
        .llm_interpretation_packet
        .current_state_evolution_boundary_summary
        .is_empty()
    {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "llmInterpretationPacket.currentStateEvolutionBoundarySummary",
            "LLM interpretation packet must summarize current-state/evolution boundary",
        ));
    }
    for (field, is_empty) in [
        (
            "llmInterpretationPacket.measurementExpansionSummary",
            packet
                .llm_interpretation_packet
                .measurement_expansion_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.atomSupportAxisSummary",
            packet
                .llm_interpretation_packet
                .atom_support_axis_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.atomCompatibilitySummary",
            packet
                .llm_interpretation_packet
                .atom_compatibility_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.lawUniverseCoverageSummary",
            packet
                .llm_interpretation_packet
                .law_universe_coverage_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.featureExtensionFormulaSummary",
            packet
                .llm_interpretation_packet
                .feature_extension_formula_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.operationCalculusLawSummary",
            packet
                .llm_interpretation_packet
                .operation_calculus_law_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.pathSignatureTrajectorySummary",
            packet
                .llm_interpretation_packet
                .path_signature_trajectory_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.homotopyOrderSensitivitySummary",
            packet
                .llm_interpretation_packet
                .homotopy_order_sensitivity_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.diagramFillabilitySummary",
            packet
                .llm_interpretation_packet
                .diagram_fillability_summary
                .is_empty(),
        ),
    ] {
        if is_empty {
            examples.push(generic_validation_example(
                &packet.analysis_id,
                field,
                "LLM interpretation packet must summarize v0.3.0 measurement expansion readings",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-llm-interpretation-surface",
        "packet carries evidence boundary, excluded readings, and LLM interpretation notes",
        examples,
        "fail",
    )
}

fn check_non_conclusions(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let present = packet
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let examples = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !present.contains(**required))
        .map(|required| {
            generic_validation_example(
                &packet.analysis_id,
                required,
                "missing required ArchSig analysis packet non-conclusion",
            )
        })
        .collect();
    check_from_examples(
        "archsig-analysis-packet-non-conclusion-boundary",
        "packet keeps theorem, global truth, completeness, score, flatness, and repair boundaries explicit",
        examples,
        "fail",
    )
}

fn selected_laws_for_atom_refs(
    law_policy: &LawPolicyDocumentV0,
    archmap: &ArchMapDocumentV0,
    atom_refs: &[String],
) -> Vec<String> {
    let atom_families = atom_refs
        .iter()
        .filter_map(|atom_ref| {
            archmap
                .atom_observations
                .iter()
                .find(|atom| atom.atom_observation_id == *atom_ref)
        })
        .map(|atom| atom.atom_family.to_ascii_lowercase())
        .collect::<BTreeSet<_>>();
    let mut law_refs = law_policy
        .selected_laws
        .iter()
        .filter(|law| {
            law.applies_to_atom_families.iter().any(|family| {
                atom_families.contains(&family.to_ascii_lowercase())
                    || atom_families.iter().any(|observed| {
                        observed.contains(&family.to_ascii_lowercase())
                            || family.to_ascii_lowercase().contains(observed)
                    })
            })
        })
        .map(|law| law.law_id.clone())
        .collect::<Vec<_>>();
    if law_refs.is_empty() {
        law_refs = law_policy
            .selected_laws
            .iter()
            .map(|law| law.law_id.clone())
            .collect();
    }
    law_refs.sort();
    law_refs.dedup();
    law_refs
}

fn matching_atom_refs_for_witness(
    archmap: &ArchMapDocumentV0,
    witness_rule: &LawPolicyWitnessRuleV0,
) -> Vec<String> {
    let mut refs = archmap
        .atom_observations
        .iter()
        .filter(|atom| {
            witness_rule
                .required_atom_families
                .iter()
                .any(|family| family_matches(atom.atom_family.as_str(), family.as_str()))
        })
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    refs.extend(
        archmap
            .semantic_observations
            .iter()
            .filter(|semantic| {
                witness_rule.required_atom_families.iter().any(|family| {
                    family_matches(semantic.semantic_family.as_str(), family.as_str())
                        || family_matches(semantic.predicate.as_str(), family.as_str())
                })
            })
            .map(|semantic| semantic.semantic_observation_id.clone()),
    );
    refs.sort();
    refs.dedup();
    refs
}

fn concern_supports_witness(concern_family: &str, witness_rule: &LawPolicyWitnessRuleV0) -> bool {
    let concern = concern_family.to_ascii_lowercase();
    let witness = witness_rule.witness_kind.to_ascii_lowercase();
    (concern.contains("missing")
        && (witness.contains("mismatch") || witness.contains("noncommutation")))
        || ((concern.contains("semantic") || concern.contains("missing"))
            && witness_rule
                .law_ref
                .to_ascii_lowercase()
                .contains("semantic"))
}

fn witness_constructible(
    witness_rule: &LawPolicyWitnessRuleV0,
    atom_refs: &[String],
    molecule_refs: &[String],
    concern_refs: &[String],
) -> bool {
    if witness_rule.required_atom_families.is_empty() {
        return !molecule_refs.is_empty() || !concern_refs.is_empty();
    }
    let required_count = witness_rule.required_atom_families.len();
    atom_refs.len() >= required_count
        || (!atom_refs.is_empty() && !molecule_refs.is_empty() && !concern_refs.is_empty())
        || (witness_rule
            .witness_kind
            .to_ascii_lowercase()
            .contains("mismatch")
            && !concern_refs.is_empty())
}

fn obstruction_circuit(
    definition: &LawPolicyObstructionCircuitDefinitionV0,
    witness_rule: &LawPolicyWitnessRuleV0,
    atom_observation_refs: Vec<String>,
    molecule_reading_refs: Vec<String>,
    concern_hint_refs: Vec<String>,
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
) -> ArchSigObstructionCircuitV0 {
    ArchSigObstructionCircuitV0 {
        obstruction_circuit_id: format!("{}:computed", definition.obstruction_circuit_id),
        law_ref: definition.law_ref.clone(),
        witness_rule_ref: definition.witness_rule_ref.clone(),
        circuit_kind: definition.circuit_kind.clone(),
        atom_observation_refs,
        molecule_reading_refs,
        concern_hint_refs,
        signature_axis_refs: signature_axis_refs_for_obstruction(definition),
        minimality_reading: definition.minimality_reading.clone(),
        evidence_summary: format!(
            "constructed by witness rule {} from observed ArchMap atoms and LawPolicy molecule boundaries",
            witness_rule.witness_rule_id
        ),
        evidence_boundary:
            "computed ArchSig witness under selected LawPolicy; concern hints are auxiliary evidence only"
                .to_string(),
        missing_evidence: obstruction_missing_evidence(archmap, law_policy, definition, witness_rule),
        excluded_readings: obstruction_excluded_readings(law_policy),
        interpretation_notes_for_llm: vec![
            "Explain this obstruction as selected LawPolicy-relative.".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn archmap_gap_missing_evidence(archmap: &ArchMapDocumentV0) -> Vec<String> {
    archmap
        .observation_gaps
        .iter()
        .map(|gap| format!("{}: {}", gap.gap_id, gap.reason))
        .collect()
}

fn coverage_missing_evidence_for_law(
    law_policy: &LawPolicyDocumentV0,
    law_ref: &str,
) -> Vec<String> {
    law_policy
        .coverage_requirements
        .iter()
        .filter(|requirement| {
            requirement.applies_to_law_refs.is_empty()
                || requirement
                    .applies_to_law_refs
                    .iter()
                    .any(|ref_id| ref_id == law_ref)
        })
        .map(|requirement| {
            format!(
                "{}: {}",
                requirement.coverage_requirement_id, requirement.missing_coverage_behavior
            )
        })
        .collect()
}

fn boundary_or_no_missing_evidence(mut values: Vec<String>, context: &str) -> Vec<String> {
    values.sort();
    values.dedup();
    if values.is_empty() {
        vec![format!(
            "no child-level missing evidence recorded for {context} inside selected ArchMap and LawPolicy; this is not global completeness"
        )]
    } else {
        values
    }
}

fn child_excluded_readings(law_policy: &LawPolicyDocumentV0) -> Vec<String> {
    let mut values = law_policy.excluded_readings.clone();
    values.extend(
        law_policy
            .exactness_assumptions
            .iter()
            .map(|assumption| format!("exactness-limited: {assumption}")),
    );
    values.extend([
        "single architecture quality score".to_string(),
        "global architecture lawfulness".to_string(),
        "automatic repair safety".to_string(),
    ]);
    values.sort();
    values.dedup();
    values
}

fn obstruction_missing_evidence(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    definition: &LawPolicyObstructionCircuitDefinitionV0,
    witness_rule: &LawPolicyWitnessRuleV0,
) -> Vec<String> {
    let mut values = archmap_gap_missing_evidence(archmap);
    values.extend(coverage_missing_evidence_for_law(
        law_policy,
        &definition.law_ref,
    ));
    if !witness_rule.missing_evidence_behavior.trim().is_empty() {
        values.push(format!(
            "{}: {}",
            witness_rule.witness_rule_id, witness_rule.missing_evidence_behavior
        ));
    }
    boundary_or_no_missing_evidence(values, &definition.obstruction_circuit_id)
}

fn obstruction_excluded_readings(law_policy: &LawPolicyDocumentV0) -> Vec<String> {
    child_excluded_readings(law_policy)
}

fn signature_axis_missing_evidence(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
    definition: &LawPolicySignatureAxisDefinitionV0,
) -> Vec<String> {
    let mut values = archmap_gap_missing_evidence(archmap);
    values.extend(coverage_missing_evidence_for_law(
        law_policy,
        &definition.law_ref,
    ));
    boundary_or_no_missing_evidence(values, &definition.signature_axis_id)
}

fn signature_axis_excluded_readings(
    law_policy: &LawPolicyDocumentV0,
    definition: &LawPolicySignatureAxisDefinitionV0,
) -> Vec<String> {
    let mut values = child_excluded_readings(law_policy);
    if !definition.coverage_boundary.trim().is_empty() {
        values.push(format!(
            "{} coverage boundary: {}",
            definition.signature_axis_id, definition.coverage_boundary
        ));
    }
    values.sort();
    values.dedup();
    values
}

fn repair_candidate_missing_evidence(
    archmap: &ArchMapDocumentV0,
    circuit: &ArchSigObstructionCircuitV0,
) -> Vec<String> {
    let mut values = archmap_gap_missing_evidence(archmap);
    values.extend(circuit.missing_evidence.clone());
    values.push(
        "implementation patch and verification evidence are not supplied by ArchSig analysis"
            .to_string(),
    );
    boundary_or_no_missing_evidence(values, &circuit.obstruction_circuit_id)
}

fn repair_candidate_excluded_readings(circuit: &ArchSigObstructionCircuitV0) -> Vec<String> {
    let mut values = circuit.excluded_readings.clone();
    values.extend([
        "causal forecast correctness".to_string(),
        "merge approval".to_string(),
        "automatic repair safety".to_string(),
    ]);
    values.sort();
    values.dedup();
    values
}

fn signature_axis_refs_for_obstruction(
    definition: &LawPolicyObstructionCircuitDefinitionV0,
) -> Vec<String> {
    definition
        .signature_axis_refs
        .iter()
        .map(|axis_ref| {
            if axis_ref.starts_with("sig-axis:") {
                axis_ref.clone()
            } else {
                format!("sig-{}", axis_ref)
            }
        })
        .collect()
}

fn coverage_summary(archmap: &ArchMapDocumentV0) -> Vec<String> {
    let mut summary = vec![
        format!("{} atom observations", archmap.atom_observations.len()),
        format!(
            "{} molecule observations",
            archmap.molecule_observations.len()
        ),
        format!(
            "{} semantic observations",
            archmap.semantic_observations.len()
        ),
    ];
    if archmap.observation_gaps.is_empty() {
        summary.push("no observation gaps reported".to_string());
    } else {
        summary.push(format!(
            "{} observation gaps preserved as gaps",
            archmap.observation_gaps.len()
        ));
    }
    summary
}

fn repair_preconditions(archmap: &ArchMapDocumentV0) -> Vec<String> {
    let mut preconditions = vec!["human review selects a repair operation".to_string()];
    preconditions.extend(
        archmap
            .observation_gaps
            .iter()
            .map(|gap| format!("resolve or explicitly accept coverage gap {}", gap.gap_id)),
    );
    preconditions
}

fn all_atom_refs(archmap: &ArchMapDocumentV0) -> Vec<String> {
    archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_observation_id.clone())
        .collect()
}

fn unique_strings(values: impl Iterator<Item = String>) -> Vec<String> {
    values.collect::<BTreeSet<_>>().into_iter().collect()
}

fn preserved_invariants_for_repair(
    signature_axes: &[ArchSigSignatureAxisReadingV0],
) -> Vec<String> {
    let invariants = signature_axes
        .iter()
        .filter(|axis| axis.value == 0)
        .map(|axis| format!("preserve zero reading for {}", axis.signature_axis_id))
        .collect::<Vec<_>>();
    if invariants.is_empty() {
        vec!["preserve existing observed atom configuration boundaries".to_string()]
    } else {
        invariants
    }
}

fn atom_source_refs_by_id(archmap: &ArchMapDocumentV0) -> BTreeMap<String, Vec<String>> {
    archmap
        .atom_observations
        .iter()
        .map(|atom| {
            (
                atom.atom_observation_id.clone(),
                atom.source_refs
                    .iter()
                    .map(source_ref_label)
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>(),
            )
        })
        .collect()
}

fn source_ref_label(source_ref: &ArchMapSourceRef) -> String {
    source_ref
        .artifact_id
        .clone()
        .or_else(|| source_ref.path.clone())
        .unwrap_or_else(|| source_ref.kind.clone())
}

fn family_matches(observed: &str, required: &str) -> bool {
    let observed = observed.to_ascii_lowercase();
    let required = required.to_ascii_lowercase();
    observed == required || observed.contains(&required) || required.contains(&observed)
}

fn stable_id(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() {
                ch.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect::<String>()
        .split('-')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("-")
}

fn artifact_ref(
    artifact_id: &str,
    artifact_kind: &str,
    schema_version: &str,
    path: Option<&str>,
) -> ArchSigAnalysisArtifactRefV0 {
    ArchSigAnalysisArtifactRefV0 {
        artifact_id: artifact_id.to_string(),
        artifact_kind: artifact_kind.to_string(),
        schema_version: schema_version.to_string(),
        path: path.map(|value| value.to_string()),
        content_hash: None,
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
    fn static_archsig_analysis_packet_validates() {
        let packet = static_archsig_analysis_packet();
        let report = validate_archsig_analysis_packet_report(&packet, "archsig-analysis.json");
        assert_eq!(
            report.schema_version,
            ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.obstruction_circuit_count, 1);
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-non-conclusion-boundary" && check.result == "pass"
        }));
    }

    #[test]
    fn missing_packet_non_conclusion_fails() {
        let mut packet = static_archsig_analysis_packet();
        packet.non_conclusions.clear();
        let report = validate_archsig_analysis_packet_report(&packet, "bad-analysis.json");
        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-non-conclusion-boundary" && check.result == "fail"
        }));
    }

    #[test]
    fn repair_without_preconditions_fails() {
        let mut packet = static_archsig_analysis_packet();
        packet.repair_operation_candidates[0].preconditions.clear();
        let report = validate_archsig_analysis_packet_report(&packet, "bad-analysis.json");
        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "archsig-analysis-packet-repair-operation-boundary"
                && check.result == "fail"
        }));
    }

    #[test]
    fn child_boundary_absence_fails_validation() {
        let mut packet = static_archsig_analysis_packet();
        packet.obstruction_circuits[0].missing_evidence.clear();
        packet.signature_axes[0].excluded_readings.clear();
        packet.repair_operation_candidates[0]
            .missing_evidence
            .clear();

        let report = validate_archsig_analysis_packet_report(&packet, "invalid.json");

        assert_eq!(report.summary.result, "fail");
        assert!(
            report.checks.iter().any(|check| {
                check.result == "fail"
                    && check.examples.iter().any(|example| {
                        example
                            .target
                            .as_deref()
                            .is_some_and(|target| target == "missingEvidence")
                            || example
                                .target
                                .as_deref()
                                .is_some_and(|target| target == "excludedReadings")
                    })
            }),
            "validation must reject missing child-level evidence boundaries"
        );
    }

    #[test]
    fn canonical_fixture_matches_static_analysis_packet() {
        let fixture: ArchSigAnalysisPacketV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/archsig_analysis_packet.json"
        ))
        .expect("ArchSig analysis packet fixture parses");
        assert_eq!(fixture, static_archsig_analysis_packet());
    }

    #[test]
    fn builds_packet_from_archmap_and_law_policy() {
        let archmap: ArchMapDocumentV0 =
            serde_json::from_str(include_str!("../tests/fixtures/minimal/archmap.json"))
                .expect("ArchMap fixture parses");
        let law_policy: LawPolicyDocumentV0 =
            serde_json::from_str(include_str!("../tests/fixtures/minimal/law_policy.json"))
                .expect("LawPolicy fixture parses");
        let packet = build_archsig_analysis_packet(
            &archmap,
            &law_policy,
            Some("archmap.json"),
            Some("law_policy.json"),
        );
        let report = validate_archsig_analysis_packet_report(&packet, "computed-analysis.json");
        assert_eq!(report.summary.result, "pass", "{:?}", report.checks);
        assert!(
            packet.obstruction_circuits.iter().any(|circuit| {
                circuit.law_ref == "law:semantic-contract-alignment"
                    && circuit
                        .concern_hint_refs
                        .contains(&"concern:missing-compensation".to_string())
            }),
            "{:?}",
            packet.obstruction_circuits
        );
        assert!(
            packet
                .signature_axes
                .iter()
                .any(
                    |axis| axis.signature_axis_id == "sig-axis:semantic-inconsistency"
                        && axis.value == 1
                )
        );
        assert!(
            packet
                .flatness_reading
                .blocked_by_coverage_gaps
                .contains(&"gap-runtime-user-db-trace".to_string())
        );
    }

    #[test]
    fn same_archmap_reanalyzes_with_different_law_policy() {
        let archmap: ArchMapDocumentV0 =
            serde_json::from_str(include_str!("../tests/fixtures/minimal/archmap.json"))
                .expect("ArchMap fixture parses");
        let mut law_policy: LawPolicyDocumentV0 =
            serde_json::from_str(include_str!("../tests/fixtures/minimal/law_policy.json"))
                .expect("LawPolicy fixture parses");
        law_policy.law_policy_id = "layer-only-law-policy-fixture".to_string();
        law_policy
            .selected_laws
            .retain(|law| law.law_id == "law:layer-respecting");
        law_policy
            .witness_rules
            .retain(|rule| rule.law_ref == "law:layer-respecting");
        law_policy
            .obstruction_circuit_definitions
            .retain(|definition| definition.law_ref == "law:layer-respecting");
        law_policy
            .signature_axis_definitions
            .retain(|axis| axis.law_ref == "law:layer-respecting");

        let packet = build_archsig_analysis_packet(&archmap, &law_policy, None, None);
        let report = validate_archsig_analysis_packet_report(&packet, "layer-only.json");
        assert_eq!(report.summary.result, "pass", "{:?}", report.checks);
        assert_eq!(packet.obstruction_circuits.len(), 0);
        assert!(
            packet
                .signature_axes
                .iter()
                .all(|axis| axis.value == 0 && axis.law_ref == "law:layer-respecting")
        );
        assert_eq!(
            packet.flatness_reading.selected_law_policy_ref,
            "layer-only-law-policy-fixture"
        );
    }
}
