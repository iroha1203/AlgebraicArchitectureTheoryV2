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
    ArchSigArchitectureStateV0, ArchSigAtomConfigurationSummaryV0, ArchSigBoundedJudgementV0,
    ArchSigChangeImpactReadingV0, ArchSigCouplingCohesionReadingV0, ArchSigDesignPressureReadingV0,
    ArchSigDesignPrincipleReadingV0, ArchSigFlatnessReadingV0, ArchSigInvariantFamilyReadingV0,
    ArchSigLawUniverseReadingV0, ArchSigLayerSplitV0, ArchSigLlmInterpretationPacketV0,
    ArchSigMoleculeReadingV0, ArchSigObstructionCircuitV0, ArchSigOperationDeltaReadingV0,
    ArchSigPathHomotopyDiagramReadingV0, ArchSigRepairOperationCandidateV0,
    ArchSigSignatureAxisReadingV0, ArchSigSpectralAnalysisReadingV0,
    ArchSigSpectralDominantComponentV0, ArchSigSpectralMatrixShapeV0, ArchSigSpectralValueV0,
    ArchSigWorkflowAtomFamilyCountV0, ArchSigWorkflowRiskAxisReadingV0,
    ArchSigWorkflowRiskReadingV0, LAW_POLICY_SCHEMA_VERSION, LawPolicyDocumentV0,
    LawPolicyObstructionCircuitDefinitionV0, LawPolicySignatureAxisDefinitionV0,
    LawPolicyWitnessRuleV0, ValidationCheck, ValidationExample,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 6] = [
    "ArchSig analysis packet is not a Lean theorem proof",
    "ArchSig analysis packet is not global architecture truth",
    "ArchSig analysis packet does not prove source extraction completeness",
    "signature axes are law-policy-relative, not universal quality scores",
    "flatness reading is blocked by coverage gaps and exactness assumptions",
    "repair operation candidates are not automatic safe refactorings",
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
    let path_homotopy_diagram_readings =
        build_path_homotopy_diagram_readings(archmap, &molecule_readings, &obstruction_circuits);
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
        design_principle_readings,
        flatness_reading,
        static_runtime_semantic_layer_split: build_layer_split(archmap),
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
