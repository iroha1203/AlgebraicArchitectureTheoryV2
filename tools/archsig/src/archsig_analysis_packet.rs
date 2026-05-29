use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION,
    ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION, ArchMapDocumentV0, ArchMapSourceRef,
    ArchSigAatConceptSurfaceV0, ArchSigAnalysisArtifactRefV0, ArchSigAnalysisPacketV0,
    ArchSigAnalysisPacketValidationInputV0, ArchSigAnalysisPacketValidationReportV0,
    ArchSigAnalysisPacketValidationSummaryV0, ArchSigAnalyticRepresentationV0,
    ArchSigArchitectureObjectProjectionV0, ArchSigArchitectureStateV0,
    ArchSigAtomConfigurationSummaryV0, ArchSigBoundedJudgementV0, ArchSigChangeImpactReadingV0,
    ArchSigCouplingCohesionReadingV0, ArchSigDesignPressureReadingV0,
    ArchSigDesignPrincipleReadingV0, ArchSigFlatnessReadingV0, ArchSigInvariantFamilyReadingV0,
    ArchSigLawUniverseReadingV0, ArchSigLayerSplitV0, ArchSigLlmInterpretationPacketV0,
    ArchSigMoleculeReadingV0, ArchSigObstructionCircuitV0, ArchSigOperationDeltaReadingV0,
    ArchSigPathHomotopyDiagramReadingV0, ArchSigRepairOperationCandidateV0,
    ArchSigSignatureAxisReadingV0, LAW_POLICY_SCHEMA_VERSION, LawPolicyDocumentV0,
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
    let design_principle_readings = build_design_principle_readings(
        archmap,
        &invariant_family_readings,
        &obstruction_circuits,
        &repair_operation_candidates,
    );
    let operation_deltas =
        build_operation_deltas(archmap, &repair_operation_candidates, &signature_axes);
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
