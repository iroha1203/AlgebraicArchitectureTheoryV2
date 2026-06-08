pub fn validate_archsig_analysis_packet_report(
    packet: &ArchSigAnalysisPacketV0,
    input_path: &str,
) -> ArchSigAnalysisPacketValidationReportV0 {
    let checks = vec![
        check_schema_version(packet),
        check_refs_and_identity(packet),
        check_north_star_aat_surfaces(packet),
        check_homotopy_complex_candidate_surface(packet),
        check_filler_architectural_hole_surface(packet),
        check_homotopy_holonomy_stokes_surface(packet),
        check_homotopy_distance_reading_surface(packet),
        check_architecture_homotopy_report_surface(packet),
        check_bounded_judgement_surface(packet),
        check_analytic_and_principle_surfaces(packet),
        check_spectral_analysis_surface(packet),
        check_spectral_mode_surface(packet),
        check_spectral_drilldown_surface(packet),
        check_curvature_support_surface(packet),
        check_curvature_transfer_surface(packet),
        check_architecture_spectrum_report_surface(packet),
        check_transfer_bridge_surface(packet),
        check_generated_middle_layer_surface(packet),
        check_part4_distance_foundation_surface(packet),
        check_part4_distance_coverage_ledger_surface(packet),
        check_atom_distance_reading_surface(packet),
        check_configuration_distance_reading_surface(packet),
        check_signature_distance_reading_surface(packet),
        check_operation_distance_reading_surface(packet),
        check_obstruction_measure_reading_surface(packet),
        check_curvature_mass_reading_surface(packet),
        check_representation_metric_reading_surface(packet),
        check_aat_structural_reading_surfaces(packet),
        check_current_state_evolution_boundary(packet),
        check_operation_square_trace_surface(packet),
        check_axis_wise_defect_ami_surface(packet),
        check_nonzero_monodromy_witness_surface(packet),
        check_feature_boundary_residual_surface(packet),
        check_feature_extension_diagnosis_surface(packet),
        check_monodromy_boundary_schema_foundation(packet),
        check_measurement_depth(packet),
        check_proxy_regression_guardrails(packet),
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
        generated_atom_shape_count: packet.generated_atom_shapes.len(),
        generated_molecule_count: packet.generated_molecules.len(),
        generated_law_input_count: packet.generated_law_inputs.len(),
        generated_obstruction_count: packet.generated_obstructions.len(),
        generated_repair_target_count: packet.generated_repair_targets.len(),
        viewer_distance_input_count: packet.viewer_distance_inputs.len(),
        part4_supporting_distance_count: packet
            .part4_distance_foundation
            .supporting_distances
            .len(),
        atom_distance_reading_count: packet.atom_distance_readings.len(),
        configuration_distance_reading_count: packet.configuration_distance_readings.len(),
        signature_distance_reading_count: packet.signature_distance_readings.len(),
        operation_distance_reading_count: packet.operation_distance_readings.len(),
        obstruction_measure_reading_count: packet.obstruction_measure_readings.len(),
        curvature_mass_reading_count: packet.curvature_mass_readings.len(),
        obstruction_circuit_count: packet.obstruction_circuits.len(),
        signature_axis_count: packet.signature_axes.len(),
        analytic_representation_count: packet.analytic_representations.len(),
        coupling_cohesion_reading_count: packet.coupling_cohesion_readings.len(),
        spectral_analysis_reading_count: packet.spectral_analysis_readings.len(),
        spectral_mode_reading_count: packet.spectral_mode_readings.len(),
        spectral_drilldown_reading_count: packet.spectral_drilldown_readings.len(),
        curvature_support_reading_count: packet.curvature_support_readings.len(),
        curvature_transfer_reading_count: packet.curvature_transfer_readings.len(),
        transfer_bridge_reading_count: packet.transfer_bridge_readings.len(),
        atom_support_axis_reading_count: packet.atom_support_axis_readings.len(),
        atom_compatibility_reading_count: packet.atom_compatibility_readings.len(),
        law_universe_coverage_reading_count: packet.law_universe_coverage_readings.len(),
        feature_extension_formula_reading_count: packet.feature_extension_formula_readings.len(),
        operation_calculus_law_reading_count: packet.operation_calculus_law_readings.len(),
        path_signature_trajectory_reading_count: packet.path_signature_trajectory_readings.len(),
        homotopy_order_sensitivity_reading_count: packet.homotopy_order_sensitivity_readings.len(),
        diagram_fillability_reading_count: packet.diagram_fillability_readings.len(),
        axis_forgetting_risk_reading_count: packet.axis_forgetting_risk_readings.len(),
        observation_projection_fidelity_reading_count: packet
            .observation_projection_fidelity_readings
            .len(),
        atom_origin_closure_debt_reading_count: packet.atom_origin_closure_debt_readings.len(),
        effect_relation_algebra_reading_count: packet.effect_relation_algebra_readings.len(),
        synthesis_blockage_reading_count: packet.synthesis_blockage_readings.len(),
        operation_precondition_readiness_reading_count: packet
            .operation_precondition_readiness_readings
            .len(),
        path_multiplicity_loss_reading_count: packet.path_multiplicity_loss_readings.len(),
        signature_trajectory_homotopy_refutation_reading_count: packet
            .signature_trajectory_homotopy_refutation_readings
            .len(),
        homotopy_distance_reading_count: packet.homotopy_distance_readings.len(),
        bridge_split_obstruction_transfer_reading_count: packet
            .bridge_split_obstruction_transfer_readings
            .len(),
        representation_strength_reading_count: packet.representation_strength_readings.len(),
        representation_metric_reading_count: packet.representation_metric_readings.len(),
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
        surface_check_count: count_check_kind(&checks, "surface"),
        measurement_depth_check_count: count_check_kind(&checks, "measurement-depth"),
        proxy_regression_check_count: count_check_kind(&checks, "proxy-regression"),
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
        packet: None,
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

fn check_homotopy_complex_candidate_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let Some(complex) = packet.homotopy_complex_summary.as_ref() else {
        return check_from_examples(
            "archsig-analysis-packet-homotopy-complex-candidates",
            "packet exposes bounded homotopy complex, path pair candidates, and loop candidates",
            vec![generic_validation_example(
                &packet.analysis_id,
                "homotopyComplexSummary",
                "packet must expose a bounded homotopy complex summary",
            )],
            "fail",
        );
    };
    push_blank(
        &mut examples,
        "homotopyComplexSummary.complexId",
        &complex.complex_id,
    );
    push_blank(
        &mut examples,
        "homotopyComplexSummary.profileRef",
        &complex.profile_ref,
    );
    push_blank(
        &mut examples,
        "homotopyComplexSummary.status",
        &complex.status,
    );
    validate_packet_measurement_boundary(
        &mut examples,
        &complex.complex_id,
        &complex.measurement_status,
        &complex.reading_boundary,
    );
    if complex.selected_axis_refs.is_empty() || has_blank(&complex.selected_axis_refs) {
        examples.push(generic_validation_example(
            &complex.complex_id,
            "selectedAxisRefs",
            "homotopy complex must retain selected axes",
        ));
    }
    for (field, cells) in [
        ("zeroCells", &complex.zero_cells),
        ("oneCells", &complex.one_cells),
        ("twoCells", &complex.two_cells),
    ] {
        if cells.is_empty() {
            examples.push(generic_validation_example(
                &complex.complex_id,
                field,
                "homotopy complex must expose 0-cell / 1-cell / 2-cell summaries",
            ));
        }
        for cell in cells.iter() {
            push_blank(&mut examples, &format!("{field}[].cellId"), &cell.cell_id);
            push_blank(
                &mut examples,
                &format!("{} cellKind", cell.cell_id),
                &cell.cell_kind,
            );
            push_blank(
                &mut examples,
                &format!("{} status", cell.cell_id),
                &cell.status,
            );
            if cell.non_conclusions.is_empty() || has_blank(&cell.non_conclusions) {
                examples.push(generic_validation_example(
                    &cell.cell_id,
                    "nonConclusions",
                    "homotopy cells must keep non-conclusions explicit",
                ));
            }
        }
    }
    push_blank(
        &mut examples,
        "homotopyComplexSummary.coverageBoundary",
        &complex.coverage_boundary,
    );
    push_blank(
        &mut examples,
        "homotopyComplexSummary.evidenceBoundary",
        &complex.evidence_boundary,
    );
    if complex.non_conclusions.is_empty() || has_blank(&complex.non_conclusions) {
        examples.push(generic_validation_example(
            &complex.complex_id,
            "nonConclusions",
            "homotopy complex must keep non-conclusions explicit",
        ));
    }
    if packet.path_pair_candidates.is_empty() {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "pathPairCandidates",
            "packet must expose path pair candidates",
        ));
    }
    for candidate in &packet.path_pair_candidates {
        push_blank(
            &mut examples,
            "pathPairCandidates[].candidateId",
            &candidate.candidate_id,
        );
        push_blank(
            &mut examples,
            &format!("{} candidateSource", candidate.candidate_id),
            &candidate.candidate_source,
        );
        push_blank(
            &mut examples,
            &format!("{} status", candidate.candidate_id),
            &candidate.status,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &candidate.candidate_id,
            &candidate.measurement_status,
            &candidate.reading_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} pPathRef", candidate.candidate_id),
            &candidate.p_path_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} qPathRef", candidate.candidate_id),
            &candidate.q_path_ref,
        );
        if candidate.p_operation_sequence.is_empty() || candidate.q_operation_sequence.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "pOperationSequence/qOperationSequence",
                "path pair candidate must carry first-class operation sequences",
            ));
        }
        if candidate.endpoint_object_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "endpointObjectRefs",
                "path pair candidate must carry endpoint object refs",
            ));
        }
        if candidate.generator_candidate_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "generatorCandidateRefs",
                "path pair candidate must record selected homotopy generator candidates",
            ));
        }
        if candidate.shared_endpoint_refs.is_empty() || has_blank(&candidate.shared_endpoint_refs) {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "sharedEndpointRefs",
                "path pair candidate must keep endpoint refs traceable",
            ));
        }
        if candidate.source_refs.is_empty() && candidate.observation_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "sourceRefs/observationRefs",
                "path pair candidate must carry traceable refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", candidate.candidate_id),
            &candidate.coverage_boundary,
        );
        if candidate.non_conclusions.is_empty() || has_blank(&candidate.non_conclusions) {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "nonConclusions",
                "path pair candidate must keep non-conclusions explicit",
            ));
        }
    }
    if packet.loop_candidates.is_empty() {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "loopCandidates",
            "packet must expose loop candidates",
        ));
    }
    for candidate in &packet.loop_candidates {
        push_blank(&mut examples, "loopCandidates[].loopId", &candidate.loop_id);
        push_blank(
            &mut examples,
            &format!("{} pathPairRef", candidate.loop_id),
            &candidate.path_pair_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} status", candidate.loop_id),
            &candidate.status,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &candidate.loop_id,
            &candidate.measurement_status,
            &candidate.reading_boundary,
        );
        if candidate.path_refs.len() < 2 || has_blank(&candidate.path_refs) {
            examples.push(generic_validation_example(
                &candidate.loop_id,
                "pathRefs",
                "loop candidate must keep both path refs",
            ));
        }
        if candidate.endpoint_object_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.loop_id,
                "endpointObjectRefs",
                "loop candidate must preserve endpoint refs from its path pair",
            ));
        }
        if candidate.filler_candidate_refs.is_empty()
            && candidate.missing_filler_evidence.is_empty()
        {
            examples.push(generic_validation_example(
                &candidate.loop_id,
                "fillerCandidateRefs/missingFillerEvidence",
                "loop candidate must distinguish filler candidates from missing filler evidence",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", candidate.loop_id),
            &candidate.coverage_boundary,
        );
        if candidate.non_conclusions.is_empty() || has_blank(&candidate.non_conclusions) {
            examples.push(generic_validation_example(
                &candidate.loop_id,
                "nonConclusions",
                "loop candidate must keep non-conclusions explicit",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-homotopy-complex-candidates",
        "packet exposes bounded homotopy complex, path pair candidates, and loop candidates",
        examples,
        "fail",
    )
}

fn check_filler_architectural_hole_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let loop_ids = packet
        .loop_candidates
        .iter()
        .map(|candidate| candidate.loop_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let profile_absent = packet
        .homotopy_complex_summary
        .as_ref()
        .map(|summary| summary.status == "profileAbsent")
        .unwrap_or(false);
    if packet.filler_candidate_readings.is_empty() && !profile_absent {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "fillerCandidateReadings",
            "packet must expose filler candidate readings",
        ));
    }
    for reading in &packet.filler_candidate_readings {
        push_blank(
            &mut examples,
            "fillerCandidateReadings[].readingId",
            &reading.reading_id,
        );
        if !loop_ids.contains(reading.loop_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.loop_ref,
                "filler candidate reading must reference a known loop candidate",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} fillerKind", reading.reading_id),
            &reading.filler_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} status", reading.reading_id),
            &reading.status,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceStatus", reading.reading_id),
            &reading.evidence_status,
        );
        if reading.filling_condition_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "fillingConditionRefs",
                "filler candidate must name the selected filling condition",
            ));
        }
        if reading.measurement_status == "measured"
            && reading.measured_filler_evidence_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "measuredFillerEvidenceRefs",
                "measured filler candidate must carry source-backed filler evidence",
            ));
        }
        if reading.next_check_refs.is_empty() || has_blank(&reading.next_check_refs) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nextCheckRefs",
                "filler candidate reading must retain next checks",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "filler candidate reading must keep non-conclusions explicit",
            ));
        }
    }
    if packet.architectural_hole_readings.is_empty() {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "architecturalHoleReadings",
            "packet must expose architectural hole readings for unfilled loops",
        ));
    }
    for reading in &packet.architectural_hole_readings {
        push_blank(
            &mut examples,
            "architecturalHoleReadings[].readingId",
            &reading.reading_id,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        if !loop_ids.contains(reading.loop_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.loop_ref,
                "architectural hole reading must reference a known loop candidate",
            ));
        }
        if reading.missing_filler_evidence.is_empty() || has_blank(&reading.missing_filler_evidence)
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "missingFillerEvidence",
                "architectural hole reading must retain missing filler evidence",
            ));
        }
        if reading.selected_diagram_refs.is_empty()
            || reading.non_fillability_witness_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "selectedDiagramRefs/nonFillabilityWitnessRefs",
                "architectural hole must connect missing filler evidence to selected diagram and non-fillability witness refs",
            ));
        }
        if reading.next_check_refs.is_empty() || has_blank(&reading.next_check_refs) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nextCheckRefs",
                "architectural hole reading must retain next checks",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "architectural hole reading must keep non-conclusions explicit",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-filler-architectural-hole-surface",
        "packet distinguishes filler candidates from unfilled architectural holes and missing filler evidence",
        examples,
        "fail",
    )
}

fn check_homotopy_holonomy_stokes_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let loop_ids = packet
        .loop_candidates
        .iter()
        .map(|candidate| candidate.loop_id.as_str())
        .collect::<BTreeSet<_>>();
    let path_pair_ids = packet
        .path_pair_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.as_str())
        .collect::<BTreeSet<_>>();
    let holonomy_ids = packet
        .homotopy_holonomy_readings
        .iter()
        .map(|reading| reading.reading_id.as_str())
        .collect::<BTreeSet<_>>();
    let holonomy_by_id = packet
        .homotopy_holonomy_readings
        .iter()
        .map(|reading| (reading.reading_id.as_str(), reading))
        .collect::<BTreeMap<_, _>>();
    let mut examples = Vec::new();
    if packet.homotopy_holonomy_readings.is_empty() {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "homotopyHolonomyReadings",
            "packet must expose selected-axis homotopy holonomy readings",
        ));
    }
    for reading in &packet.homotopy_holonomy_readings {
        push_blank(
            &mut examples,
            "homotopyHolonomyReadings[].readingId",
            &reading.reading_id,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        if !path_pair_ids.contains(reading.path_pair_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.path_pair_ref,
                "homotopy holonomy reading must reference a known path pair candidate",
            ));
        }
        if !loop_ids.contains(reading.loop_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.loop_ref,
                "homotopy holonomy reading must reference a known loop candidate",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} axisRef", reading.reading_id),
            &reading.axis_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} distanceKind", reading.reading_id),
            &reading.distance_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} comparedContinuationSummary", reading.reading_id),
            &reading.compared_continuation_summary,
        );
        if reading.compared_continuation_refs.len() < 2 || reading.distance_input_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "comparedContinuationRefs/distanceInputRefs",
                "homotopy holonomy reading must connect mu_x to compared continuation refs and distance inputs",
            ));
        }
        if reading.value != 0 && reading.mu_defect_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "muDefectRefs",
                "nonzero homotopy holonomy reading must expose positive mu_x defect refs",
            ));
        }
        if reading.filler_refs.is_empty() && reading.missing_filler_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "fillerRefs/missingFillerRefs",
                "homotopy holonomy reading must record filler or missing filler refs",
            ));
        }
        if reading.measurement_status == "measured"
            && (reading.source_refs.is_empty() || reading.distance_input_refs.is_empty())
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "sourceRefs/distanceInputRefs",
                "measured holonomy must be computed from source-backed continuation comparison inputs",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "homotopy holonomy reading must keep non-conclusions explicit",
            ));
        }
    }
    if packet.stokes_style_readings.is_empty() {
        examples.push(generic_validation_example(
            &packet.analysis_id,
            "stokesStyleReadings",
            "packet must expose Stokes-style readings",
        ));
    }
    for reading in &packet.stokes_style_readings {
        push_blank(
            &mut examples,
            "stokesStyleReadings[].readingId",
            &reading.reading_id,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        if !loop_ids.contains(reading.loop_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.loop_ref,
                "Stokes-style reading must reference a known loop candidate",
            ));
        }
        for holonomy_ref in &reading.holonomy_reading_refs {
            if !holonomy_ids.contains(holonomy_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    holonomy_ref,
                    "Stokes-style reading must reference known holonomy readings",
                ));
            }
        }
        if reading.status == "filledNonzeroHolonomyReview"
            && reading.local_curvature_cell_candidates.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "localCurvatureCellCandidates",
                "filled nonzero holonomy readings must provide a local curvature review queue",
            ));
        }
        if reading.status == "filledNonzeroHolonomyReview" {
            let has_nonzero_holonomy = reading
                .holonomy_reading_refs
                .iter()
                .filter_map(|holonomy_ref| holonomy_by_id.get(holonomy_ref.as_str()).copied())
                .any(|holonomy| holonomy.value != 0 && holonomy.measurement_status == "measured");
            if !has_nonzero_holonomy || reading.filling_evidence_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    "holonomyReadingRefs/fillingEvidenceRefs",
                    "filled nonzero Stokes-style reading must be limited to measured filler plus measured nonzero holonomy",
                ));
            }
        }
        push_blank(
            &mut examples,
            &format!("{} localCurvatureCondition", reading.reading_id),
            &reading.local_curvature_condition,
        );
        if reading.status == "blockedByArchitecturalHole"
            && reading.non_fillability_witness_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonFillabilityWitnessRefs",
                "blocked Stokes-style reading must retain non-fillability witness refs",
            ));
        }
        if reading.review_queue_refs.is_empty() || has_blank(&reading.review_queue_refs) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "reviewQueueRefs",
                "Stokes-style reading must provide review queue refs",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "Stokes-style reading must keep non-conclusions explicit",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-homotopy-holonomy-stokes-surface",
        "packet reports selected-axis homotopy holonomy and bounded Stokes-style review queues",
        examples,
        "fail",
    )
}

fn check_homotopy_distance_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let distance_ids = packet
        .homotopy_distance_readings
        .iter()
        .map(|reading| reading.homotopy_distance_reading_id.as_str())
        .collect::<BTreeSet<_>>();
    if !packet.loop_candidates.is_empty() && packet.homotopy_distance_readings.is_empty() {
        examples.push(generic_validation_example(
            "homotopyDistanceReadings",
            "empty",
            "loop candidates must have Part IV homotopy distance readings",
        ));
    }
    for loop_candidate in &packet.loop_candidates {
        if loop_candidate.part4_distance_refs.is_empty()
            || loop_candidate
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &loop_candidate.loop_id,
                "part4DistanceRefs",
                "loop candidates must point to homotopy distance readings",
            ));
        }
    }
    for filler in &packet.filler_candidate_readings {
        if filler.part4_distance_refs.is_empty()
            || filler
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &filler.reading_id,
                "part4DistanceRefs",
                "filler candidates must retain Part IV filling cost refs",
            ));
        }
    }
    for hole in &packet.architectural_hole_readings {
        if hole.part4_distance_refs.is_empty()
            || hole
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &hole.reading_id,
                "part4DistanceRefs",
                "architectural holes must retain missing-filler distance refs",
            ));
        }
    }
    for reading in &packet.homotopy_distance_readings {
        for (field, value, prefix) in [
            ("homotopyDistance", &reading.homotopy_distance, "d_hom:"),
            ("fillingCost", &reading.filling_cost, "fill_cost:"),
            (
                "observationGapLowerBound",
                &reading.observation_gap_lower_bound,
                "lipschitzAssumption:",
            ),
            ("selectedDehnArea", &reading.selected_dehn_area, "Dehn_A:"),
        ] {
            check_curvature_distance_value(
                &mut examples,
                &reading.homotopy_distance_reading_id,
                field,
                value,
                prefix,
            );
        }
        if !reading.missing_filler_refs.is_empty()
            && matches!(reading.filling_cost.status.as_str(), "measured" | "zero")
        {
            examples.push(generic_validation_example(
                &reading.homotopy_distance_reading_id,
                "fillingCost",
                "missing filler evidence must not be reported as measured zero filling cost",
            ));
        }
        if reading.lipschitz_assumption_refs.is_empty()
            || !reading
                .evidence_boundary
                .contains("missing fillers are blockers")
        {
            examples.push(generic_validation_example(
                &reading.homotopy_distance_reading_id,
                "lipschitzAssumptionRefs/evidenceBoundary",
                "homotopy distance must retain lower-bound assumptions and missing-filler boundary",
            ));
        }
    }
    if let Some(report) = &packet.architecture_homotopy_report {
        if report.part4_distance_refs.is_empty()
            || report
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &report.report_id,
                "part4DistanceRefs",
                "ArchitectureHomotopyReport must retain Part IV homotopy distance refs",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-homotopy-distance-readings",
        "packet exposes Part IV homotopy distance, filling cost, observation-gap lower bound, and selected Dehn-style area without treating missing fillers as zero",
        examples,
        "fail",
    )
}

fn check_architecture_homotopy_report_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let Some(report) = packet.architecture_homotopy_report.as_ref() else {
        return check_from_examples(
            "archsig-analysis-packet-architecture-homotopy-report-surface",
            "packet exposes ArchitectureHomotopyReport with review focus and non-conclusions",
            vec![generic_validation_example(
                &packet.analysis_id,
                "architectureHomotopyReport",
                "packet with homotopy readings must include ArchitectureHomotopyReport",
            )],
            "fail",
        );
    };
    push_blank(
        &mut examples,
        "architectureHomotopyReport.reportId",
        &report.report_id,
    );
    push_blank(
        &mut examples,
        "architectureHomotopyReport.profileRef",
        &report.profile_ref,
    );
    push_blank(
        &mut examples,
        "architectureHomotopyReport.status",
        &report.status,
    );
    validate_packet_measurement_boundary(
        &mut examples,
        &report.report_id,
        &report.measurement_status,
        &report.reading_boundary,
    );
    if report.filled_loops.is_empty()
        && report.unfilled_loops.is_empty()
        && report.nonzero_holonomy_loops.is_empty()
    {
        examples.push(generic_validation_example(
            &report.report_id,
            "filledLoops/unfilledLoops/nonzeroHolonomyLoops",
            "ArchitectureHomotopyReport must expose loop reading buckets",
        ));
    }
    if report.aggregate_readings.is_empty() {
        examples.push(generic_validation_example(
            &report.report_id,
            "aggregateReadings",
            "ArchitectureHomotopyReport must expose bounded aggregate readings",
        ));
    }
    push_blank(
        &mut examples,
        "architectureHomotopyReport.measuredBoundary",
        &report.measured_boundary,
    );
    if report.recommended_review_focus.is_empty() || has_blank(&report.recommended_review_focus) {
        examples.push(generic_validation_example(
            &report.report_id,
            "recommendedReviewFocus",
            "ArchitectureHomotopyReport must provide next action focus",
        ));
    }
    for required in [
        "ArchitectureHomotopyReport is not a single architecture quality score",
        "Stokes-style readings are review queues, not theorem discharge",
    ] {
        if !report.non_conclusions.iter().any(|value| value == required) {
            examples.push(generic_validation_example(
                &report.report_id,
                required,
                "ArchitectureHomotopyReport is missing a required non-conclusion",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-architecture-homotopy-report-surface",
        "packet exposes ArchitectureHomotopyReport with review focus and non-conclusions",
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
    for reading in &packet.design_principle_readings {
        if !matches!(
            reading.status.as_str(),
            "preserved" | "stressed" | "unmeasured" | "notApplicable"
        ) {
            examples.push(generic_validation_example(
                &reading.principle_id,
                &reading.status,
                "design principle status must be preserved / stressed / unmeasured / notApplicable",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} witnessRuleRef", reading.principle_id),
            &reading.witness_rule_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} witnessStatus", reading.principle_id),
            &reading.witness_status,
        );
        if reading.status != "notApplicable" && reading.witness_evidence_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.principle_id,
                "witnessEvidenceRefs",
                "applicable design principle readings must retain principle-specific witness evidence refs",
            ));
        }
        if reading.status == "stressed" && reading.obstruction_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.principle_id,
                "obstructionRefs",
                "stressed design principle readings must point to principle-specific obstruction refs",
            ));
        }
        if reading.recommended_next_action
            == "turn stressed readings into source review questions or repair preconditions"
        {
            examples.push(generic_validation_example(
                &reading.principle_id,
                "recommendedNextAction",
                "design principle next action must be principle-specific",
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

fn check_spectral_analysis_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let required_families = BTreeSet::from([
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
        "packet exposes AAT spectral readings as bounded finite relation and measurement representations",
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

fn validate_packet_measurement_boundary(
    examples: &mut Vec<ValidationExample>,
    subject: &str,
    measurement_status: &str,
    boundary: &ArchSigMeasurementReadingBoundaryV0,
) {
    let allowed_statuses =
        BTreeSet::from(["measured", "proxy", "unmeasured", "blockedByCoverageGap"]);
    if !allowed_statuses.contains(measurement_status) {
        examples.push(generic_validation_example(
            subject,
            measurement_status,
            "measurementStatus must be measured, proxy, unmeasured, or blockedByCoverageGap",
        ));
    }
    push_blank(
        examples,
        &format!("{subject}.readingBoundary.readingStrength"),
        &boundary.reading_strength,
    );
    if boundary.zero_reflection_assumptions.is_empty()
        || has_blank(&boundary.zero_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            "readingBoundary.zeroReflectionAssumptions",
            "measurement reading boundary must declare zero-reflection assumptions",
        ));
    }
    if boundary.obstruction_reflection_assumptions.is_empty()
        || has_blank(&boundary.obstruction_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            "readingBoundary.obstructionReflectionAssumptions",
            "measurement reading boundary must declare obstruction-reflection assumptions",
        ));
    }
    if boundary.coverage_requirement_refs.is_empty()
        || has_blank(&boundary.coverage_requirement_refs)
    {
        examples.push(generic_validation_example(
            subject,
            "readingBoundary.coverageRequirementRefs",
            "measurement reading boundary must retain coverage requirement refs",
        ));
    }
    push_blank(
        examples,
        &format!("{subject}.readingBoundary.witnessCompletenessBoundary"),
        &boundary.witness_completeness_boundary,
    );
    let reading_strength = boundary.reading_strength.to_ascii_lowercase();
    if measurement_status == "measured" && reading_strength == "proxy" {
        examples.push(generic_validation_example(
            subject,
            &boundary.reading_strength,
            "proxy readingStrength cannot be reported with measurementStatus measured",
        ));
    }
}

fn check_curvature_support_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let signature_axis_ids = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let axis_refs = set(packet
        .signature_axes
        .iter()
        .map(|axis| axis.axis_ref.as_str()));
    let support_ids = packet
        .curvature_support_readings
        .iter()
        .flat_map(|reading| reading.witness_supports.iter())
        .map(|support| support.witness_support_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    if packet.curvature_support_readings.is_empty() {
        return check_from_examples(
            "archsig-analysis-packet-curvature-support-surface",
            "optional curvature support readings are absent",
            examples,
            "fail",
        );
    }
    examples.extend(duplicate_examples(
        "curvatureSupportReadings[].readingId",
        duplicates(
            packet
                .curvature_support_readings
                .iter()
                .map(|reading| reading.reading_id.as_str()),
        ),
    ));
    for reading in &packet.curvature_support_readings {
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.status,
                "curvature support status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} profileRef", reading.reading_id),
            &reading.profile_ref,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        if reading.witness_supports.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "witnessSupports",
                "curvature support reading must keep measured witness / axis rows traceable",
            ));
        }
        if reading.top_curvature_modes.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "topCurvatureModes",
                "curvature support reading must expose top mode source data",
            ));
        }
        if reading.witness_clusters.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "witnessClusters",
                "curvature support reading must expose witness cluster source data",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
        if reading.exactness_assumption_refs.is_empty()
            || has_blank(&reading.exactness_assumption_refs)
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "exactnessAssumptionRefs",
                "curvature support reading must keep exactness assumptions explicit",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} measurementBoundary", reading.reading_id),
            &reading.measurement_boundary,
        );
        if reading.missing_evidence.is_empty() || has_blank(&reading.missing_evidence) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "missingEvidence",
                "curvature support reading must distinguish unmeasured support from measured zero",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "curvature support reading must retain non-conclusions",
            ));
        }

        for support in &reading.witness_supports {
            push_blank(
                &mut examples,
                &format!("{} witnessRuleRef", support.witness_support_id),
                &support.witness_rule_ref,
            );
            validate_packet_measurement_boundary(
                &mut examples,
                &support.witness_support_id,
                &support.measurement_status,
                &support.reading_boundary,
            );
            if !axis_refs.contains(support.selected_axis_ref.as_str())
                && !signature_axis_ids.contains(support.selected_axis_ref.as_str())
            {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    &support.selected_axis_ref,
                    "curvature witness support selectedAxisRef must be known",
                ));
            }
            if !signature_axis_ids.contains(support.signature_axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    &support.signature_axis_ref,
                    "curvature witness support signatureAxisRef must be known",
                ));
            }
            if support.curvature_value < 0 || support.weight < 0 {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    &format!("{}:{}", support.curvature_value, support.weight),
                    "curvature value and weight must be non-negative bounded measurements",
                ));
            }
            for (field, value) in [
                ("localCurvatureRef", &support.local_curvature_ref),
                ("diagramRef", &support.diagram_ref),
                ("distanceKind", &support.distance_kind),
                ("soundnessBoundary", &support.soundness_boundary),
                ("coverageStatus", &support.coverage_status),
            ] {
                push_blank(
                    &mut examples,
                    &format!("{} {field}", support.witness_support_id),
                    value,
                );
            }
            if support.measurement_status == "measured"
                && (support.lhs_observation_refs.is_empty()
                    || support.rhs_observation_refs.is_empty()
                    || support.distance_input_refs.is_empty()
                    || support.source_refs.is_empty())
            {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    "lhs/rhs/distanceInput/sourceRefs",
                    "measured curvature support row must carry kappa(D) input refs and source refs",
                ));
            }
            if support.curvature_value == 0
                && support.support_refs.is_empty()
                && support.missing_evidence.is_empty()
            {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    "missingEvidence",
                    "zero-valued support rows must carry missing evidence rather than imply measured zero",
                ));
            }
            if support.curvature_value > 0 && support.support_refs.is_empty() {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    "supportRefs",
                    "measured curvature support must keep support refs traceable",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} reading", support.witness_support_id),
                &support.reading,
            );
        }
        for mode in &reading.top_curvature_modes {
            if mode.rank == 0 {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "rank",
                    "top curvature mode rank must be positive",
                ));
            }
            if mode
                .witness_refs
                .iter()
                .any(|witness_ref| !support_ids.contains(witness_ref.as_str()))
            {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "witnessRefs",
                    "top curvature mode witness refs must point at witness support rows",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} modeKind", mode.mode_id),
                &mode.mode_kind,
            );
            if mode.operator_component_refs.is_empty() || mode.recommended_review_target.is_empty()
            {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "operatorComponentRefs/recommendedReviewTarget",
                    "top bounded mode must be operator-derived and reviewer-readable",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} reading", mode.mode_id),
                &mode.reading,
            );
        }
        for cluster in &reading.witness_clusters {
            if cluster.witness_refs.is_empty() || cluster.axis_refs.is_empty() {
                examples.push(generic_validation_example(
                    &cluster.cluster_id,
                    "witnessRefs/axisRefs",
                    "witness cluster must retain witness and axis refs",
                ));
            }
            if cluster.cluster_weight < 0 {
                examples.push(generic_validation_example(
                    &cluster.cluster_id,
                    &cluster.cluster_weight.to_string(),
                    "witness cluster weight must be non-negative",
                ));
            }
            if cluster.cluster_basis.is_empty() {
                examples.push(generic_validation_example(
                    &cluster.cluster_id,
                    "clusterBasis",
                    "witness cluster must record evidence-backed clustering basis",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} reading", cluster.cluster_id),
                &cluster.reading,
            );
        }
    }

    check_from_examples(
        "archsig-analysis-packet-curvature-support-surface",
        "packet exposes curvature support rows, top modes, witness clusters, and unmeasured boundaries",
        examples,
        "fail",
    )
}

fn check_curvature_transfer_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let allowed_statuses =
        BTreeSet::from(["actionable", "needsReview", "blocked", "nonConclusion"]);
    let support_ids = packet
        .curvature_support_readings
        .iter()
        .flat_map(|reading| reading.witness_supports.iter())
        .map(|support| support.witness_support_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    if packet.curvature_transfer_readings.is_empty() {
        return check_from_examples(
            "archsig-analysis-packet-curvature-transfer-surface",
            "optional curvature transfer readings are absent",
            examples,
            "fail",
        );
    }
    examples.extend(duplicate_examples(
        "curvatureTransferReadings[].readingId",
        duplicates(
            packet
                .curvature_transfer_readings
                .iter()
                .map(|reading| reading.reading_id.as_str()),
        ),
    ));
    for reading in &packet.curvature_transfer_readings {
        if !allowed_statuses.contains(reading.status.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.status,
                "curvature transfer status must be actionable, needsReview, blocked, or nonConclusion",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} profileRef", reading.reading_id),
            &reading.profile_ref,
        );
        validate_packet_measurement_boundary(
            &mut examples,
            &reading.reading_id,
            &reading.measurement_status,
            &reading.reading_boundary,
        );
        if reading.transfer_operator.nonzero_edge_count != reading.transfer_edges.len() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.transfer_operator.nonzero_edge_count.to_string(),
                "transfer operator edge count must match transferEdges length",
            ));
        }
        if reading.transfer_operator.sparse_entries.len() != reading.transfer_edges.len()
            || reading.transfer_operator.row_support_refs.len()
                != reading.transfer_operator.row_count
            || reading.transfer_operator.column_support_refs.len()
                != reading.transfer_operator.column_count
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "sparseEntries/rowSupportRefs/columnSupportRefs",
                "transfer operator must expose a traceable sparse finite matrix domain",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} transferOperator.entryRule", reading.reading_id),
            &reading.transfer_operator.entry_rule,
        );
        push_blank(
            &mut examples,
            &format!("{} transferOperator.spectralRadiusKind", reading.reading_id),
            &reading.transfer_operator.spectral_radius_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} transferOperator.reading", reading.reading_id),
            &reading.transfer_operator.reading,
        );
        push_blank(
            &mut examples,
            &format!("{} spectralRadiusReading.value", reading.reading_id),
            &reading.spectral_radius_reading.value,
        );
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "curvature transfer reading must retain amplification and forecast non-conclusions",
            ));
        }
        for required in [
            "rho(T^kappa) > 0 is only a bounded recurrent obstruction reading",
            "transfer operator reading does not replace FieldSig forecast",
        ] {
            if !reading
                .non_conclusions
                .iter()
                .any(|non_conclusion| non_conclusion == required)
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    required,
                    "curvature transfer reading is missing a required non-conclusion",
                ));
            }
        }
        for edge in &reading.transfer_edges {
            if !support_ids.contains(edge.source_support_ref.as_str())
                || !support_ids.contains(edge.target_support_ref.as_str())
            {
                examples.push(generic_validation_example(
                    &edge.edge_id,
                    "source/target support refs",
                    "curvature transfer edge must reference known curvature support rows",
                ));
            }
            if edge.weight <= 0 || edge.defect_value <= 0 {
                examples.push(generic_validation_example(
                    &edge.edge_id,
                    &format!("{}:{}", edge.defect_value, edge.weight),
                    "curvature transfer edge must carry positive defect value and weight",
                ));
            }
            if edge.witness_refs.is_empty() {
                examples.push(generic_validation_example(
                    &edge.edge_id,
                    "witnessRefs",
                    "curvature transfer edge must keep witness refs traceable",
                ));
            }
            if edge.evidence_refs.is_empty() || edge.extraction_rule.is_empty() {
                examples.push(generic_validation_example(
                    &edge.edge_id,
                    "evidenceRefs/extractionRule",
                    "curvature transfer edge must keep source-backed extraction evidence",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} reading", edge.edge_id),
                &edge.reading,
            );
        }
        let edge_ids = reading
            .transfer_edges
            .iter()
            .map(|edge| edge.edge_id.as_str())
            .collect::<BTreeSet<_>>();
        for mode in &reading.recurrent_obstruction_modes {
            if mode.transfer_edge_refs.is_empty()
                || mode
                    .transfer_edge_refs
                    .iter()
                    .any(|edge_ref| !edge_ids.contains(edge_ref.as_str()))
            {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "transferEdgeRefs",
                    "recurrent obstruction mode must reference known transfer edges",
                ));
            }
            if mode.support_refs.is_empty() || mode.witness_refs.is_empty() {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "supportRefs/witnessRefs",
                    "recurrent obstruction mode must keep support and witness refs traceable",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} recurrenceKind", mode.mode_id),
                &mode.recurrence_kind,
            );
            if mode.cycle_weight <= 0 {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "cycleWeight",
                    "recurrent obstruction mode must carry a positive closed-walk weight",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} spectralRadiusReading", mode.mode_id),
                &mode.spectral_radius_reading,
            );
            push_blank(
                &mut examples,
                &format!("{} recurrentObstructionReading", mode.mode_id),
                &mode.recurrent_obstruction_reading,
            );
            if mode.non_conclusions.is_empty() || has_blank(&mode.non_conclusions) {
                examples.push(generic_validation_example(
                    &mode.mode_id,
                    "nonConclusions",
                    "recurrent obstruction mode must preserve non-conclusions",
                ));
            }
        }
        if reading
            .spectral_radius_reading
            .value
            .parse::<f64>()
            .is_ok_and(|value| value > 0.0)
            && reading.recurrent_obstruction_modes.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "recurrentObstructionModes",
                "positive rho(T^kappa) finite transfer reading must be limited to recurrent obstruction modes",
            ));
        }
    }
    check_from_examples(
        "archsig-analysis-packet-curvature-transfer-surface",
        "packet exposes finite transfer operator, recurrent obstruction modes, rho(T^kappa) reading, and forecast non-conclusions",
        examples,
        "fail",
    )
}

fn check_architecture_spectrum_report_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let Some(report) = &packet.architecture_spectrum_report else {
        if !packet.curvature_support_readings.is_empty()
            || !packet.curvature_transfer_readings.is_empty()
        {
            examples.push(generic_validation_example(
                &packet.analysis_id,
                "architectureSpectrumReport",
                "packet with curvature support or transfer readings must include ArchitectureSpectrumReport",
            ));
        }
        return check_from_examples(
            "archsig-analysis-packet-architecture-spectrum-report-surface",
            "optional ArchitectureSpectrumReport is absent",
            examples,
            "fail",
        );
    };

    push_blank(
        &mut examples,
        "architectureSpectrumReport.reportId",
        &report.report_id,
    );
    push_blank(
        &mut examples,
        "architectureSpectrumReport.profileRef",
        &report.profile_ref,
    );
    validate_packet_measurement_boundary(
        &mut examples,
        &report.report_id,
        &report.measurement_status,
        &report.reading_boundary,
    );
    if report.top_hotspots.is_empty() {
        examples.push(generic_validation_example(
            &report.report_id,
            "topHotspots",
            "ArchitectureSpectrumReport must expose hotspot readings",
        ));
    }
    if report.top_eigenmodes.is_empty() {
        examples.push(generic_validation_example(
            &report.report_id,
            "topEigenmodes",
            "ArchitectureSpectrumReport must expose top mode source data",
        ));
    }
    if report.top_witness_clusters.is_empty() {
        examples.push(generic_validation_example(
            &report.report_id,
            "topWitnessClusters",
            "ArchitectureSpectrumReport must expose witness clusters",
        ));
    }
    if report.measured_boundary.trim().is_empty() {
        examples.push(generic_validation_example(
            &report.report_id,
            "measuredBoundary",
            "ArchitectureSpectrumReport must keep measured boundary explicit",
        ));
    }
    if report.recommended_review_focus.is_empty() || has_blank(&report.recommended_review_focus) {
        examples.push(generic_validation_example(
            &report.report_id,
            "recommendedReviewFocus",
            "ArchitectureSpectrumReport must provide next review actions",
        ));
    }
    if report.non_conclusions.is_empty() || has_blank(&report.non_conclusions) {
        examples.push(generic_validation_example(
            &report.report_id,
            "nonConclusions",
            "ArchitectureSpectrumReport must retain report-level non-conclusions",
        ));
    }
    for mode in &report.top_eigenmodes {
        push_blank(
            &mut examples,
            &format!("{} modeKind", mode.mode_ref),
            &mode.mode_kind,
        );
        if mode.operator_component_refs.is_empty() || mode.recommended_review_target.is_empty() {
            examples.push(generic_validation_example(
                &mode.mode_ref,
                "operatorComponentRefs/recommendedReviewTarget",
                "ArchitectureSpectrumReport mode must identify operator components and review target",
            ));
        }
    }
    for cluster in &report.top_witness_clusters {
        if cluster.cluster_basis.is_empty() {
            examples.push(generic_validation_example(
                &cluster.cluster_ref,
                "clusterBasis",
                "ArchitectureSpectrumReport witness cluster must retain clustering basis",
            ));
        }
    }
    for required in [
        "ArchitectureSpectrumReport is not a single architecture quality score",
        "ArchitectureSpectrumReport does not replace FieldSig forecast or governance",
    ] {
        if !report
            .non_conclusions
            .iter()
            .any(|non_conclusion| non_conclusion == required)
        {
            examples.push(generic_validation_example(
                &report.report_id,
                required,
                "ArchitectureSpectrumReport is missing a required non-conclusion",
            ));
        }
    }
    for hotspot in &report.top_hotspots {
        if hotspot.curvature_value < 0 {
            examples.push(generic_validation_example(
                &hotspot.hotspot_id,
                &hotspot.curvature_value.to_string(),
                "hotspot curvature value must be non-negative",
            ));
        }
        if hotspot.witness_refs.is_empty() {
            examples.push(generic_validation_example(
                &hotspot.hotspot_id,
                "witnessRefs",
                "hotspot must keep witness refs traceable",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", hotspot.hotspot_id),
            &hotspot.recommended_next_action,
        );
    }
    for recurrent in &report.recurrent_obstructions {
        if recurrent.transfer_edge_refs.is_empty()
            || recurrent.support_refs.is_empty()
            || recurrent.witness_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &recurrent.mode_ref,
                "transfer/support/witness refs",
                "recurrent obstruction report entry must keep transfer, support, and witness refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} spectralRadiusReading", recurrent.mode_ref),
            &recurrent.spectral_radius_reading,
        );
    }
    check_from_examples(
        "archsig-analysis-packet-architecture-spectrum-report-surface",
        "packet exposes ArchitectureSpectrumReport hotspots, recurrent obstructions, measured boundary, review focus, and non-conclusions",
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
        if reading.transfer_matrix_entries.is_empty()
            && reading.bridge_atom_families.is_empty()
            && reading.status != "nonConclusion"
        {
            examples.push(generic_validation_example(
                &reading.transfer_bridge_id,
                "transferMatrixEntries",
                "transfer bridge must expose repair operation x transferred axis matrix entries or bridge atom family readings",
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
    if packet.axis_forgetting_risk_readings.is_empty() {
        examples.push(generic_validation_example(
            "axisForgettingRiskReadings",
            "empty",
            "packet must expose axis-forgetting / projection reflection loss readings",
        ));
    }
    if packet.observation_projection_fidelity_readings.is_empty() {
        examples.push(generic_validation_example(
            "observationProjectionFidelityReadings",
            "empty",
            "packet must expose observation projection fidelity readings",
        ));
    }
    if packet.atom_origin_closure_debt_readings.is_empty() {
        examples.push(generic_validation_example(
            "atomOriginClosureDebtReadings",
            "empty",
            "packet must expose Atom origin closure debt readings",
        ));
    }
    if packet.effect_relation_algebra_readings.is_empty() {
        examples.push(generic_validation_example(
            "effectRelationAlgebraReadings",
            "empty",
            "packet must expose effect relation algebra readings",
        ));
    }
    if packet.synthesis_blockage_readings.is_empty() {
        examples.push(generic_validation_example(
            "synthesisBlockageReadings",
            "empty",
            "packet must expose synthesis blockage readings",
        ));
    }
    if packet.operation_precondition_readiness_readings.is_empty() {
        examples.push(generic_validation_example(
            "operationPreconditionReadinessReadings",
            "empty",
            "packet must expose operation precondition readiness readings",
        ));
    }
    if packet.path_multiplicity_loss_readings.is_empty() {
        examples.push(generic_validation_example(
            "pathMultiplicityLossReadings",
            "empty",
            "packet must expose path multiplicity loss readings",
        ));
    }
    if packet
        .signature_trajectory_homotopy_refutation_readings
        .is_empty()
    {
        examples.push(generic_validation_example(
            "signatureTrajectoryHomotopyRefutationReadings",
            "empty",
            "packet must expose selected trajectory homotopy refutation readings",
        ));
    }
    if packet.bridge_split_obstruction_transfer_readings.is_empty() {
        examples.push(generic_validation_example(
            "bridgeSplitObstructionTransferReadings",
            "empty",
            "packet must expose bridge split obstruction transfer readings",
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
        if reading.payload_comparison_policy.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "payloadComparisonPolicy",
                "Atom compatibility reading must expose the payload comparison policy",
            ));
        }
        for conflict in &reading.conflicts {
            if conflict.compared_payload_refs.is_empty()
                || conflict.payload_comparison_policy.trim().is_empty()
                || conflict.source_refs.is_empty()
                || conflict.confidence_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &conflict.slot_ref,
                    "Atom compatibility conflicts must retain payload refs, comparison policy, source refs, and confidence refs",
                ));
            }
            if conflict.inconsistency_kind.contains("Semantic")
                && conflict.semantic_conflict_relation_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &conflict.slot_ref,
                    "semantic Atom compatibility conflicts must link semantic conflict relation refs",
                ));
            }
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
        if reading.coverage_requirement_status.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "coverageRequirementStatus",
                "LawUniverse coverage must record coverage requirement status separately from law coverage",
            ));
        }
        if reading.law_witness_axis_evaluations.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "lawWitnessAxisEvaluations",
                "LawUniverse coverage must expose machine-readable law / witness / axis alignment evaluations",
            ));
        }
        for evaluation in &reading.law_witness_axis_evaluations {
            if evaluation.required_witness_refs.is_empty()
                || evaluation.required_axis_refs.is_empty()
                || evaluation.coverage_requirement_refs.is_empty()
                || evaluation.exactness_assumption_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.evaluation_id,
                    "law / witness / axis alignment evaluation must keep required witness, axis, coverage, and exactness refs",
                ));
            }
            if evaluation.alignment_status == "blocked" && evaluation.blocker_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.evaluation_id,
                    "blocked law / witness / axis alignment must retain blocker refs",
                ));
            }
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
        if reading.witness_basis.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "witnessBasis",
                "feature extension formula must retain witness-driven attribution basis",
            ));
        }
        for basis in &reading.witness_basis {
            push_blank(
                &mut examples,
                &format!("{} witnessBasis.witnessRef", reading.reading_id),
                &basis.witness_ref,
            );
            if basis.labels.is_empty() || has_blank(&basis.labels) {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &basis.witness_ref,
                    "feature extension witness basis must carry labels",
                ));
            }
            if basis.observation_refs.is_empty() && basis.source_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &basis.witness_ref,
                    "feature extension witness basis must connect to observation or source refs",
                ));
            }
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
        if reading.law_evidence.len() < 9 {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "lawEvidence",
                "operation calculus reading must expose evidence for each law axis",
            ));
        }
        for evidence in &reading.law_evidence {
            push_blank(
                &mut examples,
                &format!("{} lawEvidence.lawAxis", reading.reading_id),
                &evidence.law_axis,
            );
            push_blank(
                &mut examples,
                &format!("{} lawEvidence.status", reading.reading_id),
                &evidence.status,
            );
            if !matches!(
                evidence.status.as_str(),
                "observed" | "unmeasured" | "blocked" | "notApplicable"
            ) {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.status,
                    "operation law axis status must be observed / unmeasured / blocked / notApplicable",
                ));
            }
            if evidence.required_evidence_refs.is_empty()
                && evidence.status.as_str() != "notApplicable"
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "operation law axis must name required evidence refs",
                ));
            }
            if evidence.status == "observed" && evidence.observed_evidence_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "observed operation law axis must retain observed evidence refs",
                ));
            }
            if evidence.status == "blocked" && evidence.blocked_reason_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "blocked operation law axis must retain blocked reason refs",
                ));
            }
        }
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
    for reading in &packet.axis_forgetting_risk_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.source_projection_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} reflectionLossKind", reading.reading_id),
            &reading.reflection_loss_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} zeroReflectionStatus", reading.reading_id),
            &reading.zero_reflection_status,
        );
        push_blank(
            &mut examples,
            &format!("{} obstructionReflectionStatus", reading.reading_id),
            &reading.obstruction_reflection_status,
        );
        if reading.required_assumptions.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "requiredAssumptions",
                "axis-forgetting risk must record reflection assumptions",
            ));
        }
        if reading.selected_signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "selectedSignatureAxisRefs",
                "axis-forgetting risk must connect projection loss to selected signature axes",
            ));
        }
        if reading.zero_reflection_status.contains("blocked")
            && reading.blocked_signature_axis_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "blockedSignatureAxisRefs",
                "blocked zero reflection must name affected signature axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", reading.reading_id),
            &reading.coverage_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.observation_projection_fidelity_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.source_projection_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} fidelityStatus", reading.reading_id),
            &reading.fidelity_status,
        );
        push_blank(
            &mut examples,
            &format!("{} reflectionStatus", reading.reading_id),
            &reading.reflection_status,
        );
        push_blank(
            &mut examples,
            &format!("{} measurementBoundary", reading.reading_id),
            &reading.measurement_boundary,
        );
        if reading.fidelity_status == "projectionLossObserved"
            && reading.reconstruction_blocker_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "reconstructionBlockerRefs",
                "projection fidelity loss must retain typed reconstruction blocker refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.reading_id),
            &reading.recommended_next_action,
        );
    }
    for reading in &packet.atom_origin_closure_debt_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.closure_status);
        if reading.weakens_zero_or_repair_claims.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "weakensZeroOrRepairClaims",
                "Atom origin closure debt must state affected zero/repair/synthesis claim boundaries",
            ));
        }
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
    for reading in &packet.effect_relation_algebra_readings {
        if reading.required_effect_relations.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "requiredEffectRelations",
                "effect relation algebra must enumerate effect/replay/compensation relations",
            ));
        }
        if reading.relation_inputs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "relationInputs",
                "effect relation algebra must retain relation input rows",
            ));
        }
        if reading.relation_evaluations.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "relationEvaluations",
                "effect relation algebra must evaluate ordering/replay/idempotency/compensation/authority axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} relationEvaluatorStatus", reading.reading_id),
            &reading.relation_evaluator_status,
        );
        for input in &reading.relation_inputs {
            push_blank(
                &mut examples,
                &format!("{} relationInputId", reading.reading_id),
                &input.relation_input_id,
            );
            if input.effect_refs.is_empty()
                && input.ordering_refs.is_empty()
                && input.replay_or_idempotency_refs.is_empty()
                && input.compensation_or_finalization_refs.is_empty()
                && input.authority_requirement_refs.is_empty()
                && input.runtime_or_trace_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &input.relation_input_id,
                    "effect relation input must retain effect, ordering, replay, compensation, authority, or runtime refs",
                ));
            }
        }
        for evaluation in &reading.relation_evaluations {
            if !matches!(
                evaluation.status.as_str(),
                "observed" | "blocked" | "unmeasured" | "notApplicable"
            ) {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.status,
                    "effect relation law evaluation status must be observed / blocked / unmeasured / notApplicable",
                ));
            }
            if evaluation.status == "blocked" && evaluation.blocked_reason_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.law_axis,
                    "blocked effect relation law evaluation must retain blocker refs",
                ));
            }
            if evaluation.status == "observed" && evaluation.observed_input_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.law_axis,
                    "observed effect relation law evaluation must retain observed input refs",
                ));
            }
        }
        push_blank(
            &mut examples,
            &format!("{} effectOrderingPressure", reading.reading_id),
            &reading.effect_ordering_pressure,
        );
        push_blank(
            &mut examples,
            &format!("{} stateTransitionRef", reading.reading_id),
            &reading.state_transition_ref,
        );
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
    for reading in &packet.synthesis_blockage_readings {
        push_blank(
            &mut examples,
            &format!("{} blockageStatus", reading.reading_id),
            &reading.blockage_status,
        );
        push_blank(
            &mut examples,
            &format!("{} noSolutionCertificateStatus", reading.reading_id),
            &reading.no_solution_certificate_status,
        );
        push_blank(
            &mut examples,
            &format!("{} synthesisBoundary", reading.reading_id),
            &reading.synthesis_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.reading_id),
            &reading.recommended_next_action,
        );
    }
    for reading in &packet.operation_precondition_readiness_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.operation_ref);
        push_blank(
            &mut examples,
            &format!("{} readinessStatus", reading.reading_id),
            &reading.readiness_status,
        );
        push_blank(
            &mut examples,
            &format!("{} candidateBoundary", reading.reading_id),
            &reading.candidate_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} recommendedNextAction", reading.reading_id),
            &reading.recommended_next_action,
        );
    }
    for reading in &packet.path_multiplicity_loss_readings {
        push_blank(&mut examples, &reading.reading_id, &reading.scope_ref);
        push_blank(
            &mut examples,
            &format!("{} multiplicityLossStatus", reading.reading_id),
            &reading.multiplicity_loss_status,
        );
        push_blank(
            &mut examples,
            &format!("{} homotopyBoundary", reading.reading_id),
            &reading.homotopy_boundary,
        );
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
    for reading in &packet.signature_trajectory_homotopy_refutation_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.selected_homotopy_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} trajectoryEquivalenceStatus", reading.reading_id),
            &reading.trajectory_equivalence_status,
        );
        push_blank(
            &mut examples,
            &format!("{} homotopyRefutationStatus", reading.reading_id),
            &reading.homotopy_refutation_status,
        );
        push_blank(
            &mut examples,
            &format!("{} selectedEquivalenceBoundary", reading.reading_id),
            &reading.selected_equivalence_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", reading.reading_id),
            &reading.evidence_boundary,
        );
    }
    for reading in &packet.bridge_split_obstruction_transfer_readings {
        push_blank(
            &mut examples,
            &reading.reading_id,
            &reading.split_readiness_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} fillerEvidenceStatus", reading.reading_id),
            &reading.filler_evidence_status,
        );
        push_blank(
            &mut examples,
            &format!("{} liftingEvidenceStatus", reading.reading_id),
            &reading.lifting_evidence_status,
        );
        push_blank(
            &mut examples,
            &format!("{} transferRiskStatus", reading.reading_id),
            &reading.transfer_risk_status,
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
        if reading.source_coordinates.is_empty() || reading.observed_coordinates.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "sourceCoordinates/observedCoordinates",
                "observation projection must expose canonical source and observed coordinate rows",
            ));
        }
        for coordinate in reading
            .source_coordinates
            .iter()
            .chain(reading.observed_coordinates.iter())
            .chain(reading.forgotten_coordinate_evidence.iter())
        {
            push_blank(
                &mut examples,
                &format!("{} coordinateId", reading.reading_id),
                &coordinate.coordinate_id,
            );
            push_blank(
                &mut examples,
                &format!("{} coordinateKind", reading.reading_id),
                &coordinate.coordinate_kind,
            );
            push_blank(
                &mut examples,
                &format!("{} coordinate.atomFamily", reading.reading_id),
                &coordinate.atom_family,
            );
            if coordinate.coordinate_kind == "observedAtomCoordinate"
                && coordinate.atom_observation_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &coordinate.coordinate_id,
                    "observed projection coordinates must retain atom observation refs",
                ));
            }
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
        for candidate in &reading.non_injectivity_candidates {
            if candidate.coordinate_refs.is_empty()
                || candidate.atom_observation_refs.is_empty()
                || candidate.evidence_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &candidate.candidate_id,
                    "non-injectivity candidates must carry coordinate, atom, and evidence refs",
                ));
            }
        }
        if !reading.forgotten_coordinates.is_empty()
            && reading.reconstruction_blocker_evidence.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "reconstructionBlockerEvidence",
                "forgotten coordinates must be backed by typed reconstruction blockers",
            ));
        }
        for blocker in &reading.reconstruction_blocker_evidence {
            if blocker.gap_refs.is_empty()
                || blocker.evidence_refs.is_empty()
                || blocker.expected_atom_families.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &blocker.blocker_id,
                    "reconstruction blockers must carry gap refs, expected atom families, and evidence refs",
                ));
            }
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
        if reading.transition_relation_inputs.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "transitionRelationInputs",
                "state transition algebra must retain from/event/to transition relation input rows",
            ));
        }
        if reading.law_evaluations.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "lawEvaluations",
                "state transition algebra must evaluate transition, commutativity, idempotency, replay, ordering, and invariant axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} lawEvaluatorStatus", reading.reading_id),
            &reading.law_evaluator_status,
        );
        for input in &reading.transition_relation_inputs {
            push_blank(
                &mut examples,
                &format!("{} transitionInputId", reading.reading_id),
                &input.transition_input_id,
            );
            if input.from_refs.is_empty()
                && input.event_refs.is_empty()
                && input.to_refs.is_empty()
                && input.operation_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &input.transition_input_id,
                    "state transition input must retain from, event, to, or operation refs",
                ));
            }
        }
        for evaluation in &reading.law_evaluations {
            if !matches!(
                evaluation.status.as_str(),
                "observed" | "blocked" | "unmeasured" | "notApplicable"
            ) {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.status,
                    "state transition law evaluation status must be observed / blocked / unmeasured / notApplicable",
                ));
            }
            if evaluation.status == "blocked" && evaluation.blocked_reason_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.law_axis,
                    "blocked state transition law evaluation must retain blocker refs",
                ));
            }
            if evaluation.status == "observed" && evaluation.observed_input_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.law_axis,
                    "observed state transition law evaluation must retain observed input refs",
                ));
            }
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

fn check_operation_square_trace_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let candidate_ids = set(packet
        .operation_square_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.as_str()));
    let trace_ids = set(packet
        .path_continuation_traces
        .iter()
        .map(|trace| trace.trace_id.as_str()));
    let required_axis_families = BTreeSet::from([
        "static",
        "contract",
        "semantic",
        "state",
        "effect",
        "authority",
        "runtime",
        "projection",
    ]);
    let has_measurable_operation_square = packet
        .operation_square_candidates
        .iter()
        .any(|candidate| candidate.candidate_source != "blocked");
    let mut examples = Vec::new();
    if packet.operation_square_candidates.is_empty() {
        examples.push(generic_validation_example(
            "operationSquareCandidates",
            "empty",
            "packet must enumerate operation square candidates",
        ));
    }
    examples.extend(duplicate_examples(
        "operationSquareCandidates[].candidateId",
        duplicates(
            packet
                .operation_square_candidates
                .iter()
                .map(|candidate| candidate.candidate_id.as_str()),
        ),
    ));
    for candidate in &packet.operation_square_candidates {
        if !matches!(
            candidate.candidate_source.as_str(),
            "inferred" | "supplied" | "blocked"
        ) {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                &candidate.candidate_source,
                "candidateSource must distinguish supplied, inferred, and blocked operation pairs",
            ));
        }
        let is_blocked = candidate.candidate_source == "blocked";
        push_blank(
            &mut examples,
            &format!("{} leftOperationRef", candidate.candidate_id),
            &candidate.left_operation_ref,
        );
        if !is_blocked {
            push_blank(
                &mut examples,
                &format!("{} rightOperationRef", candidate.candidate_id),
                &candidate.right_operation_ref,
            );
        }
        if !is_blocked
            && (!candidate.p_path_ref.contains(" . ") || !candidate.q_path_ref.contains(" . "))
        {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "pPathRef/qPathRef",
                "candidate must record p = g . f and q = f . g path pair expressions",
            ));
        }
        if candidate.candidate_basis.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "candidateBasis",
                "candidate must record why the operation pair was selected",
            ));
        }
        if candidate.candidate_basis_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "candidateBasisRefs",
                "candidate basis must be backed by source, observation, or endpoint refs",
            ));
        }
        if candidate.source_refs.is_empty() && candidate.observation_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "sourceRefs/observationRefs",
                "candidate must preserve source or observation refs",
            ));
        }
        if candidate.candidate_source == "blocked" && candidate.missing_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "missingRefs",
                "blocked candidate must retain missing refs so absent operation evidence is not read as zero",
            ));
        }
        if candidate.candidate_source == "inferred"
            && !candidate
                .evidence_boundary
                .to_ascii_lowercase()
                .contains("reviewcueonly")
        {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "evidenceBoundary",
                "inferred candidate must be explicitly marked reviewCueOnly, not measurement truth",
            ));
        }
        if candidate.candidate_source == "supplied" && candidate.supplied_pair_ref.is_none() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "suppliedPairRef",
                "supplied candidate must point back to first-class ArchMap operation square evidence",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", candidate.candidate_id),
            &candidate.evidence_boundary,
        );
        if !is_blocked
            && (candidate.p_operation_sequence.is_empty()
                || candidate.q_operation_sequence.is_empty())
        {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "pOperationSequence/qOperationSequence",
                "operation square candidate must carry first-class operation sequences",
            ));
        }
        if !is_blocked && candidate.endpoint_object_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "endpointObjectRefs",
                "operation square candidate must keep endpoint object refs traceable",
            ));
        }
        if !is_blocked && candidate.generator_candidate_refs.is_empty() {
            examples.push(generic_validation_example(
                &candidate.candidate_id,
                "generatorCandidateRefs",
                "operation square candidate must record homotopy generator candidates",
            ));
        }
    }

    if has_measurable_operation_square && packet.path_continuation_traces.is_empty() {
        examples.push(generic_validation_example(
            "pathContinuationTraces",
            "empty",
            "packet must record path continuation traces",
        ));
    }
    examples.extend(duplicate_examples(
        "pathContinuationTraces[].traceId",
        duplicates(
            packet
                .path_continuation_traces
                .iter()
                .map(|trace| trace.trace_id.as_str()),
        ),
    ));
    for trace in &packet.path_continuation_traces {
        if !candidate_ids.contains(trace.candidate_ref.as_str()) {
            examples.push(generic_validation_example(
                &trace.trace_id,
                &trace.candidate_ref,
                "path continuation trace references an unknown operation square candidate",
            ));
        }
        if !matches!(trace.path_role.as_str(), "p" | "q") {
            examples.push(generic_validation_example(
                &trace.trace_id,
                &trace.path_role,
                "pathRole must be p or q",
            ));
        }
        if trace.axis_traces.is_empty() {
            examples.push(generic_validation_example(
                &trace.trace_id,
                "axisTraces",
                "path continuation trace must carry axis-wise traces",
            ));
        }
        if trace.operation_sequence.is_empty() || trace.continuation_step_refs.is_empty() {
            examples.push(generic_validation_example(
                &trace.trace_id,
                "operationSequence/continuationStepRefs",
                "path continuation trace must reconstruct step-wise Cont_x(p) data",
            ));
        }
        let present_axis_families = trace
            .axis_traces
            .iter()
            .map(|axis| axis.axis_family.as_str())
            .collect::<BTreeSet<_>>();
        for required in &required_axis_families {
            if !present_axis_families.contains(required) {
                examples.push(generic_validation_example(
                    &trace.trace_id,
                    required,
                    "path continuation trace must include every required axis family",
                ));
            }
        }
        for axis in &trace.axis_traces {
            push_blank(
                &mut examples,
                &format!("{} axisFamily", trace.trace_id),
                &axis.axis_family,
            );
            push_blank(
                &mut examples,
                &format!("{} distanceEvaluatorKind", trace.trace_id),
                &axis.distance_evaluator_kind,
            );
            push_blank(
                &mut examples,
                &format!("{} continuationSummary", trace.trace_id),
                &axis.continuation_summary,
            );
            if axis.trace_status != "unmeasured"
                && (axis.continuation_states.is_empty() || axis.distance_input_refs.is_empty())
            {
                examples.push(generic_validation_example(
                    &trace.trace_id,
                    &axis.axis_family,
                    "measured continuation axes must carry continuation states and distance input refs",
                ));
            }
            if axis.trace_status != "unmeasured" && axis.comparable_continuation_values.is_empty() {
                examples.push(generic_validation_example(
                    &trace.trace_id,
                    &axis.axis_family,
                    "measured continuation axes must carry comparable continuation values for d_x(Cont_x(p), Cont_x(q))",
                ));
            }
            if axis.trace_status == "unmeasured" && axis.missing_refs.is_empty() {
                examples.push(generic_validation_example(
                    &trace.trace_id,
                    &axis.axis_family,
                    "unmeasured axis must carry missingRefs and must not be read as zero",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} unmeasuredBoundary", trace.trace_id),
                &axis.unmeasured_boundary,
            );
        }
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", trace.trace_id),
            &trace.evidence_boundary,
        );
    }

    for trace_ref in packet
        .monodromy_reading_family
        .path_continuation_trace_refs
        .iter()
    {
        if !trace_ids.contains(trace_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.monodromy_reading_family.reading_family_id,
                trace_ref,
                "monodromy reading family references an unknown path continuation trace",
            ));
        }
    }
    for candidate_ref in packet
        .monodromy_reading_family
        .operation_square_candidate_refs
        .iter()
    {
        if !candidate_ids.contains(candidate_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.monodromy_reading_family.reading_family_id,
                candidate_ref,
                "monodromy reading family references an unknown operation square candidate",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-operation-square-trace-surface",
        "packet enumerates inferred/supplied operation square candidates and axis-wise path continuation traces",
        examples,
        "fail",
    )
}

fn check_axis_wise_defect_ami_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let candidate_ids = set(packet
        .operation_square_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.as_str()));
    let has_measurable_operation_square = packet
        .operation_square_candidates
        .iter()
        .any(|candidate| candidate.candidate_source != "blocked");
    let defect_ids = set(packet
        .axis_wise_monodromy_defects
        .iter()
        .map(|defect| defect.defect_id.as_str()));
    let mut examples = Vec::new();
    if has_measurable_operation_square && packet.axis_wise_monodromy_defects.is_empty() {
        examples.push(generic_validation_example(
            "axisWiseMonodromyDefects",
            "empty",
            "packet must compute mu_x(sigma) axis-wise defect surfaces",
        ));
    }
    examples.extend(duplicate_examples(
        "axisWiseMonodromyDefects[].defectId",
        duplicates(
            packet
                .axis_wise_monodromy_defects
                .iter()
                .map(|defect| defect.defect_id.as_str()),
        ),
    ));
    for defect in &packet.axis_wise_monodromy_defects {
        if !candidate_ids.contains(defect.candidate_ref.as_str()) {
            examples.push(generic_validation_example(
                &defect.defect_id,
                &defect.candidate_ref,
                "axis-wise defect references an unknown operation square candidate",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} distanceKind", defect.defect_id),
            &defect.distance_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} pContinuationRef", defect.defect_id),
            &defect.p_continuation_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} qContinuationRef", defect.defect_id),
            &defect.q_continuation_ref,
        );
        if defect.measurement_status == "measured" && defect.distance_input_refs.is_empty() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "distanceInputRefs",
                "measured mu_x defect must carry continuation distance input refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} positiveWitnessBoundary", defect.defect_id),
            &defect.positive_witness_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} measurementStatus", defect.defect_id),
            &defect.measurement_status,
        );
        if defect.measurement_status == "measured" && defect.distance_value.is_none() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "distanceValue",
                "measured axis-wise defect must carry a distance value",
            ));
        }
        if defect.measurement_status == "unmeasured" && defect.missing_refs.is_empty() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "missingRefs",
                "unmeasured axis-wise defect must preserve missing evidence instead of reading as zero",
            ));
        }
        if defect.measured_support_refs.is_empty() && defect.missing_refs.is_empty() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "measuredSupportRefs/missingRefs",
                "axis-wise defect must carry measured support or missing refs",
            ));
        }
        if defect.witness_refs.is_empty() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "witnessRefs",
                "axis-wise defect must carry witness refs for review",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", defect.defect_id),
            &defect.coverage_boundary,
        );
        if defect.zero_reflection_assumptions.is_empty()
            || has_blank(&defect.zero_reflection_assumptions)
        {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "zeroReflectionAssumptions",
                "axis-wise defect must record zero-reflection assumptions",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} cancellationBoundary", defect.defect_id),
            &defect.cancellation_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", defect.defect_id),
            &defect.evidence_boundary,
        );
    }

    if packet.ami_aggregate_readings.is_empty() {
        examples.push(generic_validation_example(
            "amiAggregateReadings",
            "empty",
            "packet must emit AMI aggregate review readings",
        ));
    }
    examples.extend(duplicate_examples(
        "amiAggregateReadings[].aggregateId",
        duplicates(
            packet
                .ami_aggregate_readings
                .iter()
                .map(|aggregate| aggregate.aggregate_id.as_str()),
        ),
    ));
    for aggregate in &packet.ami_aggregate_readings {
        push_blank(
            &mut examples,
            &format!("{} selectedSquareFamily", aggregate.aggregate_id),
            &aggregate.selected_square_family,
        );
        if has_measurable_operation_square && aggregate.selected_axis_family.is_empty() {
            examples.push(generic_validation_example(
                &aggregate.aggregate_id,
                "selectedAxisFamily",
                "AMI must report selected axis family",
            ));
        }
        if has_measurable_operation_square
            && (aggregate.measured_defect_refs.is_empty()
                || aggregate.positive_weight_defect_refs.is_empty())
        {
            examples.push(generic_validation_example(
                &aggregate.aggregate_id,
                "measuredDefectRefs/positiveWeightDefectRefs",
                "AMI must distinguish selected measured squares and positive-weight local entries",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} weightPolicy", aggregate.aggregate_id),
            &aggregate.weight_policy,
        );
        push_blank(
            &mut examples,
            &format!("{} distanceKind", aggregate.aggregate_id),
            &aggregate.distance_kind,
        );
        if has_measurable_operation_square && aggregate.top_contributors.is_empty() {
            examples.push(generic_validation_example(
                &aggregate.aggregate_id,
                "topContributors",
                "AMI must expose top contributors for review",
            ));
        }
        for contributor in &aggregate.top_contributors {
            if !defect_ids.contains(contributor.defect_ref.as_str()) {
                examples.push(generic_validation_example(
                    &aggregate.aggregate_id,
                    &contributor.defect_ref,
                    "AMI top contributor references an unknown defect",
                ));
            }
            push_blank(
                &mut examples,
                &format!("{} topContributors[].reviewFocus", aggregate.aggregate_id),
                &contributor.review_focus,
            );
        }
        if aggregate.zero_reflection_assumptions.is_empty()
            || has_blank(&aggregate.zero_reflection_assumptions)
        {
            examples.push(generic_validation_example(
                &aggregate.aggregate_id,
                "zeroReflectionAssumptions",
                "AMI must retain zero-reflection assumptions",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} cancellationBoundary", aggregate.aggregate_id),
            &aggregate.cancellation_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} aggregateToLocalReadingBoundary", aggregate.aggregate_id),
            &aggregate.aggregate_to_local_reading_boundary,
        );
        if aggregate
            .aggregate_to_local_reading_boundary
            .to_ascii_lowercase()
            .contains("merge gate")
        {
            examples.push(generic_validation_example(
                &aggregate.aggregate_id,
                "aggregateToLocalReadingBoundary",
                "AMI must not be framed as a merge gate",
            ));
        }
    }

    for defect_ref in &packet.monodromy_reading_family.axis_wise_defect_refs {
        if !defect_ids.contains(defect_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.monodromy_reading_family.reading_family_id,
                defect_ref,
                "monodromy reading family references an unknown axis-wise defect",
            ));
        }
    }
    let aggregate_ids = set(packet
        .ami_aggregate_readings
        .iter()
        .map(|aggregate| aggregate.aggregate_id.as_str()));
    for aggregate_ref in &packet.monodromy_reading_family.ami_aggregate_reading_refs {
        if !aggregate_ids.contains(aggregate_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.monodromy_reading_family.reading_family_id,
                aggregate_ref,
                "monodromy reading family references an unknown AMI aggregate reading",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-axis-defect-ami-surface",
        "packet carries mu_x(sigma) axis-wise defects and AMI aggregate review readings without theorem or merge-gate conclusions",
        examples,
        "fail",
    )
}

fn check_nonzero_monodromy_witness_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let defect_ids = set(packet
        .axis_wise_monodromy_defects
        .iter()
        .map(|defect| defect.defect_id.as_str()));
    let candidate_ids = set(packet
        .operation_square_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.as_str()));
    let witness_ids = set(packet
        .nonzero_monodromy_witnesses
        .iter()
        .map(|witness| witness.witness_id.as_str()));
    let mut examples = Vec::new();
    if packet
        .axis_wise_monodromy_defects
        .iter()
        .any(|defect| defect.distance_value.is_some_and(|value| value > 0))
        && packet.nonzero_monodromy_witnesses.is_empty()
    {
        examples.push(generic_validation_example(
            "nonzeroMonodromyWitnesses",
            "empty",
            "positive measured defects must be surfaced as nonzero monodromy witnesses",
        ));
    }
    examples.extend(duplicate_examples(
        "nonzeroMonodromyWitnesses[].witnessId",
        duplicates(
            packet
                .nonzero_monodromy_witnesses
                .iter()
                .map(|witness| witness.witness_id.as_str()),
        ),
    ));
    for witness in &packet.nonzero_monodromy_witnesses {
        if !defect_ids.contains(witness.defect_ref.as_str()) {
            examples.push(generic_validation_example(
                &witness.witness_id,
                &witness.defect_ref,
                "nonzero witness references an unknown axis-wise defect",
            ));
        }
        if !candidate_ids.contains(witness.candidate_ref.as_str()) {
            examples.push(generic_validation_example(
                &witness.witness_id,
                &witness.candidate_ref,
                "nonzero witness references an unknown operation square candidate",
            ));
        }
        if witness.operation_pair.len() != 2 || witness.path_pair.len() != 2 {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "operationPair/pathPair",
                "nonzero witness must record operation pair and path pair",
            ));
        }
        if witness.defect_value <= 0 {
            examples.push(generic_validation_example(
                &witness.witness_id,
                &witness.defect_value.to_string(),
                "nonzero witness must have positive measured defect value",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} axisFamily", witness.witness_id),
            &witness.axis_family,
        );
        if witness.affected_atom_refs.is_empty() {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "affectedAtomRefs",
                "nonzero witness must keep affected Atom / observation refs traceable",
            ));
        }
        if witness.law_refs.is_empty() || witness.signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "lawRefs/signatureAxisRefs",
                "nonzero witness must keep law and signature axis refs traceable",
            ));
        }
        if witness.compared_trace_summary.is_empty() {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "comparedTraceSummary",
                "nonzero witness must summarize compared traces",
            ));
        }
        if witness.suggested_filler_evidence.is_empty()
            || witness.suggested_lifting_evidence.is_empty()
            || witness.suggested_boundary_evidence.is_empty()
        {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "suggestedEvidence",
                "nonzero witness must suggest filler, lifting, and boundary evidence",
            ));
        }
        if witness.recommended_review_focus.is_empty() {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "recommendedReviewFocus",
                "nonzero witness must provide review cues",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} coverageBoundary", witness.witness_id),
            &witness.coverage_boundary,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", witness.witness_id),
            &witness.evidence_boundary,
        );
        if witness.non_conclusions.is_empty() || has_blank(&witness.non_conclusions) {
            examples.push(generic_validation_example(
                &witness.witness_id,
                "nonConclusions",
                "nonzero witness must retain machine-readable non-conclusions",
            ));
        }
    }
    for witness_ref in &packet
        .boundary_holonomy_reading_family
        .nonzero_monodromy_witness_refs
    {
        if !witness_ids.contains(witness_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.boundary_holonomy_reading_family.reading_family_id,
                witness_ref,
                "boundary holonomy reading family references an unknown nonzero witness",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-nonzero-monodromy-witness-surface",
        "packet surfaces positive measured mu_x(sigma) defects as reviewer-readable nonzero monodromy witnesses",
        examples,
        "fail",
    )
}

fn check_feature_boundary_residual_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let feature_extension_ids = set(packet
        .feature_extension_formula_readings
        .iter()
        .map(|reading| reading.reading_id.as_str()));
    let reading_ids = set(packet
        .feature_boundary_residual_readings
        .iter()
        .map(|reading| reading.reading_id.as_str()));
    let defect_ids = set(packet
        .axis_wise_monodromy_defects
        .iter()
        .map(|defect| defect.defect_id.as_str()));
    let required_axes = BTreeSet::from([
        "Hol_static",
        "Hol_contract",
        "Hol_semantic",
        "Hol_state",
        "Hol_effect",
        "Hol_authority",
        "Hol_runtime",
        "Hol_projection",
    ]);
    let mut examples = Vec::new();
    if !packet.feature_extension_formula_readings.is_empty()
        && packet.feature_boundary_residual_readings.is_empty()
    {
        examples.push(generic_validation_example(
            "featureBoundaryResidualReadings",
            "empty",
            "feature extension formulas must be lifted to Boundary(A,f) residual readings",
        ));
    }
    examples.extend(duplicate_examples(
        "featureBoundaryResidualReadings[].readingId",
        duplicates(
            packet
                .feature_boundary_residual_readings
                .iter()
                .map(|reading| reading.reading_id.as_str()),
        ),
    ));
    for reading in &packet.feature_boundary_residual_readings {
        if !feature_extension_ids.contains(reading.feature_extension_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.feature_extension_ref,
                "feature boundary residual references an unknown feature extension formula",
            ));
        }
        for (field, value) in [
            ("boundaryRef", &reading.boundary_ref),
            ("status", &reading.status),
            ("coreScopeRef", &reading.core_scope_ref),
            ("featureScopeRef", &reading.feature_scope_ref),
            (
                "supportSeparationPolicy",
                &reading.support_separation_policy,
            ),
            ("attributionPolicy", &reading.attribution_policy),
            ("coverageBoundary", &reading.coverage_boundary),
            ("exactnessBoundary", &reading.exactness_boundary),
            ("evidenceBoundary", &reading.evidence_boundary),
        ] {
            push_blank(
                &mut examples,
                &format!("{} {field}", reading.reading_id),
                value,
            );
        }
        if reading.mixed_subconfiguration_refs.is_empty()
            || reading.boundary_support_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "mixedSubconfigurationRefs/boundarySupportRefs",
                "Boundary(A,f) reading must expose mixed core/feature boundary support",
            ));
        }
        if reading.coverage_assumptions.is_empty() || reading.exactness_assumptions.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "coverageAssumptions/exactnessAssumptions",
                "feature boundary residual must record support coverage and exactness assumptions",
            ));
        }
        if !reading
            .exactness_boundary
            .contains("does not prove Ob(B)=Ob(A)+Ob(f)+Hol(Boundary(A,f))")
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.exactness_boundary,
                "feature boundary residual must not claim the boundary holonomy conjecture as a theorem",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "nonConclusions",
                "feature boundary residual must retain machine-readable non-conclusions",
            ));
        }
        let axis_refs = reading
            .holonomy_axes
            .iter()
            .map(|axis| axis.holonomy_axis_ref.as_str())
            .collect::<BTreeSet<_>>();
        if axis_refs != required_axes {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "holonomyAxes",
                "feature boundary residual must expose all Hol_* axes",
            ));
        }
        for axis in &reading.holonomy_axes {
            for (field, value) in [
                ("holonomyAxisRef", &axis.holonomy_axis_ref),
                ("axisFamily", &axis.axis_family),
                ("status", &axis.status),
                ("reading", &axis.reading),
            ] {
                push_blank(
                    &mut examples,
                    &format!("{} {} {field}", reading.reading_id, axis.holonomy_axis_ref),
                    value,
                );
            }
            if axis.support_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &axis.holonomy_axis_ref,
                    "each Hol_* axis must keep boundary support refs traceable",
                ));
            }
            if axis.residual_value > 0 && axis.measured_defect_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &axis.holonomy_axis_ref,
                    "positive Hol_* residual value must reference measured defects",
                ));
            }
            for defect_ref in &axis.measured_defect_refs {
                if !defect_ids.contains(defect_ref.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.reading_id,
                        defect_ref,
                        "Hol_* axis references an unknown axis-wise defect",
                    ));
                }
            }
        }
    }
    for residual_ref in &packet
        .boundary_holonomy_reading_family
        .feature_boundary_residual_refs
    {
        if !reading_ids.contains(residual_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.boundary_holonomy_reading_family.reading_family_id,
                residual_ref,
                "boundary holonomy reading family references an unknown feature boundary residual",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-feature-boundary-residual-surface",
        "packet surfaces Boundary(A,f) residual holonomy axes as bounded review telemetry",
        examples,
        "fail",
    )
}

fn check_feature_extension_diagnosis_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let feature_extension_ids = set(packet
        .feature_extension_formula_readings
        .iter()
        .map(|reading| reading.reading_id.as_str()));
    let boundary_residual_ids = set(packet
        .feature_boundary_residual_readings
        .iter()
        .map(|reading| reading.reading_id.as_str()));
    let diagnosis_ids = set(packet
        .feature_extension_diagnosis_readings
        .iter()
        .map(|reading| reading.diagnosis_id.as_str()));
    let required_labels = BTreeSet::from([
        "inheritedCoreObstruction",
        "featureLocalObstruction",
        "boundaryHolonomy",
        "liftingFailure",
        "fillingFailure",
        "complexityTransfer",
        "residualCoverageGap",
    ]);
    let mut examples = Vec::new();
    if !packet.feature_extension_formula_readings.is_empty()
        && packet.feature_extension_diagnosis_readings.is_empty()
    {
        examples.push(generic_validation_example(
            "featureExtensionDiagnosisReadings",
            "empty",
            "feature extension formulas must be classified into multi-label diagnosis readings",
        ));
    }
    examples.extend(duplicate_examples(
        "featureExtensionDiagnosisReadings[].diagnosisId",
        duplicates(
            packet
                .feature_extension_diagnosis_readings
                .iter()
                .map(|reading| reading.diagnosis_id.as_str()),
        ),
    ));
    for reading in &packet.feature_extension_diagnosis_readings {
        if !feature_extension_ids.contains(reading.feature_extension_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                &reading.feature_extension_ref,
                "feature extension diagnosis references an unknown feature extension formula",
            ));
        }
        if reading.boundary_residual_ref != "feature-boundary-residual:none-observed"
            && !boundary_residual_ids.contains(reading.boundary_residual_ref.as_str())
        {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                &reading.boundary_residual_ref,
                "feature extension diagnosis references an unknown boundary residual reading",
            ));
        }
        for (field, value) in [
            ("status", &reading.status),
            ("classifierVersion", &reading.classifier_version),
            ("classificationBoundary", &reading.classification_boundary),
            ("fieldSigBoundary", &reading.fieldsig_boundary),
            ("evidenceBoundary", &reading.evidence_boundary),
        ] {
            push_blank(
                &mut examples,
                &format!("{} {field}", reading.diagnosis_id),
                value,
            );
        }
        if reading.classification_summary.len() != 7 {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                "classificationSummary",
                "feature extension diagnosis must report all seven classification axes",
            ));
        }
        let summary_labels = reading
            .classification_summary
            .iter()
            .map(|summary| summary.axis.as_str())
            .collect::<BTreeSet<_>>();
        if summary_labels != required_labels {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                "classificationSummary.axis",
                "feature extension diagnosis must retain the seven named attribution labels",
            ));
        }
        if reading.attribution_records.is_empty() {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                "attributionRecords",
                "feature extension diagnosis must retain witness-level attribution records",
            ));
        }
        if !reading
            .attribution_records
            .iter()
            .any(|record| record.labels.len() > 1)
        {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                "attributionRecords.labels",
                "at least one witness must demonstrate non-disjoint multi-label attribution",
            ));
        }
        if reading.non_conclusions.is_empty() || has_blank(&reading.non_conclusions) {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                "nonConclusions",
                "feature extension diagnosis must retain machine-readable non-conclusions",
            ));
        }
        if !reading.fieldsig_boundary.contains("FieldSig") {
            examples.push(generic_validation_example(
                &reading.diagnosis_id,
                &reading.fieldsig_boundary,
                "feature extension diagnosis must preserve the ArchSig / FieldSig boundary",
            ));
        }
        for record in &reading.attribution_records {
            push_blank(
                &mut examples,
                &format!("{} attribution.witnessRef", reading.diagnosis_id),
                &record.witness_ref,
            );
            if record.labels.is_empty() || has_blank(&record.labels) {
                examples.push(generic_validation_example(
                    &reading.diagnosis_id,
                    &record.witness_ref,
                    "witness attribution must carry one or more labels",
                ));
            }
            if record.observation_refs.is_empty() && record.source_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.diagnosis_id,
                    &record.witness_ref,
                    "witness attribution must retain source or observation refs",
                ));
            }
            for label in &record.labels {
                if !required_labels.contains(label.as_str()) {
                    examples.push(generic_validation_example(
                        &reading.diagnosis_id,
                        label,
                        "witness attribution carries an unknown feature-extension label",
                    ));
                }
            }
            push_blank(
                &mut examples,
                &format!("{} attribution.reading", reading.diagnosis_id),
                &record.reading,
            );
        }
    }
    for diagnosis_ref in &packet
        .boundary_holonomy_reading_family
        .extension_diagnosis_refs
    {
        if !diagnosis_ids.contains(diagnosis_ref.as_str()) {
            examples.push(generic_validation_example(
                &packet.boundary_holonomy_reading_family.reading_family_id,
                diagnosis_ref,
                "boundary holonomy reading family references an unknown feature extension diagnosis",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-feature-extension-diagnosis-surface",
        "packet reports non-disjoint feature-extension multi-label attribution without replacing FieldSig evolution analysis",
        examples,
        "fail",
    )
}

fn check_monodromy_boundary_schema_foundation(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let store_refs = &packet.arch_map_store_refs;
    let axis_refs = packet
        .signature_axes
        .iter()
        .flat_map(|axis| [axis.signature_axis_id.as_str(), axis.axis_ref.as_str()])
        .collect::<BTreeSet<_>>();

    push_blank(
        &mut examples,
        "archMapStoreRefs.refSetId",
        &store_refs.ref_set_id,
    );
    if store_refs.arch_map_ref != packet.arch_map_ref.artifact_id {
        examples.push(generic_validation_example(
            "archMapStoreRefs.archMapRef",
            &store_refs.arch_map_ref,
            "ArchMapStore refs must connect back to the packet ArchMap ref",
        ));
    }
    for (field, artifact, kind, schema_version) in [
        (
            "deltaRef",
            &store_refs.delta_ref,
            "archmap-delta",
            "archmap-delta-v0",
        ),
        (
            "commitRef",
            &store_refs.commit_ref,
            "archmap-commit",
            "archmap-commit-v0",
        ),
        (
            "snapshotRef",
            &store_refs.snapshot_ref,
            "archmap-snapshot",
            "archmap-snapshot-v0",
        ),
        (
            "indexRef",
            &store_refs.index_ref,
            "archmap-index",
            "archmap-index-v0",
        ),
    ] {
        push_blank(
            &mut examples,
            &format!("archMapStoreRefs.{field}.artifactId"),
            &artifact.artifact_id,
        );
        if artifact.artifact_kind != kind || artifact.schema_version != schema_version {
            examples.push(generic_validation_example(
                &format!("archMapStoreRefs.{field}"),
                &format!("{}:{}", artifact.artifact_kind, artifact.schema_version),
                "ArchMapStore refs must preserve delta / commit / snapshot / index schema kinds",
            ));
        }
    }
    push_blank(
        &mut examples,
        "archMapStoreRefs.rawDiffBoundary",
        &store_refs.raw_diff_boundary,
    );
    push_blank(
        &mut examples,
        "archMapStoreRefs.compactionBoundary",
        &store_refs.compaction_boundary,
    );
    if store_refs.non_conclusions.is_empty() || has_blank(&store_refs.non_conclusions) {
        examples.push(generic_validation_example(
            &store_refs.ref_set_id,
            "nonConclusions",
            "ArchMapStore refs must keep non-conclusions explicit",
        ));
    }

    check_monodromy_family(
        "monodromyReadingFamily",
        &packet.monodromy_reading_family.reading_family_id,
        &packet.monodromy_reading_family.status,
        &packet.monodromy_reading_family.arch_map_store_ref_set_ref,
        &packet.monodromy_reading_family.selected_axis_refs,
        &packet.monodromy_reading_family.distance_kind,
        &packet.monodromy_reading_family.weight_policy,
        &packet.monodromy_reading_family.coverage_policy,
        packet.monodromy_reading_family.measured_axis_count,
        packet.monodromy_reading_family.unmeasured_axis_count,
        packet.monodromy_reading_family.positive_witness_count,
        packet.monodromy_reading_family.coverage_blocker_count,
        &packet.monodromy_reading_family.reading_boundary,
        &packet.monodromy_reading_family.evidence_boundary,
        &packet.monodromy_reading_family.non_conclusions,
        &store_refs.ref_set_id,
        &axis_refs,
        &mut examples,
    );
    check_monodromy_family(
        "boundaryHolonomyReadingFamily",
        &packet.boundary_holonomy_reading_family.reading_family_id,
        &packet.boundary_holonomy_reading_family.status,
        &packet
            .boundary_holonomy_reading_family
            .arch_map_store_ref_set_ref,
        &packet.boundary_holonomy_reading_family.selected_axis_refs,
        &packet.boundary_holonomy_reading_family.distance_kind,
        &packet.boundary_holonomy_reading_family.weight_policy,
        &packet.boundary_holonomy_reading_family.coverage_policy,
        packet.boundary_holonomy_reading_family.measured_axis_count,
        packet
            .boundary_holonomy_reading_family
            .unmeasured_axis_count,
        packet
            .boundary_holonomy_reading_family
            .positive_witness_count,
        packet
            .boundary_holonomy_reading_family
            .coverage_blocker_count,
        &packet.boundary_holonomy_reading_family.reading_boundary,
        &packet.boundary_holonomy_reading_family.evidence_boundary,
        &packet.boundary_holonomy_reading_family.non_conclusions,
        &store_refs.ref_set_id,
        &axis_refs,
        &mut examples,
    );
    push_blank(
        &mut examples,
        "monodromyReadingFamily.aggregateReadingKind",
        &packet.monodromy_reading_family.aggregate_reading_kind,
    );
    push_blank(
        &mut examples,
        "boundaryHolonomyReadingFamily.attributionBoundary",
        &packet.boundary_holonomy_reading_family.attribution_boundary,
    );

    check_from_examples(
        "archsig-analysis-packet-monodromy-boundary-foundation",
        "packet defines ArchMapStore refs and monodromy / boundary holonomy reading family policy surfaces",
        examples,
        "fail",
    )
}

#[allow(clippy::too_many_arguments)]
fn check_monodromy_family(
    field: &str,
    reading_family_id: &str,
    status: &str,
    arch_map_store_ref_set_ref: &str,
    selected_axis_refs: &[String],
    distance_kind: &str,
    weight_policy: &str,
    coverage_policy: &str,
    measured_axis_count: usize,
    unmeasured_axis_count: usize,
    positive_witness_count: usize,
    coverage_blocker_count: usize,
    reading_boundary: &str,
    evidence_boundary: &str,
    non_conclusions: &[String],
    expected_ref_set_id: &str,
    known_axis_refs: &BTreeSet<&str>,
    examples: &mut Vec<ValidationExample>,
) {
    push_blank(
        examples,
        &format!("{field}.readingFamilyId"),
        reading_family_id,
    );
    push_blank(examples, &format!("{field}.status"), status);
    if status == "schemaFoundationOnly" {
        examples.push(generic_validation_example(
            reading_family_id,
            status,
            "reading family still has schema-only status; measured, partial, or blocked status must be derived from evidence counts",
        ));
    }
    if !matches!(
        status,
        "measured" | "partial" | "blockedByCoverageGap" | "measuredZeroUnderSelectedAxes"
    ) {
        examples.push(generic_validation_example(
            reading_family_id,
            status,
            "reading family status must be evidence-derived",
        ));
    }
    if measured_axis_count == 0 && status != "blockedByCoverageGap" {
        examples.push(generic_validation_example(
            reading_family_id,
            "measuredAxisCount",
            "status must be blocked when no measured axes exist",
        ));
    }
    if status == "measured" && (positive_witness_count == 0 || coverage_blocker_count > 0) {
        examples.push(generic_validation_example(
            reading_family_id,
            "positiveWitnessCount/coverageBlockerCount",
            "measured status requires positive witnesses and no coverage blockers",
        ));
    }
    if status == "partial" && unmeasured_axis_count == 0 && coverage_blocker_count == 0 {
        examples.push(generic_validation_example(
            reading_family_id,
            "unmeasuredAxisCount/coverageBlockerCount",
            "partial status must be backed by unmeasured axes or coverage blockers",
        ));
    }
    if arch_map_store_ref_set_ref != expected_ref_set_id {
        examples.push(generic_validation_example(
            reading_family_id,
            arch_map_store_ref_set_ref,
            "reading family must reference archMapStoreRefs.refSetId",
        ));
    }
    if selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_family_id,
            "selectedAxisRefs",
            "reading family must retain selected measurement axes",
        ));
    }
    for axis_ref in selected_axis_refs {
        if !known_axis_refs.contains(axis_ref.as_str()) {
            examples.push(generic_validation_example(
                reading_family_id,
                axis_ref,
                "reading family selectedAxisRefs must resolve to packet signature axis refs",
            ));
        }
    }
    push_blank(examples, &format!("{field}.distanceKind"), distance_kind);
    push_blank(examples, &format!("{field}.weightPolicy"), weight_policy);
    push_blank(
        examples,
        &format!("{field}.coveragePolicy"),
        coverage_policy,
    );
    push_blank(
        examples,
        &format!("{field}.readingBoundary"),
        reading_boundary,
    );
    push_blank(
        examples,
        &format!("{field}.evidenceBoundary"),
        evidence_boundary,
    );
    if non_conclusions.is_empty() || has_blank(non_conclusions) {
        examples.push(generic_validation_example(
            reading_family_id,
            "nonConclusions",
            "reading family must keep non-conclusions explicit",
        ));
    }
}

fn check_generated_middle_layer_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let generated_shape_ids = packet
        .generated_atom_shapes
        .iter()
        .map(|shape| shape.atom_shape_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut generated_molecule_shape_refs = BTreeMap::<String, BTreeSet<String>>::new();
    let mut generated_molecule_shape_pairs = BTreeSet::<(String, String, String)>::new();
    if packet.generated_atom_shapes.is_empty() {
        examples.push(generic_validation_example(
            "generatedAtomShapes",
            "empty",
            "packet must expose AtomShape records generated from observed atoms",
        ));
    }
    if packet.generated_molecules.is_empty() {
        examples.push(generic_validation_example(
            "generatedMolecules",
            "empty",
            "packet must expose generated molecules before law and obstruction readings",
        ));
    }
    if packet.generated_law_inputs.is_empty() {
        examples.push(generic_validation_example(
            "generatedLawInputs",
            "empty",
            "packet must expose generated law inputs derived from generated molecules",
        ));
    }
    if !packet.obstruction_circuits.is_empty() && packet.generated_obstructions.is_empty() {
        examples.push(generic_validation_example(
            "generatedObstructions",
            "empty",
            "packet must connect obstruction circuits to generated law inputs and molecules",
        ));
    }
    if !packet.repair_operation_candidates.is_empty() && packet.generated_repair_targets.is_empty()
    {
        examples.push(generic_validation_example(
            "generatedRepairTargets",
            "empty",
            "packet must localize repair candidates to generated shape-level targets",
        ));
    }
    if packet
        .generated_molecules
        .iter()
        .any(|molecule| molecule.atom_observation_refs.len() > 1)
        && packet.viewer_distance_inputs.is_empty()
    {
        examples.push(generic_validation_example(
            "viewerDistanceInputs",
            "empty",
            "packet must expose AtomShape-based distance inputs for viewer layout",
        ));
    }

    for shape in &packet.generated_atom_shapes {
        push_blank(
            &mut examples,
            &shape.atom_shape_id,
            &shape.atom_observation_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} family", shape.atom_shape_id),
            &shape.family,
        );
        push_blank(
            &mut examples,
            &format!("{} axis", shape.atom_shape_id),
            &shape.axis,
        );
        push_blank(
            &mut examples,
            &format!("{} valenceSummary", shape.atom_shape_id),
            &shape.valence_summary,
        );
        if shape.ports.is_empty() {
            examples.push(generic_validation_example(
                &shape.atom_shape_id,
                "ports",
                "generated AtomShape must expose at least one valence port",
            ));
        }
    }
    for molecule in &packet.generated_molecules {
        push_blank(
            &mut examples,
            &molecule.generated_molecule_id,
            &molecule.source_molecule_observation_ref,
        );
        let shape_ref_set = molecule
            .atom_shape_refs
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        generated_molecule_shape_refs.insert(
            molecule.generated_molecule_id.clone(),
            shape_ref_set.clone(),
        );
        let molecule_shape_refs = shape_ref_set.into_iter().collect::<Vec<_>>();
        for left_index in 0..molecule_shape_refs.len() {
            for right_index in (left_index + 1)..molecule_shape_refs.len() {
                let (left, right) = ordered_shape_pair(
                    &molecule_shape_refs[left_index],
                    &molecule_shape_refs[right_index],
                );
                generated_molecule_shape_pairs.insert((
                    molecule.generated_molecule_id.clone(),
                    left,
                    right,
                ));
            }
        }
        if molecule.atom_shape_refs.is_empty() {
            examples.push(generic_validation_example(
                &molecule.generated_molecule_id,
                "atomShapeRefs",
                "generated molecule must retain AtomShape refs",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} notArbitrarySetBoundary", molecule.generated_molecule_id),
            &molecule.not_arbitrary_set_boundary,
        );
    }
    for input in &packet.generated_law_inputs {
        push_blank(
            &mut examples,
            &input.generated_law_input_id,
            &input.generated_molecule_ref,
        );
        if input.law_refs.is_empty()
            || input.atom_shape_refs.is_empty()
            || input.applicable_law_axes.is_empty()
            || input.local_statuses.is_empty()
        {
            examples.push(generic_validation_example(
                &input.generated_law_input_id,
                "lawRefs/applicableLawAxes/atomShapeRefs/localStatuses",
                "generated law input must connect applicable law axes to AtomShape-backed molecules and local status",
            ));
        }
    }
    for obstruction in &packet.generated_obstructions {
        push_blank(
            &mut examples,
            &obstruction.generated_obstruction_id,
            &obstruction.obstruction_circuit_ref,
        );
        if obstruction.generated_law_input_refs.is_empty()
            || obstruction.generated_molecule_refs.is_empty()
            || obstruction.local_status.is_empty()
            || obstruction.blocker_status.is_empty()
        {
            examples.push(generic_validation_example(
                &obstruction.generated_obstruction_id,
                "generatedLawInputRefs/generatedMoleculeRefs/localStatus/blockerStatus",
                "generated obstruction must keep generated refs and local violated / blocked status",
            ));
        }
    }
    for target in &packet.generated_repair_targets {
        push_blank(&mut examples, &target.repair_target_id, &target.target_kind);
        push_blank(
            &mut examples,
            &format!("{} requiredPortOrSlot", target.repair_target_id),
            &target.required_port_or_slot,
        );
        if target.generated_obstruction_refs.is_empty() || target.atom_shape_refs.is_empty() {
            examples.push(generic_validation_example(
                &target.repair_target_id,
                "generatedObstructionRefs/atomShapeRefs",
                "generated repair target must localize to generated obstruction and AtomShape refs",
            ));
        }
    }
    let mut covered_distance_pairs = BTreeSet::<(String, String, String)>::new();
    for distance in &packet.viewer_distance_inputs {
        push_blank(
            &mut examples,
            &distance.distance_input_id,
            &distance.distance_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} sourceRef", distance.distance_input_id),
            &distance.source_ref,
        );
        push_blank(
            &mut examples,
            &format!("{} targetRef", distance.distance_input_id),
            &distance.target_ref,
        );
        let generated_molecule_ref = distance.generated_molecule_ref.as_deref();
        if generated_molecule_ref.is_none_or(|molecule_ref| molecule_ref.trim().is_empty()) {
            examples.push(generic_validation_example(
                &distance.distance_input_id,
                "generatedMoleculeRef",
                "viewer distance input must be anchored to the generated molecule whose AtomShape pair it compares",
            ));
        }
        if distance.atom_shape_refs.len() != 2 || distance.coordinate_components.len() < 5 {
            examples.push(generic_validation_example(
                &distance.distance_input_id,
                "atomShapeRefs/coordinateComponents",
                "viewer distance input must compare exactly two AtomShape coordinate records with full coordinate components",
            ));
        }
        for shape_ref in &distance.atom_shape_refs {
            if !generated_shape_ids.contains(shape_ref.as_str()) {
                examples.push(generic_validation_example(
                    &distance.distance_input_id,
                    "atomShapeRefs",
                    "viewer distance input must refer to generated AtomShape records",
                ));
            }
        }
        if let Some(molecule_ref) = generated_molecule_ref {
            if let Some(shape_refs) = generated_molecule_shape_refs.get(molecule_ref) {
                if distance.atom_shape_refs.len() == 2 {
                    let left = &distance.atom_shape_refs[0];
                    let right = &distance.atom_shape_refs[1];
                    if !shape_refs.contains(left) || !shape_refs.contains(right) {
                        examples.push(generic_validation_example(
                            &distance.distance_input_id,
                            "generatedMoleculeRef/atomShapeRefs",
                            "viewer distance input must compare AtomShape refs belonging to its generated molecule",
                        ));
                    } else {
                        let (left, right) = ordered_shape_pair(left, right);
                        covered_distance_pairs.insert((molecule_ref.to_string(), left, right));
                    }
                }
            } else if !molecule_ref.trim().is_empty() {
                examples.push(generic_validation_example(
                    &distance.distance_input_id,
                    "generatedMoleculeRef",
                    "viewer distance input must reference an existing generated molecule",
                ));
            }
        }
        match (
            distance.distance_value,
            viewer_distance_delta_sum(&distance.coordinate_components),
        ) {
            (Some(value), Some(delta_sum)) if value == delta_sum => {}
            (Some(_), Some(_)) => examples.push(generic_validation_example(
                &distance.distance_input_id,
                "distanceValue/coordinateComponents",
                "viewer distance value must equal the sum of AtomShape coordinate delta components",
            )),
            _ => examples.push(generic_validation_example(
                &distance.distance_input_id,
                "distanceValue/coordinateComponents",
                "viewer distance input must carry a computed distance value and delta components",
            )),
        }
    }
    for (molecule_ref, left, right) in generated_molecule_shape_pairs {
        if !covered_distance_pairs.contains(&(molecule_ref.clone(), left.clone(), right.clone())) {
            examples.push(generic_validation_example(
                &molecule_ref,
                "viewerDistanceInputs",
                "viewer distance inputs must cover every generated molecule AtomShape pair",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-generated-middle-layer",
        "packet materializes generated AtomShape, molecule, law input, obstruction, repair target, and viewer distance inputs",
        examples,
        "fail",
    )
}

fn ordered_shape_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

fn viewer_distance_delta_sum(coordinate_components: &[String]) -> Option<i64> {
    let mut sum = 0i64;
    let mut found = false;
    for component in coordinate_components {
        let (_prefix, delta) = component.rsplit_once("delta=")?;
        sum += delta.parse::<i64>().ok()?;
        found = true;
    }
    found.then_some(sum)
}

fn check_part4_distance_foundation_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let foundation = &packet.part4_distance_foundation;
    if foundation.foundation_id.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation",
            "foundationId",
            "packet must expose a Part IV distance foundation id",
        ));
    }
    push_blank(
        &mut examples,
        "part4DistanceFoundation.profile.profileId",
        &foundation.profile.profile_id,
    );
    push_blank(
        &mut examples,
        "part4DistanceFoundation.profile.profileSourceRef",
        &foundation.profile.profile_source_ref,
    );
    if foundation.diagnostic_scope.distance_profile_ref != foundation.profile.profile_id {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope.distanceProfileRef",
            "profileRef",
            "DiagnosticScope must point to the selected DistanceProfile, not a stale or unrelated profile",
        ));
    }
    if foundation.profile.atom_weights.is_empty() || foundation.profile.signature_weights.is_empty()
    {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.profile",
            "atomWeights/signatureWeights",
            "DistanceProfile must record selected atom and signature weights instead of an implicit score",
        ));
    }
    if !foundation
        .profile
        .unmeasured_policy
        .to_ascii_lowercase()
        .contains("not zero")
    {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.profile",
            "unmeasuredPolicy",
            "DistanceProfile must state that unmeasured is not zero",
        ));
    }
    push_blank(
        &mut examples,
        "part4DistanceFoundation.diagnosticScope.scopeId",
        &foundation.diagnostic_scope.scope_id,
    );
    if foundation.diagnostic_scope.observed_atom_refs.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope",
            "observedAtomRefs",
            "DiagnosticScope must retain ArchMap observed Atom refs",
        ));
    }
    if foundation.diagnostic_scope.blocker_refs.is_empty()
        && !foundation.diagnostic_scope.unmeasured_axis_refs.is_empty()
    {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope",
            "blockerRefs",
            "unmeasured axes must retain blocker refs",
        ));
    }
    let scope_measured_axis_refs = foundation
        .diagnostic_scope
        .measured_axis_refs
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let scope_unmeasured_axis_refs = foundation
        .diagnostic_scope
        .unmeasured_axis_refs
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let signature_axis_aliases = part4_signature_axis_aliases(&packet.signature_distance_readings);
    let scope_measured_axis_aliases = scope_measured_axis_refs
        .iter()
        .flat_map(|axis| part4_canonical_axis_refs(axis, &signature_axis_aliases))
        .collect::<BTreeSet<_>>();
    let scope_unmeasured_axis_aliases = scope_unmeasured_axis_refs
        .iter()
        .flat_map(|axis| part4_canonical_axis_refs(axis, &signature_axis_aliases))
        .collect::<BTreeSet<_>>();
    let overlap = scope_measured_axis_refs
        .intersection(&scope_unmeasured_axis_refs)
        .cloned()
        .collect::<Vec<_>>();
    if !overlap.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope",
            &format!("axis status overlap: {}", overlap.join(", ")),
            "DiagnosticScope must not classify the same axis as measured and unmeasured",
        ));
    }
    for blocker in &foundation.diagnostic_scope.blocker_refs {
        if blocker.starts_with("issue:#") {
            examples.push(generic_validation_example(
                "part4DistanceFoundation.diagnosticScope.blockerRefs",
                blocker,
                "DiagnosticScope blocker refs must reflect evaluator evidence gaps after measurement, not closed implementation issue placeholders",
            ));
        }
        if blocker.strip_prefix("unmeasuredAxis:").is_some_and(|axis| {
            part4_canonical_axis_refs(axis, &signature_axis_aliases)
                .into_iter()
                .any(|axis| scope_measured_axis_aliases.contains(&axis))
        }) {
            examples.push(generic_validation_example(
                "part4DistanceFoundation.diagnosticScope.blockerRefs",
                blocker,
                "DiagnosticScope blocker refs must not retain an unmeasured-axis blocker for a measured or zero axis",
            ));
        }
    }
    let expected_measured_axis_refs = packet
        .signature_distance_readings
        .iter()
        .flat_map(|reading| reading.measured_axis_refs.iter().cloned())
        .collect::<BTreeSet<_>>();
    let expected_measured_axis_aliases = expected_measured_axis_refs
        .iter()
        .flat_map(|axis| part4_canonical_axis_refs(axis, &signature_axis_aliases))
        .collect::<BTreeSet<_>>();
    let expected_unmeasured_axis_refs = packet
        .signature_distance_readings
        .iter()
        .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned())
        .chain(
            packet
                .signature_distance_readings
                .iter()
                .flat_map(|reading| reading.incomparable_axis_refs.iter().cloned()),
        )
        .chain(
            packet
                .operation_distance_readings
                .iter()
                .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned()),
        )
        .chain(
            packet
                .curvature_mass_readings
                .iter()
                .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned()),
        )
        .filter(|axis| {
            part4_canonical_axis_refs(axis, &signature_axis_aliases)
                .into_iter()
                .all(|axis| !expected_measured_axis_aliases.contains(&axis))
        })
        .collect::<BTreeSet<_>>();
    let missing_measured = expected_measured_axis_refs
        .difference(&scope_measured_axis_refs)
        .cloned()
        .collect::<Vec<_>>();
    if !missing_measured.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope.measuredAxisRefs",
            &format!("missing measured axes: {}", missing_measured.join(", ")),
            "DiagnosticScope measuredAxisRefs must include measured or zero signature-distance axes",
        ));
    }
    let stale_unmeasured = scope_unmeasured_axis_aliases
        .intersection(&expected_measured_axis_aliases)
        .cloned()
        .collect::<Vec<_>>();
    if !stale_unmeasured.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope.unmeasuredAxisRefs",
            &format!("measured axes still unmeasured: {}", stale_unmeasured.join(", ")),
            "Measured or zero signature-distance axes must be removed from DiagnosticScope unmeasuredAxisRefs",
        ));
    }
    let missing_unmeasured = expected_unmeasured_axis_refs
        .iter()
        .filter(|axis| {
            part4_canonical_axis_refs(axis, &signature_axis_aliases)
                .into_iter()
                .all(|axis| !scope_unmeasured_axis_aliases.contains(&axis))
        })
        .cloned()
        .collect::<Vec<_>>();
    if !missing_unmeasured.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.diagnosticScope.unmeasuredAxisRefs",
            &format!("missing unmeasured axes: {}", missing_unmeasured.join(", ")),
            "DiagnosticScope unmeasuredAxisRefs must include non-measured Part IV evaluator axes without reclassifying measured signature axes",
        ));
    }
    if foundation.supporting_distances.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.supportingDistances",
            "empty",
            "Part IV distance foundation must enumerate distance families for downstream evaluators",
        ));
    }

    let allowed = BTreeSet::from([
        "measured",
        "zero",
        "unmeasured",
        "unavailable",
        "incomparable",
        "infinite",
        "blocked",
    ]);
    let mut counts = ArchSigDistanceStatusSummaryV0::default();
    for distance in &foundation.supporting_distances {
        push_blank(
            &mut examples,
            &format!("{} distanceFamily", distance.distance_id),
            &distance.distance_family,
        );
        push_blank(
            &mut examples,
            &format!("{} distanceKind", distance.distance_id),
            &distance.distance_kind,
        );
        push_blank(
            &mut examples,
            &format!("{} profileRef", distance.distance_id),
            &distance.profile_ref,
        );
        if distance.profile_ref != foundation.profile.profile_id
            || distance.diagnostic_scope_ref != foundation.diagnostic_scope.scope_id
        {
            examples.push(generic_validation_example(
                &distance.distance_id,
                "profile/scope",
                "supporting DistanceValue rows must be tied to the selected DistanceProfile and DiagnosticScope",
            ));
        }
        let status = distance.value.status.as_str();
        if !allowed.contains(status) {
            examples.push(generic_validation_example(
                &distance.distance_id,
                status,
                "DistanceValue status must be measured, zero, unmeasured, unavailable, incomparable, infinite, or blocked",
            ));
        }
        match status {
            "measured" => counts.measured_count += 1,
            "zero" => counts.zero_count += 1,
            "unmeasured" => counts.unmeasured_count += 1,
            "unavailable" => counts.unavailable_count += 1,
            "incomparable" => counts.incomparable_count += 1,
            "infinite" => counts.infinite_count += 1,
            "blocked" => counts.blocked_count += 1,
            "schemaFoundationOnly" => counts.schema_foundation_only_count += 1,
            _ => {}
        }
        if matches!(status, "measured" | "zero") {
            if distance.value.provenance_refs.is_empty()
                || distance.value.evaluator_basis_refs.is_empty()
                || distance.value.coverage_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &distance.distance_id,
                    "provenance/evaluatorBasis/coverage",
                    "measured or zero distances must retain provenance, evaluator basis, and coverage refs",
                ));
            }
            if part4_distance_refs_are_concern_only(
                &distance.value.provenance_refs,
                &distance.value.evaluator_basis_refs,
            ) {
                examples.push(generic_validation_example(
                    &distance.distance_id,
                    "concern-only provenance",
                    "concern cues alone cannot back a measured or zero Part IV distance",
                ));
            }
        } else if distance.value.blocker_refs.is_empty() {
            examples.push(generic_validation_example(
                &distance.distance_id,
                "blockerRefs",
                "unmeasured, unavailable, incomparable, infinite, or blocked distances must retain blocker refs",
            ));
        }
        if contains_hard_coded_marker(&distance.value.provenance_refs)
            || contains_hard_coded_marker(&distance.value.evaluator_basis_refs)
        {
            examples.push(generic_validation_example(
                &distance.distance_id,
                "hard-coded fixture marker",
                "Part IV distance values must not be backed by hard-coded fixture markers",
            ));
        }
    }
    if counts != foundation.status_summary {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.statusSummary",
            "mismatch",
            "statusSummary must equal the actual supporting DistanceValue statuses",
        ));
    }
    if foundation.status_summary.schema_foundation_only_count != 0 {
        examples.push(generic_validation_example(
            "part4DistanceFoundation.statusSummary",
            "schemaFoundationOnly",
            "schemaFoundationOnly must not be counted as a measured or acceptable distance status",
        ));
    }

    check_from_examples(
        "archsig-analysis-packet-part4-distance-foundation",
        "packet exposes Part IV DistanceValue, DistanceProfile, DiagnosticScope, and anti-proxy distance provenance",
        examples,
        "fail",
    )
}

fn check_part4_distance_coverage_ledger_surface(
    packet: &ArchSigAnalysisPacketV0,
) -> ValidationCheck {
    let mut examples = Vec::new();
    let ledger = &packet.part4_distance_coverage_ledger;
    if ledger.is_empty() {
        examples.push(generic_validation_example(
            "part4DistanceCoverageLedger",
            "empty",
            "Part IV distance coverage ledger must enumerate the definition families covered by the packet",
        ));
    }
    examples.extend(duplicate_examples(
        "part4DistanceCoverageLedger.ledgerEntryId",
        duplicates(ledger.iter().map(|entry| entry.ledger_entry_id.as_str())),
    ));

    let expected_entries = BTreeMap::from([
        ("part4-ledger:distance-aat", ("definition:1.1", "foundation")),
        (
            "part4-ledger:atom-geometry",
            ("definitions:2.1-2.5", "atomGeometry"),
        ),
        (
            "part4-ledger:configuration-context",
            ("definitions:3.1-3.2", "configurationGeometry"),
        ),
        (
            "part4-ledger:signature-geometry",
            ("definitions:4.1-4.4", "signatureGeometry"),
        ),
        (
            "part4-ledger:operation-geometry",
            ("definitions:5.1-5.5", "operationGeometry"),
        ),
        (
            "part4-ledger:obstruction-curvature",
            ("definitions:6.1-6.3", "curvatureGeometry"),
        ),
        (
            "part4-ledger:homotopy-filling",
            ("definitions:7.1-7.4", "homotopyFillingGeometry"),
        ),
        (
            "part4-ledger:representation-metric",
            ("definitions:8.1-8.2", "representationMetric"),
        ),
        (
            "part4-ledger:measurement-boundary",
            ("definitions:9.1-9.3", "measurementBoundary"),
        ),
        (
            "part4-ledger:bounded-diagnostic-conclusion",
            ("definitions:10.1-10.2", "boundedDiagnosticConclusion"),
        ),
    ]);
    let ledger_by_id = ledger
        .iter()
        .map(|entry| (entry.ledger_entry_id.as_str(), entry))
        .collect::<BTreeMap<_, _>>();
    for (entry_id, (definition_ref, distance_family)) in &expected_entries {
        match ledger_by_id.get(entry_id) {
            Some(entry) => {
                if entry.part4_definition_ref != *definition_ref {
                    examples.push(generic_validation_example(
                        &entry.ledger_entry_id,
                        &entry.part4_definition_ref,
                        "coverage ledger entry must keep the expected Part IV definition ref",
                    ));
                }
                if entry.distance_family != *distance_family {
                    examples.push(generic_validation_example(
                        &entry.ledger_entry_id,
                        &entry.distance_family,
                        "coverage ledger entry must keep the expected Part IV distance family",
                    ));
                }
            }
            None => examples.push(generic_validation_example(
                "part4DistanceCoverageLedger",
                entry_id,
                "coverage ledger must include every first-class Part IV definition family",
            )),
        }
    }

    let supporting_by_family = packet
        .part4_distance_foundation
        .supporting_distances
        .iter()
        .map(|distance| (distance.distance_family.as_str(), distance))
        .collect::<BTreeMap<_, _>>();
    let foundation_status = if packet.part4_distance_foundation.status_summary.blocked_count > 0 {
        "blocked"
    } else if packet
        .part4_distance_foundation
        .status_summary
        .unmeasured_count
        > 0
    {
        "partial"
    } else if packet
        .part4_distance_foundation
        .status_summary
        .measured_count
        > 0
        || packet.part4_distance_foundation.status_summary.zero_count > 0
    {
        "measured"
    } else {
        "unmeasured"
    };
    let allowed_coverage = BTreeSet::from([
        "primary",
        "partial",
        "primary-blocked",
        "raw-packet-only",
        "missing-readings",
        "blocked-without-readings",
        "not-applicable",
    ]);
    let allowed_measurement = BTreeSet::from([
        "measured",
        "zero",
        "unmeasured",
        "unavailable",
        "incomparable",
        "infinite",
        "blocked",
        "partial",
    ]);

    for entry in ledger {
        push_blank(
            &mut examples,
            "part4DistanceCoverageLedger.ledgerEntryId",
            &entry.ledger_entry_id,
        );
        push_blank(
            &mut examples,
            &format!("{} definitionTitle", entry.ledger_entry_id),
            &entry.definition_title,
        );
        push_blank(
            &mut examples,
            &format!("{} theorySectionRef", entry.ledger_entry_id),
            &entry.theory_section_ref,
        );
        if !entry
            .theory_section_ref
            .contains("part_4_distance_measure_geometry.md")
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                &entry.theory_section_ref,
                "coverage ledger theory refs must point back to the Part IV source text",
            ));
        }
        if !allowed_coverage.contains(entry.coverage_status.as_str())
            || entry.coverage_status == "schemaFoundationOnly"
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                &entry.coverage_status,
                "coverageStatus must be a bounded ledger status and never schemaFoundationOnly",
            ));
        }
        if !allowed_measurement.contains(entry.measurement_status.as_str())
            || entry.measurement_status == "schemaFoundationOnly"
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                &entry.measurement_status,
                "measurementStatus must mirror the foundation/supporting distance state and never schemaFoundationOnly",
            ));
        }
        if entry.primary_artifact_refs.is_empty() || has_blank(&entry.primary_artifact_refs) {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                "primaryArtifactRefs",
                "coverage ledger entries must point to primary output artifacts",
            ));
        }
        if entry.raw_packet_refs.is_empty() || has_blank(&entry.raw_packet_refs) {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                "rawPacketRefs",
                "coverage ledger entries must point to raw packet rows",
            ));
        }
        if entry.evidence_boundary.trim().is_empty()
            || entry
                .evidence_boundary
                .to_ascii_lowercase()
                .contains("prove")
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                "evidenceBoundary",
                "coverage ledger evidenceBoundary must be non-empty and avoid proof-style claims",
            ));
        }
        if !entry
            .non_conclusions
            .iter()
            .any(|non_conclusion| non_conclusion.contains("not a Lean theorem proof"))
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                "nonConclusions",
                "coverage ledger entries must preserve ArchSig/Lean boundary language",
            ));
        }
        for follow_up in &entry.follow_up_issue_refs {
            if !follow_up.starts_with('#') {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    follow_up,
                    "follow-up issue refs must use repo-local # issue refs",
                ));
            }
        }

        if let Some(supporting_distance) = supporting_by_family.get(entry.distance_family.as_str()) {
            if entry.measurement_status != supporting_distance.value.status {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    &entry.measurement_status,
                    "measurementStatus must match the selected supporting distance status for this Part IV family",
                ));
            }
            if entry.supporting_distance_refs.is_empty() {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    "supportingDistanceRefs",
                    "families backed by supporting distances must point to those distance rows",
                ));
            }
        } else if matches!(
            entry.distance_family.as_str(),
            "foundation" | "measurementBoundary" | "boundedDiagnosticConclusion"
        ) && entry.measurement_status != foundation_status
        {
            examples.push(generic_validation_example(
                &entry.ledger_entry_id,
                &entry.measurement_status,
                "foundation-level ledger rows must mirror the Part IV foundation status summary",
            ));
        }

        for support_ref in &entry.supporting_distance_refs {
            let Some((pointer, distance_id)) = support_ref.split_once('#') else {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    support_ref,
                    "supportingDistanceRefs must include a packet pointer and distance id",
                ));
                continue;
            };
            let Some(index) = pointer
                .strip_prefix("/part4DistanceFoundation/supportingDistances/")
                .and_then(|raw_index| raw_index.parse::<usize>().ok())
            else {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    support_ref,
                    "supportingDistanceRefs must resolve inside part4DistanceFoundation.supportingDistances",
                ));
                continue;
            };
            let Some(distance) = packet
                .part4_distance_foundation
                .supporting_distances
                .get(index)
            else {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    support_ref,
                    "supportingDistanceRefs index is out of range",
                ));
                continue;
            };
            if distance.distance_id != distance_id {
                examples.push(generic_validation_example(
                    &entry.ledger_entry_id,
                    support_ref,
                    "supportingDistanceRefs distance id must match the referenced supporting distance row",
                ));
            }
        }

        match entry.measurement_status.as_str() {
            "measured" | "zero" => {
                if entry.supporting_distance_refs.is_empty() {
                    examples.push(generic_validation_example(
                        &entry.ledger_entry_id,
                        "supportingDistanceRefs",
                        "measured or zero ledger rows must retain supporting distance refs",
                    ));
                }
            }
            "blocked" | "unmeasured" | "unavailable" | "incomparable" | "infinite" => {
                if entry.blocker_refs.is_empty() {
                    examples.push(generic_validation_example(
                        &entry.ledger_entry_id,
                        "blockerRefs",
                        "blocked, unmeasured, unavailable, incomparable, or infinite ledger rows must retain blocker refs",
                    ));
                }
            }
            _ => {}
        }
    }

    check_from_examples(
        "archsig-analysis-packet-part4-distance-coverage-ledger",
        "packet maps Part IV definition families to primary artifacts, raw rows, supporting distances, blockers, and follow-up issues",
        examples,
        "fail",
    )
}

fn check_atom_distance_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let atom_refs = packet
        .generated_atom_shapes
        .iter()
        .map(|shape| shape.atom_observation_ref.as_str())
        .collect::<BTreeSet<_>>();
    let viewer_distance_refs = packet
        .viewer_distance_inputs
        .iter()
        .map(|input| input.distance_input_id.as_str())
        .collect::<BTreeSet<_>>();
    if atom_refs.len() > 1 && packet.atom_distance_readings.is_empty() {
        examples.push(generic_validation_example(
            "atomDistanceReadings",
            "empty",
            "packet with multiple observed atoms must expose diagnostic Atom distance readings",
        ));
    }

    for reading in &packet.atom_distance_readings {
        push_blank(
            &mut examples,
            "atomDistanceReadings.atomDistanceReadingId",
            &reading.atom_distance_reading_id,
        );
        if reading.source_atom_ref == reading.target_atom_ref {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "atom pair",
                "Atom distance reading must compare two distinct atoms",
            ));
        }
        if !atom_refs.contains(reading.source_atom_ref.as_str())
            || !atom_refs.contains(reading.target_atom_ref.as_str())
        {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "sourceAtomRef/targetAtomRef",
                "Atom distance reading must refer to generated AtomShape-backed observed atoms",
            ));
        }
        if reading.molecule_refs.is_empty() {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "moleculeRefs",
                "Atom distance reading must be scoped by molecule/configuration membership",
            ));
        }
        if reading.distance_profile_ref != packet.part4_distance_foundation.profile.profile_id
            || reading.diagnostic_scope_ref
                != packet.part4_distance_foundation.diagnostic_scope.scope_id
        {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "profile/scope",
                "Atom distance reading must be tied to the selected Part IV DistanceProfile and DiagnosticScope",
            ));
        }
        if !reading
            .evidence_boundary
            .contains("viewer layout distance refs remain separate")
        {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "evidenceBoundary",
                "Atom diagnostic distance must separate viewer layout refs from the diagnostic value",
            ));
        }
        for viewer_ref in &reading.viewer_distance_input_refs {
            if !viewer_distance_refs.contains(viewer_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.atom_distance_reading_id,
                    viewer_ref,
                    "viewer distance refs must resolve when retained as separated layout evidence",
                ));
            }
        }

        check_atom_distance_value(
            &mut examples,
            &reading.atom_distance_reading_id,
            "fiberDistance",
            &reading.fiber_distance,
            "fiber:",
            true,
        );
        check_atom_distance_value(
            &mut examples,
            &reading.atom_distance_reading_id,
            "carrierDistance",
            &reading.carrier_distance,
            "carrier:",
            true,
        );
        check_atom_distance_value(
            &mut examples,
            &reading.atom_distance_reading_id,
            "valenceDistance",
            &reading.valence_distance,
            "valence:",
            true,
        );
        check_atom_distance_value(
            &mut examples,
            &reading.atom_distance_reading_id,
            "semanticAnchorDistance",
            &reading.semantic_anchor_distance,
            "semantic:",
            false,
        );

        let component_kinds = reading
            .component_distances
            .iter()
            .map(|component| component.component_kind.as_str())
            .collect::<BTreeSet<_>>();
        for required in ["fiber", "carrier", "valence", "semanticAnchor"] {
            if !component_kinds.contains(required) {
                examples.push(generic_validation_example(
                    &reading.atom_distance_reading_id,
                    required,
                    "Atom distance reading must retain all Part IV Atom geometry components",
                ));
            }
        }
        if matches!(
            reading.semantic_anchor_distance.status.as_str(),
            "unmeasured" | "blocked" | "unavailable"
        ) && matches!(
            reading.atom_layout_distance_bundle.status.as_str(),
            "measured" | "zero"
        ) {
            examples.push(generic_validation_example(
                &reading.atom_distance_reading_id,
                "atomLayoutDistanceBundle",
                "layout bundle must not become measured or zero while semantic anchor distance is unmeasured or blocked",
            ));
        }
        if matches!(
            reading.atom_layout_distance_bundle.status.as_str(),
            "measured" | "zero"
        ) {
            for required_prefix in ["fiber:", "carrier:", "valence:", "semantic:"] {
                if !reading
                    .atom_layout_distance_bundle
                    .evaluator_basis_refs
                    .iter()
                    .any(|basis| basis.starts_with(required_prefix))
                {
                    examples.push(generic_validation_example(
                        &reading.atom_distance_reading_id,
                        required_prefix,
                        "measured atom layout bundle must retain component evaluator basis refs",
                    ));
                }
            }
        }
    }

    check_from_examples(
        "archsig-analysis-packet-atom-distance-readings",
        "packet exposes proxy-free Part IV Atom distance evaluator readings separated from viewer layout distance",
        examples,
        "fail",
    )
}

fn check_configuration_distance_reading_surface(
    packet: &ArchSigAnalysisPacketV0,
) -> ValidationCheck {
    let mut examples = Vec::new();
    let atom_refs = packet
        .generated_atom_shapes
        .iter()
        .map(|shape| shape.atom_observation_ref.as_str())
        .collect::<BTreeSet<_>>();
    let molecule_refs = packet
        .generated_molecules
        .iter()
        .map(|molecule| molecule.generated_molecule_id.as_str())
        .collect::<BTreeSet<_>>();
    let has_atom_pairs = atom_refs.len() > 1;
    if has_atom_pairs && packet.configuration_distance_readings.is_empty() {
        examples.push(generic_validation_example(
            "configurationDistanceReadings",
            "empty",
            "packet with multiple observed atoms must expose Part IV configuration hypergraph distance readings",
        ));
    }
    let configuration_distance = packet
        .part4_distance_foundation
        .supporting_distances
        .iter()
        .find(|distance| distance.distance_family == "configurationGeometry");
    if let Some(distance) = configuration_distance {
        if !packet.configuration_distance_readings.is_empty()
            && distance.value.evaluator_basis_refs.is_empty()
        {
            examples.push(generic_validation_example(
                "part4DistanceFoundation.configurationGeometry",
                "evaluatorBasisRefs",
                "configurationGeometry supporting distance must be backed by configurationDistanceReadings",
            ));
        }
    }

    for reading in &packet.configuration_distance_readings {
        push_blank(
            &mut examples,
            "configurationDistanceReadings.configurationDistanceReadingId",
            &reading.configuration_distance_reading_id,
        );
        if reading.source_atom_ref == reading.target_atom_ref {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "atom pair",
                "Configuration distance reading must compare two distinct atoms",
            ));
        }
        if !atom_refs.contains(reading.source_atom_ref.as_str())
            || !atom_refs.contains(reading.target_atom_ref.as_str())
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "sourceAtomRef/targetAtomRef",
                "Configuration distance reading must refer to generated AtomShape-backed observed atoms",
            ));
        }
        if reading.distance_profile_ref != packet.part4_distance_foundation.profile.profile_id
            || reading.diagnostic_scope_ref
                != packet.part4_distance_foundation.diagnostic_scope.scope_id
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "profile/scope",
                "Configuration distance reading must be tied to the selected Part IV DistanceProfile and DiagnosticScope",
            ));
        }
        if reading.hypergraph_ref.is_empty()
            || (reading.typed_hyperedges.is_empty()
                && matches!(
                    reading.configuration_indexed_distance.status.as_str(),
                    "measured" | "zero"
                ))
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "typedHyperedges",
                "Configuration distance reading must retain typed ArchMap hyperedges, not a relation-count proxy",
            ));
        }
        if !reading
            .evidence_boundary
            .contains("observation gaps block aggregation")
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "evidenceBoundary",
                "Configuration distance must state that observation gaps block aggregation rather than becoming zero",
            ));
        }
        for molecule_ref in &reading.molecule_refs {
            if !molecule_refs.contains(molecule_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.configuration_distance_reading_id,
                    molecule_ref,
                    "moleculeRefs must resolve to generated molecules when present",
                ));
            }
        }
        for hyperedge in &reading.typed_hyperedges {
            if hyperedge.hyperedge_id.is_empty()
                || hyperedge.hyperedge_kind.is_empty()
                || hyperedge.atom_refs.len() < 2
                || hyperedge.source_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.configuration_distance_reading_id,
                    "typedHyperedges",
                    "typed hyperedges must retain id, kind, two or more atom refs, and source refs",
                ));
            }
            if hyperedge
                .atom_refs
                .iter()
                .any(|atom_ref| !atom_refs.contains(atom_ref.as_str()))
            {
                examples.push(generic_validation_example(
                    &reading.configuration_distance_reading_id,
                    &hyperedge.hyperedge_id,
                    "typed hyperedge atom refs must resolve to observed atoms",
                ));
            }
        }

        check_configuration_distance_value(
            &mut examples,
            &reading.configuration_distance_reading_id,
            "configurationIndexedDistance",
            &reading.configuration_indexed_distance,
            "shortestPath:",
            true,
        );
        check_configuration_distance_value(
            &mut examples,
            &reading.configuration_distance_reading_id,
            "contextDistance",
            &reading.context_distance,
            "context:",
            true,
        );
        check_configuration_distance_value(
            &mut examples,
            &reading.configuration_distance_reading_id,
            "configurationDistanceBundle",
            &reading.configuration_distance_bundle,
            "hyperedge:",
            false,
        );
        if matches!(
            reading.configuration_indexed_distance.status.as_str(),
            "measured" | "zero"
        ) && (reading.shortest_path_atom_refs.len() < 2
            || reading.shortest_path_hyperedge_refs.is_empty()
            || !reading
                .configuration_indexed_distance
                .evaluator_basis_refs
                .iter()
                .any(|basis| basis.starts_with("hyperedge:")))
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "shortestPath/hyperedge",
                "measured configuration-indexed distance must retain shortest path atom refs and hyperedge refs",
            ));
        }
        if matches!(
            reading.configuration_indexed_distance.status.as_str(),
            "measured" | "zero"
        ) && !reading
            .configuration_indexed_distance
            .evaluator_basis_refs
            .is_empty()
            && reading
                .configuration_indexed_distance
                .evaluator_basis_refs
                .iter()
                .all(|basis| basis.contains("relation-count") || basis.contains("relationCount"))
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "relation-count-only",
                "configuration indexed distance must not be backed by a relation-count-only proxy",
            ));
        }
        if !packet
            .atom_configuration_summary
            .source_refs
            .iter()
            .filter(|source_ref| source_ref.starts_with("gap"))
            .collect::<Vec<_>>()
            .is_empty()
            && matches!(
                reading.configuration_distance_bundle.status.as_str(),
                "measured" | "zero"
            )
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "observation gaps",
                "missing relation or observation gap evidence must block the configuration bundle instead of becoming measured zero",
            ));
        }
        if contains_hard_coded_marker(&reading.configuration_indexed_distance.provenance_refs)
            || contains_hard_coded_marker(
                &reading.configuration_indexed_distance.evaluator_basis_refs,
            )
            || contains_hard_coded_marker(&reading.context_distance.provenance_refs)
            || contains_hard_coded_marker(&reading.context_distance.evaluator_basis_refs)
            || contains_hard_coded_marker(&reading.configuration_distance_bundle.provenance_refs)
            || contains_hard_coded_marker(
                &reading.configuration_distance_bundle.evaluator_basis_refs,
            )
        {
            examples.push(generic_validation_example(
                &reading.configuration_distance_reading_id,
                "hard-coded fixture marker",
                "Configuration distance readings must not be backed by hard-coded fixture markers",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-configuration-distance-readings",
        "packet exposes proxy-free Part IV configuration hypergraph distance readings with shortest-path, context, and gap blockers",
        examples,
        "fail",
    )
}

fn check_configuration_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
    must_measure_when_not_blocked: bool,
) {
    let allowed = BTreeSet::from([
        "measured",
        "zero",
        "unmeasured",
        "unavailable",
        "incomparable",
        "infinite",
        "blocked",
    ]);
    if !allowed.contains(value.status.as_str()) {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "Configuration distance status must be measured, zero, unmeasured, unavailable, incomparable, infinite, or blocked",
        ));
    }
    if must_measure_when_not_blocked
        && !matches!(value.status.as_str(), "measured" | "zero" | "infinite")
    {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "configuration indexed and context distances must be computed from ArchMap hypergraph/context evidence when available",
        ));
    }
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured or zero Configuration distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "measured Configuration distance must be backed by evaluator-specific basis refs, not name-only or presence-only evidence",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "unmeasured, unavailable, incomparable, infinite, or blocked Configuration distance must retain blocker refs",
        ));
    }
}

fn check_signature_distance_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let axis_ids = packet
        .signature_axes
        .iter()
        .map(|axis| axis.signature_axis_id.as_str())
        .collect::<BTreeSet<_>>();
    if !packet.signature_axes.is_empty() && packet.signature_distance_readings.is_empty() {
        examples.push(generic_validation_example(
            "signatureDistanceReadings",
            "empty",
            "packet with selected signature axes must expose Part IV signature distance readings",
        ));
    }
    for axis in &packet.signature_axes {
        if axis.signature_distance_reading_refs.is_empty() {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "signatureDistanceReadingRefs",
                "signature axis readings must point to first-class signature distance readings instead of remaining count-only surfaces",
            ));
        }
    }
    for reading in &packet.signature_distance_readings {
        push_blank(
            &mut examples,
            "signatureDistanceReadings.signatureDistanceReadingId",
            &reading.signature_distance_reading_id,
        );
        if reading.distance_profile_ref != packet.part4_distance_foundation.profile.profile_id
            || reading.diagnostic_scope_ref
                != packet.part4_distance_foundation.diagnostic_scope.scope_id
        {
            examples.push(generic_validation_example(
                &reading.signature_distance_reading_id,
                "profile/scope",
                "Signature distance reading must be tied to the selected Part IV DistanceProfile and DiagnosticScope",
            ));
        }
        if reading.axis_distances.is_empty() {
            examples.push(generic_validation_example(
                &reading.signature_distance_reading_id,
                "axisDistances",
                "Signature distance reading must retain axis-wise rho_i and DistanceValue records",
            ));
        }
        for axis_distance in &reading.axis_distances {
            if !axis_ids.contains(axis_distance.signature_axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.signature_distance_reading_id,
                    &axis_distance.signature_axis_ref,
                    "axis distance must refer to a known signature axis",
                ));
            }
            check_signature_distance_value(
                &mut examples,
                &reading.signature_distance_reading_id,
                "rhoI",
                &axis_distance.rho_i,
                "rho_i:",
            );
            check_signature_distance_value(
                &mut examples,
                &reading.signature_distance_reading_id,
                "axisDistance",
                &axis_distance.axis_distance,
                "axisValue:",
            );
            if axis_distance.source_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.signature_distance_reading_id,
                    "sourceRefs",
                    "axis distance must retain source refs instead of being a raw count",
                ));
            }
        }
        let classified_count = reading.measured_axis_refs.len()
            + reading.unmeasured_axis_refs.len()
            + reading.incomparable_axis_refs.len();
        if classified_count != reading.axis_distances.len() {
            examples.push(generic_validation_example(
                &reading.signature_distance_reading_id,
                "measured/unmeasured/incomparable axes",
                "signature aggregate must classify every selected axis",
            ));
        }
        for value in [
            &reading.total_measured_distance,
            &reading.safe_region_margin,
            &reading.path_drift,
            &reading.endpoint_distance,
        ] {
            if matches!(value.status.as_str(), "measured" | "zero")
                && !value
                    .evaluator_basis_refs
                    .iter()
                    .any(|basis| basis.starts_with("rho_i:"))
            {
                examples.push(generic_validation_example(
                    &reading.signature_distance_reading_id,
                    "rho_i:",
                    "signature aggregate values must retain rho_i evaluator basis refs",
                ));
            }
            if matches!(
                value.status.as_str(),
                "unmeasured" | "blocked" | "incomparable" | "infinite"
            ) && value.blocker_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &reading.signature_distance_reading_id,
                    "blockerRefs",
                    "non-measured signature aggregate values must retain blocker refs",
                ));
            }
        }
        if reading.safe_region_status.trim().is_empty()
            || reading.hidden_excursion_status.trim().is_empty()
            || reading.confidence.trim().is_empty()
            || reading.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.signature_distance_reading_id,
                "safe region / hidden excursion / coverage",
                "signature distance reading must expose selected-profile safe region, hidden excursion status, confidence, and coverage refs",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-signature-distance-readings",
        "packet exposes proxy-free Part IV signature distance readings with rho_i, safe-region margin, drift, and coverage blockers",
        examples,
        "fail",
    )
}

fn check_signature_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
) {
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured or zero Signature distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "measured Signature distance must be backed by axis-specific evaluator basis refs",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "unmeasured, blocked, infinite, or incomparable Signature distance must retain blocker refs",
        ));
    }
}

fn check_operation_distance_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let operation_ids = packet
        .operation_deltas
        .iter()
        .map(|delta| delta.operation_delta_id.as_str())
        .collect::<BTreeSet<_>>();
    let repair_ids = packet
        .repair_operation_candidates
        .iter()
        .map(|candidate| candidate.repair_operation_candidate_id.as_str())
        .collect::<BTreeSet<_>>();
    let operation_distance_ids = packet
        .operation_distance_readings
        .iter()
        .map(|reading| reading.operation_distance_reading_id.as_str())
        .collect::<BTreeSet<_>>();
    if !packet.operation_deltas.is_empty() && packet.operation_distance_readings.is_empty() {
        examples.push(generic_validation_example(
            "operationDistanceReadings",
            "empty",
            "packet with operation deltas must expose Part IV operation distance readings",
        ));
    }
    for candidate in &packet.repair_operation_candidates {
        if candidate.part4_distance_refs.is_empty()
            || candidate
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !operation_distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &candidate.repair_operation_candidate_id,
                "part4DistanceRefs",
                "repair candidates must point to operation distance readings for cost and side-effect evidence",
            ));
        }
    }
    for delta in &packet.operation_deltas {
        if delta.part4_distance_refs.is_empty()
            || delta
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !operation_distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &delta.operation_delta_id,
                "part4DistanceRefs",
                "operation deltas must point to operation distance readings",
            ));
        }
    }
    for reading in &packet.operation_distance_readings {
        if !operation_ids.contains(reading.operation_delta_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.operation_distance_reading_id,
                &reading.operation_delta_ref,
                "operation distance reading must refer to a known operation delta",
            ));
        }
        if let Some(candidate_ref) = &reading.repair_candidate_ref {
            if !repair_ids.contains(candidate_ref.as_str()) {
                examples.push(generic_validation_example(
                    &reading.operation_distance_reading_id,
                    candidate_ref,
                    "operation distance repair candidate ref must resolve",
                ));
            }
        }
        for (field, value, required_prefix) in [
            ("operationCost", &reading.operation_cost, "operationCost:"),
            (
                "targetDistanceDecrease",
                &reading.target_distance_decrease,
                "targetDecrease:",
            ),
            (
                "protectedAxisMovement",
                &reading.protected_axis_movement,
                "protectedAxisMovement:",
            ),
            (
                "distanceToSelectedFlat",
                &reading.distance_to_selected_flat,
                "distanceToSelectedFlat:",
            ),
            ("sideEffectBound", &reading.side_effect_bound, "sideEffect"),
        ] {
            check_operation_distance_value(
                &mut examples,
                &reading.operation_distance_reading_id,
                field,
                value,
                required_prefix,
            );
        }
        if !reading.transfer_risk_refs.is_empty()
            && matches!(
                reading.side_effect_bound.status.as_str(),
                "measured" | "zero"
            )
        {
            examples.push(generic_validation_example(
                &reading.operation_distance_reading_id,
                "sideEffectBound",
                "side-effect bound must not become measured zero while transfer risk refs remain",
            ));
        }
        if reading.evidence_refs.is_empty()
            || reading.repair_route_status.trim().is_empty()
            || !reading
                .evidence_boundary
                .contains("not automatic repair safety")
        {
            examples.push(generic_validation_example(
                &reading.operation_distance_reading_id,
                "evidenceRefs/repairRouteStatus/evidenceBoundary",
                "operation distance must retain evidence refs, route status, and non-safety boundary",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-operation-distance-readings",
        "packet exposes proxy-free Part IV operation cost, repair distance, protected-axis movement, and side-effect blockers",
        examples,
        "fail",
    )
}

fn check_operation_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
) {
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured or zero Operation distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "measured Operation distance must be backed by operation-specific evaluator basis refs",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "unmeasured, blocked, infinite, or incomparable Operation distance must retain blocker refs",
        ));
    }
}

fn check_obstruction_measure_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let support_ids = packet
        .curvature_support_readings
        .iter()
        .flat_map(|reading| reading.witness_supports.iter())
        .map(|support| support.witness_support_id.as_str())
        .collect::<BTreeSet<_>>();
    let measure_ids = packet
        .obstruction_measure_readings
        .iter()
        .map(|reading| reading.obstruction_measure_reading_id.as_str())
        .collect::<BTreeSet<_>>();

    if !packet.curvature_support_readings.is_empty()
        && packet.obstruction_measure_readings.is_empty()
    {
        examples.push(generic_validation_example(
            "obstructionMeasureReadings",
            "empty",
            "curvature support readings must be backed by obstruction measure readings",
        ));
    }
    for support_reading in &packet.curvature_support_readings {
        for support in &support_reading.witness_supports {
            if support.obstruction_measure_reading_refs.is_empty()
                || support
                    .obstruction_measure_reading_refs
                    .iter()
                    .any(|reading_ref| !measure_ids.contains(reading_ref.as_str()))
            {
                examples.push(generic_validation_example(
                    &support.witness_support_id,
                    "obstructionMeasureReadingRefs",
                    "curvature witness support rows must point to obstruction measure readings",
                ));
            }
        }
    }
    for reading in &packet.obstruction_measure_readings {
        if !support_ids.contains(reading.witness_support_ref.as_str()) {
            examples.push(generic_validation_example(
                &reading.obstruction_measure_reading_id,
                &reading.witness_support_ref,
                "obstruction measure reading must reference a known curvature witness support row",
            ));
        }
        for field in [
            &reading.profile_ref,
            &reading.obstruction_circuit_ref,
            &reading.witness_rule_ref,
            &reading.selected_axis_ref,
            &reading.signature_axis_ref,
            &reading.distance_profile_ref,
            &reading.diagnostic_scope_ref,
            &reading.measurement_status,
            &reading.evidence_boundary,
        ] {
            push_blank(
                &mut examples,
                &reading.obstruction_measure_reading_id,
                field,
            );
        }
        check_curvature_distance_value(
            &mut examples,
            &reading.obstruction_measure_reading_id,
            "witnessValue",
            &reading.witness_value,
            "witness",
        );
        check_curvature_distance_value(
            &mut examples,
            &reading.obstruction_measure_reading_id,
            "measureValue",
            &reading.measure_value,
            "Omega_U:",
        );
        if reading.measure_value.status == "zero"
            && reading.support_refs.is_empty()
            && reading.missing_evidence.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.obstruction_measure_reading_id,
                "measureValue",
                "obstruction measure must not turn absent witness support into zero curvature",
            ));
        }
        if !reading
            .evidence_boundary
            .contains("missing witnesses remain blockers")
        {
            examples.push(generic_validation_example(
                &reading.obstruction_measure_reading_id,
                "evidenceBoundary",
                "obstruction measure must state the missing-witness blocker boundary",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-obstruction-measure-readings",
        "packet exposes witness-backed Part IV obstruction measure rows and preserves missing witnesses as blockers",
        examples,
        "fail",
    )
}

fn check_curvature_mass_reading_surface(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let mass_ids = packet
        .curvature_mass_readings
        .iter()
        .map(|reading| reading.curvature_mass_reading_id.as_str())
        .collect::<BTreeSet<_>>();
    let measure_ids = packet
        .obstruction_measure_readings
        .iter()
        .map(|reading| reading.obstruction_measure_reading_id.as_str())
        .collect::<BTreeSet<_>>();
    if !packet.obstruction_measure_readings.is_empty() && packet.curvature_mass_readings.is_empty()
    {
        examples.push(generic_validation_example(
            "curvatureMassReadings",
            "empty",
            "obstruction measure readings must aggregate into curvature mass readings",
        ));
    }
    for support in &packet.curvature_support_readings {
        if support.part4_distance_refs.is_empty()
            || support
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !mass_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &support.reading_id,
                "part4DistanceRefs",
                "curvature support readings must point to Part IV curvature mass readings",
            ));
        }
    }
    for transfer in &packet.curvature_transfer_readings {
        if transfer.part4_distance_refs.is_empty()
            || transfer
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !mass_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &transfer.reading_id,
                "part4DistanceRefs",
                "curvature transfer readings must point to Part IV curvature mass readings",
            ));
        }
        for edge in &transfer.transfer_edges {
            if edge.part4_distance_refs.is_empty()
                || edge
                    .part4_distance_refs
                    .iter()
                    .any(|reading_ref| !mass_ids.contains(reading_ref.as_str()))
            {
                examples.push(generic_validation_example(
                    &edge.edge_id,
                    "part4DistanceRefs",
                    "curvature transfer edges must retain curvature transport distance refs",
                ));
            }
        }
    }
    if let Some(report) = &packet.architecture_spectrum_report {
        if report.curvature_mass_reading_refs.is_empty()
            || report
                .curvature_mass_reading_refs
                .iter()
                .any(|reading_ref| !mass_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &report.report_id,
                "curvatureMassReadingRefs",
                "ArchitectureSpectrumReport must read curvature mass as selected measure refs, not score",
            ));
        }
    }
    for reading in &packet.curvature_mass_readings {
        if reading.obstruction_measure_reading_refs.is_empty()
            || reading
                .obstruction_measure_reading_refs
                .iter()
                .any(|reading_ref| !measure_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &reading.curvature_mass_reading_id,
                "obstructionMeasureReadingRefs",
                "curvature mass must aggregate known obstruction measure rows",
            ));
        }
        for (field, value, prefix) in [
            ("curvatureMass", &reading.curvature_mass, "curv_mass_U:"),
            (
                "beforeOperationMass",
                &reading.before_operation_mass,
                "beforeOperation:",
            ),
            (
                "afterOperationMass",
                &reading.after_operation_mass,
                "afterOperation:",
            ),
            (
                "targetAxisDecrease",
                &reading.target_axis_decrease,
                "curvatureTransport:targetAxisDecrease",
            ),
            (
                "protectedAxisMovement",
                &reading.protected_axis_movement,
                "curvatureTransport:protectedAxisMovement",
            ),
            (
                "transportDistance",
                &reading.transport_distance,
                "transport_U:",
            ),
        ] {
            check_curvature_distance_value(
                &mut examples,
                &reading.curvature_mass_reading_id,
                field,
                value,
                prefix,
            );
        }
        if !reading.unmeasured_axis_refs.is_empty()
            && matches!(reading.curvature_mass.status.as_str(), "measured" | "zero")
        {
            examples.push(generic_validation_example(
                &reading.curvature_mass_reading_id,
                "curvatureMass",
                "curvature mass must not be measured while selected axes remain unmeasured",
            ));
        }
        if !reading
            .evidence_boundary
            .contains("not global flatness or future incident claims")
        {
            examples.push(generic_validation_example(
                &reading.curvature_mass_reading_id,
                "evidenceBoundary",
                "curvature mass must preserve selected-scope and non-forecast boundary",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-curvature-mass-readings",
        "packet exposes Part IV curvature mass and curvature transport distances without promoting unmeasured witnesses to zero",
        examples,
        "fail",
    )
}

fn check_curvature_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
) {
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured curvature distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "curvature distance must be backed by Part IV curvature-specific evaluator basis refs",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "blocked or unmeasured curvature distance must retain blocker refs",
        ));
    }
}

fn check_representation_metric_reading_surface(
    packet: &ArchSigAnalysisPacketV0,
) -> ValidationCheck {
    let mut examples = Vec::new();
    let metric_ids = packet
        .representation_metric_readings
        .iter()
        .map(|reading| reading.representation_metric_reading_id.as_str())
        .collect::<BTreeSet<_>>();
    let analytic_ids = set(packet
        .analytic_representations
        .iter()
        .map(|reading| reading.representation_id.as_str()));
    let spectral_ids = set(packet
        .spectral_analysis_readings
        .iter()
        .map(|reading| reading.spectral_reading_id.as_str()));
    let spectral_mode_ids = set(packet
        .spectral_mode_readings
        .iter()
        .map(|reading| reading.spectral_mode_id.as_str()));
    let drilldown_ids = set(packet
        .spectral_drilldown_readings
        .iter()
        .map(|reading| reading.drilldown_id.as_str()));
    let strength_ids = set(packet
        .representation_strength_readings
        .iter()
        .map(|reading| reading.reading_id.as_str()));
    if !packet.representation_strength_readings.is_empty()
        && packet.representation_metric_readings.is_empty()
    {
        examples.push(generic_validation_example(
            "representationMetricReadings",
            "empty",
            "representation strength readings must be backed by Part IV representation metric readings",
        ));
    }
    for representation in &packet.analytic_representations {
        if representation.part4_distance_refs.is_empty()
            || representation
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !metric_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &representation.representation_id,
                "part4DistanceRefs",
                "analytic representations must point to representation metric readings",
            ));
        }
    }
    for spectral in &packet.spectral_analysis_readings {
        if spectral.part4_distance_refs.is_empty()
            || spectral
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !metric_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &spectral.spectral_reading_id,
                "part4DistanceRefs",
                "spectral readings must point to representation metric readings",
            ));
        }
    }
    for mode in &packet.spectral_mode_readings {
        if mode.part4_distance_refs.is_empty()
            || mode
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !metric_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &mode.spectral_mode_id,
                "part4DistanceRefs",
                "spectral mode readings must point to representation metric readings",
            ));
        }
    }
    for drilldown in &packet.spectral_drilldown_readings {
        if drilldown.part4_distance_refs.is_empty()
            || drilldown
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !metric_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &drilldown.drilldown_id,
                "part4DistanceRefs",
                "spectral drilldown readings must point to representation metric readings",
            ));
        }
    }
    for strength in &packet.representation_strength_readings {
        if strength.part4_distance_refs.is_empty()
            || strength
                .part4_distance_refs
                .iter()
                .any(|reading_ref| !metric_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &strength.reading_id,
                "part4DistanceRefs",
                "representation strength readings must point to representation metric readings",
            ));
        }
    }

    for reading in &packet.representation_metric_readings {
        if reading.distance_profile_ref != packet.part4_distance_foundation.profile.profile_id
            || reading.diagnostic_scope_ref
                != packet.part4_distance_foundation.diagnostic_scope.scope_id
        {
            examples.push(generic_validation_example(
                &reading.representation_metric_reading_id,
                "profile/scope",
                "representation metric reading must be tied to the selected Part IV DistanceProfile and DiagnosticScope",
            ));
        }
        for reference in &reading.analytic_representation_refs {
            if !analytic_ids.contains(reference.as_str()) {
                examples.push(generic_validation_example(
                    &reading.representation_metric_reading_id,
                    reference,
                    "representation metric analyticRepresentationRefs must resolve",
                ));
            }
        }
        for reference in &reading.spectral_reading_refs {
            if !spectral_ids.contains(reference.as_str()) {
                examples.push(generic_validation_example(
                    &reading.representation_metric_reading_id,
                    reference,
                    "representation metric spectralReadingRefs must resolve",
                ));
            }
        }
        for reference in &reading.spectral_mode_refs {
            if !spectral_mode_ids.contains(reference.as_str()) {
                examples.push(generic_validation_example(
                    &reading.representation_metric_reading_id,
                    reference,
                    "representation metric spectralModeRefs must resolve",
                ));
            }
        }
        for reference in &reading.spectral_drilldown_refs {
            if !drilldown_ids.contains(reference.as_str()) {
                examples.push(generic_validation_example(
                    &reading.representation_metric_reading_id,
                    reference,
                    "representation metric spectralDrilldownRefs must resolve",
                ));
            }
        }
        for reference in &reading.representation_strength_refs {
            if !strength_ids.contains(reference.as_str()) {
                examples.push(generic_validation_example(
                    &reading.representation_metric_reading_id,
                    reference,
                    "representation metric representationStrengthRefs must resolve",
                ));
            }
        }
        for (field, value, prefix) in [
            (
                "structuralDistance",
                &reading.structural_distance,
                "structuralDistance:",
            ),
            (
                "analyticDistance",
                &reading.analytic_distance,
                "analyticDistance:",
            ),
            (
                "lipschitzStability",
                &reading.lipschitz_stability,
                "lipschitz:",
            ),
            (
                "biLipschitzFaithfulness",
                &reading.bi_lipschitz_faithfulness,
                "biLipschitz:",
            ),
        ] {
            check_representation_metric_distance_value(
                &mut examples,
                &reading.representation_metric_reading_id,
                field,
                value,
                prefix,
            );
        }
        if reading.coverage_blocker_refs.is_empty()
            && reading.witness_completeness_blocker_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &reading.representation_metric_reading_id,
                "coverage/witness blockers",
                "representation faithfulness must retain coverage and witness-completeness blockers instead of silently claiming lower-bound faithfulness",
            ));
        }
        if !reading.bi_lipschitz_faithfulness.blocker_refs.is_empty()
            && matches!(
                reading.bi_lipschitz_faithfulness.status.as_str(),
                "measured" | "zero"
            )
        {
            examples.push(generic_validation_example(
                &reading.representation_metric_reading_id,
                "biLipschitzFaithfulness",
                "bi-Lipschitz lower-bound faithfulness must not be measured while coverage or witness blockers remain",
            ));
        }
        if !reading
            .evidence_boundary
            .contains("not structural faithfulness")
        {
            examples.push(generic_validation_example(
                &reading.representation_metric_reading_id,
                "evidenceBoundary",
                "representation metric must state that analytic closeness is not structural faithfulness without coverage and witness completeness",
            ));
        }
        if !reading
            .analytic_distance
            .reading
            .contains("not an architecture quality score")
        {
            examples.push(generic_validation_example(
                &reading.representation_metric_reading_id,
                "analyticDistance.reading",
                "analytic distance must be framed as a selected representation reading, not a quality score",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-representation-metric-readings",
        "packet exposes Part IV representation metric, Lipschitz stability, and coverage-blocked faithfulness readings",
        examples,
        "fail",
    )
}

fn check_representation_metric_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
) {
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured or zero Representation metric distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "representation metric distance must be backed by representation-specific evaluator basis refs",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "blocked or unmeasured Representation metric distance must retain blocker refs",
        ));
    }
}

fn check_atom_distance_value(
    examples: &mut Vec<ValidationExample>,
    reading_id: &str,
    field: &str,
    value: &ArchSigDistanceValueV0,
    required_basis_prefix: &str,
    must_measure: bool,
) {
    let allowed = BTreeSet::from([
        "measured",
        "zero",
        "unmeasured",
        "unavailable",
        "incomparable",
        "infinite",
        "blocked",
    ]);
    if !allowed.contains(value.status.as_str()) {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "Atom distance status must be measured, zero, unmeasured, unavailable, incomparable, infinite, or blocked",
        ));
    }
    if must_measure && !matches!(value.status.as_str(), "measured" | "zero") {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "fiber, carrier, and valence distance must be measured from ArchMap atom fields, not left as presence-only rows",
        ));
    }
    if matches!(value.status.as_str(), "measured" | "zero") {
        if value.measured_value.is_none()
            || value.provenance_refs.is_empty()
            || value.evaluator_basis_refs.is_empty()
            || value.coverage_refs.is_empty()
        {
            examples.push(generic_validation_example(
                reading_id,
                field,
                "measured or zero Atom distance must retain value, provenance refs, evaluator basis refs, and coverage refs",
            ));
        }
        if !value
            .evaluator_basis_refs
            .iter()
            .any(|basis| basis.starts_with(required_basis_prefix))
        {
            examples.push(generic_validation_example(
                reading_id,
                required_basis_prefix,
                "measured Atom distance must be backed by component-specific evaluator basis refs, not name-only or presence-only evidence",
            ));
        }
    } else if value.blocker_refs.is_empty() {
        examples.push(generic_validation_example(
            reading_id,
            field,
            "unmeasured, unavailable, incomparable, infinite, or blocked Atom distance must retain blocker refs",
        ));
    }
    if contains_hard_coded_marker(&value.provenance_refs)
        || contains_hard_coded_marker(&value.evaluator_basis_refs)
    {
        examples.push(generic_validation_example(
            reading_id,
            "hard-coded fixture marker",
            "Atom distance readings must not be backed by hard-coded fixture markers",
        ));
    }
}

fn part4_distance_refs_are_concern_only(
    provenance_refs: &[String],
    evaluator_basis_refs: &[String],
) -> bool {
    let refs = provenance_refs
        .iter()
        .chain(evaluator_basis_refs.iter())
        .collect::<Vec<_>>();
    !refs.is_empty()
        && refs.iter().all(|reference| {
            let reference = reference.to_ascii_lowercase();
            reference.starts_with("concern:")
                || reference.contains("concernhint")
                || reference.contains("concern-hint")
        })
}

fn check_measurement_depth(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();

    for reading in &packet.law_universe_coverage_readings {
        if reading.exactness_assumption_status.is_empty() {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "exactnessAssumptionStatus",
                "LawUniverse coverage must preserve exactness-assumption status, not only law family presence",
            ));
        }
        if reading.blocked_witness_refs.is_empty() && reading.unmeasured_required_law_count > 0 {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "blockedWitnessRefs",
                "unmeasured required laws must expose blocked witness refs",
            ));
        }
        for coverage in reading
            .required_law_coverage
            .iter()
            .chain(reading.witness_family_coverage.iter())
            .chain(reading.signature_axis_coverage.iter())
            .chain(reading.coverage_requirement_status.iter())
            .chain(reading.exactness_assumption_status.iter())
        {
            push_blank(
                &mut examples,
                &format!("{} coverage.refId", reading.reading_id),
                &coverage.ref_id,
            );
            push_blank(
                &mut examples,
                &format!("{} coverage.status", reading.reading_id),
                &coverage.status,
            );
            push_blank(
                &mut examples,
                &format!("{} coverage.reading", reading.reading_id),
                &coverage.reading,
            );
            if coverage.status.contains("blocked")
                || coverage.status.contains("gap")
                || coverage.status.contains("unmeasured")
            {
                if coverage.blocker_refs.is_empty() {
                    examples.push(generic_validation_example(
                        &reading.reading_id,
                        &coverage.ref_id,
                        "blocked or unmeasured LawUniverse coverage rows must retain blocker refs",
                    ));
                }
            } else if coverage.status != "notApplicable" && coverage.evidence_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &coverage.ref_id,
                    "measured LawUniverse coverage rows must retain evidence refs",
                ));
            }
        }
        for evaluation in &reading.law_witness_axis_evaluations {
            push_blank(
                &mut examples,
                &format!("{} alignmentStatus", reading.reading_id),
                &evaluation.alignment_status,
            );
            push_blank(
                &mut examples,
                &format!("{} coverageStatus", reading.reading_id),
                &evaluation.coverage_status,
            );
            push_blank(
                &mut examples,
                &format!("{} exactnessStatus", reading.reading_id),
                &evaluation.exactness_status,
            );
            if evaluation.alignment_status == "aligned"
                && (evaluation.observed_witness_refs.is_empty()
                    || evaluation.observed_axis_refs.is_empty()
                    || evaluation.source_backed_evidence_refs.is_empty())
            {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evaluation.evaluation_id,
                    "aligned law evaluation must retain observed witness, axis, and source-backed evidence refs",
                ));
            }
        }
        if !reading.law_witness_axis_alignment.contains("laws")
            || !reading.law_witness_axis_alignment.contains("witness")
            || !reading.law_witness_axis_alignment.contains("axes")
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "lawWitnessAxisAlignment",
                "LawUniverse coverage must explicitly align laws, witness rules, and signature axes",
            ));
        }
    }

    for defect in &packet.axis_wise_monodromy_defects {
        if defect.measurement_status == "measured" {
            if defect.distance_value.is_none() {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "distanceValue",
                    "measured monodromy defects must retain the computed distance value",
                ));
            }
            if defect.distance_input_refs.is_empty() {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "distanceInputRefs",
                    "measured monodromy defects must retain distance evaluator input refs",
                ));
            }
            if contains_hard_coded_marker(&defect.distance_input_refs)
                || contains_hard_coded_marker(&defect.source_refs)
                || contains_hard_coded_marker(&defect.observation_refs)
            {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "hard-coded fixture marker",
                    "measured monodromy defects must not be backed by hard-coded fixture markers",
                ));
            }
            if defect.measured_support_refs.is_empty() {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "measuredSupportRefs",
                    "measured monodromy defects must retain measured support refs",
                ));
            }
            if defect.source_refs.is_empty() && defect.observation_refs.is_empty() {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "sourceRefs/observationRefs",
                    "measured monodromy defects must retain source or observation refs",
                ));
            }
            if defect.distance_value.is_some_and(|value| value != 0)
                && defect.witness_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &defect.defect_id,
                    "witnessRefs",
                    "nonzero measured monodromy defects must retain witness refs",
                ));
            }
        }
        if defect.measurement_status == "unmeasured" && defect.missing_refs.is_empty() {
            examples.push(generic_validation_example(
                &defect.defect_id,
                "missingRefs",
                "unmeasured monodromy defects must retain missing refs so absence is not read as zero",
            ));
        }
    }

    for holonomy in &packet.homotopy_holonomy_readings {
        if holonomy.measurement_status == "measured" {
            if holonomy.compared_continuation_refs.is_empty() {
                examples.push(generic_validation_example(
                    &holonomy.reading_id,
                    "comparedContinuationRefs",
                    "measured holonomy must retain compared continuation refs",
                ));
            }
            if holonomy.distance_input_refs.is_empty() {
                examples.push(generic_validation_example(
                    &holonomy.reading_id,
                    "distanceInputRefs",
                    "measured holonomy must retain distance evaluator input refs",
                ));
            }
            if contains_hard_coded_marker(&holonomy.distance_input_refs)
                || contains_hard_coded_marker(&holonomy.source_refs)
                || contains_hard_coded_marker(&holonomy.observation_refs)
            {
                examples.push(generic_validation_example(
                    &holonomy.reading_id,
                    "hard-coded fixture marker",
                    "measured holonomy must not be backed by hard-coded fixture markers",
                ));
            }
            if holonomy.source_refs.is_empty()
                && holonomy.observation_refs.is_empty()
                && holonomy.mu_defect_refs.is_empty()
            {
                examples.push(generic_validation_example(
                    &holonomy.reading_id,
                    "sourceRefs/observationRefs/muDefectRefs",
                    "measured holonomy must retain source, observation, or monodromy defect refs",
                ));
            }
            if holonomy.value != 0 && holonomy.mu_defect_refs.is_empty() {
                examples.push(generic_validation_example(
                    &holonomy.reading_id,
                    "muDefectRefs",
                    "nonzero holonomy must be backed by positive selected-axis continuation defects, not semantic evidence alone",
                ));
            }
        }
        if holonomy.measurement_status != "measured" && holonomy.missing_filler_refs.is_empty() {
            examples.push(generic_validation_example(
                &holonomy.reading_id,
                "missingFillerRefs",
                "unmeasured or blocked holonomy must retain missing filler refs",
            ));
        }
    }

    for reading in &packet.operation_calculus_law_readings {
        if reading.law_evidence.len() < 9 {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "lawEvidence",
                "operation calculus laws must keep one evaluator row per selected law axis",
            ));
        }
        for evidence in &reading.law_evidence {
            if evidence.status == "observed" && evidence.observed_evidence_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "observed operation law evidence must retain observed evidence refs",
                ));
            }
            if evidence.status == "blocked" && evidence.blocked_reason_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "blocked operation law evidence must retain blocked reason refs",
                ));
            }
            if evidence.status != "notApplicable" && evidence.required_evidence_refs.is_empty() {
                examples.push(generic_validation_example(
                    &reading.reading_id,
                    &evidence.law_axis,
                    "operation law evidence must retain required evidence refs",
                ));
            }
        }
    }

    check_from_examples(
        "archsig-analysis-packet-measurement-depth",
        "measurement-depth pass: measured readings retain evaluator inputs, distance provenance, witness alignment, and coverage blockers",
        examples,
        "fail",
    )
}

fn contains_hard_coded_marker(values: &[String]) -> bool {
    values.iter().any(|value| {
        let normalized = value.to_ascii_lowercase();
        normalized.contains("hard-coded")
            || normalized.contains("hardcoded")
            || normalized.contains("fixture-marker")
    })
}

fn check_proxy_regression_guardrails(packet: &ArchSigAnalysisPacketV0) -> ValidationCheck {
    let mut examples = Vec::new();

    for (family_id, status, measured_axis_count, coverage_blocker_count) in [
        (
            packet.monodromy_reading_family.reading_family_id.as_str(),
            packet.monodromy_reading_family.status.as_str(),
            packet.monodromy_reading_family.measured_axis_count,
            packet.monodromy_reading_family.coverage_blocker_count,
        ),
        (
            packet
                .boundary_holonomy_reading_family
                .reading_family_id
                .as_str(),
            packet.boundary_holonomy_reading_family.status.as_str(),
            packet.boundary_holonomy_reading_family.measured_axis_count,
            packet
                .boundary_holonomy_reading_family
                .coverage_blocker_count,
        ),
    ] {
        if status == "schemaFoundationOnly" {
            examples.push(generic_validation_example(
                family_id,
                status,
                "schemaFoundationOnly is a schema surface and must fail measurement validation",
            ));
        }
        if status == "measured" && measured_axis_count == 0 {
            examples.push(generic_validation_example(
                family_id,
                "measuredAxisCount",
                "measured family status requires at least one measured axis",
            ));
        }
        if status == "measured" && coverage_blocker_count > 0 {
            examples.push(generic_validation_example(
                family_id,
                "coverageBlockerCount",
                "measured family status cannot hide coverage blockers",
            ));
        }
    }

    for reading in &packet.representation_strength_readings {
        let proxy_marked = [
            reading.zero_preserving.as_str(),
            reading.zero_reflecting.as_str(),
            reading.obstruction_preserving.as_str(),
            reading.obstruction_reflecting.as_str(),
            reading.aggregate_zero_safety.as_str(),
            reading.cancellation_risk.as_str(),
        ]
        .iter()
        .any(|value| value.to_ascii_lowercase().contains("proxy"));
        let boundary = reading.evidence_boundary.to_ascii_lowercase();
        if proxy_marked
            && (boundary.contains("measured claim") || boundary.contains("measurement truth"))
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "evidenceBoundary",
                "bounded proxy representation strength cannot be promoted to a measured claim",
            ));
        }
    }

    for reading in &packet.axis_wise_monodromy_defects {
        if reading.measurement_status == "measured"
            && (reading.distance_input_refs.is_empty()
                || (reading.source_refs.is_empty() && reading.observation_refs.is_empty()))
        {
            examples.push(generic_validation_example(
                &reading.defect_id,
                "measurementStatus",
                "monodromy defect cannot be measured without distance provenance and source-backed support",
            ));
        }
    }
    for reading in &packet.homotopy_holonomy_readings {
        if reading.measurement_status == "measured"
            && (reading.distance_input_refs.is_empty()
                || reading.compared_continuation_refs.is_empty())
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "measurementStatus",
                "holonomy cannot be measured without continuation comparison and distance provenance",
            ));
        }
    }

    check_from_examples(
        "archsig-analysis-packet-proxy-regression-guardrails",
        "proxy-regression pass: proxy/schema-only readings cannot masquerade as measured analysis",
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
        if circuit.atom_observation_refs.is_empty() {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "atomObservationRefs",
                "obstruction circuit must be backed by required witness atom families, not policy text or concern cues",
            ));
        }
        if !circuit.concern_hint_refs.is_empty()
            && (circuit.atom_observation_refs.is_empty()
                || circuit.molecule_reading_refs.is_empty())
        {
            examples.push(generic_validation_example(
                &circuit.obstruction_circuit_id,
                "concernHintRefs",
                "concernHints may only be auxiliary context after atom and molecule witness support are present",
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
    let signature_distance_ids = set(packet
        .signature_distance_readings
        .iter()
        .map(|reading| reading.signature_distance_reading_id.as_str()));
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
        let constructed_value = packet
            .obstruction_circuits
            .iter()
            .filter(|circuit| {
                circuit
                    .signature_axis_refs
                    .contains(&axis.signature_axis_id)
            })
            .count() as i64;
        push_blank(&mut examples, &axis.signature_axis_id, &axis.law_ref);
        push_blank(
            &mut examples,
            &format!("{} axisRef", axis.signature_axis_id),
            &axis.axis_ref,
        );
        if axis.value != constructed_value {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "value",
                "signature axis value must equal constructed obstruction circuit count for that axis",
            ));
        }
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
        if axis.signature_distance_reading_refs.is_empty()
            || axis
                .signature_distance_reading_refs
                .iter()
                .any(|reading_ref| !signature_distance_ids.contains(reading_ref.as_str()))
        {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                "signatureDistanceReadingRefs",
                "signature axis must resolve to signature distance reading provenance",
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
            "llmInterpretationPacket.distanceDiagnosisSummary",
            packet
                .llm_interpretation_packet
                .distance_diagnosis_summary
                .is_empty()
                || !packet
                    .llm_interpretation_packet
                    .distance_diagnosis_summary
                    .iter()
                    .any(|summary| summary.contains("diagnosticScope measuredAxes=")),
        ),
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
        (
            "llmInterpretationPacket.axisForgettingRiskSummary",
            packet
                .llm_interpretation_packet
                .axis_forgetting_risk_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.signatureTrajectoryHomotopyRefutationSummary",
            packet
                .llm_interpretation_packet
                .signature_trajectory_homotopy_refutation_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.bridgeSplitObstructionTransferSummary",
            packet
                .llm_interpretation_packet
                .bridge_split_obstruction_transfer_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.nonzeroMonodromyWitnessSummary",
            !packet.nonzero_monodromy_witnesses.is_empty()
                && packet
                    .llm_interpretation_packet
                    .nonzero_monodromy_witness_summary
                    .is_empty(),
        ),
        (
            "llmInterpretationPacket.curvatureSupportSummary",
            !packet.curvature_support_readings.is_empty()
                && packet
                    .llm_interpretation_packet
                    .curvature_support_summary
                    .is_empty(),
        ),
        (
            "llmInterpretationPacket.featureBoundaryResidualSummary",
            packet
                .llm_interpretation_packet
                .feature_boundary_residual_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.featureExtensionDiagnosisSummary",
            packet
                .llm_interpretation_packet
                .feature_extension_diagnosis_summary
                .is_empty(),
        ),
        (
            "llmInterpretationPacket.curvatureTransferSummary",
            !packet.curvature_transfer_readings.is_empty()
                && packet
                    .llm_interpretation_packet
                    .curvature_transfer_summary
                    .is_empty(),
        ),
        (
            "llmInterpretationPacket.architectureSpectrumReportSummary",
            packet.architecture_spectrum_report.is_some()
                && packet
                    .llm_interpretation_packet
                    .architecture_spectrum_report_summary
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
