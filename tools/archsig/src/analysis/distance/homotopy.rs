fn build_homotopy_distance_readings(
    complex: &ArchSigHomotopyComplexSummaryV0,
    loop_candidates: &[ArchSigLoopCandidateV0],
    filler_candidate_readings: &[ArchSigFillerCandidateReadingV0],
    architectural_hole_readings: &[ArchSigArchitecturalHoleReadingV0],
    holonomy_readings: &[ArchSigHomotopyHolonomyReadingV0],
    stokes_style_readings: &[ArchSigStokesStyleReadingV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigHomotopyDistanceReadingV0> {
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    loop_candidates
        .iter()
        .map(|loop_candidate| {
            let filler_refs = filler_candidate_readings
                .iter()
                .filter(|reading| reading.loop_ref == loop_candidate.loop_id)
                .collect::<Vec<_>>();
            let hole_refs = architectural_hole_readings
                .iter()
                .filter(|reading| reading.loop_ref == loop_candidate.loop_id)
                .collect::<Vec<_>>();
            let holonomy_refs = holonomy_readings
                .iter()
                .filter(|reading| reading.loop_ref == loop_candidate.loop_id)
                .collect::<Vec<_>>();
            let stokes_refs = stokes_style_readings
                .iter()
                .filter(|reading| reading.loop_ref == loop_candidate.loop_id)
                .collect::<Vec<_>>();
            let measured_filler_refs = unique_strings(
                filler_refs
                    .iter()
                    .flat_map(|reading| reading.measured_filler_evidence_refs.clone()),
            );
            let missing_filler_refs = unique_strings(
                loop_candidate
                    .missing_filler_evidence
                    .iter()
                    .cloned()
                    .chain(
                        filler_refs
                            .iter()
                            .flat_map(|reading| reading.missing_filler_evidence.clone()),
                    )
                    .chain(
                        hole_refs
                            .iter()
                            .flat_map(|reading| reading.missing_filler_evidence.clone()),
                    )
                    .chain(
                        holonomy_refs
                            .iter()
                            .flat_map(|reading| reading.missing_filler_refs.clone()),
                    ),
            );
            let non_fillability_witness_refs = unique_strings(
                hole_refs
                    .iter()
                    .flat_map(|reading| reading.non_fillability_witness_refs.clone())
                    .chain(
                        stokes_refs
                            .iter()
                            .flat_map(|reading| reading.non_fillability_witness_refs.clone()),
                    ),
            );
            let holonomy_value = holonomy_refs
                .iter()
                .map(|reading| reading.value.max(0))
                .sum::<i64>();
            let generator_cost = loop_candidate.path_refs.len() as i64
                + loop_candidate.filler_candidate_refs.len() as i64
                + holonomy_value;
            let filler_cost_value = measured_filler_refs.len() as i64;
            let missing_cost = missing_filler_refs.len() as i64;
            let evidence_refs = unique_strings(
                loop_candidate
                    .source_refs
                    .iter()
                    .cloned()
                    .chain(loop_candidate.path_refs.iter().cloned())
                    .chain(
                        filler_refs
                            .iter()
                            .flat_map(|reading| reading.source_refs.clone()),
                    )
                    .chain(
                        holonomy_refs
                            .iter()
                            .flat_map(|reading| reading.distance_input_refs.clone()),
                    ),
            );
            let blockers = if missing_filler_refs.is_empty() {
                Vec::new()
            } else {
                missing_filler_refs.clone()
            };
            let homotopy_distance = if blockers.is_empty() {
                measured_part4_distance_value(
                    generator_cost,
                    "homotopy-generator-cost",
                    evidence_refs.clone(),
                    vec![
                        format!("d_hom:pathPair:{}", loop_candidate.path_pair_ref),
                        format!("generatorCount:{}", loop_candidate.filler_candidate_refs.len()),
                    ],
                    &coverage_refs,
                    "homotopy distance is selected generator cost over measured path pair and filler evidence",
                )
            } else {
                blocked_curvature_distance_value(
                    "homotopy-generator-cost",
                    evidence_refs.clone(),
                    vec![format!("d_hom:pathPair:{}", loop_candidate.path_pair_ref)],
                    &coverage_refs,
                    blockers.clone(),
                    "homotopy distance is blocked by missing filler evidence and cannot be read as zero",
                )
            };
            let filling_cost = if blockers.is_empty() {
                measured_part4_distance_value(
                    filler_cost_value,
                    "filling-cost",
                    measured_filler_refs.clone(),
                    vec![format!("fill_cost:loop:{}", loop_candidate.loop_id)],
                    &coverage_refs,
                    "filling cost is measured from selected filler evidence refs",
                )
            } else {
                blocked_curvature_distance_value(
                    "filling-cost",
                    non_fillability_witness_refs.clone(),
                    vec![format!("fill_cost:loop:{}", loop_candidate.loop_id)],
                    &coverage_refs,
                    blockers.clone(),
                    "filling cost is blocked while filler evidence is missing; missing filler is not zero cost",
                )
            };
            let observation_gap_lower_bound = if missing_cost > 0 {
                measured_part4_distance_value(
                    missing_cost,
                    "observation-gap-lower-bound",
                    missing_filler_refs.clone(),
                    vec![
                        "lipschitzAssumption:selectedObservationGap".to_string(),
                        format!("deltaOverL:{}", missing_cost),
                    ],
                    &coverage_refs,
                    "observation gap lower bound uses explicit selected Lipschitz and distance assumptions",
                )
            } else {
                measured_part4_distance_value(
                    0,
                    "observation-gap-lower-bound",
                    evidence_refs.clone(),
                    vec!["lipschitzAssumption:noSelectedGap".to_string()],
                    &coverage_refs,
                    "no selected observation gap contributes a lower bound in this bounded loop",
                )
            };
            let selected_dehn_area = if blockers.is_empty() {
                measured_part4_distance_value(
                    filler_cost_value + holonomy_value,
                    "selected-dehn-area",
                    measured_filler_refs.clone(),
                    vec![
                        format!("Dehn_A:n<= {}", loop_candidate.path_refs.len()),
                        format!("area:{}", filler_cost_value + holonomy_value),
                    ],
                    &coverage_refs,
                    "selected Dehn-style area is finite over bounded loop candidates only",
                )
            } else {
                blocked_curvature_distance_value(
                    "selected-dehn-area",
                    non_fillability_witness_refs.clone(),
                    vec![format!("Dehn_A:n<= {}", loop_candidate.path_refs.len())],
                    &coverage_refs,
                    blockers,
                    "selected Dehn-style area is blocked by architectural holes and missing filler evidence",
                )
            };

            ArchSigHomotopyDistanceReadingV0 {
                homotopy_distance_reading_id: format!(
                    "homotopy-distance:{}",
                    stable_id(&loop_candidate.loop_id)
                ),
                profile_ref: complex.profile_ref.clone(),
                loop_ref: loop_candidate.loop_id.clone(),
                path_pair_ref: loop_candidate.path_pair_ref.clone(),
                distance_profile_ref: foundation.profile.profile_id.clone(),
                diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                homotopy_distance,
                filling_cost,
                observation_gap_lower_bound,
                selected_dehn_area,
                filler_candidate_refs: loop_candidate.filler_candidate_refs.clone(),
                measured_filler_refs,
                missing_filler_refs,
                holonomy_reading_refs: holonomy_refs
                    .iter()
                    .map(|reading| reading.reading_id.clone())
                    .collect(),
                non_fillability_witness_refs,
                evidence_refs,
                lipschitz_assumption_refs: vec![
                    "selected observation is L-Lipschitz for declared filling generators"
                        .to_string(),
                    "lower bound is scoped to supplied ArchMap observation gaps".to_string(),
                ],
                evidence_boundary:
                    "homotopy and filling distances are selected bounded readings; missing fillers are blockers, not zero cost or global homology claims"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_HOMOTOPY_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn attach_homotopy_distance_refs(
    loop_candidates: &mut [ArchSigLoopCandidateV0],
    filler_candidate_readings: &mut [ArchSigFillerCandidateReadingV0],
    architectural_hole_readings: &mut [ArchSigArchitecturalHoleReadingV0],
    holonomy_readings: &mut [ArchSigHomotopyHolonomyReadingV0],
    stokes_style_readings: &mut [ArchSigStokesStyleReadingV0],
    report: &mut ArchSigArchitectureHomotopyReportV0,
    readings: &[ArchSigHomotopyDistanceReadingV0],
) {
    for reading in readings {
        if let Some(loop_candidate) = loop_candidates
            .iter_mut()
            .find(|candidate| candidate.loop_id == reading.loop_ref)
        {
            loop_candidate
                .part4_distance_refs
                .push(reading.homotopy_distance_reading_id.clone());
        }
        for filler in filler_candidate_readings
            .iter_mut()
            .filter(|filler| filler.loop_ref == reading.loop_ref)
        {
            filler
                .part4_distance_refs
                .push(reading.homotopy_distance_reading_id.clone());
        }
        for hole in architectural_hole_readings
            .iter_mut()
            .filter(|hole| hole.loop_ref == reading.loop_ref)
        {
            hole.part4_distance_refs
                .push(reading.homotopy_distance_reading_id.clone());
        }
        for holonomy in holonomy_readings
            .iter_mut()
            .filter(|holonomy| holonomy.loop_ref == reading.loop_ref)
        {
            holonomy
                .part4_distance_refs
                .push(reading.homotopy_distance_reading_id.clone());
        }
        for stokes in stokes_style_readings
            .iter_mut()
            .filter(|stokes| stokes.loop_ref == reading.loop_ref)
        {
            stokes
                .part4_distance_refs
                .push(reading.homotopy_distance_reading_id.clone());
        }
        report
            .part4_distance_refs
            .push(reading.homotopy_distance_reading_id.clone());
    }
}

fn promote_homotopy_filling_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigHomotopyDistanceReadingV0],
) {
    if readings.is_empty() {
        return;
    }
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "homotopyFillingGeometry")
    {
        let blockers = readings
            .iter()
            .flat_map(|reading| reading.filling_cost.blocker_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        distance.value = if blockers.is_empty() {
            measured_part4_distance_value(
                readings
                    .iter()
                    .filter_map(|reading| reading.filling_cost.measured_value)
                    .sum::<i64>(),
                "filling-cost",
                readings
                    .iter()
                    .map(|reading| reading.homotopy_distance_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| format!("fill_cost:{}", reading.loop_ref))
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                "homotopyFillingGeometry aggregates selected filling costs over bounded loop candidates",
            )
        } else {
            blocked_curvature_distance_value(
                "filling-cost",
                readings
                    .iter()
                    .map(|reading| reading.homotopy_distance_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| format!("homotopyDistance:{}", reading.loop_ref))
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                blockers,
                "homotopyFillingGeometry remains blocked while selected fillers are missing",
            )
        };
        distance.evidence_boundary =
            "homotopyFillingGeometry reads selected path-pair and filler evidence; it is not global homology or path truth"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}
