fn build_representation_metric_readings(
    archmap: &ArchMapDocumentV0,
    analytic_representations: &[ArchSigAnalyticRepresentationV0],
    spectral_analysis_readings: &[ArchSigSpectralAnalysisReadingV0],
    spectral_mode_readings: &[ArchSigSpectralModeReadingV0],
    spectral_drilldown_readings: &[ArchSigSpectralDrilldownReadingV0],
    representation_strength_readings: &[ArchSigRepresentationStrengthReadingV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigRepresentationMetricReadingV0> {
    let analytic_by_id = analytic_representations
        .iter()
        .map(|reading| (reading.representation_id.as_str(), reading))
        .collect::<BTreeMap<_, _>>();
    let spectral_by_id = spectral_analysis_readings
        .iter()
        .map(|reading| (reading.spectral_reading_id.as_str(), reading))
        .collect::<BTreeMap<_, _>>();
    let modes_by_spectral_ref = spectral_mode_readings.iter().fold(
        BTreeMap::<&str, Vec<&ArchSigSpectralModeReadingV0>>::new(),
        |mut map, mode| {
            map.entry(mode.source_spectral_reading_ref.as_str())
                .or_default()
                .push(mode);
            map
        },
    );
    let drilldowns_by_mode_ref = spectral_drilldown_readings
        .iter()
        .flat_map(|drilldown| {
            drilldown
                .source_spectral_mode_refs
                .iter()
                .map(move |mode_ref| (mode_ref.as_str(), drilldown))
        })
        .fold(
            BTreeMap::<&str, Vec<&ArchSigSpectralDrilldownReadingV0>>::new(),
            |mut map, (mode_ref, drilldown)| {
                map.entry(mode_ref).or_default().push(drilldown);
                map
            },
        );
    let coverage_blockers = archmap
        .observation_gaps
        .iter()
        .map(|gap| gap.gap_id.clone())
        .collect::<Vec<_>>();
    let witness_blockers = vec![
        "witness-completeness:selected-LawPolicy-not-certified".to_string(),
        "coverage-completeness:selected-representation-not-global".to_string(),
    ];
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();

    representation_strength_readings
        .iter()
        .map(|strength| {
            let mut source_reading_refs = vec![strength.source_reading_ref.clone()];
            let mut analytic_representation_refs = Vec::new();
            let mut spectral_reading_refs = Vec::new();
            let mut spectral_mode_refs = Vec::new();
            let mut spectral_drilldown_refs = Vec::new();
            let mut evidence_refs = Vec::new();
            let mut structural_basis = vec![
                format!("structuralDistance:representationStrength:{}", strength.reading_id),
                format!("structuralDistance:family:{}", strength.representation_family),
            ];
            let mut analytic_basis = vec![
                format!("analyticDistance:representationFamily:{}", strength.representation_family),
            ];
            let mut structural_value = 0_i64;
            let mut analytic_value = 0_i64;
            let mut analytic_status = "measured";

            if let Some(representation) = analytic_by_id.get(strength.source_reading_ref.as_str()) {
                analytic_representation_refs.push(representation.representation_id.clone());
                evidence_refs.extend(representation.graph_scope_refs.clone());
                evidence_refs.extend(representation.walk_witness_refs.clone());
                structural_value += representation.graph_scope_refs.len() as i64;
                structural_value += representation.axis_refs.len() as i64;
                structural_value += representation.walk_witness_refs.len() as i64;
                structural_basis.extend(
                    representation
                        .axis_refs
                        .iter()
                        .map(|axis| format!("structuralDistance:axis:{axis}")),
                );
                structural_basis.extend(
                    representation
                        .graph_scope_refs
                        .iter()
                        .map(|graph_ref| format!("structuralDistance:graphScope:{graph_ref}")),
                );
                let (value, basis, measured) = analytic_metric_value_from_representation(representation);
                analytic_value += value;
                analytic_basis.extend(basis);
                if !measured {
                    analytic_status = "blocked";
                }
            }

            if let Some(spectral) = spectral_by_id.get(strength.source_reading_ref.as_str()) {
                spectral_reading_refs.push(spectral.spectral_reading_id.clone());
                evidence_refs.extend(spectral.support_refs.clone());
                structural_value += spectral.support_refs.len() as i64;
                structural_value += spectral.dominant_components.len() as i64;
                structural_basis.extend(
                    spectral
                        .support_refs
                        .iter()
                        .map(|support| format!("structuralDistance:spectralSupport:{support}")),
                );
                let (value, basis) = analytic_metric_value_from_spectral(spectral);
                analytic_value += value;
                analytic_basis.extend(basis);
                if let Some(modes) = modes_by_spectral_ref.get(strength.source_reading_ref.as_str()) {
                    for mode in modes {
                        spectral_mode_refs.push(mode.spectral_mode_id.clone());
                        source_reading_refs.push(mode.spectral_mode_id.clone());
                        analytic_basis.push(format!(
                            "analyticDistance:spectralMode:{}:gap={}:localization={}:density={}",
                            mode.spectral_mode_id,
                            mode.spectral_gap_proxy.value,
                            mode.localization_index.value,
                            mode.matrix_density.value
                        ));
                        analytic_value += scaled_spectral_value(&mode.spectral_gap_proxy.value).abs();
                        analytic_value += scaled_spectral_value(&mode.localization_index.value).abs();
                        analytic_value += scaled_spectral_value(&mode.matrix_density.value).abs();
                        if let Some(drilldowns) = drilldowns_by_mode_ref.get(mode.spectral_mode_id.as_str()) {
                            for drilldown in drilldowns {
                                spectral_drilldown_refs.push(drilldown.drilldown_id.clone());
                                source_reading_refs.push(drilldown.drilldown_id.clone());
                                evidence_refs.extend(
                                    drilldown
                                        .dominant_atom_family_composition
                                        .iter()
                                        .flat_map(|composition| composition.atom_observation_refs.clone()),
                                );
                                analytic_basis.push(format!(
                                    "analyticDistance:spectralDrilldown:{}:atomFamilies={}:overlapPairs={}:repairAxisDeltas={}",
                                    drilldown.drilldown_id,
                                    drilldown.dominant_atom_family_composition.len(),
                                    drilldown.high_overlap_molecule_pairs.len(),
                                    drilldown.repair_axis_delta_readings.len()
                                ));
                            }
                        }
                    }
                }
            }

            let coverage_blocker_refs = unique_strings(
                coverage_blockers
                    .iter()
                    .cloned()
                    .chain(strength.blocked_by.iter().cloned()),
            );
            let witness_completeness_blocker_refs = unique_strings(
                witness_blockers
                    .iter()
                    .cloned()
                    .chain(strength.blocked_reflection_or_preservation_reasons.iter().cloned()),
            );
            let evidence_refs = if evidence_refs.is_empty() {
                vec![strength.source_reading_ref.clone()]
            } else {
                unique_strings(evidence_refs.into_iter())
            };
            let source_reading_refs = unique_strings(source_reading_refs.into_iter());
            let structural_distance = measured_part4_distance_value(
                structural_value.max(0),
                "selected-structural-support-count",
                evidence_refs.clone(),
                unique_strings(structural_basis.into_iter()),
                &coverage_refs,
                "selected structural distance is the bounded support size of this representation reading, not global architecture distance",
            );
            let analytic_distance = if analytic_status == "measured" {
                measured_part4_distance_value(
                    analytic_value.max(0),
                    "selected-analytic-magnitude-x100",
                    source_reading_refs.clone(),
                    unique_strings(analytic_basis.into_iter()),
                    &coverage_refs,
                    "selected analytic distance reads this representation's finite matrix, vector, spectral, or boundary magnitude; it is not an architecture quality score",
                )
            } else {
                blocked_curvature_distance_value(
                    "selected-analytic-magnitude-x100",
                    source_reading_refs.clone(),
                    unique_strings(analytic_basis.into_iter()),
                    &coverage_refs,
                    witness_completeness_blocker_refs.clone(),
                    "selected analytic distance is blocked when the representation value is boundary-only or unavailable; it is not an architecture quality score",
                )
            };
            let lipschitz_stability = if matches!(analytic_distance.status.as_str(), "measured" | "zero") {
                let denominator = structural_distance.measured_value.unwrap_or_default().max(1);
                let numerator = analytic_distance.measured_value.unwrap_or_default();
                measured_part4_distance_value(
                    ((numerator + denominator - 1) / denominator).max(1),
                    "selected-L-upper-bound-x100",
                    source_reading_refs.clone(),
                    vec![
                        format!("lipschitz:analyticDistance={numerator}"),
                        format!("lipschitz:structuralDistance={denominator}"),
                        format!("lipschitz:selectedRepresentation:{}", strength.representation_family),
                    ],
                    &coverage_refs,
                    "Lipschitz stability is a selected finite-representation upper-bound reading; it does not prove stability for all comparable architectures",
                )
            } else {
                blocked_curvature_distance_value(
                    "selected-L-upper-bound-x100",
                    source_reading_refs.clone(),
                    vec![format!("lipschitz:selectedRepresentation:{}", strength.representation_family)],
                    &coverage_refs,
                    analytic_distance.blocker_refs.clone(),
                    "Lipschitz upper-bound reading is blocked because analytic distance is unavailable",
                )
            };
            let bi_lipschitz_faithfulness = blocked_curvature_distance_value(
                "selected-bi-lipschitz-lower-bound",
                source_reading_refs.clone(),
                vec![
                    format!("biLipschitz:structuralDistance:{}", strength.representation_family),
                    format!("biLipschitz:analyticDistance:{}", strength.representation_family),
                    "biLipschitz:requiresCoverageAndWitnessCompleteness".to_string(),
                ],
                &coverage_refs,
                unique_strings(
                    coverage_blocker_refs
                        .iter()
                        .cloned()
                        .chain(witness_completeness_blocker_refs.iter().cloned()),
                ),
                "bi-Lipschitz faithfulness lower bound is blocked unless coverage and witness completeness are supplied for the selected scope",
            );

            ArchSigRepresentationMetricReadingV0 {
                representation_metric_reading_id: format!(
                    "representation-metric:{}",
                    stable_id(&strength.reading_id)
                ),
                representation_ref: strength.source_reading_ref.clone(),
                representation_family: strength.representation_family.clone(),
                source_reading_refs,
                distance_profile_ref: foundation.profile.profile_id.clone(),
                diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                structural_distance,
                analytic_distance,
                lipschitz_stability,
                bi_lipschitz_faithfulness,
                coverage_blocker_refs,
                witness_completeness_blocker_refs,
                analytic_representation_refs,
                spectral_reading_refs,
                spectral_mode_refs: unique_strings(spectral_mode_refs.into_iter()),
                spectral_drilldown_refs: unique_strings(spectral_drilldown_refs.into_iter()),
                representation_strength_refs: vec![strength.reading_id.clone()],
                evidence_refs,
                evidence_boundary:
                    "representation metric is selected-scope evidence over ArchMap + LawPolicy; analytic closeness is not structural faithfulness without coverage and witness completeness"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn analytic_metric_value_from_representation(
    representation: &ArchSigAnalyticRepresentationV0,
) -> (i64, Vec<String>, bool) {
    let mut basis = Vec::new();
    match representation.value_type.as_str() {
        "nat" => {
            let value = representation.value.parse::<i64>().unwrap_or_default();
            basis.push(format!(
                "analyticDistance:{}:nat={value}",
                representation.representation_id
            ));
            (value, basis, true)
        }
        "float" => {
            let value = scaled_spectral_value(&representation.value).abs();
            basis.push(format!(
                "analyticDistance:{}:float={}",
                representation.representation_id, representation.value
            ));
            (value, basis, true)
        }
        "matrixShape" => {
            let value = representation
                .sparse_matrix_entries
                .iter()
                .map(|entry| entry.value.abs())
                .sum::<i64>();
            basis.push(format!(
                "analyticDistance:{}:matrixEntries={}",
                representation.representation_id,
                representation.sparse_matrix_entries.len()
            ));
            (value, basis, true)
        }
        "vector" => {
            let trimmed = representation
                .value
                .trim_matches(|ch| ch == '[' || ch == ']');
            let value = scaled_spectral_value(trimmed).abs();
            basis.push(format!(
                "analyticDistance:{}:vector={}",
                representation.representation_id, representation.value
            ));
            (value, basis, true)
        }
        "boundaryStatus" if representation.status == "measured" => {
            basis.push(format!(
                "analyticDistance:{}:boundaryStatus={}",
                representation.representation_id, representation.value
            ));
            (1, basis, true)
        }
        _ => {
            basis.push(format!(
                "analyticDistance:{}:blockedBoundaryStatus={}",
                representation.representation_id, representation.value
            ));
            (0, basis, false)
        }
    }
}

fn analytic_metric_value_from_spectral(
    spectral: &ArchSigSpectralAnalysisReadingV0,
) -> (i64, Vec<String>) {
    let mut value = 0_i64;
    let mut basis = Vec::new();
    for spectral_value in &spectral.values {
        let scaled = scaled_spectral_value(&spectral_value.value).abs();
        value += scaled;
        basis.push(format!(
            "analyticDistance:{}:{}={}",
            spectral.spectral_reading_id, spectral_value.name, spectral_value.value
        ));
    }
    (value, basis)
}

fn scaled_spectral_value(value: &str) -> i64 {
    value
        .parse::<f64>()
        .map(|value| (value * 100.0).round() as i64)
        .unwrap_or_default()
}

fn attach_representation_metric_refs(
    analytic_representations: &mut [ArchSigAnalyticRepresentationV0],
    spectral_analysis_readings: &mut [ArchSigSpectralAnalysisReadingV0],
    spectral_mode_readings: &mut [ArchSigSpectralModeReadingV0],
    spectral_drilldown_readings: &mut [ArchSigSpectralDrilldownReadingV0],
    representation_strength_readings: &mut [ArchSigRepresentationStrengthReadingV0],
    metric_readings: &[ArchSigRepresentationMetricReadingV0],
) {
    for metric in metric_readings {
        for representation in analytic_representations.iter_mut().filter(|reading| {
            metric
                .analytic_representation_refs
                .contains(&reading.representation_id)
        }) {
            representation
                .part4_distance_refs
                .push(metric.representation_metric_reading_id.clone());
        }
        for spectral in spectral_analysis_readings.iter_mut().filter(|reading| {
            metric
                .spectral_reading_refs
                .contains(&reading.spectral_reading_id)
        }) {
            spectral
                .part4_distance_refs
                .push(metric.representation_metric_reading_id.clone());
        }
        for mode in spectral_mode_readings.iter_mut().filter(|reading| {
            metric
                .spectral_mode_refs
                .contains(&reading.spectral_mode_id)
        }) {
            mode.part4_distance_refs
                .push(metric.representation_metric_reading_id.clone());
        }
        for drilldown in spectral_drilldown_readings.iter_mut().filter(|reading| {
            metric
                .spectral_drilldown_refs
                .contains(&reading.drilldown_id)
        }) {
            drilldown
                .part4_distance_refs
                .push(metric.representation_metric_reading_id.clone());
        }
        for strength in representation_strength_readings
            .iter_mut()
            .filter(|reading| {
                metric
                    .representation_strength_refs
                    .contains(&reading.reading_id)
            })
        {
            strength
                .part4_distance_refs
                .push(metric.representation_metric_reading_id.clone());
        }
    }
}

fn promote_representation_metric_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigRepresentationMetricReadingV0],
) {
    if readings.is_empty() {
        return;
    }
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "representationMetric")
    {
        let blockers = readings
            .iter()
            .flat_map(|reading| reading.bi_lipschitz_faithfulness.blocker_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        distance.value = if blockers.is_empty() {
            measured_part4_distance_value(
                readings
                    .iter()
                    .filter_map(|reading| reading.lipschitz_stability.measured_value)
                    .sum::<i64>(),
                "selected-representation-stability",
                readings
                    .iter()
                    .map(|reading| reading.representation_metric_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| {
                        format!("representationMetric:{}", reading.representation_family)
                    })
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                "representationMetric aggregates selected representation stability readings only",
            )
        } else {
            blocked_curvature_distance_value(
                "selected-representation-faithfulness",
                readings
                    .iter()
                    .map(|reading| reading.representation_metric_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| {
                        format!("representationMetric:{}", reading.representation_family)
                    })
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                blockers,
                "representationMetric supporting distance is blocked for faithfulness until coverage and witness completeness are supplied",
            )
        };
        distance.evidence_boundary =
            "representationMetric reads selected analytic stability; it does not certify global structural faithfulness"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}
