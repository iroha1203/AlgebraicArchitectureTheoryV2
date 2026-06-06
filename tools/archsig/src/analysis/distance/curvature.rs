fn build_obstruction_measure_readings(
    curvature_support_readings: &[ArchSigCurvatureSupportReadingV0],
    obstruction_circuits: &[ArchSigObstructionCircuitV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigObstructionMeasureReadingV0> {
    let circuit_by_axis_and_witness = obstruction_circuits
        .iter()
        .flat_map(|circuit| {
            circuit.signature_axis_refs.iter().map(move |axis_ref| {
                (
                    (axis_ref.as_str(), circuit.witness_rule_ref.as_str()),
                    circuit,
                )
            })
        })
        .collect::<BTreeMap<_, _>>();
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    curvature_support_readings
        .iter()
        .flat_map(|reading| {
            reading.witness_supports.iter().map(|support| {
                let circuit_ref = circuit_by_axis_and_witness
                    .get(&(
                        support.signature_axis_ref.as_str(),
                        support.witness_rule_ref.as_str(),
                    ))
                    .map(|circuit| circuit.obstruction_circuit_id.clone())
                    .unwrap_or_else(|| format!("unmeasured:{}", support.witness_support_id));
                let obstruction_measure_reading_id = format!(
                    "obstruction-measure:{}",
                    stable_id(&support.witness_support_id)
                );
                let (witness_value, measure_value, measurement_status) =
                    if support.measurement_status == "measured" && support.curvature_value > 0 {
                        let witness_value = measured_part4_distance_value(
                            support.curvature_value,
                            "obstruction-witness-value",
                            support.support_refs.clone(),
                            vec![
                                format!("witnessRule:{}", support.witness_rule_ref),
                                format!("selectedAxis:{}", support.selected_axis_ref),
                            ],
                            &coverage_refs,
                            "witness value is measured from source-backed obstruction support rows",
                        );
                        let measure_value = measured_part4_distance_value(
                            support.curvature_value * support.weight.max(1),
                            "obstruction-measure-mass",
                            vec![support.witness_support_id.clone()],
                            vec![
                                format!("Omega_U:circuit:{circuit_ref}"),
                                format!("curvatureSupport:{}", support.witness_support_id),
                            ],
                            &coverage_refs,
                            "Omega_U(A) mass contribution over the selected obstruction circuit",
                        );
                        (witness_value, measure_value, "measured".to_string())
                    } else {
                        let blockers = if support.missing_evidence.is_empty() {
                            vec![format!("unmeasuredWitness:{}", support.witness_support_id)]
                        } else {
                            support.missing_evidence.clone()
                        };
                        let value = ArchSigDistanceValueV0 {
                            status: "blocked".to_string(),
                            measured_value: None,
                            unit: "obstruction-measure-mass".to_string(),
                            provenance_refs: vec![support.witness_support_id.clone()],
                            evaluator_basis_refs: vec![
                                format!("Omega_U:unmeasuredWitness:{}", support.witness_rule_ref),
                                format!("selectedAxis:{}", support.selected_axis_ref),
                            ],
                            coverage_refs: coverage_refs.clone(),
                            blocker_refs: blockers,
                            reading:
                                "missing witness support blocks obstruction measure; it is not zero curvature"
                                    .to_string(),
                        };
                        (value.clone(), value, "blockedByMissingWitness".to_string())
                    };

                ArchSigObstructionMeasureReadingV0 {
                    obstruction_measure_reading_id,
                    profile_ref: reading.profile_ref.clone(),
                    obstruction_circuit_ref: circuit_ref,
                    witness_support_ref: support.witness_support_id.clone(),
                    witness_rule_ref: support.witness_rule_ref.clone(),
                    selected_axis_ref: support.selected_axis_ref.clone(),
                    signature_axis_ref: support.signature_axis_ref.clone(),
                    distance_profile_ref: foundation.profile.profile_id.clone(),
                    diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                    witness_value,
                    measure_value,
                    support_refs: support.support_refs.clone(),
                    source_refs: support.source_refs.clone(),
                    observation_refs: support.observation_refs.clone(),
                    missing_evidence: support.missing_evidence.clone(),
                    measurement_status,
                    evidence_boundary:
                        "obstruction measure is computed from selected witness support rows under LawPolicy; missing witnesses remain blockers, not zero curvature"
                            .to_string(),
                    non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
                }
            })
        })
        .collect()
}

fn attach_obstruction_measure_refs(
    curvature_support_readings: &mut [ArchSigCurvatureSupportReadingV0],
    obstruction_measure_readings: &[ArchSigObstructionMeasureReadingV0],
) {
    for support_reading in curvature_support_readings {
        for support in &mut support_reading.witness_supports {
            support.obstruction_measure_reading_refs = obstruction_measure_readings
                .iter()
                .filter(|reading| reading.witness_support_ref == support.witness_support_id)
                .map(|reading| reading.obstruction_measure_reading_id.clone())
                .collect();
        }
    }
}

fn build_curvature_mass_readings(
    curvature_support_readings: &[ArchSigCurvatureSupportReadingV0],
    curvature_transfer_readings: &[ArchSigCurvatureTransferReadingV0],
    operation_distance_readings: &[ArchSigOperationDistanceReadingV0],
    obstruction_measure_readings: &[ArchSigObstructionMeasureReadingV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigCurvatureMassReadingV0> {
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    curvature_support_readings
        .iter()
        .map(|support_reading| {
            let measure_refs = obstruction_measure_readings
                .iter()
                .filter(|reading| reading.profile_ref == support_reading.profile_ref)
                .collect::<Vec<_>>();
            let measured_mass = measure_refs
                .iter()
                .filter_map(|reading| reading.measure_value.measured_value)
                .sum::<i64>();
            let blockers = unique_strings(
                support_reading
                    .unmeasured_axis_refs
                    .iter()
                    .map(|axis| format!("unmeasuredAxis:{axis}"))
                    .chain(support_reading.missing_evidence.iter().cloned())
                    .chain(
                        measure_refs
                            .iter()
                            .flat_map(|reading| reading.measure_value.blocker_refs.clone()),
                    ),
            );
            let measure_ids = measure_refs
                .iter()
                .map(|reading| reading.obstruction_measure_reading_id.clone())
                .collect::<Vec<_>>();
            let curvature_mass = if blockers.is_empty() {
                measured_part4_distance_value(
                    measured_mass,
                    "curvature-mass",
                    measure_ids.clone(),
                    vec![
                        format!("curv_mass_U:{}", support_reading.profile_ref),
                        "norm:sumSelectedObstructionMeasure".to_string(),
                    ],
                    &coverage_refs,
                    "curvature mass is the selected norm of witness-backed obstruction measure rows",
                )
            } else {
                ArchSigDistanceValueV0 {
                    status: "blocked".to_string(),
                    measured_value: None,
                    unit: "curvature-mass".to_string(),
                    provenance_refs: measure_ids.clone(),
                    evaluator_basis_refs: vec![
                        format!("curv_mass_U:{}", support_reading.profile_ref),
                        "unmeasuredIsNotZero".to_string(),
                    ],
                    coverage_refs: coverage_refs.clone(),
                    blocker_refs: blockers.clone(),
                    reading:
                        "curvature mass is blocked while selected witness rows or axes are unmeasured; absence is not zero curvature"
                            .to_string(),
                }
            };
            let operation_target_decrease = operation_distance_readings
                .iter()
                .filter_map(|reading| reading.target_distance_decrease.measured_value)
                .sum::<i64>();
            let protected_axis_movement = operation_distance_readings
                .iter()
                .filter_map(|reading| reading.protected_axis_movement.measured_value)
                .sum::<i64>();
            let transfer_reading = curvature_transfer_readings
                .iter()
                .find(|reading| reading.profile_ref == support_reading.profile_ref);
            let transfer_weight = transfer_reading
                .map(|reading| {
                    reading
                        .transfer_edges
                        .iter()
                        .map(|edge| edge.weight)
                        .sum::<i64>()
                })
                .unwrap_or(0);
            let transferred_obstruction_refs = transfer_reading
                .map(|reading| {
                    unique_strings(reading.transfer_edges.iter().flat_map(|edge| {
                        edge.witness_refs
                            .iter()
                            .cloned()
                            .chain(std::iter::once(edge.edge_id.clone()))
                    }))
                })
                .unwrap_or_default();
            let operation_distance_refs = operation_distance_readings
                .iter()
                .map(|reading| reading.operation_distance_reading_id.clone())
                .collect::<Vec<_>>();
            let before_operation_mass = measured_part4_distance_value(
                measured_mass,
                "curvature-mass",
                measure_ids.clone(),
                vec!["beforeOperation:Omega_U(A)".to_string()],
                &coverage_refs,
                "before-operation mass is the measured selected support contribution only",
            );
            let after_value = measured_mass
                .saturating_sub(operation_target_decrease)
                .saturating_add(protected_axis_movement);
            let after_operation_mass = if blockers.is_empty() {
                measured_part4_distance_value(
                    after_value,
                    "curvature-mass",
                    measure_ids.clone(),
                    vec![
                        format!("afterOperation:targetDecrease:{operation_target_decrease}"),
                        format!("afterOperation:protectedMovement:{protected_axis_movement}"),
                    ],
                    &coverage_refs,
                    "after-operation mass separates target-axis decrease from protected-axis movement",
                )
            } else {
                blocked_curvature_distance_value(
                    "curvature-mass",
                    measure_ids.clone(),
                    vec!["afterOperation:blockedByUnmeasuredCurvature".to_string()],
                    &coverage_refs,
                    blockers.clone(),
                    "after-operation curvature mass is blocked while selected curvature rows remain unmeasured",
                )
            };
            let target_axis_decrease = measured_part4_distance_value(
                operation_target_decrease,
                "curvature-target-axis-decrease",
                operation_distance_refs.clone(),
                vec!["curvatureTransport:targetAxisDecrease".to_string()],
                &coverage_refs,
                "target-axis curvature decrease is read separately from protected-axis movement",
            );
            let protected_axis_movement_value = measured_part4_distance_value(
                protected_axis_movement,
                "curvature-protected-axis-movement",
                operation_distance_refs.clone(),
                vec!["curvatureTransport:protectedAxisMovement".to_string()],
                &coverage_refs,
                "protected-axis movement is tracked as possible curvature transport, not erased target improvement",
            );
            let transport_distance = if blockers.is_empty() {
                measured_part4_distance_value(
                    transfer_weight + protected_axis_movement,
                    "curvature-transport-distance",
                    transfer_reading
                        .map(|reading| vec![reading.reading_id.clone()])
                        .unwrap_or_default(),
                    vec![
                        format!("transport_U:transferWeight:{transfer_weight}"),
                        format!("transport_U:protectedMovement:{protected_axis_movement}"),
                    ],
                    &coverage_refs,
                    "curvature transport compares selected obstruction measure before and after operation over measured supports",
                )
            } else {
                blocked_curvature_distance_value(
                    "curvature-transport-distance",
                    transfer_reading
                        .map(|reading| vec![reading.reading_id.clone()])
                        .unwrap_or_else(|| measure_ids.clone()),
                    vec!["transport_U:blockedByUnmeasuredCurvature".to_string()],
                    &coverage_refs,
                    blockers.clone(),
                    "curvature transport is blocked by unmeasured witness rows or axes and cannot be read as zero transfer",
                )
            };
            ArchSigCurvatureMassReadingV0 {
                curvature_mass_reading_id: format!(
                    "curvature-mass:{}",
                    stable_id(&support_reading.reading_id)
                ),
                profile_ref: support_reading.profile_ref.clone(),
                support_reading_ref: support_reading.reading_id.clone(),
                transfer_reading_ref: transfer_reading.map(|reading| reading.reading_id.clone()),
                distance_profile_ref: foundation.profile.profile_id.clone(),
                diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                obstruction_measure_reading_refs: measure_ids,
                measured_axis_refs: support_reading.measured_axis_refs.clone(),
                unmeasured_axis_refs: support_reading.unmeasured_axis_refs.clone(),
                curvature_mass,
                before_operation_mass,
                after_operation_mass,
                target_axis_decrease,
                protected_axis_movement: protected_axis_movement_value,
                transport_distance,
                transferred_obstruction_refs,
                complexity_transfer_distance_refs: operation_distance_refs,
                evidence_refs: unique_strings(
                    support_reading
                        .witness_supports
                        .iter()
                        .flat_map(|support| support.support_refs.iter().cloned()),
                ),
                evidence_boundary:
                    "curvature mass and transport are selected LawPolicy-relative readings over witness-backed obstruction measure; they are not global flatness or future incident claims"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn blocked_curvature_distance_value(
    unit: &str,
    provenance_refs: Vec<String>,
    evaluator_basis_refs: Vec<String>,
    coverage_refs: &[String],
    blocker_refs: Vec<String>,
    reading: &str,
) -> ArchSigDistanceValueV0 {
    ArchSigDistanceValueV0 {
        status: "blocked".to_string(),
        measured_value: None,
        unit: unit.to_string(),
        provenance_refs,
        evaluator_basis_refs,
        coverage_refs: coverage_refs.to_vec(),
        blocker_refs,
        reading: reading.to_string(),
    }
}

fn attach_curvature_mass_refs(
    curvature_support_readings: &mut [ArchSigCurvatureSupportReadingV0],
    curvature_transfer_readings: &mut [ArchSigCurvatureTransferReadingV0],
    curvature_mass_readings: &[ArchSigCurvatureMassReadingV0],
) {
    for mass in curvature_mass_readings {
        if let Some(support) = curvature_support_readings
            .iter_mut()
            .find(|reading| reading.reading_id == mass.support_reading_ref)
        {
            support
                .part4_distance_refs
                .push(mass.curvature_mass_reading_id.clone());
        }
        if let Some(transfer_ref) = &mass.transfer_reading_ref {
            if let Some(transfer) = curvature_transfer_readings
                .iter_mut()
                .find(|reading| reading.reading_id == *transfer_ref)
            {
                transfer
                    .part4_distance_refs
                    .push(mass.curvature_mass_reading_id.clone());
                for edge in &mut transfer.transfer_edges {
                    edge.part4_distance_refs
                        .push(mass.curvature_mass_reading_id.clone());
                }
            }
        }
    }
}

fn promote_curvature_geometry_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigCurvatureMassReadingV0],
) {
    if readings.is_empty() {
        return;
    }
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "curvatureGeometry")
    {
        let blockers = readings
            .iter()
            .flat_map(|reading| reading.curvature_mass.blocker_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let total = readings
            .iter()
            .filter_map(|reading| reading.curvature_mass.measured_value)
            .sum::<i64>();
        distance.value = if blockers.is_empty() {
            measured_part4_distance_value(
                total,
                "curvature-mass",
                readings
                    .iter()
                    .map(|reading| reading.curvature_mass_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| format!("curv_mass_U:{}", reading.profile_ref))
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                "curvatureGeometry aggregates selected witness-backed curvature mass readings",
            )
        } else {
            blocked_curvature_distance_value(
                "curvature-mass",
                readings
                    .iter()
                    .map(|reading| reading.curvature_mass_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| format!("curvatureMass:{}", reading.curvature_mass_reading_id))
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                blockers,
                "curvatureGeometry remains blocked while selected witness rows or axes are unmeasured",
            )
        };
        distance.evidence_boundary =
            "curvatureGeometry reads selected obstruction measure and transport; it is not global zero-curvature proof"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}
