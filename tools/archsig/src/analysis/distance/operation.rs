fn build_operation_distance_readings(
    repair_candidates: &[ArchSigRepairOperationCandidateV0],
    operation_deltas: &[ArchSigOperationDeltaReadingV0],
    signature_distance_readings: &[ArchSigSignatureDistanceReadingV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigOperationDistanceReadingV0> {
    let candidate_by_kind = repair_candidates
        .iter()
        .map(|candidate| (candidate.operation_kind.as_str(), candidate))
        .collect::<BTreeMap<_, _>>();
    let signature_reading = signature_distance_readings.first();
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    operation_deltas
        .iter()
        .map(|delta| {
            let candidate = candidate_by_kind.get(delta.operation_kind.as_str()).copied();
            let operation_cost = operation_cost_distance_value(delta, foundation, &coverage_refs);
            let target_distance_decrease =
                target_distance_decrease_value(delta, candidate, &coverage_refs);
            let protected_axis_movement =
                protected_axis_movement_value(delta, candidate, &coverage_refs);
            let transfer_risk_refs = unique_strings(
                delta
                    .transferred_obstructions
                    .iter()
                    .cloned()
                    .chain(candidate.into_iter().flat_map(|c| c.transfer_risks.clone())),
            );
            let unmeasured_axis_refs = signature_reading
                .map(|reading| reading.unmeasured_axis_refs.clone())
                .unwrap_or_default();
            let signature_blockers = signature_reading
                .map(|reading| reading.total_measured_distance.blocker_refs.clone())
                .unwrap_or_default();
            let distance_to_selected_flat = distance_to_selected_flat_value(
                signature_reading,
                &target_distance_decrease,
                &signature_blockers,
                &coverage_refs,
            );
            let side_effect_bound = side_effect_bound_value(
                delta,
                &transfer_risk_refs,
                &unmeasured_axis_refs,
                &signature_blockers,
                &coverage_refs,
            );
            let operation_distance_reading_id = format!(
                "operation-distance:{}",
                stable_id(&delta.operation_delta_id)
            );
            ArchSigOperationDistanceReadingV0 {
                operation_distance_reading_id,
                operation_delta_ref: delta.operation_delta_id.clone(),
                repair_candidate_ref: candidate.map(|c| c.repair_operation_candidate_id.clone()),
                operation_kind: delta.operation_kind.clone(),
                distance_profile_ref: foundation.profile.profile_id.clone(),
                diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                operation_cost,
                target_distance_decrease,
                protected_axis_movement,
                distance_to_selected_flat,
                side_effect_bound,
                transfer_risk_refs,
                unmeasured_axis_refs,
                evidence_refs: unique_strings(
                    delta
                        .support_refs
                        .iter()
                        .cloned()
                        .chain(delta.decreased_axes.iter().cloned())
                        .chain(delta.transferred_obstructions.iter().cloned()),
                ),
                repair_route_status: if !delta.transferred_obstructions.is_empty()
                    || !signature_blockers.is_empty()
                {
                    "candidateRouteBlockedByTransferRiskOrCoverage".to_string()
                } else if delta.decreased_axes.is_empty() {
                    "candidateRouteHasNoSelectedTargetDecrease".to_string()
                } else {
                    "candidateRouteHasSelectedTargetDecrease".to_string()
                },
                evidence_boundary:
                    "operation distance is a selected repair-route reading over candidate deltas; it is not automatic repair safety"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn operation_cost_distance_value(
    delta: &ArchSigOperationDeltaReadingV0,
    foundation: &ArchSigPart4DistanceFoundationV0,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let Some(cost) = selected_operation_cost(&delta.operation_kind, foundation) else {
        return blocked_curvature_distance_value(
            "operation-cost",
            vec![delta.operation_delta_id.clone()],
            vec![format!("profile:{}", foundation.profile.profile_id)],
            coverage_refs,
            vec![format!("missingOperationCost:{}", delta.operation_kind)],
            "operation cost is blocked because the selected Part IV DistanceProfile does not declare this operation kind",
        );
    };
    measured_part4_distance_value(
        cost,
        "operation-cost",
        vec![delta.operation_delta_id.clone()],
        vec![
            format!("operationCost:{}", delta.operation_kind),
            format!("profile:{}", foundation.profile.profile_id),
        ],
        coverage_refs,
        "operation cost is selected from the Part IV DistanceProfile operation cost table",
    )
}

fn selected_operation_cost(
    operation_kind: &str,
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Option<i64> {
    let kind = operation_kind.to_ascii_lowercase();
    foundation
        .profile
        .operation_costs
        .iter()
        .find(|cost| cost.operation_kind.eq_ignore_ascii_case(&kind))
        .map(|cost| cost.cost)
}

fn target_distance_decrease_value(
    delta: &ArchSigOperationDeltaReadingV0,
    candidate: Option<&ArchSigRepairOperationCandidateV0>,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let decrease = delta.decreased_axes.len() as i64 * 1000;
    measured_part4_distance_value(
        decrease,
        "milli-target-distance-decrease",
        unique_strings(
            std::iter::once(delta.operation_delta_id.clone())
                .chain(delta.decreased_axes.iter().cloned())
                .chain(
                    candidate
                        .into_iter()
                        .flat_map(|c| c.target_obstruction_refs.clone()),
                ),
        ),
        if delta.decreased_axes.is_empty() {
            vec!["targetDecrease:noneSelected".to_string()]
        } else {
            delta
                .decreased_axes
                .iter()
                .map(|axis| format!("targetDecrease:{axis}"))
                .collect()
        },
        coverage_refs,
        "target distance decrease counts selected nonzero signature axes targeted by the candidate transition",
    )
}

fn protected_axis_movement_value(
    delta: &ArchSigOperationDeltaReadingV0,
    candidate: Option<&ArchSigRepairOperationCandidateV0>,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let movement = delta.transferred_obstructions.len() as i64 * 1000;
    measured_part4_distance_value(
        movement,
        "milli-protected-axis-movement",
        unique_strings(
            std::iter::once(delta.operation_delta_id.clone())
                .chain(delta.transferred_obstructions.iter().cloned())
                .chain(
                    candidate
                        .into_iter()
                        .flat_map(|c| c.preserved_invariants.clone()),
                ),
        ),
        delta
            .transferred_obstructions
            .iter()
            .map(|risk| format!("protectedAxisMovement:{}", stable_id(risk)))
            .chain(std::iter::once(format!(
                "preservedInvariantCount:{}",
                candidate.map(|c| c.preserved_invariants.len()).unwrap_or(0)
            )))
            .collect(),
        coverage_refs,
        "protected-axis movement is separated from target decrease and records transferred obstruction risk",
    )
}

fn distance_to_selected_flat_value(
    signature_reading: Option<&ArchSigSignatureDistanceReadingV0>,
    target_decrease: &ArchSigDistanceValueV0,
    signature_blockers: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let current = signature_reading
        .and_then(|reading| reading.total_measured_distance.measured_value)
        .unwrap_or(0);
    let decrease = target_decrease.measured_value.unwrap_or(0);
    let remaining = current.saturating_sub(decrease);
    if !signature_blockers.is_empty() {
        return ArchSigDistanceValueV0 {
            status: "blocked".to_string(),
            measured_value: None,
            unit: "milli-distance-to-selected-flat".to_string(),
            provenance_refs: signature_reading
                .map(|reading| vec![reading.signature_distance_reading_id.clone()])
                .unwrap_or_default(),
            evaluator_basis_refs: vec!["distanceToSelectedFlat:signatureDistanceReading".to_string()],
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: signature_blockers.to_vec(),
            reading:
                "distance to selected flat region is blocked while signature aggregate coverage is blocked"
                    .to_string(),
        };
    }
    measured_part4_distance_value(
        remaining,
        "milli-distance-to-selected-flat",
        signature_reading
            .map(|reading| vec![reading.signature_distance_reading_id.clone()])
            .unwrap_or_default(),
        vec![
            format!("currentSignatureDistance:{current}"),
            format!("targetDecrease:{}", decrease),
        ],
        coverage_refs,
        "distance to selected flat region subtracts target decrease from selected signature distance without claiming global flatness",
    )
}

fn side_effect_bound_value(
    delta: &ArchSigOperationDeltaReadingV0,
    transfer_risk_refs: &[String],
    unmeasured_axis_refs: &[String],
    signature_blockers: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let blockers = unique_strings(
        transfer_risk_refs
            .iter()
            .cloned()
            .chain(
                unmeasured_axis_refs
                    .iter()
                    .map(|axis| format!("unmeasuredProtectedAxis:{axis}")),
            )
            .chain(signature_blockers.iter().cloned()),
    );
    if !blockers.is_empty() {
        return ArchSigDistanceValueV0 {
            status: "blocked".to_string(),
            measured_value: None,
            unit: "milli-side-effect-bound".to_string(),
            provenance_refs: delta.support_refs.clone(),
            evaluator_basis_refs: blockers
                .iter()
                .map(|blocker| format!("sideEffectBlocker:{}", stable_id(blocker)))
                .collect(),
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: blockers,
            reading:
                "side-effect bound remains blocked while transfer risks or unmeasured protected axes remain"
                    .to_string(),
        };
    }
    measured_part4_distance_value(
        0,
        "milli-side-effect-bound",
        delta.support_refs.clone(),
        vec!["sideEffectBound:noSelectedTransferRisk".to_string()],
        coverage_refs,
        "side-effect bound is zero only when no selected transfer risk or unmeasured protected axis is present",
    )
}

fn attach_operation_distance_refs(
    repair_candidates: &mut [ArchSigRepairOperationCandidateV0],
    operation_deltas: &mut [ArchSigOperationDeltaReadingV0],
    readings: &[ArchSigOperationDistanceReadingV0],
) {
    for reading in readings {
        if let Some(delta) = operation_deltas
            .iter_mut()
            .find(|delta| delta.operation_delta_id == reading.operation_delta_ref)
        {
            delta
                .part4_distance_refs
                .push(reading.operation_distance_reading_id.clone());
        }
        if let Some(candidate_ref) = &reading.repair_candidate_ref {
            if let Some(candidate) = repair_candidates
                .iter_mut()
                .find(|candidate| candidate.repair_operation_candidate_id == *candidate_ref)
            {
                candidate
                    .part4_distance_refs
                    .push(reading.operation_distance_reading_id.clone());
            }
        }
    }
}

fn promote_operation_geometry_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigOperationDistanceReadingV0],
) {
    if readings.is_empty() {
        return;
    }
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "operationGeometry")
    {
        let blockers = readings
            .iter()
            .flat_map(|reading| {
                reading
                    .operation_cost
                    .blocker_refs
                    .iter()
                    .chain(reading.side_effect_bound.blocker_refs.iter())
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let cost_total = readings
            .iter()
            .filter_map(|reading| reading.operation_cost.measured_value)
            .sum::<i64>();
        distance.value = if blockers.is_empty() {
            measured_part4_distance_value(
                cost_total,
                "operation-cost",
                readings
                    .iter()
                    .map(|reading| reading.operation_distance_reading_id.clone())
                    .collect(),
                readings
                    .iter()
                    .map(|reading| format!("operationCost:{}", reading.operation_kind))
                    .collect(),
                &foundation.profile.coverage_policy_refs,
                "operationGeometry aggregates operation costs for selected repair routes without claiming repair safety",
            )
        } else {
            ArchSigDistanceValueV0 {
                status: "blocked".to_string(),
                measured_value: None,
                unit: "operation-cost".to_string(),
                provenance_refs: readings
                    .iter()
                    .map(|reading| reading.operation_distance_reading_id.clone())
                    .collect(),
                evaluator_basis_refs: readings
                    .iter()
                    .map(|reading| format!("operationDistance:{}", reading.operation_distance_reading_id))
                    .collect(),
                coverage_refs: foundation.profile.coverage_policy_refs.clone(),
                blocker_refs: blockers,
                reading:
                    "operationGeometry remains blocked while selected repair routes have missing profile costs, transfer risks, or unmeasured protected axes"
                        .to_string(),
            }
        };
        distance.evidence_boundary =
            "operationGeometry reads repair-route cost and side-effect blockers; it is not automatic patch safety"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}
