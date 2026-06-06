pub(crate) fn build_pr_review_report(
    base_archmap_path: &Path,
    base_archmap: &serde_json::Value,
    after_archmap_path: Option<&Path>,
    after_archmap: Option<&serde_json::Value>,
    path_archmap_paths: &[PathBuf],
    path_archmaps: &[serde_json::Value],
    delta_archmap_path: &Path,
    delta_archmap: &serde_json::Value,
    law_policy_path: &Path,
    law_policy: &serde_json::Value,
    base_archmap_typed: &ArchMapDocumentV0,
    after_archmap_typed: Option<&ArchMapDocumentV0>,
    path_archmap_typed: &[ArchMapDocumentV0],
    law_policy_typed: &LawPolicyDocumentV0,
) -> serde_json::Value {
    let changed_refs = string_array(delta_archmap, "changedObservationRefs");
    let matched_observations = changed_archmap_observations(base_archmap, &changed_refs);
    let changed_families = changed_atom_families(base_archmap, &changed_refs);
    let matched_laws = matched_policy_laws(law_policy, &changed_families);
    let matched_axis_refs = matched_policy_axis_refs(&matched_laws);
    let source_targets =
        source_targets_for_changed_refs(base_archmap, delta_archmap, &changed_refs);
    let base_packet = build_archsig_analysis_packet(
        base_archmap_typed,
        law_policy_typed,
        Some(&base_archmap_path.display().to_string()),
        Some(&law_policy_path.display().to_string()),
    );
    let base_packet_value = serde_json::to_value(&base_packet).unwrap_or(serde_json::Value::Null);
    let after_packet_value = after_archmap_typed.map(|after_archmap_typed| {
        let after_path = after_archmap_path
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "after-archmap".to_string());
        let packet = build_archsig_analysis_packet(
            after_archmap_typed,
            law_policy_typed,
            Some(&after_path),
            Some(&law_policy_path.display().to_string()),
        );
        serde_json::to_value(&packet).unwrap_or(serde_json::Value::Null)
    });
    let path_packet_values = path_archmap_typed
        .iter()
        .enumerate()
        .map(|(index, path_archmap_typed)| {
            let path = path_archmap_paths
                .get(index)
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| format!("path-archmap:{index}"));
            let packet = build_archsig_analysis_packet(
                path_archmap_typed,
                law_policy_typed,
                Some(&path),
                Some(&law_policy_path.display().to_string()),
            );
            serde_json::to_value(&packet).unwrap_or(serde_json::Value::Null)
        })
        .collect::<Vec<_>>();
    let pr_drift_readings = pr_drift_readings(
        base_archmap,
        after_archmap,
        delta_archmap,
        &changed_refs,
        &base_packet_value,
        &path_packet_values,
        after_packet_value.as_ref(),
    );
    let architecture_navigation_report = architecture_navigation_report(&pr_drift_readings);

    serde_json::json!({
        "schemaVersion": "archsig-pr-review-report-v1",
        "reviewId": format!(
            "archsig-pr-review:{}:{}:{}",
            json_string(base_archmap, "mapId", "base-archmap"),
            json_string(delta_archmap, "deltaId", "delta-archmap"),
            json_string(law_policy, "lawPolicyId", "law-policy")
        ),
        "canonicalInputs": {
            "baseArchMap": {
                "path": base_archmap_path.display().to_string(),
                "schemaVersion": schema_string(base_archmap),
                "mapId": json_field(base_archmap, "mapId"),
                "architectureId": json_field(base_archmap, "architectureId")
            },
            "afterArchMap": after_archmap.map(|after_archmap| serde_json::json!({
                "path": after_archmap_path
                    .map(|path| path.display().to_string())
                    .unwrap_or_else(|| "after-archmap".to_string()),
                "schemaVersion": schema_string(after_archmap),
                "mapId": json_field(after_archmap, "mapId"),
                "architectureId": json_field(after_archmap, "architectureId")
            })).unwrap_or(serde_json::Value::Null),
            "pathArchMaps": serde_json::Value::Array(path_archmaps.iter().enumerate().map(|(index, path_archmap)| {
                serde_json::json!({
                    "path": path_archmap_paths
                        .get(index)
                        .map(|path| path.display().to_string())
                        .unwrap_or_else(|| format!("path-archmap:{index}")),
                    "schemaVersion": schema_string(path_archmap),
                    "mapId": json_field(path_archmap, "mapId"),
                    "architectureId": json_field(path_archmap, "architectureId")
                })
            }).collect()),
            "deltaArchMap": {
                "path": delta_archmap_path.display().to_string(),
                "schemaVersion": schema_string(delta_archmap),
                "deltaId": json_field(delta_archmap, "deltaId"),
                "baseSnapshotRef": json_field(delta_archmap, "baseSnapshotRef"),
                "headSnapshotRef": json_field(delta_archmap, "headSnapshotRef"),
                "changedObservationRefs": array_field(delta_archmap, "changedObservationRefs")
            },
            "lawPolicy": {
                "path": law_policy_path.display().to_string(),
                "schemaVersion": schema_string(law_policy),
                "lawPolicyId": json_field(law_policy, "lawPolicyId"),
                "policyVersion": json_field(law_policy, "policyVersion"),
                "measurementPolicyId": json_field(
                    law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                    "policyId"
                )
            }
        },
        "policyBoundary": {
            "lawPolicyRequired": true,
            "rule": "No LawPolicy, no ArchSig judgement",
            "selectedAxisRefs": array_field(
                law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                "selectedAxisRefs"
            ),
            "coveragePolicy": json_field(
                law_policy.get("measurementPolicy").unwrap_or(&serde_json::Value::Null),
                "coveragePolicy"
            )
        },
        "changeLocalDiagnosis": {
            "changedObservationCount": changed_refs.len(),
            "matchedBaseObservationCount": matched_observations.as_array().map(Vec::len).unwrap_or_default(),
            "changedAtomFamilies": json_string_array(changed_families.iter()),
            "policyMatchedLawCount": matched_laws.as_array().map(Vec::len).unwrap_or_default(),
            "policyMatchedAxisRefs": json_string_array(matched_axis_refs.iter()),
            "sourceTargetCount": source_targets.as_array().map(Vec::len).unwrap_or_default()
        },
        "changedObservations": matched_observations,
        "policyMatchedLaws": matched_laws,
        "sourceTargets": source_targets,
        "prDriftReadings": pr_drift_readings,
        "architectureNavigationReport": architecture_navigation_report,
        "evidenceBoundary": "ArchSig PR review reads base/head ArchMap, PR-local ArchMap delta, and LawPolicy as canonical inputs. Raw diff and ArchMapCommit are outside this input surface. Base/head analysis packets are generated internally from those inputs and are not accepted as PR-review input artifacts."
    })
}

fn pr_drift_readings(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    delta_archmap: &serde_json::Value,
    changed_refs: &[String],
    base_packet: &serde_json::Value,
    path_packets: &[serde_json::Value],
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let coverage_gaps = pr_coverage_gaps(base_archmap, after_archmap, base_packet, after_packet);
    let endpoint_distance = pr_endpoint_signature_distance(base_packet, after_packet);
    let total_path_movement = pr_total_path_movement(base_packet, path_packets, after_packet);
    let hidden_excursion_status = if !path_packets.is_empty() && after_packet.is_some() {
        "measuredFromSuppliedIntermediateArchMapSnapshots"
    } else if after_packet.is_some() {
        "blockedWithoutIntermediateArchMapPathSnapshots"
    } else {
        "blockedWithoutAfterArchMap"
    };
    let safe_change_budget = pr_safe_change_budget(base_packet, &endpoint_distance, &coverage_gaps);
    let top_moved_axes = pr_top_moved_axes(base_packet, after_packet);
    let top_moved_atoms = pr_top_moved_atoms(base_archmap, after_archmap, changed_refs);
    let review_focus = pr_review_focus(
        delta_archmap,
        &top_moved_axes,
        &top_moved_atoms,
        &coverage_gaps,
    );

    serde_json::Value::Array(vec![serde_json::json!({
        "readingId": format!(
            "pr-drift:{}:{}",
            json_string(base_archmap, "mapId", "base-archmap"),
            after_archmap
                .map(|document| json_string(document, "mapId", "after-archmap"))
                .unwrap_or_else(|| "after-archmap-missing".to_string())
        ),
        "distanceProfileRef": json_field(
            base_packet.get("part4DistanceFoundation")
                .and_then(|foundation| foundation.get("profile"))
                .unwrap_or(&serde_json::Value::Null),
            "profileId"
        ),
        "baseAnalysisRef": json_field(base_packet, "analysisId"),
        "afterAnalysisRef": after_packet
            .map(|packet| json_field(packet, "analysisId"))
            .unwrap_or(serde_json::Value::Null),
        "endpointSignatureDistance": endpoint_distance,
        "totalPathMovement": total_path_movement,
        "hiddenExcursionStatus": hidden_excursion_status,
        "topMovedAtoms": top_moved_atoms,
        "topMovedAxes": top_moved_axes,
        "coverageGaps": coverage_gaps,
        "safeChangeBudget": safe_change_budget,
        "reviewFocus": review_focus,
        "evidenceBoundary": "PR drift is measured from base/head ArchSig packets generated from ArchMap + LawPolicy and localized by ArchMapDelta; it is not raw diff analysis, merge approval, repair safety, or forecast.",
        "nonConclusions": [
            "PR drift is not merge approval",
            "PR drift does not prove automatic repair safety",
            "PR drift does not predict future incidents",
            "coverage gaps limit safe-change budget instead of becoming measured zero"
        ]
    })])
}

fn architecture_navigation_report(pr_drift_readings: &serde_json::Value) -> serde_json::Value {
    let Some(reading) = pr_drift_readings.as_array().and_then(|items| items.first()) else {
        return serde_json::json!({
            "status": "blocked",
            "recommendedReviewFocus": [],
            "safeChangeStatus": "blockedWithoutPrDriftReading"
        });
    };
    serde_json::json!({
        "status": "needsReview",
        "endpointSignatureDistance": json_field(reading, "endpointSignatureDistance"),
        "totalPathMovement": json_field(reading, "totalPathMovement"),
        "hiddenExcursionStatus": json_field(reading, "hiddenExcursionStatus"),
        "safeChangeBudget": json_field(reading, "safeChangeBudget"),
        "topMovedAtoms": array_field_with_limit(reading, "topMovedAtoms", Some(5)),
        "topMovedAxes": array_field_with_limit(reading, "topMovedAxes", Some(5)),
        "recommendedReviewFocus": array_field(reading, "reviewFocus"),
        "evidenceBoundary": "Architecture navigation report ranks source-backed PR drift surfaces; reviewers still inspect the cited source refs and supplied ArchMap evidence."
    })
}

fn pr_endpoint_signature_distance(
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return pr_distance_value(
            "blocked",
            None,
            "milli-signature-endpoint-distance",
            vec![],
            vec!["afterArchMap:not-supplied".to_string()],
            "endpoint signature distance requires --after-archmap; missing head evidence is blocked, not zero",
        );
    };
    let base_axes = signature_axis_value_map(base_packet);
    let after_axes = signature_axis_value_map(after_packet);
    let axis_refs = base_axes
        .keys()
        .chain(after_axes.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut total = 0_i64;
    let mut provenance_refs = Vec::new();
    let mut basis_refs = Vec::new();
    for axis_ref in axis_refs {
        let before = base_axes.get(&axis_ref).copied().unwrap_or_default();
        let after = after_axes.get(&axis_ref).copied().unwrap_or_default();
        total += (after - before).abs() * 1000;
        provenance_refs.push(axis_ref.clone());
        basis_refs.push(format!("axisDelta:{axis_ref}:{before}->{after}"));
    }
    pr_distance_value(
        "measured",
        Some(total),
        "milli-signature-endpoint-distance",
        provenance_refs,
        basis_refs,
        "endpoint signature distance is the selected-axis L1 delta between internally generated base/head ArchSig packets",
    )
}

fn pr_total_path_movement(
    base_packet: &serde_json::Value,
    path_packets: &[serde_json::Value],
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return pr_distance_value(
            "blocked",
            None,
            "milli-signature-path-movement",
            vec![],
            vec!["afterArchMap:not-supplied".to_string()],
            "total path movement requires --after-archmap; missing head evidence is blocked, not zero",
        );
    };
    let mut packets = Vec::with_capacity(path_packets.len() + 2);
    packets.push(base_packet);
    packets.extend(path_packets.iter());
    packets.push(after_packet);
    let mut total = 0_i64;
    let mut provenance_refs = BTreeSet::new();
    let mut basis_refs = Vec::new();
    for (index, window) in packets.windows(2).enumerate() {
        let before = signature_axis_value_map(window[0]);
        let after = signature_axis_value_map(window[1]);
        let axis_refs = before
            .keys()
            .chain(after.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        for axis_ref in axis_refs {
            let before_value = before.get(&axis_ref).copied().unwrap_or_default();
            let after_value = after.get(&axis_ref).copied().unwrap_or_default();
            total += (after_value - before_value).abs() * 1000;
            provenance_refs.insert(axis_ref.clone());
            basis_refs.push(format!(
                "pathSegment:{index}:axisDelta:{axis_ref}:{before_value}->{after_value}"
            ));
        }
    }
    let mut value = pr_distance_value(
        "measured",
        Some(total),
        "milli-signature-path-movement",
        provenance_refs.into_iter().collect(),
        basis_refs,
        if path_packets.is_empty() {
            "total path movement is measured as the two-point base/head lower bound; hidden intermediate excursions require supplied ArchMap path snapshots"
        } else {
            "total path movement is the selected-axis sum across supplied base/intermediate/head ArchMap snapshots"
        },
    );
    if let Some(object) = value.as_object_mut() {
        object.insert(
            "pathGranularity".to_string(),
            serde_json::Value::String(if path_packets.is_empty() {
                "twoPointBaseHead".to_string()
            } else {
                "suppliedIntermediateSnapshots".to_string()
            }),
        );
        object.insert(
            "pathSnapshotCount".to_string(),
            serde_json::Value::Number((path_packets.len() as i64).into()),
        );
    }
    value
}

fn pr_safe_change_budget(
    base_packet: &serde_json::Value,
    endpoint_distance: &serde_json::Value,
    coverage_gaps: &serde_json::Value,
) -> serde_json::Value {
    let base_margin = first_signature_distance(base_packet)
        .and_then(|reading| reading.get("safeRegionMargin"))
        .and_then(|margin| margin.get("measuredValue"))
        .and_then(serde_json::Value::as_i64);
    let endpoint = endpoint_distance
        .get("measuredValue")
        .and_then(serde_json::Value::as_i64);
    let has_coverage_gaps = coverage_gaps
        .as_array()
        .is_some_and(|items| !items.is_empty());
    let remaining = match (base_margin, endpoint) {
        (Some(base_margin), Some(endpoint)) => Some((base_margin - endpoint).max(0)),
        _ => None,
    };
    serde_json::json!({
        "status": if has_coverage_gaps {
            "blockedByCoverageGap"
        } else if remaining.is_some() {
            "measured"
        } else {
            "blocked"
        },
        "baseSafeRegionMargin": base_margin,
        "prMovement": endpoint,
        "remainingBudget": remaining,
        "marginUsage": match (base_margin, endpoint) {
            (Some(base_margin), Some(endpoint)) if base_margin > 0 => {
                serde_json::Value::String(format!("{endpoint}/{base_margin}"))
            }
            _ => serde_json::Value::Null
        },
        "coverageGapLimited": has_coverage_gaps,
        "blockerRefs": string_vec_from_array_objects(coverage_gaps, "gapId"),
        "reading": "safe change budget is evaluated against selected Part IV signature margin; coverage gaps block safe-region conclusion instead of being counted as zero risk"
    })
}

fn pr_top_moved_axes(
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(after_packet) = after_packet else {
        return serde_json::Value::Array(Vec::new());
    };
    let base_axes = signature_axis_object_map(base_packet);
    let after_axes = signature_axis_object_map(after_packet);
    let axis_refs = base_axes
        .keys()
        .chain(after_axes.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = axis_refs
        .into_iter()
        .filter_map(|axis_ref| {
            let before = base_axes
                .get(&axis_ref)
                .and_then(|axis| axis.get("value"))
                .and_then(serde_json::Value::as_i64)
                .unwrap_or_default();
            let after = after_axes
                .get(&axis_ref)
                .and_then(|axis| axis.get("value"))
                .and_then(serde_json::Value::as_i64)
                .unwrap_or_default();
            let delta = after - before;
            if delta == 0 {
                return None;
            }
            let base_axis = base_axes.get(&axis_ref).copied().unwrap_or(&serde_json::Value::Null);
            let after_axis = after_axes
                .get(&axis_ref)
                .copied()
                .unwrap_or(&serde_json::Value::Null);
            Some(serde_json::json!({
                "axisRef": axis_ref,
                "beforeValue": before,
                "afterValue": after,
                "delta": delta,
                "movementMagnitude": delta.abs(),
                "baseCoverageStatus": json_field(base_axis, "coverageStatus"),
                "afterCoverageStatus": json_field(after_axis, "coverageStatus"),
                "sourceRefs": json_string_array(
                    string_vec_from_value(base_axis, "sourceRefs")
                        .into_iter()
                        .chain(string_vec_from_value(after_axis, "sourceRefs"))
                ),
                "blockerRefs": json_string_array(
                    string_vec_from_value(base_axis, "missingEvidence")
                        .into_iter()
                        .chain(string_vec_from_value(after_axis, "missingEvidence"))
                ),
                "evidenceBoundary": "axis movement is read from generated base/head signature axis values under the same LawPolicy"
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("movementMagnitude")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(8).collect())
}

fn pr_top_moved_atoms(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    changed_refs: &[String],
) -> serde_json::Value {
    let Some(after_archmap) = after_archmap else {
        return serde_json::Value::Array(Vec::new());
    };
    let base_atoms = observation_object_map(base_archmap, "atomObservations", "atomObservationId");
    let after_atoms =
        observation_object_map(after_archmap, "atomObservations", "atomObservationId");
    let changed = changed_refs.iter().cloned().collect::<BTreeSet<_>>();
    let atom_refs = base_atoms
        .keys()
        .chain(after_atoms.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut rows = atom_refs
        .into_iter()
        .filter_map(|atom_ref| {
            let before = base_atoms.get(&atom_ref).copied();
            let after = after_atoms.get(&atom_ref).copied();
            if before.map(observation_movement_fingerprint)
                == after.map(observation_movement_fingerprint)
            {
                return None;
            }
            let movement_kind = match (before, after) {
                (None, Some(_)) => "added",
                (Some(_), None) => "removed",
                (Some(_), Some(_)) => "changed",
                (None, None) => return None,
            };
            let base = before.unwrap_or(&serde_json::Value::Null);
            let head = after.unwrap_or(&serde_json::Value::Null);
            let source_refs = if after.is_some() {
                array_field(head, "sourceRefs")
            } else {
                array_field(base, "sourceRefs")
            };
            let score = match movement_kind {
                "added" | "removed" => 3,
                _ => 1,
            } + i64::from(changed.contains(&atom_ref)) * 2;
            Some(serde_json::json!({
                "atomObservationRef": atom_ref,
                "movementKind": movement_kind,
                "movementScore": score,
                "changedByDelta": changed.contains(&atom_ref),
                "beforeFamily": json_field(base, "atomFamily"),
                "afterFamily": json_field(head, "atomFamily"),
                "beforePredicate": json_field(base, "predicate"),
                "afterPredicate": json_field(head, "predicate"),
                "sourceRefs": source_refs,
                "evidenceBoundary": "moved atom rows compare base/head ArchMap atom observations and retain source refs from the supplied ArchMap evidence"
            }))
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("movementScore")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(8).collect())
}

fn pr_coverage_gaps(
    base_archmap: &serde_json::Value,
    after_archmap: Option<&serde_json::Value>,
    base_packet: &serde_json::Value,
    after_packet: Option<&serde_json::Value>,
) -> serde_json::Value {
    let mut gaps: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    for (side, document) in [("base", Some(base_archmap)), ("after", after_archmap)] {
        if let Some(document) = document {
            for gap in array_items(document, "observationGaps") {
                let gap_id = json_string(gap, "gapId", "observation-gap");
                gaps.insert(
                    format!("{side}:{gap_id}"),
                    serde_json::json!({
                        "side": side,
                        "gapId": gap_id,
                        "gapKind": json_field(gap, "gapKind"),
                        "reason": json_field(gap, "reason"),
                        "sourceRefs": array_field(gap, "sourceRefs")
                    }),
                );
            }
        }
    }
    for (side, packet) in [("base", Some(base_packet)), ("after", after_packet)] {
        if let Some(packet) = packet {
            for axis in array_items(packet, "signatureAxes") {
                for missing in string_vec_from_value(axis, "missingEvidence") {
                    gaps.insert(
                        format!("{side}:{}", missing),
                        serde_json::json!({
                            "side": side,
                            "gapId": missing,
                            "gapKind": "signatureAxisMissingEvidence",
                            "reason": "selected signature axis has missing evidence under LawPolicy",
                            "sourceRefs": array_field(axis, "sourceRefs")
                        }),
                    );
                }
            }
        }
    }
    serde_json::Value::Array(gaps.into_values().collect())
}

fn observation_movement_fingerprint(observation: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "atomFamily": json_field(observation, "atomFamily"),
        "predicate": json_field(observation, "predicate"),
        "subjectRef": json_field(observation, "subjectRef"),
        "objectRefs": array_field(observation, "objectRefs"),
        "observationStatus": json_field(observation, "observationStatus"),
        "evidenceBoundary": json_field(observation, "evidenceBoundary"),
        "confidence": json_field(observation, "confidence"),
        "uncertainty": array_field(observation, "uncertainty"),
        "projectionRefs": array_field(observation, "projectionRefs")
    })
}

fn pr_review_focus(
    delta_archmap: &serde_json::Value,
    top_moved_axes: &serde_json::Value,
    top_moved_atoms: &serde_json::Value,
    coverage_gaps: &serde_json::Value,
) -> serde_json::Value {
    let mut focus = Vec::new();
    for axis in array_items(
        delta_archmap
            .get("reviewIntent")
            .unwrap_or(&serde_json::Value::Null),
        "expectedReviewAxes",
    ) {
        if let Some(axis) = axis.as_str() {
            focus.push(format!("delta-requested-axis:{axis}"));
        }
    }
    for axis in top_moved_axes.as_array().into_iter().flatten().take(5) {
        if let Some(axis_ref) = axis.get("axisRef").and_then(serde_json::Value::as_str) {
            focus.push(format!("moved-axis:{axis_ref}"));
        }
    }
    for atom in top_moved_atoms.as_array().into_iter().flatten().take(5) {
        if let Some(atom_ref) = atom
            .get("atomObservationRef")
            .and_then(serde_json::Value::as_str)
        {
            focus.push(format!("moved-atom:{atom_ref}"));
        }
    }
    if coverage_gaps
        .as_array()
        .is_some_and(|items| !items.is_empty())
    {
        focus.push("coverage-gaps-limit-safe-change-budget".to_string());
    }
    json_string_array(focus.iter())
}

fn pr_distance_value(
    status: &str,
    measured_value: Option<i64>,
    unit: &str,
    provenance_refs: Vec<String>,
    evaluator_basis_refs: Vec<String>,
    reading: &str,
) -> serde_json::Value {
    let mut value = serde_json::json!({
        "status": status,
        "unit": unit,
        "provenanceRefs": json_string_array(provenance_refs.iter()),
        "evaluatorBasisRefs": json_string_array(evaluator_basis_refs.iter()),
        "coverageRefs": [],
        "blockerRefs": [],
        "reading": reading
    });
    if let Some(measured_value) = measured_value {
        if let Some(object) = value.as_object_mut() {
            object.insert(
                "measuredValue".to_string(),
                serde_json::Value::Number(measured_value.into()),
            );
        }
    }
    value
}

fn changed_archmap_observations(
    base_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> serde_json::Value {
    serde_json::Value::Array(
        changed_refs
            .iter()
            .map(|changed_ref| {
                if let Some((kind, observation)) =
                    find_archmap_observation(base_archmap, changed_ref)
                {
                    serde_json::json!({
                        "ref": changed_ref,
                        "matched": true,
                        "kind": kind,
                        "family": observation_family(kind, observation),
                        "subjectRef": json_field(observation, "subjectRef"),
                        "predicate": json_field(observation, "predicate"),
                        "roleName": json_field(observation, "roleName"),
                        "sourceRefs": array_field(observation, "sourceRefs")
                    })
                } else {
                    serde_json::json!({
                        "ref": changed_ref,
                        "matched": false
                    })
                }
            })
            .collect(),
    )
}

fn find_archmap_observation<'a>(
    archmap: &'a serde_json::Value,
    observation_ref: &str,
) -> Option<(&'static str, &'a serde_json::Value)> {
    for observation in array_items(archmap, "atomObservations") {
        if observation
            .get("atomObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("atom", observation));
        }
    }
    for observation in array_items(archmap, "moleculeObservations") {
        if observation
            .get("moleculeObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("molecule", observation));
        }
    }
    for observation in array_items(archmap, "semanticObservations") {
        if observation
            .get("semanticObservationId")
            .and_then(serde_json::Value::as_str)
            == Some(observation_ref)
        {
            return Some(("semantic", observation));
        }
    }
    None
}

fn observation_family(kind: &str, observation: &serde_json::Value) -> serde_json::Value {
    match kind {
        "atom" => json_field(observation, "atomFamily"),
        "molecule" => json_field(observation, "moleculeFamily"),
        "semantic" => serde_json::Value::String("semantic".to_string()),
        _ => serde_json::Value::Null,
    }
}

fn changed_atom_families(
    base_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> BTreeSet<String> {
    changed_refs
        .iter()
        .filter_map(|changed_ref| {
            find_archmap_observation(base_archmap, changed_ref).and_then(|(kind, observation)| {
                if kind == "atom" {
                    observation
                        .get("atomFamily")
                        .and_then(serde_json::Value::as_str)
                        .map(str::to_string)
                } else if kind == "semantic" {
                    Some("semantic".to_string())
                } else {
                    None
                }
            })
        })
        .collect()
}

fn matched_policy_laws(
    law_policy: &serde_json::Value,
    changed_families: &BTreeSet<String>,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(law_policy, "selectedLaws")
            .into_iter()
            .filter(|law| {
                array_items(law, "appliesToAtomFamilies")
                    .into_iter()
                    .filter_map(serde_json::Value::as_str)
                    .any(|family| changed_families.contains(family))
            })
            .map(|law| {
                serde_json::json!({
                    "lawId": json_field(law, "lawId"),
                    "lawFamily": json_field(law, "lawFamily"),
                    "requiredAxisRefs": array_field(law, "requiredAxisRefs"),
                    "matchedAtomFamilies": json_string_array(
                        array_items(law, "appliesToAtomFamilies")
                            .into_iter()
                            .filter_map(serde_json::Value::as_str)
                            .filter(|family| changed_families.contains(*family))
                    )
                })
            })
            .collect(),
    )
}

fn matched_policy_axis_refs(matched_laws: &serde_json::Value) -> BTreeSet<String> {
    matched_laws
        .as_array()
        .into_iter()
        .flat_map(|laws| laws.iter())
        .flat_map(|law| array_items(law, "requiredAxisRefs"))
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn source_targets_for_changed_refs(
    base_archmap: &serde_json::Value,
    delta_archmap: &serde_json::Value,
    changed_refs: &[String],
) -> serde_json::Value {
    let mut paths = BTreeSet::new();
    for target in array_items(
        delta_archmap
            .get("reviewIntent")
            .unwrap_or(&serde_json::Value::Null),
        "sourceFirstTargets",
    ) {
        if let Some(path) = target.as_str() {
            paths.insert(path.to_string());
        }
    }
    for changed_ref in changed_refs {
        if let Some((_kind, observation)) = find_archmap_observation(base_archmap, changed_ref) {
            for source_ref in array_items(observation, "sourceRefs") {
                if let Some(path) = source_ref.get("path").and_then(serde_json::Value::as_str) {
                    let target = if let Some(symbol) =
                        source_ref.get("symbol").and_then(serde_json::Value::as_str)
                    {
                        format!("{path}:{symbol}")
                    } else {
                        path.to_string()
                    };
                    paths.insert(target);
                }
            }
        }
    }
    json_string_array(paths.iter())
}

fn first_signature_distance(packet: &serde_json::Value) -> Option<&serde_json::Value> {
    packet
        .get("signatureDistanceReadings")
        .and_then(serde_json::Value::as_array)
        .and_then(|items| items.first())
}

fn signature_axis_value_map(packet: &serde_json::Value) -> BTreeMap<String, i64> {
    array_items(packet, "signatureAxes")
        .into_iter()
        .filter_map(|axis| {
            Some((
                axis.get("signatureAxisId")?.as_str()?.to_string(),
                axis.get("value").and_then(serde_json::Value::as_i64)?,
            ))
        })
        .collect()
}

fn signature_axis_object_map<'a>(
    packet: &'a serde_json::Value,
) -> BTreeMap<String, &'a serde_json::Value> {
    array_items(packet, "signatureAxes")
        .into_iter()
        .filter_map(|axis| Some((axis.get("signatureAxisId")?.as_str()?.to_string(), axis)))
        .collect()
}

fn observation_object_map<'a>(
    document: &'a serde_json::Value,
    collection_key: &str,
    id_key: &str,
) -> BTreeMap<String, &'a serde_json::Value> {
    array_items(document, collection_key)
        .into_iter()
        .filter_map(|observation| {
            Some((observation.get(id_key)?.as_str()?.to_string(), observation))
        })
        .collect()
}

fn json_string_array<I, S>(items: I) -> serde_json::Value
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut values: Vec<String> = items
        .into_iter()
        .map(|item| item.as_ref().to_string())
        .collect();
    values.sort();
    values.dedup();
    serde_json::Value::Array(values.into_iter().map(serde_json::Value::String).collect())
}

fn string_vec_from_value(value: &serde_json::Value, key: &str) -> Vec<String> {
    array_items(value, key)
        .into_iter()
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn string_vec_from_array_objects(value: &serde_json::Value, key: &str) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flat_map(|items| items.iter())
        .filter_map(|item| item.get(key))
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

pub(crate) fn string_array(value: &serde_json::Value, key: &str) -> Vec<String> {
    array_items(value, key)
        .into_iter()
        .filter_map(serde_json::Value::as_str)
        .map(str::to_string)
        .collect()
}

fn schema_string(document: &serde_json::Value) -> serde_json::Value {
    document
        .get("schemaVersion")
        .or_else(|| document.get("schema"))
        .cloned()
        .unwrap_or(serde_json::Value::Null)
}

fn json_string(document: &serde_json::Value, field: &str, fallback: &str) -> String {
    document
        .get(field)
        .and_then(|value| value.as_str())
        .unwrap_or(fallback)
        .to_string()
}
