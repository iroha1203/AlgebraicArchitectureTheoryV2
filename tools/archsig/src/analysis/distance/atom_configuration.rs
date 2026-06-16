fn build_viewer_distance_inputs(
    archmap: &ArchMapDocumentV0,
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
    generated_atom_shapes: &[ArchSigGeneratedAtomShapeV0],
) -> Vec<ArchSigViewerDistanceInputV0> {
    let atoms_by_ref = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let shapes_by_atom = generated_atom_shapes
        .iter()
        .map(|shape| (shape.atom_observation_ref.as_str(), shape))
        .collect::<BTreeMap<_, _>>();

    let mut inputs = Vec::new();
    for molecule in generated_molecules {
        for left_index in 0..molecule.atom_observation_refs.len() {
            for right_index in (left_index + 1)..molecule.atom_observation_refs.len() {
                let left_ref = &molecule.atom_observation_refs[left_index];
                let right_ref = &molecule.atom_observation_refs[right_index];
                let Some(left) = atoms_by_ref.get(left_ref.as_str()) else {
                    continue;
                };
                let Some(right) = atoms_by_ref.get(right_ref.as_str()) else {
                    continue;
                };
                let Some(left_shape) = shapes_by_atom.get(left_ref.as_str()) else {
                    continue;
                };
                let Some(right_shape) = shapes_by_atom.get(right_ref.as_str()) else {
                    continue;
                };
                let (distance_value, coordinate_components) =
                    atom_shape_distance_components(left, right);
                inputs.push(ArchSigViewerDistanceInputV0 {
                    distance_input_id: format!(
                        "viewer-distance:{}:{}:{}",
                        stable_id(&molecule.generated_molecule_id),
                        stable_id(left_ref),
                        stable_id(right_ref)
                    ),
                    distance_kind: "atom-shape-coordinate-mismatch-count".to_string(),
                    source_ref: left_ref.clone(),
                    target_ref: right_ref.clone(),
                    generated_molecule_ref: Some(molecule.generated_molecule_id.clone()),
                    atom_shape_refs: vec![
                        left_shape.atom_shape_id.clone(),
                        right_shape.atom_shape_id.clone(),
                    ],
                    distance_value: Some(distance_value),
                    coordinate_components,
                    evidence_boundary:
                        "viewer distance input is computed from AtomShape coordinates for layout and review; it is not semantic equivalence or theorem distance"
                            .to_string(),
                    non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
                });
            }
        }
    }
    inputs
}

fn build_atom_distance_readings(
    archmap: &ArchMapDocumentV0,
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
    viewer_distance_inputs: &[ArchSigViewerDistanceInputV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigAtomDistanceReadingV0> {
    let atoms_by_ref = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let semantic_by_atom = semantic_anchor_sets_by_atom(archmap);
    let molecule_refs_by_pair = molecule_refs_by_atom_pair(generated_molecules);
    let viewer_refs_by_pair = viewer_distance_refs_by_atom_pair(viewer_distance_inputs);
    let mut pair_refs = molecule_refs_by_pair.keys().cloned().collect::<Vec<_>>();
    pair_refs.sort();

    pair_refs
        .into_iter()
        .filter_map(|(left_ref, right_ref)| {
            let left = atoms_by_ref.get(left_ref.as_str())?;
            let right = atoms_by_ref.get(right_ref.as_str())?;
            let molecule_refs = molecule_refs_by_pair
                .get(&(left_ref.clone(), right_ref.clone()))
                .cloned()
                .unwrap_or_default();
            let viewer_distance_input_refs = viewer_refs_by_pair
                .get(&(left_ref.clone(), right_ref.clone()))
                .cloned()
                .unwrap_or_default();
            let coverage_refs = foundation.profile.coverage_policy_refs.clone();
            let fiber_distance = atom_fiber_distance_value(left, right, &coverage_refs);
            let carrier_distance = atom_carrier_distance_value(left, right, &coverage_refs);
            let valence_distance = atom_valence_distance_value(left, right, &coverage_refs);
            let semantic_anchor_distance = atom_semantic_anchor_distance_value(
                left,
                right,
                semantic_by_atom.get(left_ref.as_str()),
                semantic_by_atom.get(right_ref.as_str()),
                &coverage_refs,
            );
            let component_distances = vec![
                atom_distance_component(
                    "fiber",
                    weighted_atom_component_weight("atom.fiber", 250, foundation),
                    fiber_distance.clone(),
                ),
                atom_distance_component(
                    "carrier",
                    weighted_atom_component_weight("atom.carrier", 350, foundation),
                    carrier_distance.clone(),
                ),
                atom_distance_component(
                    "valence",
                    weighted_atom_component_weight("atom.valence", 250, foundation),
                    valence_distance.clone(),
                ),
                atom_distance_component(
                    "semanticAnchor",
                    weighted_atom_component_weight("atom.semanticAnchor", 150, foundation),
                    semantic_anchor_distance.clone(),
                ),
            ];
            let atom_layout_distance_bundle =
                atom_layout_distance_bundle_value(&component_distances, &coverage_refs);
            let high_distance_reasons =
                atom_high_distance_reasons(&component_distances, &atom_layout_distance_bundle);
            Some(ArchSigAtomDistanceReadingV0 {
                atom_distance_reading_id: format!(
                    "atom-distance:{}:{}",
                    stable_id(left_ref.as_str()),
                    stable_id(right_ref.as_str())
                ),
                source_atom_ref: left_ref,
                target_atom_ref: right_ref,
                molecule_refs,
                distance_profile_ref: foundation.profile.profile_id.clone(),
                diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
                fiber_distance,
                carrier_distance,
                valence_distance,
                semantic_anchor_distance,
                atom_layout_distance_bundle,
                component_distances,
                high_distance_reasons,
                viewer_distance_input_refs,
                evidence_boundary:
                    "Atom diagnostic distance is computed from ArchMap atom, carrier, valence, and semantic evidence; viewer layout distance refs remain separate evidence and are not the diagnostic value"
                        .to_string(),
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            })
        })
        .collect()
}

fn promote_atom_geometry_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigAtomDistanceReadingV0],
) {
    let measured_readings = readings
        .iter()
        .filter(|reading| {
            matches!(
                reading.atom_layout_distance_bundle.status.as_str(),
                "measured" | "zero"
            )
        })
        .collect::<Vec<_>>();
    if measured_readings.is_empty() {
        return;
    }
    let max_distance = measured_readings
        .iter()
        .filter_map(|reading| reading.atom_layout_distance_bundle.measured_value)
        .max()
        .unwrap_or(0);
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "atomGeometry")
    {
        let blocker_refs = readings
            .iter()
            .flat_map(|reading| reading.semantic_anchor_distance.blocker_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let fully_measured = blocker_refs.is_empty();
        distance.value = ArchSigDistanceValueV0 {
            status: if fully_measured {
                if max_distance == 0 { "zero" } else { "measured" }
            } else {
                "blocked"
            }
            .to_string(),
            measured_value: fully_measured.then_some(max_distance),
            unit: "milli-distance".to_string(),
            provenance_refs: vec![
                "aat-theory:distance-extension-design"
                    .to_string(),
                "atomDistanceReadings".to_string(),
            ],
            evaluator_basis_refs: measured_readings
                .iter()
                .map(|reading| reading.atom_distance_reading_id.clone())
                .collect(),
            coverage_refs: foundation.profile.coverage_policy_refs.clone(),
            blocker_refs,
            reading:
                "Atom geometry distance rows are computed from fiber, carrier, valence, and semantic-anchor evaluators; family-level status remains blocked while selected semantic anchors are missing"
                    .to_string(),
        };
        distance.evidence_boundary =
            "atomGeometry is measured only through atomDistanceReadings; viewerDistanceInputs stay visualization evidence, not diagnostic distance"
                .to_string();
    }
    foundation.status_summary.measured_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "measured")
        .count();
    foundation.status_summary.zero_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "zero")
        .count();
    foundation.status_summary.unmeasured_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "unmeasured")
        .count();
    foundation.status_summary.unavailable_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "unavailable")
        .count();
    foundation.status_summary.incomparable_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "incomparable")
        .count();
    foundation.status_summary.infinite_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "infinite")
        .count();
    foundation.status_summary.blocked_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "blocked")
        .count();
    foundation.status_summary.schema_foundation_only_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "schemaFoundationOnly")
        .count();
}

fn build_configuration_distance_readings(
    archmap: &ArchMapDocumentV0,
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigConfigurationDistanceReadingV0> {
    let atoms_by_ref = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let atom_refs = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_observation_id.clone())
        .collect::<Vec<_>>();
    let context_refs_by_atom = molecule_context_refs_by_atom(generated_molecules);
    let molecule_refs_by_pair = molecule_refs_by_atom_pair(generated_molecules);
    let hypergraph_ref = configuration_hypergraph_ref(&archmap.map_id);
    let typed_hyperedges =
        build_configuration_hyperedges(archmap, generated_molecules, &hypergraph_ref);
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    let observation_gap_blockers = configuration_observation_gap_blockers(archmap);
    let pair_refs = selected_configuration_distance_pair_refs(&atom_refs, &molecule_refs_by_pair);

    let mut readings = Vec::new();
    for (left_ref, right_ref) in pair_refs {
        let Some(left) = atoms_by_ref.get(left_ref.as_str()) else {
            continue;
        };
        let Some(right) = atoms_by_ref.get(right_ref.as_str()) else {
            continue;
        };
        let molecule_refs = molecule_refs_by_pair
            .get(&(left_ref.clone(), right_ref.clone()))
            .cloned()
            .unwrap_or_default();
        let configuration_ref = molecule_refs
            .first()
            .map(|molecule_ref| format!("configuration:{molecule_ref}"))
            .unwrap_or_else(|| "configuration:observed-atom-hypergraph".to_string());
        let path = shortest_configuration_path(&typed_hyperedges, &left_ref, &right_ref);
        let (configuration_indexed_distance, shortest_path_atom_refs, shortest_path_hyperedge_refs) =
            match path {
                Some((path_atom_refs, path_hyperedge_refs)) => {
                    let provenance_refs = configuration_pair_provenance_refs(
                        left,
                        right,
                        &typed_hyperedges,
                        &path_hyperedge_refs,
                    );
                    let evaluator_basis_refs = path_atom_refs
                        .iter()
                        .map(|atom_ref| format!("shortestPath:atom:{}", stable_id(atom_ref)))
                        .chain(
                            path_hyperedge_refs
                                .iter()
                                .map(|hyperedge_ref| format!("hyperedge:{hyperedge_ref}")),
                        )
                        .collect::<Vec<_>>();
                    (
                        measured_part4_distance_value(
                            path_hyperedge_refs.len() as i64,
                            "configuration-hop",
                            provenance_refs,
                            evaluator_basis_refs,
                            &coverage_refs,
                            "configuration-indexed distance is the shortest path length in the typed ArchMap configuration hypergraph",
                        ),
                        path_atom_refs,
                        path_hyperedge_refs,
                    )
                }
                None => (
                    infinite_part4_distance_value(
                        "configuration-hop",
                        atom_pair_provenance_refs(left, right),
                        vec![format!(
                            "unreachablePair:{}:{}",
                            stable_id(&left_ref),
                            stable_id(&right_ref)
                        )],
                        &coverage_refs,
                        "configuration-indexed distance is infinite because no typed hypergraph path connects the selected atoms",
                    ),
                    Vec::new(),
                    Vec::new(),
                ),
            };
        let context_distance = configuration_context_distance_value(
            left,
            right,
            context_refs_by_atom.get(left_ref.as_str()),
            context_refs_by_atom.get(right_ref.as_str()),
            &coverage_refs,
        );
        let small_molecule_weight_milli =
            small_molecule_weight_milli(generated_molecules, &molecule_refs);
        let unreachable_pair_refs = if configuration_indexed_distance.status == "infinite" {
            vec![format!("{left_ref}<->{right_ref}")]
        } else {
            Vec::new()
        };
        let configuration_distance_bundle = configuration_distance_bundle_value(
            &configuration_indexed_distance,
            &context_distance,
            small_molecule_weight_milli,
            &observation_gap_blockers,
            &coverage_refs,
        );
        let reading_hyperedges = configuration_reading_hyperedges(
            &typed_hyperedges,
            &left_ref,
            &right_ref,
            &shortest_path_hyperedge_refs,
        );
        readings.push(ArchSigConfigurationDistanceReadingV0 {
            configuration_distance_reading_id: format!(
                "configuration-distance:{}:{}",
                stable_id(&left_ref),
                stable_id(&right_ref)
            ),
            source_atom_ref: left_ref,
            target_atom_ref: right_ref,
            configuration_ref,
            molecule_refs,
            distance_profile_ref: foundation.profile.profile_id.clone(),
            diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
            hypergraph_ref: hypergraph_ref.clone(),
            typed_hyperedges: reading_hyperedges,
            shortest_path_atom_refs,
            shortest_path_hyperedge_refs,
            configuration_indexed_distance,
            context_distance,
            small_molecule_weight_milli,
            high_context_overlap: small_molecule_weight_milli > 0,
            unreachable_pair_refs,
            configuration_distance_bundle,
            evidence_boundary:
                "Configuration distance is computed for molecule-local pairs plus bounded cross-context diagnostic pairs from typed ArchMap hyperedges and molecule context; observation gaps block aggregation and are not measured zero"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        });
    }
    readings
}

fn promote_configuration_geometry_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigConfigurationDistanceReadingV0],
) {
    if readings.is_empty() {
        return;
    }
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "configurationGeometry")
    {
        let blocker_refs = readings
            .iter()
            .flat_map(|reading| {
                reading
                    .configuration_distance_bundle
                    .blocker_refs
                    .iter()
                    .cloned()
                    .chain(
                        reading
                            .configuration_indexed_distance
                            .blocker_refs
                            .iter()
                            .cloned(),
                    )
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let max_bundle_distance = readings
            .iter()
            .filter_map(|reading| reading.configuration_distance_bundle.measured_value)
            .max()
            .or_else(|| {
                readings
                    .iter()
                    .filter_map(|reading| reading.configuration_indexed_distance.measured_value)
                    .max()
            })
            .unwrap_or(0);
        let fully_measured = blocker_refs.is_empty();
        distance.value = ArchSigDistanceValueV0 {
            status: if fully_measured {
                if max_bundle_distance == 0 {
                    "zero"
                } else {
                    "measured"
                }
            } else {
                "blocked"
            }
            .to_string(),
            measured_value: fully_measured.then_some(max_bundle_distance),
            unit: "configuration-distance".to_string(),
            provenance_refs: vec![
                "aat-theory:distance-extension-design"
                    .to_string(),
                "configurationDistanceReadings".to_string(),
            ],
            evaluator_basis_refs: readings
                .iter()
                .map(|reading| reading.configuration_distance_reading_id.clone())
                .collect(),
            coverage_refs: foundation.profile.coverage_policy_refs.clone(),
            blocker_refs,
            reading:
                "Configuration geometry distance rows are computed from typed hypergraph shortest paths and molecule context; family-level status remains blocked while observation gaps could hide configuration edges"
                    .to_string(),
        };
        distance.evidence_boundary =
            "configurationGeometry is measured only through configurationDistanceReadings; missing relation and observation gaps are blockers, not zero distances"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}

fn refresh_part4_status_summary(foundation: &mut ArchSigPart4DistanceFoundationV0) {
    foundation.status_summary.measured_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "measured")
        .count();
    foundation.status_summary.zero_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "zero")
        .count();
    foundation.status_summary.unmeasured_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "unmeasured")
        .count();
    foundation.status_summary.unavailable_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "unavailable")
        .count();
    foundation.status_summary.incomparable_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "incomparable")
        .count();
    foundation.status_summary.infinite_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "infinite")
        .count();
    foundation.status_summary.blocked_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "blocked")
        .count();
    foundation.status_summary.schema_foundation_only_count = foundation
        .supporting_distances
        .iter()
        .filter(|distance| distance.value.status == "schemaFoundationOnly")
        .count();
}

fn sync_part4_diagnostic_scope(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    signature_distance_readings: &[ArchSigSignatureDistanceReadingV0],
    operation_distance_readings: &[ArchSigOperationDistanceReadingV0],
    curvature_mass_readings: &[ArchSigCurvatureMassReadingV0],
) {
    let signature_axis_aliases = part4_signature_axis_aliases(signature_distance_readings);
    let measured_axis_refs = signature_distance_readings
        .iter()
        .flat_map(|reading| reading.measured_axis_refs.iter().cloned())
        .collect::<BTreeSet<_>>();
    let measured_axis_aliases = measured_axis_refs
        .iter()
        .flat_map(|axis| part4_canonical_axis_refs(axis, &signature_axis_aliases))
        .collect::<BTreeSet<_>>();
    let unmeasured_axis_refs = signature_distance_readings
        .iter()
        .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned())
        .chain(
            signature_distance_readings
                .iter()
                .flat_map(|reading| reading.incomparable_axis_refs.iter().cloned()),
        )
        .chain(
            operation_distance_readings
                .iter()
                .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned()),
        )
        .chain(
            curvature_mass_readings
                .iter()
                .flat_map(|reading| reading.unmeasured_axis_refs.iter().cloned()),
        )
        .filter(|axis| {
            part4_canonical_axis_refs(axis, &signature_axis_aliases)
                .into_iter()
                .all(|canonical| !measured_axis_aliases.contains(&canonical))
        })
        .collect::<BTreeSet<_>>();
    let blocker_refs = signature_distance_readings
        .iter()
        .flat_map(|reading| reading.total_measured_distance.blocker_refs.iter().cloned())
        .chain(
            signature_distance_readings
                .iter()
                .flat_map(|reading| reading.safe_region_margin.blocker_refs.iter().cloned()),
        )
        .chain(
            signature_distance_readings
                .iter()
                .flat_map(|reading| reading.path_drift.blocker_refs.iter().cloned()),
        )
        .chain(
            operation_distance_readings
                .iter()
                .flat_map(|reading| reading.side_effect_bound.blocker_refs.iter().cloned()),
        )
        .chain(
            curvature_mass_readings
                .iter()
                .flat_map(|reading| reading.curvature_mass.blocker_refs.iter().cloned()),
        )
        .filter(|blocker| {
            blocker.strip_prefix("unmeasuredAxis:").is_none_or(|axis| {
                part4_canonical_axis_refs(axis, &signature_axis_aliases)
                    .into_iter()
                    .all(|canonical| !measured_axis_aliases.contains(&canonical))
            })
        })
        .collect::<BTreeSet<_>>();

    foundation.diagnostic_scope.measured_axis_refs = measured_axis_refs.into_iter().collect();
    foundation.diagnostic_scope.unmeasured_axis_refs = unmeasured_axis_refs.into_iter().collect();
    foundation.diagnostic_scope.blocker_refs = blocker_refs.into_iter().collect();
    foundation.diagnostic_scope.evidence_boundary =
        "Diagnostic scope is synchronized from Part IV evaluator readings; measured or zero signature-distance axes are removed from unmeasuredAxisRefs, while operation and curvature partial measurements can keep evidence blockers rather than becoming measured zero"
            .to_string();
}

fn part4_signature_axis_aliases(
    signature_distance_readings: &[ArchSigSignatureDistanceReadingV0],
) -> BTreeMap<String, BTreeSet<String>> {
    let mut aliases = BTreeMap::<String, BTreeSet<String>>::new();
    for axis in signature_distance_readings
        .iter()
        .flat_map(|reading| reading.axis_distances.iter())
    {
        let refs = BTreeSet::from([
            axis.signature_axis_ref.clone(),
            axis.axis_ref.clone(),
            axis.law_ref.clone(),
        ]);
        for axis_ref in &refs {
            aliases
                .entry(axis_ref.clone())
                .or_default()
                .extend(refs.iter().cloned());
        }
    }
    aliases
}

fn part4_canonical_axis_refs(
    axis_ref: &str,
    aliases: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    aliases.get(axis_ref).cloned().unwrap_or_else(|| {
        let mut refs = BTreeSet::new();
        refs.insert(axis_ref.to_string());
        refs
    })
}

fn atom_fiber_distance_value(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let left_axis = atom_shape_axis(left);
    let right_axis = atom_shape_axis(right);
    let components = [
        (
            "atomFamily",
            left.atom_family.as_str(),
            right.atom_family.as_str(),
        ),
        ("axis", left_axis.as_str(), right_axis.as_str()),
        (
            "predicate",
            left.predicate.as_str(),
            right.predicate.as_str(),
        ),
        (
            "observationStatus",
            left.observation_status.as_str(),
            right.observation_status.as_str(),
        ),
        (
            "confidence",
            left.confidence.as_str(),
            right.confidence.as_str(),
        ),
    ];
    let mismatch_count = components
        .iter()
        .filter(|(_, left_value, right_value)| left_value != right_value)
        .count() as i64;
    let value = mismatch_count * 1000 / components.len() as i64;
    let evaluator_basis_refs = components
        .iter()
        .map(|(field, left_value, right_value)| {
            format!(
                "fiber:{field}:left={}:right={}",
                stable_id(left_value),
                stable_id(right_value)
            )
        })
        .collect::<Vec<_>>();
    measured_part4_distance_value(
        value,
        "milli-distance",
        atom_pair_provenance_refs(left, right),
        evaluator_basis_refs,
        coverage_refs,
        "fiber distance compares atom family, derived axis, predicate, observation status, and confidence payload fields",
    )
}

fn atom_carrier_distance_value(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let left_carrier = atom_carrier_set(left);
    let right_carrier = atom_carrier_set(right);
    let value = milli_jaccard_distance(&left_carrier, &right_carrier).unwrap_or(1000);
    measured_part4_distance_value(
        value,
        "milli-distance",
        atom_pair_provenance_refs(left, right),
        vec![
            format!("carrier:left={}", refs_join(&left_carrier)),
            format!("carrier:right={}", refs_join(&right_carrier)),
        ],
        coverage_refs,
        "carrier distance is weighted-set distance over subject, object, and source-backed carrier refs",
    )
}

fn atom_valence_distance_value(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let left_valence = atom_valence_set(left);
    let right_valence = atom_valence_set(right);
    let value = milli_jaccard_distance(&left_valence, &right_valence).unwrap_or(1000);
    measured_part4_distance_value(
        value,
        "milli-distance",
        atom_pair_provenance_refs(left, right),
        vec![
            format!("valence:left={}", refs_join(&left_valence)),
            format!("valence:right={}", refs_join(&right_valence)),
        ],
        coverage_refs,
        "valence distance compares architectural affordance sets derived from atom family and relation roles",
    )
}

fn atom_semantic_anchor_distance_value(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    left_semantic: Option<&BTreeSet<String>>,
    right_semantic: Option<&BTreeSet<String>>,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let Some(left_semantic) = left_semantic else {
        return unmeasured_part4_distance_value(
            "milli-distance",
            atom_pair_provenance_refs(left, right),
            vec![format!(
                "missing semantic anchor evidence for {}",
                left.atom_observation_id
            )],
            coverage_refs,
            "semantic anchor distance is unmeasured until both atoms have semantic observation support",
        );
    };
    let Some(right_semantic) = right_semantic else {
        return unmeasured_part4_distance_value(
            "milli-distance",
            atom_pair_provenance_refs(left, right),
            vec![format!(
                "missing semantic anchor evidence for {}",
                right.atom_observation_id
            )],
            coverage_refs,
            "semantic anchor distance is unmeasured until both atoms have semantic observation support",
        );
    };
    let value = milli_jaccard_distance(left_semantic, right_semantic).unwrap_or(1000);
    measured_part4_distance_value(
        value,
        "milli-distance",
        atom_pair_provenance_refs(left, right),
        vec![
            format!("semantic:left={}", refs_join(left_semantic)),
            format!("semantic:right={}", refs_join(right_semantic)),
        ],
        coverage_refs,
        "semantic anchor distance compares supplied ArchMap semantic observation closures and does not infer ontology distance from names",
    )
}

fn atom_layout_distance_bundle_value(
    components: &[ArchSigAtomDistanceComponentV0],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let blockers = components
        .iter()
        .flat_map(|component| component.value.blocker_refs.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if !blockers.is_empty() {
        return ArchSigDistanceValueV0 {
            status: "blocked".to_string(),
            measured_value: None,
            unit: "milli-distance".to_string(),
            provenance_refs: components
                .iter()
                .flat_map(|component| component.value.provenance_refs.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            evaluator_basis_refs: components
                .iter()
                .flat_map(|component| component.evaluator_basis_refs.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: blockers,
            reading:
                "atom layout distance bundle is blocked until all selected component distances are measured; blocked components are not zero"
                    .to_string(),
        };
    }
    let mut weighted_sum = 0;
    let mut total_weight = 0;
    for component in components {
        if let Some(value) = component.value.measured_value {
            weighted_sum += value * component.weight;
            total_weight += component.weight;
        }
    }
    let value = if total_weight == 0 {
        0
    } else {
        weighted_sum / total_weight
    };
    measured_part4_distance_value(
        value,
        "milli-distance",
        components
            .iter()
            .flat_map(|component| component.value.provenance_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        components
            .iter()
            .flat_map(|component| component.evaluator_basis_refs.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        coverage_refs,
        "atom layout distance bundle is the selected weighted aggregate of measured fiber, carrier, valence, and semantic-anchor components",
    )
}

fn measured_part4_distance_value(
    value: i64,
    unit: &str,
    provenance_refs: Vec<String>,
    evaluator_basis_refs: Vec<String>,
    coverage_refs: &[String],
    reading: &str,
) -> ArchSigDistanceValueV0 {
    ArchSigDistanceValueV0 {
        status: if value == 0 { "zero" } else { "measured" }.to_string(),
        measured_value: Some(value),
        unit: unit.to_string(),
        provenance_refs,
        evaluator_basis_refs,
        coverage_refs: coverage_refs.to_vec(),
        blocker_refs: Vec::new(),
        reading: reading.to_string(),
    }
}

fn unmeasured_part4_distance_value(
    unit: &str,
    provenance_refs: Vec<String>,
    blocker_refs: Vec<String>,
    coverage_refs: &[String],
    reading: &str,
) -> ArchSigDistanceValueV0 {
    ArchSigDistanceValueV0 {
        status: "unmeasured".to_string(),
        measured_value: None,
        unit: unit.to_string(),
        provenance_refs,
        evaluator_basis_refs: Vec::new(),
        coverage_refs: coverage_refs.to_vec(),
        blocker_refs,
        reading: reading.to_string(),
    }
}

fn infinite_part4_distance_value(
    unit: &str,
    provenance_refs: Vec<String>,
    blocker_refs: Vec<String>,
    coverage_refs: &[String],
    reading: &str,
) -> ArchSigDistanceValueV0 {
    ArchSigDistanceValueV0 {
        status: "infinite".to_string(),
        measured_value: None,
        unit: unit.to_string(),
        provenance_refs,
        evaluator_basis_refs: Vec::new(),
        coverage_refs: coverage_refs.to_vec(),
        blocker_refs,
        reading: reading.to_string(),
    }
}

fn configuration_hypergraph_ref(configuration_ref: &str) -> String {
    format!("configuration-hypergraph:{}", stable_id(configuration_ref))
}

fn build_configuration_hyperedges(
    archmap: &ArchMapDocumentV0,
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
    hypergraph_ref: &str,
) -> Vec<ArchSigConfigurationHyperedgeV0> {
    let atoms_by_ref = archmap
        .atom_observations
        .iter()
        .map(|atom| (atom.atom_observation_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let atom_scope = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.atom_observation_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut hyperedges = BTreeMap::<String, ArchSigConfigurationHyperedgeV0>::new();

    for molecule in generated_molecules {
        push_configuration_hyperedge(
            &mut hyperedges,
            hypergraph_ref,
            "moleculeMembership",
            molecule.atom_observation_refs.clone(),
            vec![molecule.source_molecule_observation_ref.clone()],
        );
    }

    push_grouped_configuration_edges(
        &mut hyperedges,
        hypergraph_ref,
        "sameSubject",
        archmap.atom_observations.iter().fold(
            BTreeMap::<String, Vec<String>>::new(),
            |mut groups, atom| {
                groups
                    .entry(atom.subject_ref.clone())
                    .or_default()
                    .push(atom.atom_observation_id.clone());
                groups
            },
        ),
    );
    let mut object_groups = BTreeMap::<String, Vec<String>>::new();
    for atom in &archmap.atom_observations {
        for object_ref in &atom.object_refs {
            object_groups
                .entry(object_ref.clone())
                .or_default()
                .push(atom.atom_observation_id.clone());
        }
    }
    push_grouped_configuration_edges(
        &mut hyperedges,
        hypergraph_ref,
        "sharedObjectRef",
        object_groups,
    );

    for atom in &archmap.atom_observations {
        let family = atom.atom_family.to_ascii_lowercase();
        let predicate = atom.predicate.to_ascii_lowercase();
        if family.contains("relation")
            || predicate.contains("delegates")
            || predicate.contains("calls")
            || predicate.contains("depends")
        {
            let endpoint_atoms = endpoint_atoms_for(atom, &archmap.atom_observations);
            push_configuration_hyperedge(
                &mut hyperedges,
                hypergraph_ref,
                "relationEndpoint",
                endpoint_atoms,
                atom.source_refs.iter().map(source_ref_label).collect(),
            );
        }
        if family.contains("contract") || predicate.contains("contract") {
            push_configuration_hyperedge(
                &mut hyperedges,
                hypergraph_ref,
                "contractAttachment",
                endpoint_atoms_for(atom, &archmap.atom_observations),
                atom.source_refs.iter().map(source_ref_label).collect(),
            );
        }
        if family.contains("effect") || predicate.contains("effect") {
            push_configuration_hyperedge(
                &mut hyperedges,
                hypergraph_ref,
                "effectSurface",
                endpoint_atoms_for(atom, &archmap.atom_observations),
                atom.source_refs.iter().map(source_ref_label).collect(),
            );
        }
        if family.contains("authority")
            || family.contains("boundary")
            || predicate.contains("authority")
            || predicate.contains("boundary")
        {
            push_configuration_hyperedge(
                &mut hyperedges,
                hypergraph_ref,
                "boundaryAuthoritySurface",
                endpoint_atoms_for(atom, &archmap.atom_observations),
                atom.source_refs.iter().map(source_ref_label).collect(),
            );
        }
    }

    for semantic in &archmap.semantic_observations {
        let scoped_atoms = semantic
            .atom_observation_refs
            .iter()
            .filter(|atom_ref| atom_scope.contains(atom_ref.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        push_configuration_hyperedge(
            &mut hyperedges,
            hypergraph_ref,
            "semanticInterpretation",
            scoped_atoms,
            vec![semantic.semantic_observation_id.clone()]
                .into_iter()
                .chain(semantic.source_refs.iter().map(source_ref_label))
                .collect(),
        );
    }
    for evidence in &archmap.operation_square_evidence {
        let scoped_atoms = evidence
            .atom_observation_refs
            .iter()
            .filter(|atom_ref| atom_scope.contains(atom_ref.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        push_configuration_hyperedge(
            &mut hyperedges,
            hypergraph_ref,
            "operationSquare",
            scoped_atoms,
            vec![evidence.operation_square_evidence_id.clone()]
                .into_iter()
                .chain(evidence.source_refs.iter().map(source_ref_label))
                .collect(),
        );
    }
    for concern in &archmap.concern_hints {
        let scoped_atoms = concern
            .atom_observation_refs
            .iter()
            .filter(|atom_ref| atom_scope.contains(atom_ref.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        push_configuration_hyperedge(
            &mut hyperedges,
            hypergraph_ref,
            "sharedConcernSurface",
            scoped_atoms,
            vec![concern.concern_hint_id.clone()]
                .into_iter()
                .chain(concern.source_refs.iter().map(source_ref_label))
                .collect(),
        );
    }

    let mut source_groups = BTreeMap::<String, Vec<String>>::new();
    for atom in &archmap.atom_observations {
        for source_ref in &atom.source_refs {
            source_groups
                .entry(source_ref_label(source_ref))
                .or_default()
                .push(atom.atom_observation_id.clone());
        }
    }
    push_grouped_configuration_edges(
        &mut hyperedges,
        hypergraph_ref,
        "sourceBackedCoObservation",
        source_groups,
    );

    hyperedges
        .into_values()
        .filter(|edge| {
            edge.atom_refs
                .iter()
                .all(|atom_ref| atoms_by_ref.contains_key(atom_ref.as_str()))
        })
        .collect()
}

fn push_grouped_configuration_edges(
    hyperedges: &mut BTreeMap<String, ArchSigConfigurationHyperedgeV0>,
    hypergraph_ref: &str,
    kind: &str,
    groups: BTreeMap<String, Vec<String>>,
) {
    for (group_ref, atom_refs) in groups {
        push_configuration_hyperedge(
            hyperedges,
            hypergraph_ref,
            kind,
            atom_refs,
            vec![format!("{kind}:{group_ref}")],
        );
    }
}

fn push_configuration_hyperedge(
    hyperedges: &mut BTreeMap<String, ArchSigConfigurationHyperedgeV0>,
    hypergraph_ref: &str,
    kind: &str,
    atom_refs: Vec<String>,
    source_refs: Vec<String>,
) {
    let atom_refs = unique_strings(atom_refs.into_iter());
    if atom_refs.len() < 2 {
        return;
    }
    let source_refs = unique_strings(source_refs.into_iter());
    let hyperedge_id = format!(
        "{hypergraph_ref}:hyperedge:{kind}:{}",
        stable_id(&atom_refs.join("|"))
    );
    hyperedges.entry(hyperedge_id.clone()).or_insert_with(|| {
        ArchSigConfigurationHyperedgeV0 {
            hyperedge_id,
            hyperedge_kind: kind.to_string(),
            atom_refs,
            source_refs,
            evidence_boundary:
                "typed configuration hyperedge is extracted from explicit ArchMap observation refs; absent relations are not synthesized"
                    .to_string(),
        }
    });
}

fn endpoint_atoms_for(
    seed: &ArchMapAtomObservationV0,
    atoms: &[ArchMapAtomObservationV0],
) -> Vec<String> {
    let endpoint_refs = seed
        .object_refs
        .iter()
        .chain(std::iter::once(&seed.subject_ref))
        .cloned()
        .collect::<BTreeSet<_>>();
    atoms
        .iter()
        .filter(|candidate| {
            candidate.atom_observation_id == seed.atom_observation_id
                || endpoint_refs.contains(&candidate.subject_ref)
                || candidate
                    .object_refs
                    .iter()
                    .any(|object_ref| endpoint_refs.contains(object_ref))
        })
        .map(|candidate| candidate.atom_observation_id.clone())
        .collect()
}

fn shortest_configuration_path(
    hyperedges: &[ArchSigConfigurationHyperedgeV0],
    source_ref: &str,
    target_ref: &str,
) -> Option<(Vec<String>, Vec<String>)> {
    let mut adjacency = BTreeMap::<String, Vec<(String, String)>>::new();
    for edge in hyperedges {
        for atom_ref in &edge.atom_refs {
            for neighbor_ref in &edge.atom_refs {
                if atom_ref != neighbor_ref {
                    adjacency
                        .entry(atom_ref.clone())
                        .or_default()
                        .push((neighbor_ref.clone(), edge.hyperedge_id.clone()));
                }
            }
        }
    }
    let mut queue = VecDeque::from([source_ref.to_string()]);
    let mut previous = BTreeMap::<String, (String, String)>::new();
    let mut seen = BTreeSet::from([source_ref.to_string()]);
    while let Some(current) = queue.pop_front() {
        if current == target_ref {
            break;
        }
        for (neighbor, hyperedge_ref) in adjacency.get(&current).cloned().unwrap_or_default() {
            if seen.insert(neighbor.clone()) {
                previous.insert(neighbor.clone(), (current.clone(), hyperedge_ref));
                queue.push_back(neighbor);
            }
        }
    }
    if !seen.contains(target_ref) {
        return None;
    }
    let mut atoms = vec![target_ref.to_string()];
    let mut edges = Vec::new();
    let mut cursor = target_ref.to_string();
    while cursor != source_ref {
        let (prior, edge_ref) = previous.get(&cursor)?.clone();
        edges.push(edge_ref);
        atoms.push(prior.clone());
        cursor = prior;
    }
    atoms.reverse();
    edges.reverse();
    Some((atoms, edges))
}

fn configuration_pair_provenance_refs(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    hyperedges: &[ArchSigConfigurationHyperedgeV0],
    path_hyperedge_refs: &[String],
) -> Vec<String> {
    let path_hyperedge_set = path_hyperedge_refs.iter().collect::<BTreeSet<_>>();
    unique_strings(
        atom_pair_provenance_refs(left, right)
            .into_iter()
            .chain(std::iter::once(
                "aat-theory:distance-extension-design"
                    .to_string(),
            ))
            .chain(
                hyperedges
                    .iter()
                    .filter(|edge| path_hyperedge_set.contains(&edge.hyperedge_id))
                    .flat_map(|edge| {
                        std::iter::once(edge.hyperedge_id.clone())
                            .chain(edge.source_refs.iter().cloned())
                    }),
            ),
    )
}

fn configuration_reading_hyperedges(
    hyperedges: &[ArchSigConfigurationHyperedgeV0],
    source_ref: &str,
    target_ref: &str,
    path_hyperedge_refs: &[String],
) -> Vec<ArchSigConfigurationHyperedgeV0> {
    let path_hyperedge_refs = path_hyperedge_refs.iter().collect::<BTreeSet<_>>();
    let mut selected = hyperedges
        .iter()
        .filter(|edge| path_hyperedge_refs.contains(&edge.hyperedge_id))
        .cloned()
        .collect::<Vec<_>>();
    if selected.is_empty() {
        selected = hyperedges
            .iter()
            .filter(|edge| {
                edge.atom_refs
                    .iter()
                    .any(|atom_ref| atom_ref == source_ref || atom_ref == target_ref)
            })
            .take(16)
            .cloned()
            .collect();
    }
    selected
}

fn molecule_context_refs_by_atom(
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
) -> BTreeMap<String, BTreeSet<String>> {
    let mut refs = BTreeMap::<String, BTreeSet<String>>::new();
    for molecule in generated_molecules {
        for atom_ref in &molecule.atom_observation_refs {
            refs.entry(atom_ref.clone())
                .or_default()
                .insert(molecule.generated_molecule_id.clone());
        }
    }
    refs
}

fn configuration_context_distance_value(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
    left_context: Option<&BTreeSet<String>>,
    right_context: Option<&BTreeSet<String>>,
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let Some(left_context) = left_context else {
        return unmeasured_part4_distance_value(
            "milli-distance",
            atom_pair_provenance_refs(left, right),
            vec![format!(
                "missing molecule context for {}",
                left.atom_observation_id
            )],
            coverage_refs,
            "context distance is unmeasured until both atoms have molecule membership context",
        );
    };
    let Some(right_context) = right_context else {
        return unmeasured_part4_distance_value(
            "milli-distance",
            atom_pair_provenance_refs(left, right),
            vec![format!(
                "missing molecule context for {}",
                right.atom_observation_id
            )],
            coverage_refs,
            "context distance is unmeasured until both atoms have molecule membership context",
        );
    };
    let value = milli_jaccard_distance(left_context, right_context).unwrap_or(1000);
    measured_part4_distance_value(
        value,
        "milli-distance",
        atom_pair_provenance_refs(left, right),
        vec![
            format!("context:left={}", refs_join(left_context)),
            format!("context:right={}", refs_join(right_context)),
        ],
        coverage_refs,
        "context distance is one minus Jaccard overlap of observed molecule memberships",
    )
}

fn small_molecule_weight_milli(
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
    molecule_refs: &[String],
) -> i64 {
    let shared = molecule_refs.iter().collect::<BTreeSet<_>>();
    generated_molecules
        .iter()
        .filter(|molecule| shared.contains(&molecule.generated_molecule_id))
        .map(|molecule| {
            let size = molecule.atom_observation_refs.len().max(1) as i64;
            1000 / size
        })
        .sum()
}

fn configuration_observation_gap_blockers(archmap: &ArchMapDocumentV0) -> Vec<String> {
    archmap
        .observation_gaps
        .iter()
        .map(|gap| format!("observationGap:{}:{}", gap.gap_id, stable_id(&gap.reason)))
        .collect()
}

fn configuration_distance_bundle_value(
    configuration_indexed_distance: &ArchSigDistanceValueV0,
    context_distance: &ArchSigDistanceValueV0,
    small_molecule_weight_milli: i64,
    observation_gap_blockers: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let blockers = configuration_indexed_distance
        .blocker_refs
        .iter()
        .cloned()
        .chain(context_distance.blocker_refs.iter().cloned())
        .chain(observation_gap_blockers.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let provenance_refs = unique_strings(
        configuration_indexed_distance
            .provenance_refs
            .iter()
            .cloned()
            .chain(context_distance.provenance_refs.iter().cloned()),
    );
    let evaluator_basis_refs = unique_strings(
        configuration_indexed_distance
            .evaluator_basis_refs
            .iter()
            .cloned()
            .chain(context_distance.evaluator_basis_refs.iter().cloned())
            .chain(std::iter::once(format!(
                "smallMoleculeWeightMilli:{small_molecule_weight_milli}"
            ))),
    );
    if !blockers.is_empty() {
        return ArchSigDistanceValueV0 {
            status: "blocked".to_string(),
            measured_value: None,
            unit: "configuration-distance".to_string(),
            provenance_refs,
            evaluator_basis_refs,
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: blockers,
            reading:
                "configuration distance bundle is blocked until selected configuration paths, context, and observation gaps are resolved; blockers are not numeric zero"
                    .to_string(),
        };
    }
    let Some(path_hops) = configuration_indexed_distance.measured_value else {
        return unmeasured_part4_distance_value(
            "configuration-distance",
            provenance_refs,
            vec!["configuration indexed distance lacks measured path hops".to_string()],
            coverage_refs,
            "configuration bundle requires measured shortest path hops",
        );
    };
    let Some(context_value) = context_distance.measured_value else {
        return unmeasured_part4_distance_value(
            "configuration-distance",
            provenance_refs,
            vec!["configuration context distance lacks measured overlap".to_string()],
            coverage_refs,
            "configuration bundle requires measured molecule context overlap",
        );
    };
    let path_milli = (path_hops * 250).min(1000);
    let overlap_discount = (small_molecule_weight_milli / 2).min(500);
    let value = ((path_milli + context_value) / 2).saturating_sub(overlap_discount);
    measured_part4_distance_value(
        value,
        "configuration-distance",
        provenance_refs,
        evaluator_basis_refs,
        coverage_refs,
        "configuration bundle combines shortest-path hops, context distance, and small-molecule overlap weight within the selected evidence contract",
    )
}

fn atom_distance_component(
    component_kind: &str,
    weight: i64,
    value: ArchSigDistanceValueV0,
) -> ArchSigAtomDistanceComponentV0 {
    let evaluator_basis_refs = unique_strings(value.evaluator_basis_refs.iter().cloned().chain(
        std::iter::once(format!("profileWeight:{component_kind}:{weight}")),
    ));
    ArchSigAtomDistanceComponentV0 {
        component_kind: component_kind.to_string(),
        weight,
        evaluator_basis_refs,
        value,
    }
}

fn weighted_atom_component_weight(
    axis_ref: &str,
    base_weight: i64,
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> i64 {
    base_weight.saturating_mul(
        foundation
            .profile
            .atom_weights
            .iter()
            .find(|weight| weight.axis_ref == axis_ref)
            .map(|weight| weight.weight)
            .unwrap_or(1),
    )
}

fn atom_high_distance_reasons(
    components: &[ArchSigAtomDistanceComponentV0],
    bundle: &ArchSigDistanceValueV0,
) -> Vec<String> {
    let mut reasons = components
        .iter()
        .filter_map(|component| {
            let value = component.value.measured_value?;
            (value >= 500).then(|| {
                format!(
                    "{} distance is high at {} {}",
                    component.component_kind, value, component.value.unit
                )
            })
        })
        .collect::<Vec<_>>();
    if bundle.status == "blocked" {
        reasons.push(
            "selected atom layout distance is blocked by unmeasured component evidence".to_string(),
        );
    }
    reasons
}

fn molecule_refs_by_atom_pair(
    generated_molecules: &[ArchSigGeneratedMoleculeV0],
) -> BTreeMap<(String, String), Vec<String>> {
    let mut refs = BTreeMap::<(String, String), Vec<String>>::new();
    for molecule in generated_molecules {
        for left_index in 0..molecule.atom_observation_refs.len() {
            for right_index in (left_index + 1)..molecule.atom_observation_refs.len() {
                let pair = sorted_pair(
                    &molecule.atom_observation_refs[left_index],
                    &molecule.atom_observation_refs[right_index],
                );
                refs.entry(pair)
                    .or_default()
                    .push(molecule.generated_molecule_id.clone());
            }
        }
    }
    for values in refs.values_mut() {
        values.sort();
        values.dedup();
    }
    refs
}

fn selected_configuration_distance_pair_refs(
    atom_refs: &[String],
    molecule_refs_by_pair: &BTreeMap<(String, String), Vec<String>>,
) -> Vec<(String, String)> {
    let mut pair_refs = molecule_refs_by_pair
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut sampled_cross_context_count = 0usize;
    const MAX_CROSS_CONTEXT_CONFIGURATION_PAIRS: usize = 256;
    'outer: for left_index in 0..atom_refs.len() {
        for right_index in (left_index + 1)..atom_refs.len() {
            let pair = sorted_pair(&atom_refs[left_index], &atom_refs[right_index]);
            if pair_refs.contains(&pair) {
                continue;
            }
            pair_refs.insert(pair);
            sampled_cross_context_count += 1;
            if sampled_cross_context_count >= MAX_CROSS_CONTEXT_CONFIGURATION_PAIRS {
                break 'outer;
            }
        }
    }
    pair_refs.into_iter().collect()
}

fn viewer_distance_refs_by_atom_pair(
    viewer_distance_inputs: &[ArchSigViewerDistanceInputV0],
) -> BTreeMap<(String, String), Vec<String>> {
    let mut refs = BTreeMap::<(String, String), Vec<String>>::new();
    for input in viewer_distance_inputs {
        let pair = sorted_pair(&input.source_ref, &input.target_ref);
        refs.entry(pair)
            .or_default()
            .push(input.distance_input_id.clone());
    }
    refs
}

fn sorted_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

fn atom_pair_provenance_refs(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
) -> Vec<String> {
    let mut refs = vec![
        left.atom_observation_id.clone(),
        right.atom_observation_id.clone(),
        "aat-theory:distance-extension-design"
            .to_string(),
    ];
    refs.extend(left.source_refs.iter().map(source_ref_label));
    refs.extend(right.source_refs.iter().map(source_ref_label));
    unique_strings(refs.into_iter())
}

fn atom_carrier_set(atom: &ArchMapAtomObservationV0) -> BTreeSet<String> {
    let mut carrier = BTreeSet::from([format!("subject:{}", stable_id(&atom.subject_ref))]);
    carrier.extend(
        atom.object_refs
            .iter()
            .map(|object_ref| format!("object:{}", stable_id(object_ref))),
    );
    carrier.extend(
        atom.source_refs
            .iter()
            .map(source_ref_label)
            .map(|source_ref| format!("source:{}", stable_id(&source_ref))),
    );
    carrier
}

fn atom_valence_set(atom: &ArchMapAtomObservationV0) -> BTreeSet<String> {
    let family = atom.atom_family.to_ascii_lowercase();
    let predicate = atom.predicate.to_ascii_lowercase();
    let mut valence = BTreeSet::from(["can_be_vertex".to_string()]);
    if family.contains("relation") || predicate.contains("delegates") || predicate.contains("calls")
    {
        valence.insert("can_be_edge".to_string());
    }
    if family.contains("contract") || predicate.contains("contract") {
        valence.insert("can_attach_contract".to_string());
    }
    if family.contains("state") || predicate.contains("state") {
        valence.insert("can_own_state".to_string());
    }
    if family.contains("effect") || predicate.contains("effect") {
        valence.insert("can_emit_effect".to_string());
    }
    if family.contains("authority") || predicate.contains("authority") {
        valence.insert("can_require_authority".to_string());
    }
    if family.contains("semantic")
        || predicate.contains("semantic")
        || predicate.contains("meaning")
    {
        valence.insert("can_carry_semantic_reading".to_string());
    }
    if family.contains("runtime") || predicate.contains("runtime") {
        valence.insert("can_participate_runtime_path".to_string());
    }
    if family.contains("boundary") || predicate.contains("boundary") {
        valence.insert("can_be_observed_as_boundary".to_string());
    }
    valence
}

fn semantic_anchor_sets_by_atom(archmap: &ArchMapDocumentV0) -> BTreeMap<String, BTreeSet<String>> {
    let mut refs = BTreeMap::<String, BTreeSet<String>>::new();
    for semantic in &archmap.semantic_observations {
        for atom_ref in &semantic.atom_observation_refs {
            let entry = refs.entry(atom_ref.clone()).or_default();
            entry.insert(format!(
                "semanticObservation:{}",
                stable_id(&semantic.semantic_observation_id)
            ));
            entry.insert(format!(
                "semanticFamily:{}",
                stable_id(&semantic.semantic_family)
            ));
            entry.insert(format!(
                "semanticSubject:{}",
                stable_id(&semantic.subject_ref)
            ));
            entry.insert(format!(
                "semanticPredicate:{}",
                stable_id(&semantic.predicate)
            ));
        }
    }
    refs
}

fn milli_jaccard_distance(left: &BTreeSet<String>, right: &BTreeSet<String>) -> Option<i64> {
    let union = left.union(right).count();
    if union == 0 {
        return None;
    }
    let intersection = left.intersection(right).count();
    Some(1000 - (intersection as i64 * 1000 / union as i64))
}

fn refs_join(refs: &BTreeSet<String>) -> String {
    refs.iter().cloned().collect::<Vec<_>>().join("|")
}

fn atom_shape_ref(atom_observation_ref: &str) -> String {
    format!("atom-shape:{}", stable_id(atom_observation_ref))
}

fn generated_molecule_ref(molecule_observation_ref: &str) -> String {
    format!("generated-molecule:{}", stable_id(molecule_observation_ref))
}

fn atom_shape_axis(atom: &ArchMapAtomObservationV0) -> String {
    let family = atom.atom_family.to_ascii_lowercase();
    let predicate = atom.predicate.to_ascii_lowercase();
    if family.contains("runtime") || predicate.contains("runtime") {
        "runtime"
    } else if family.contains("authority")
        || family.contains("boundary")
        || predicate.contains("authority")
        || predicate.contains("boundary")
    {
        "boundary"
    } else if family.contains("contract") || predicate.contains("contract") {
        "specification"
    } else if family.contains("state") || predicate.contains("state") {
        "dataflow"
    } else if family.contains("effect")
        || family.contains("semantic")
        || predicate.contains("effect")
        || predicate.contains("semantic")
    {
        "semantic"
    } else if family.contains("policy") || predicate.contains("policy") {
        "policy"
    } else {
        "static"
    }
    .to_string()
}

fn atom_shape_direction(atom: &ArchMapAtomObservationV0) -> &'static str {
    let family = atom.atom_family.to_ascii_lowercase();
    let predicate = atom.predicate.to_ascii_lowercase();
    if family.contains("relation")
        || family.contains("runtime")
        || family.contains("effect")
        || predicate.contains("calls")
        || predicate.contains("depends")
        || predicate.contains("writes")
    {
        "outgoing"
    } else {
        "neutral"
    }
}

fn atom_shape_distance_components(
    left: &ArchMapAtomObservationV0,
    right: &ArchMapAtomObservationV0,
) -> (i64, Vec<String>) {
    let left_axis = atom_shape_axis(left);
    let right_axis = atom_shape_axis(right);
    let left_objects = left.object_refs.join("|");
    let right_objects = right.object_refs.join("|");
    let components = [
        (
            "family",
            left.atom_family.as_str(),
            right.atom_family.as_str(),
        ),
        ("axis", left_axis.as_str(), right_axis.as_str()),
        (
            "subject",
            left.subject_ref.as_str(),
            right.subject_ref.as_str(),
        ),
        (
            "predicate",
            left.predicate.as_str(),
            right.predicate.as_str(),
        ),
        (
            "objectSlotSet",
            left_objects.as_str(),
            right_objects.as_str(),
        ),
    ];
    let mut distance = 0i64;
    let mut labels = Vec::new();
    for (name, left_value, right_value) in components {
        let contribution = if left_value == right_value { 0 } else { 1 };
        distance += contribution;
        labels.push(format!(
            "{name}:left={}:right={}:delta={contribution}",
            stable_id(left_value),
            stable_id(right_value)
        ));
    }
    (distance, labels)
}
