fn build_part4_distance_foundation(
    archmap: &ArchMapDocumentV0,
    law_policy: &LawPolicyDocumentV0,
) -> ArchSigPart4DistanceFoundationV0 {
    let scope_id = format!("part4-diagnostic-scope:{}", archmap.map_id);
    let coverage_policy_refs = law_policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.clone())
        .collect::<Vec<_>>();
    let profile = selected_part4_distance_profile(law_policy, &coverage_policy_refs);
    let profile_id = profile.profile_id.clone();
    let signature_axis_refs = law_policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.clone())
        .collect::<Vec<_>>();
    let blocker_refs = vec![
        "issue:#1702 atom geometry evaluator".to_string(),
        "issue:#1703 configuration hypergraph evaluator".to_string(),
        "issue:#1708 signature distance evaluator".to_string(),
        "issue:#1706 operation repair distance evaluator".to_string(),
        "issue:#1709 curvature distance evaluator".to_string(),
        "issue:#1707 homotopy filling distance evaluator".to_string(),
        "issue:#1711 representation metric evaluator".to_string(),
    ];
    let supporting_distances = vec![
        unmeasured_part4_distance(
            "part4-distance:atom-geometry",
            "atomGeometry",
            "fiber-carrier-valence-semantic-anchor",
            "issue:#1702 atom geometry evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:configuration-geometry",
            "configurationGeometry",
            "configuration-indexed-hypergraph-distance",
            "issue:#1703 configuration hypergraph evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:signature-geometry",
            "signatureGeometry",
            "axis-wise-signature-distance-aggregate",
            "issue:#1708 signature distance evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:operation-geometry",
            "operationGeometry",
            "operation-cost-repair-side-effect-bound",
            "issue:#1706 operation repair distance evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:curvature-geometry",
            "curvatureGeometry",
            "obstruction-measure-curvature-transport",
            "issue:#1709 curvature distance evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:homotopy-filling-geometry",
            "homotopyFillingGeometry",
            "homotopy-distance-filling-cost-observation-gap",
            "issue:#1707 homotopy filling distance evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
        unmeasured_part4_distance(
            "part4-distance:representation-metric",
            "representationMetric",
            "representation-stability-faithfulness-distance",
            "issue:#1711 representation metric evaluator",
            &profile_id,
            &scope_id,
            &coverage_policy_refs,
        ),
    ];

    ArchSigPart4DistanceFoundationV0 {
        foundation_id: format!("part4-distance-foundation:{}", archmap.map_id),
        profile,
        diagnostic_scope: ArchSigDiagnosticScopeV0 {
            scope_id: scope_id.clone(),
            observed_atom_refs: archmap
                .atom_observations
                .iter()
                .map(|atom| atom.atom_observation_id.clone())
                .collect(),
            configuration_refs: archmap
                .molecule_observations
                .iter()
                .map(|molecule| molecule.molecule_observation_id.clone())
                .collect(),
            law_universe_ref: law_policy.law_policy_id.clone(),
            distance_profile_ref: profile_id,
            measured_axis_refs: Vec::new(),
            unmeasured_axis_refs: signature_axis_refs,
            coverage_policy_refs,
            blocker_refs,
            evidence_boundary:
                "Diagnostic scope is initialized from selected ArchMap observations and LawPolicy coverage, then synchronized from Part IV evaluator readings before output"
                    .to_string(),
        },
        supporting_distances,
        status_summary: ArchSigDistanceStatusSummaryV0 {
            measured_count: 0,
            zero_count: 0,
            unmeasured_count: 7,
            unavailable_count: 0,
            incomparable_count: 0,
            infinite_count: 0,
            blocked_count: 0,
            schema_foundation_only_count: 0,
        },
        measurement_boundary:
            "Part4 distance foundation is a proxy-free measurement contract: no distance is measured until an evaluator supplies provenance, basis refs, and coverage refs"
                .to_string(),
        proxy_guardrails: vec![
            "schemaFoundationOnly is never a measured distance".to_string(),
            "concernHints cannot produce measured distance without evaluator provenance".to_string(),
            "fixed fixture markers cannot back measured distance".to_string(),
            "viewer layout distance is not AAT diagnostic distance".to_string(),
            "unmeasured and blocked values are not zero".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn build_part4_distance_coverage_ledger(
    foundation: &ArchSigPart4DistanceFoundationV0,
    atom_distance_readings: &[ArchSigAtomDistanceReadingV0],
    configuration_distance_readings: &[ArchSigConfigurationDistanceReadingV0],
    signature_distance_readings: &[ArchSigSignatureDistanceReadingV0],
    operation_distance_readings: &[ArchSigOperationDistanceReadingV0],
    obstruction_measure_readings: &[ArchSigObstructionMeasureReadingV0],
    curvature_mass_readings: &[ArchSigCurvatureMassReadingV0],
    homotopy_distance_readings: &[ArchSigHomotopyDistanceReadingV0],
    representation_metric_readings: &[ArchSigRepresentationMetricReadingV0],
) -> Vec<ArchSigPart4DistanceCoverageLedgerEntryV0> {
    vec![
        part4_ledger_entry(
            "part4-ledger:distance-aat",
            "definition:1.1",
            "DistanceAAT",
            "aat-theory:distance-extension-design",
            "foundation",
            "primary",
            foundation_status(foundation),
            foundation.supporting_distances.len(),
            &["archsig-analysis-packet.json#/part4DistanceFoundation"],
            &["/part4DistanceFoundation"],
            supporting_distance_refs(foundation, &[
                "atomGeometry",
                "configurationGeometry",
                "signatureGeometry",
                "operationGeometry",
                "curvatureGeometry",
                "homotopyFillingGeometry",
                "representationMetric",
            ]),
            foundation.diagnostic_scope.blocker_refs.clone(),
            &[],
            "DistanceAAT is represented as the Part IV foundation, profile, diagnostic scope, supporting distances, and non-conclusion boundary.",
        ),
        part4_ledger_entry(
            "part4-ledger:atom-geometry",
            "definitions:2.1-2.5",
            "Fiber / Carrier / Valence / Semantic Anchor / Atom Layout distance",
            "aat-theory:distance-extension-design",
            "atomGeometry",
            coverage_status_for_family(
                foundation,
                "atomGeometry",
                atom_distance_readings.len(),
                true,
            ),
            supporting_status(foundation, "atomGeometry"),
            atom_distance_readings.len(),
            &[
                "architecture-distance.json#/atomDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/topMovedAtoms",
                "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
            ],
            &["/atomDistanceReadings", "/viewerDistanceInputs"],
            supporting_distance_refs(foundation, &["atomGeometry"]),
            supporting_blockers(foundation, "atomGeometry"),
            &["#1859"],
            "Atom geometry is expected to expose each Part IV atom-distance component without treating viewer layout distance as diagnostic distance.",
        ),
        part4_ledger_entry(
            "part4-ledger:configuration-context",
            "definitions:3.1-3.2",
            "Configuration-indexed distance and Context distance",
            "aat-theory:distance-extension-design",
            "configurationGeometry",
            coverage_status_for_family(
                foundation,
                "configurationGeometry",
                configuration_distance_readings.len(),
                true,
            ),
            supporting_status(foundation, "configurationGeometry"),
            configuration_distance_readings.len(),
            &[
                "architecture-distance.json#/configurationDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis",
                "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
            ],
            &["/configurationDistanceReadings"],
            supporting_distance_refs(foundation, &["configurationGeometry"]),
            supporting_blockers(foundation, "configurationGeometry"),
            &["#1859"],
            "Configuration distance must stay typed-hypergraph and context based; molecule size alone is not complete Part IV coverage.",
        ),
        part4_ledger_entry(
            "part4-ledger:signature-geometry",
            "definitions:4.1-4.4",
            "Axis distance, Signature distance, Safe margin, and Signature drift",
            "aat-theory:distance-extension-design",
            "signatureGeometry",
            coverage_status_for_family(
                foundation,
                "signatureGeometry",
                signature_distance_readings.len(),
                true,
            ),
            supporting_status(foundation, "signatureGeometry"),
            signature_distance_readings.len(),
            &[
                "architecture-distance.json#/signatureDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/topMovedAxes",
                "llm-interpretation-packet.json#/distanceDiagnosisSummary",
            ],
            &["/signatureDistanceReadings", "/signatureAxes"],
            supporting_distance_refs(foundation, &["signatureGeometry"]),
            supporting_blockers(foundation, "signatureGeometry"),
            &["#1861"],
            "Signature geometry is LawPolicy-relative and must preserve measured, blocked, unmeasured, and incomparable axis states.",
        ),
        part4_ledger_entry(
            "part4-ledger:operation-geometry",
            "definitions:5.1-5.5",
            "Operation cost, Operation distance, Flatness distance, Repair route, and Side-effect bound",
            "aat-theory:distance-extension-design",
            "operationGeometry",
            coverage_status_for_family(
                foundation,
                "operationGeometry",
                operation_distance_readings.len(),
                true,
            ),
            supporting_status(foundation, "operationGeometry"),
            operation_distance_readings.len(),
            &[
                "architecture-distance.json#/operationDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/repairDistance",
            ],
            &[
                "/operationDistanceReadings",
                "/repairOperationCandidates",
                "/operationDeltas",
            ],
            supporting_distance_refs(foundation, &["operationGeometry"]),
            supporting_blockers(foundation, "operationGeometry"),
            &["#1860"],
            "Operation geometry must be profile-driven and blocked when operation costs, preconditions, or side-effect evidence are missing.",
        ),
        part4_ledger_entry(
            "part4-ledger:obstruction-curvature",
            "definitions:6.1-6.3",
            "Obstruction measure, Curvature mass, and Curvature transport",
            "aat-theory:distance-extension-design",
            "curvatureGeometry",
            coverage_status_for_family(
                foundation,
                "curvatureGeometry",
                curvature_mass_readings.len(),
                true,
            ),
            supporting_status(foundation, "curvatureGeometry"),
            obstruction_measure_readings.len() + curvature_mass_readings.len(),
            &[
                "archsig-analysis-summary.json#/distanceDiagnosis/curvatureDistance",
                "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
            ],
            &[
                "/obstructionMeasureReadings",
                "/curvatureMassReadings",
                "/curvatureTransferReadings",
            ],
            supporting_distance_refs(foundation, &["curvatureGeometry"]),
            supporting_blockers(foundation, "curvatureGeometry"),
            &["#1864"],
            "Curvature geometry must expose obstruction-measure support and transport state, not just raw packet rows.",
        ),
        part4_ledger_entry(
            "part4-ledger:homotopy-filling",
            "definitions:7.1-7.4",
            "Homotopy distance, Filling cost, Observation gap lower bound, and Architectural Dehn function",
            "aat-theory:distance-extension-design",
            "homotopyFillingGeometry",
            coverage_status_for_family(
                foundation,
                "homotopyFillingGeometry",
                homotopy_distance_readings.len(),
                true,
            ),
            supporting_status(foundation, "homotopyFillingGeometry"),
            homotopy_distance_readings.len(),
            &[
                "archsig-analysis-summary.json#/distanceDiagnosis/homotopyDistance",
                "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
            ],
            &[
                "/homotopyDistanceReadings",
                "/architectureHomotopyReport",
                "/homotopyHolonomyReadings",
            ],
            supporting_distance_refs(foundation, &["homotopyFillingGeometry"]),
            supporting_blockers(foundation, "homotopyFillingGeometry"),
            &["#1867"],
            "Homotopy and filling readings must make missing filler evidence an actionable blocker, not a hidden non-conclusion.",
        ),
        part4_ledger_entry(
            "part4-ledger:representation-metric",
            "definitions:8.1-8.2",
            "Representation stability and Representation faithfulness",
            "aat-theory:distance-extension-design",
            "representationMetric",
            coverage_status_for_family(
                foundation,
                "representationMetric",
                representation_metric_readings.len(),
                true,
            ),
            supporting_status(foundation, "representationMetric"),
            representation_metric_readings.len(),
            &[
                "archsig-analysis-summary.json#/distanceDiagnosis/representationMetric",
                "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
            ],
            &[
                "/representationMetricReadings",
                "/analyticRepresentations",
                "/representationStrengthReadings",
            ],
            supporting_distance_refs(foundation, &["representationMetric"]),
            supporting_blockers(foundation, "representationMetric"),
            &["#1865"],
            "Representation metrics must distinguish measured structural distance, bounded proxy telemetry, blocked Lipschitz evidence, and faithfulness blockers.",
        ),
        part4_ledger_entry(
            "part4-ledger:measurement-boundary",
            "definitions:9.1-9.3",
            "DistanceValue, unmeasured-is-not-zero, and DistanceProfile",
            "aat-theory:distance-extension-design",
            "measurementBoundary",
            "primary",
            foundation_status(foundation),
            foundation.supporting_distances.len(),
            &[
                "archsig-run-manifest.json#/validationResultSummary",
                "archsig-analysis-summary.json#/measurementStatusSummary",
            ],
            &[
                "/part4DistanceFoundation/profile",
                "/part4DistanceFoundation/statusSummary",
                "/part4DistanceFoundation/diagnosticScope",
            ],
            supporting_distance_refs(foundation, &[
                "atomGeometry",
                "configurationGeometry",
                "signatureGeometry",
                "operationGeometry",
                "curvatureGeometry",
                "homotopyFillingGeometry",
                "representationMetric",
            ]),
            foundation.diagnostic_scope.blocker_refs.clone(),
            &["#1861", "#1866"],
            "Measurement boundary rows record that blocked and unmeasured values remain first-class states and are not aggregated as measured zero.",
        ),
        part4_ledger_entry(
            "part4-ledger:bounded-diagnostic-conclusion",
            "definitions:10.1-10.2",
            "Diagnostic scope and Bounded diagnostic conclusion",
            "aat-theory:distance-extension-design",
            "boundedDiagnosticConclusion",
            "partial",
            foundation_status(foundation),
            foundation.supporting_distances.len(),
            &[
                "archsig-analysis-summary.json#/conclusion",
                "archsig-analysis-summary.json#/distanceDiagnosis",
                "llm-interpretation-packet.json#/distanceDiagnosisSummary",
            ],
            &[
                "/part4DistanceFoundation/diagnosticScope",
                "/boundedJudgements",
                "/llmInterpretationPacket",
            ],
            Vec::new(),
            foundation.diagnostic_scope.blocker_refs.clone(),
            &["#1863", "#1866"],
            "Bounded diagnostic conclusion is partially covered until distanceInsights and full-output docs make the distance reading actionable.",
        ),
    ]
}

fn part4_ledger_entry(
    ledger_entry_id: &str,
    part4_definition_ref: &str,
    definition_title: &str,
    theory_section_ref: &str,
    distance_family: &str,
    coverage_status: impl Into<String>,
    measurement_status: impl Into<String>,
    reading_count: usize,
    primary_artifact_refs: &[&str],
    raw_packet_refs: &[&str],
    supporting_distance_refs: Vec<String>,
    blocker_refs: Vec<String>,
    follow_up_issue_refs: &[&str],
    evidence_boundary: &str,
) -> ArchSigPart4DistanceCoverageLedgerEntryV0 {
    ArchSigPart4DistanceCoverageLedgerEntryV0 {
        ledger_entry_id: ledger_entry_id.to_string(),
        part4_definition_ref: part4_definition_ref.to_string(),
        definition_title: definition_title.to_string(),
        theory_section_ref: theory_section_ref.to_string(),
        distance_family: distance_family.to_string(),
        coverage_status: coverage_status.into(),
        measurement_status: measurement_status.into(),
        reading_count,
        primary_artifact_refs: primary_artifact_refs
            .iter()
            .map(|entry| (*entry).to_string())
            .collect(),
        raw_packet_refs: raw_packet_refs.iter().map(|entry| (*entry).to_string()).collect(),
        supporting_distance_refs,
        blocker_refs,
        follow_up_issue_refs: follow_up_issue_refs
            .iter()
            .map(|entry| (*entry).to_string())
            .collect(),
        evidence_boundary: evidence_boundary.to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn coverage_status_for_family(
    foundation: &ArchSigPart4DistanceFoundationV0,
    family: &str,
    reading_count: usize,
    has_primary_refs: bool,
) -> String {
    let status = supporting_status(foundation, family);
    if reading_count == 0 {
        return match status.as_str() {
            "unavailable" => "not-applicable".to_string(),
            "unmeasured" => "missing-readings".to_string(),
            "blocked" => "blocked-without-readings".to_string(),
            _ => "missing-readings".to_string(),
        };
    }
    if !has_primary_refs {
        return "raw-packet-only".to_string();
    }
    match status.as_str() {
        "measured" | "zero" => "primary".to_string(),
        "blocked" => "primary-blocked".to_string(),
        "unmeasured" => "raw-packet-only".to_string(),
        _ => status,
    }
}

fn foundation_status(foundation: &ArchSigPart4DistanceFoundationV0) -> String {
    if foundation.status_summary.blocked_count > 0 {
        "blocked".to_string()
    } else if foundation.status_summary.unmeasured_count > 0 {
        "partial".to_string()
    } else if foundation.status_summary.measured_count > 0
        || foundation.status_summary.zero_count > 0
    {
        "measured".to_string()
    } else {
        "unmeasured".to_string()
    }
}

fn supporting_status(foundation: &ArchSigPart4DistanceFoundationV0, family: &str) -> String {
    foundation
        .supporting_distances
        .iter()
        .find(|distance| distance.distance_family == family)
        .map(|distance| distance.value.status.clone())
        .unwrap_or_else(|| "missing".to_string())
}

fn supporting_distance_refs(
    foundation: &ArchSigPart4DistanceFoundationV0,
    families: &[&str],
) -> Vec<String> {
    foundation
        .supporting_distances
        .iter()
        .enumerate()
        .filter_map(|(index, distance)| {
            families
                .iter()
                .any(|family| distance.distance_family == *family)
                .then(|| {
                    format!(
                        "/part4DistanceFoundation/supportingDistances/{index}#{}",
                        distance.distance_id
                    )
                })
        })
        .collect()
}

fn supporting_blockers(foundation: &ArchSigPart4DistanceFoundationV0, family: &str) -> Vec<String> {
    foundation
        .supporting_distances
        .iter()
        .find(|distance| distance.distance_family == family)
        .map(|distance| distance.value.blocker_refs.clone())
        .unwrap_or_default()
}

fn selected_part4_distance_profile(
    law_policy: &LawPolicyDocumentV0,
    default_coverage_refs: &[String],
) -> ArchSigDistanceProfileV0 {
    if let Some(profile) = law_policy.part4_distance_profile.as_ref() {
        return ArchSigDistanceProfileV0 {
            profile_id: profile.profile_id.clone(),
            profile_source_ref: format!(
                "law-policy:{}#part4DistanceProfile:{}",
                law_policy.law_policy_id, profile.profile_id
            ),
            atom_weights: profile
                .atom_weights
                .iter()
                .map(|weight| ArchSigDistanceProfileWeightV0 {
                    axis_ref: weight.axis_ref.clone(),
                    weight: weight.weight,
                    source_ref: weight.source_ref.clone(),
                })
                .collect(),
            signature_weights: profile
                .signature_weights
                .iter()
                .map(|weight| ArchSigDistanceProfileWeightV0 {
                    axis_ref: weight.axis_ref.clone(),
                    weight: weight.weight,
                    source_ref: weight.source_ref.clone(),
                })
                .collect(),
            operation_costs: profile
                .operation_costs
                .iter()
                .map(|cost| ArchSigDistanceOperationCostV0 {
                    operation_kind: cost.operation_kind.clone(),
                    cost: cost.cost,
                    source_ref: cost.source_ref.clone(),
                })
                .collect(),
            aggregation_policy: profile.aggregation_policy.clone(),
            unmeasured_policy: profile.unmeasured_policy.clone(),
            law_overlay_policy: profile.law_overlay_policy.clone(),
            coverage_policy_refs: if profile.coverage_requirement_refs.is_empty() {
                default_coverage_refs.to_vec()
            } else {
                profile.coverage_requirement_refs.clone()
            },
            evidence_boundary: profile.evidence_boundary.clone(),
        };
    }

    ArchSigDistanceProfileV0 {
        profile_id: format!("part4-distance-profile:{}", law_policy.law_policy_id),
        profile_source_ref: law_policy.law_policy_id.clone(),
        atom_weights: vec![
            distance_weight("atom.fiber", 1),
            distance_weight("atom.carrier", 1),
            distance_weight("atom.valence", 1),
            distance_weight("atom.semanticAnchor", 1),
        ],
        signature_weights: law_policy
            .signature_axis_definitions
            .iter()
            .map(|axis| ArchSigDistanceProfileWeightV0 {
                axis_ref: axis.signature_axis_id.clone(),
                weight: 1,
                source_ref: axis.law_ref.clone(),
            })
            .collect(),
        operation_costs: vec![
            operation_cost("rename", 1),
            operation_cost("move", 2),
            operation_cost("extract", 3),
            operation_cost("evidence-enrichment", 3),
            operation_cost("introduce-port", 4),
            operation_cost("split-module", 5),
            operation_cost("change-contract", 8),
            operation_cost("semantic-rewrite", 13),
            operation_cost("repair-boundaryleakcircuit", 13),
            operation_cost("repair-semanticmismatchcircuit", 13),
            operation_cost("runtime-protocol-shift", 21),
        ],
        aggregation_policy:
            "aggregate measured axes only; propagate unmeasured, unavailable, incomparable, and blocked status separately"
                .to_string(),
        unmeasured_policy:
            "unmeasured is not zero and cannot contribute numeric zero to total measured distance"
                .to_string(),
        law_overlay_policy:
            "law-relative distance is an overlay over ArchMap Atom observations, not an Atom generator"
                .to_string(),
        coverage_policy_refs: default_coverage_refs.to_vec(),
        evidence_boundary:
            "legacy LawPolicy did not declare part4DistanceProfile; ArchSig used compatibility defaults"
                .to_string(),
    }
}

fn distance_weight(axis_ref: &str, weight: i64) -> ArchSigDistanceProfileWeightV0 {
    ArchSigDistanceProfileWeightV0 {
        axis_ref: axis_ref.to_string(),
        weight,
        source_ref: "aat-theory:distance-extension-design".to_string(),
    }
}

fn operation_cost(operation_kind: &str, cost: i64) -> ArchSigDistanceOperationCostV0 {
    ArchSigDistanceOperationCostV0 {
        operation_kind: operation_kind.to_string(),
        cost,
        source_ref:
            "aat-theory:distance-extension-design"
                .to_string(),
    }
}

fn unmeasured_part4_distance(
    distance_id: &str,
    distance_family: &str,
    distance_kind: &str,
    blocker_ref: &str,
    profile_ref: &str,
    diagnostic_scope_ref: &str,
    coverage_refs: &[String],
) -> ArchSigSupportingDistanceV0 {
    ArchSigSupportingDistanceV0 {
        distance_id: distance_id.to_string(),
        distance_family: distance_family.to_string(),
        distance_kind: distance_kind.to_string(),
        source_ref: "ArchMap".to_string(),
        target_ref: "Part4DistanceEngine".to_string(),
        value: ArchSigDistanceValueV0 {
            status: "unmeasured".to_string(),
            measured_value: None,
            unit: "selected-distance-unit".to_string(),
            provenance_refs: vec![
                "aat-theory:distance-extension-design".to_string(),
                "aat-theory:distance-extension-design".to_string(),
            ],
            evaluator_basis_refs: Vec::new(),
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: vec![blocker_ref.to_string()],
            reading:
                "distance family is represented in the Part4 contract but has not been measured by its evaluator yet"
                    .to_string(),
        },
        profile_ref: profile_ref.to_string(),
        diagnostic_scope_ref: diagnostic_scope_ref.to_string(),
        evidence_boundary:
            "unmeasured means no evaluator result has been supplied; it must not be aggregated as zero"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}
