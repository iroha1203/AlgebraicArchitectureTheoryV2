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
        source_ref: "docs/aat/mathematical_theory/part_4_distance_measure_geometry.md".to_string(),
    }
}

fn operation_cost(operation_kind: &str, cost: i64) -> ArchSigDistanceOperationCostV0 {
    ArchSigDistanceOperationCostV0 {
        operation_kind: operation_kind.to_string(),
        cost,
        source_ref:
            "docs/aat/mathematical_theory/part_4_distance_measure_geometry.md#5-operation-geometry"
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
                "docs/aat/mathematical_theory/part_4_distance_measure_geometry.md".to_string(),
                "docs/aat/AAT_Distance_Extension_Design.md".to_string(),
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
