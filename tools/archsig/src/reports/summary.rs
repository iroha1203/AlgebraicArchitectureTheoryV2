pub(crate) fn build_analysis_summary(
    packet: &serde_json::Value,
    archmap_validation: Option<&serde_json::Value>,
    law_policy_validation: Option<&serde_json::Value>,
    analysis_validation: Option<&serde_json::Value>,
) -> serde_json::Value {
    serde_json::json!({
        "packet": {
            "schemaVersion": json_field(packet, "schemaVersion"),
            "analysisId": json_field(packet, "analysisId"),
            "archMapRef": json_field(packet, "archMapRef"),
            "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
            "generatedAt": json_field(packet, "generatedAt")
        },
        "validation": {
            "archmap": validation_summary(archmap_validation),
            "lawPolicy": validation_summary(law_policy_validation),
            "analysis": validation_summary(analysis_validation)
        },
        "verdict": analysis_verdict(packet),
        "analysisUsefulness": analysis_usefulness(packet),
        "qualityMeasurement": quality_measurement(packet),
        "distanceDiagnosis": distance_diagnosis(packet),
        "measurementStatusSummary": measurement_status_summary(packet),
        "trendDiagnosis": trend_diagnosis(packet),
        "architectureInsightSummary": architecture_insight_summary(packet),
        "reviewSupport": review_support(packet),
        "dominantFindings": dominant_findings(packet),
        "actionQueue": action_queue(packet),
        "axisSummary": axis_summary(packet),
        "aatObservationAxisSummary": aat_observation_axis_summary(packet),
        "designPrincipleSummary": design_principle_summary(packet),
        "architecturalHoleSummary": architectural_hole_summary(packet),
        "bridgeSummary": bridge_summary(packet),
        "coverageGapSummary": coverage_gap_summary(packet),
        "detailIndex": detail_index(packet),
        "measurementBasis": measurement_basis(
            packet,
            archmap_validation,
            law_policy_validation,
            analysis_validation
        ),
        "metadata": {
            "nonConclusions": array_field(packet, "nonConclusions"),
            "spectrumNonConclusions": array_field(
                packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null),
                "nonConclusions"
            ),
            "homotopyNonConclusions": array_field(
                packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null),
                "nonConclusions"
            ),
            "excludedReadings": array_field(packet, "excludedReadings")
        }
    })
}

const DOMINANT_FINDING_LIMIT: usize = 8;

fn dominant_findings(packet: &serde_json::Value) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);

    serde_json::json!({
        "nonzeroAxes": nonzero_axis_findings(packet, DOMINANT_FINDING_LIMIT),
        "spectrumHotspots": hotspot_findings(spectrum, DOMINANT_FINDING_LIMIT),
        "recurrentObstructions": recurrent_obstruction_findings(spectrum, DOMINANT_FINDING_LIMIT),
        "architecturalHoles": loop_ref_findings(
            homotopy,
            "unfilledLoops",
            "/architectureHomotopyReport/unfilledLoops",
            "unfilledLoopMeasured",
            DOMINANT_FINDING_LIMIT
        ),
        "nonzeroHolonomy": loop_ref_findings(
            homotopy,
            "nonzeroHolonomyLoops",
            "/architectureHomotopyReport/nonzeroHolonomyLoops",
            "nonzeroSelectedAxisContinuationDistance",
            DOMINANT_FINDING_LIMIT
        ),
        "bridgePressure": bridge_pressure_findings(packet, DOMINANT_FINDING_LIMIT),
        "projectionFidelityLoss": projection_fidelity_findings(packet, DOMINANT_FINDING_LIMIT),
        "atomOriginClosureDebt": atom_origin_closure_findings(packet, DOMINANT_FINDING_LIMIT),
        "effectRelationPressure": effect_relation_findings(packet, DOMINANT_FINDING_LIMIT),
        "synthesisBlockage": synthesis_blockage_findings(packet, DOMINANT_FINDING_LIMIT),
        "operationPreconditionReadiness": operation_precondition_findings(packet, DOMINANT_FINDING_LIMIT),
        "pathMultiplicityLoss": path_multiplicity_findings(packet, DOMINANT_FINDING_LIMIT)
    })
}

const READING_MODE_FINDING_LIMIT: usize = 1;

fn trend_diagnosis(packet: &serde_json::Value) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "verdict": analysis_verdict(packet),
        "trendCounts": trend_counts(packet),
        "pressureConcentration": {
            "nonzeroAxisRefs": nonzero_axis_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "spectrumHotspotRefs": compact_ref_list(spectrum, "topHotspots", "hotspotId", READING_MODE_FINDING_LIMIT),
            "recurrentObstructionRefs": compact_ref_list(spectrum, "recurrentObstructions", "modeRef", READING_MODE_FINDING_LIMIT),
            "bridgePressureRefs": bridge_pressure_ref_list(packet, READING_MODE_FINDING_LIMIT),
            "pathMultiplicityLossRefs": compact_ref_list(packet, "pathMultiplicityLossReadings", "readingId", 1),
            "projectionFidelityLossRefs": compact_ref_list(packet, "observationProjectionFidelityReadings", "readingId", 1),
            "atomOriginClosureDebtRefs": compact_ref_list(packet, "atomOriginClosureDebtReadings", "readingId", 1)
        },
        "trendInsights": trend_insights(packet),
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport",
            "/transferBridgeReadings",
            "/pathMultiplicityLossReadings",
            "/observationProjectionFidelityReadings",
            "/atomOriginClosureDebtReadings"
        ])
    })
}

fn review_support(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "actionQueueCount": array_len_keyless(&action_queue(packet)),
        "blockerSummary": {
            "architecturalHoleRefs": homotopy_ref_list(packet, "unfilledLoops", READING_MODE_FINDING_LIMIT),
            "nonzeroHolonomyRefs": homotopy_ref_list(packet, "nonzeroHolonomyLoops", READING_MODE_FINDING_LIMIT),
            "operationPreconditionRefs": compact_ref_list(packet, "operationPreconditionReadinessReadings", "operationRef", READING_MODE_FINDING_LIMIT),
            "synthesisBlockageRefs": compact_ref_list(packet, "synthesisBlockageReadings", "readingId", READING_MODE_FINDING_LIMIT),
            "effectRelationPressureRefs": compact_ref_list(packet, "effectRelationAlgebraReadings", "readingId", READING_MODE_FINDING_LIMIT),
            "coverageGapRefs": json_string_array(coverage_gap_refs(packet).iter())
        },
        "packetRefs": packet_refs(&[
            "/architectureHomotopyReport",
            "/operationPreconditionReadinessReadings",
            "/synthesisBlockageReadings",
            "/effectRelationAlgebraReadings",
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}

fn analysis_usefulness(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    let coverage_gap_count = coverage_gap_refs(packet).len();
    let nonzero_axis_count = array_len(flatness, "nonzeroSignatureAxisRefs");
    let hotspot_count = array_len(spectrum, "topHotspots");
    let architectural_hole_count = array_len(homotopy, "unfilledLoops");
    let repair_candidate_count = array_len(packet, "repairOperationCandidates");

    serde_json::json!({
        "mode": if coverage_gap_count > 0 {
            "gapQualifiedActionableAnalysis"
        } else {
            "closedCoverageActionableAnalysis"
        },
        "valueStatement": if coverage_gap_count > 0 {
            "coverage gaps qualify zero, flatness, completeness, and repair-safety claims, but they do not block structural pressure localization or review prioritization"
        } else {
            "no coverage gap was recorded in the selected coverage universe; pressure and zero readings can be read against the supplied ArchMap and LawPolicy"
        },
        "usableNow": usable_now_findings(
            nonzero_axis_count,
            hotspot_count,
            architectural_hole_count,
            repair_candidate_count,
        ),
        "blockedByGaps": blocked_claims_by_gaps(coverage_gap_count),
        "evidenceToUpgradeConfidence": evidence_to_upgrade_confidence(packet),
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/architectureHomotopyReport/unfilledLoops",
            "/repairOperationCandidates",
            "/flatnessReading/blockedByCoverageGaps"
        ])
    })
}

fn usable_now_findings(
    nonzero_axis_count: usize,
    hotspot_count: usize,
    architectural_hole_count: usize,
    repair_candidate_count: usize,
) -> serde_json::Value {
    let mut findings = Vec::new();
    if nonzero_axis_count > 0 {
        findings.push(serde_json::json!({
            "kind": "selectedLawPressure",
            "claim": format!("{nonzero_axis_count} selected LawPolicy axis/axes have nonzero observed support"),
            "use": "prioritize architecture review around selected law pressure rather than treating the repo as uniformly unknown"
        }));
    }
    if hotspot_count > 0 {
        findings.push(serde_json::json!({
            "kind": "curvatureHotspots",
            "claim": format!("{hotspot_count} spectrum hotspot(s) localize repeated obstruction support"),
            "use": "start review from the highest hotspot detail refs"
        }));
    }
    if architectural_hole_count > 0 {
        findings.push(serde_json::json!({
            "kind": "architecturalHoles",
            "claim": format!("{architectural_hole_count} unfilled loop(s) were measured"),
            "use": "identify contract, runtime, policy, or source-backed filler evidence to inspect next"
        }));
    }
    if repair_candidate_count > 0 {
        findings.push(serde_json::json!({
            "kind": "repairReviewQueue",
            "claim": format!("{repair_candidate_count} repair candidate(s) were derived as review cues"),
            "use": "turn candidates into implementation tasks only after preconditions and transfer risk are checked"
        }));
    }
    serde_json::Value::Array(findings)
}

fn blocked_claims_by_gaps(coverage_gap_count: usize) -> serde_json::Value {
    if coverage_gap_count == 0 {
        return serde_json::json!({
            "coverageGapCount": 0,
            "claims": []
        });
    }
    serde_json::json!({
        "coverageGapCount": coverage_gap_count,
        "claims": [
            {
                "claim": "global architecture flatness or lawfulness",
                "reason": "selected coverage gaps prevent promoting absent evidence to zero"
            },
            {
                "claim": "automatic repair safety",
                "reason": "repair candidates still need precondition, runtime, and transfer-risk evidence"
            },
            {
                "claim": "source extraction completeness",
                "reason": "ArchMap observation gaps explicitly bound the supplied source universe"
            }
        ]
    })
}

fn evidence_to_upgrade_confidence(packet: &serde_json::Value) -> serde_json::Value {
    let mut refs = coverage_gap_refs(packet).into_iter().collect::<Vec<_>>();
    refs.sort();
    serde_json::Value::Array(
        refs.into_iter()
            .take(ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
            .map(|gap_ref| {
                let evidence_kind = if gap_ref.contains("runtime") {
                    "runtime traces, request logs, queue traces, or provider execution logs"
                } else if gap_ref.contains("openapi") || gap_ref.contains("framework") {
                    "expanded framework registry, route table, dependency graph, or generated contract"
                } else if gap_ref.contains("provider") || gap_ref.contains("credentials") {
                    "provider policy, credential scope, webhook headers, or provider response samples"
                } else if gap_ref.contains("db") || gap_ref.contains("rls") {
                    "database migration, RLS policy, and deployed tenant-policy evidence"
                } else {
                    "source-backed evidence for the named coverage gap"
                };
                serde_json::json!({
                    "gapRef": gap_ref,
                    "evidenceKind": evidence_kind
                })
            })
            .collect(),
    )
}

const ARCHITECTURE_INSIGHT_LIMIT: usize = 3;
const ARCHITECTURE_INSIGHT_REF_LIMIT: usize = 2;

fn architecture_insight_summary(packet: &serde_json::Value) -> serde_json::Value {
    let clusters = architecture_pressure_clusters(packet);
    serde_json::json!({
        "topInsight": architecture_top_insight(packet, &clusters),
        "insightCards": architecture_insight_cards(packet, &clusters, ARCHITECTURE_INSIGHT_LIMIT),
        "primaryPressureClusters": cluster_summaries(&clusters, ARCHITECTURE_INSIGHT_LIMIT),
        "coverageBlockers": coverage_blocker_insights(packet, ARCHITECTURE_INSIGHT_LIMIT),
        "repairPlanning": repair_planning_summary(packet, ARCHITECTURE_INSIGHT_LIMIT),
        "readNext": architecture_read_next(&clusters),
        "claimBoundary": "insights are structural reading aids over the supplied ArchMap and LawPolicy; they are not a proof, forecast, or automatic repair plan",
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/repairOperationCandidates",
            "/operationPreconditionReadinessReadings",
            "/operationDeltas"
        ])
    })
}

fn architecture_top_insight(
    packet: &serde_json::Value,
    clusters: &[ArchitectureInsightCluster],
) -> serde_json::Value {
    let top_cluster = clusters.first();
    let top_cluster_title = top_cluster
        .map(|cluster| concern_metadata(&cluster.concern).0)
        .unwrap_or("no dominant pressure cluster");
    let coverage_gap_count = coverage_gap_refs(packet).len();
    let repair_candidate_count = array_len(packet, "repairOperationCandidates");
    serde_json::json!({
        "headline": if top_cluster.is_some() {
            format!("{top_cluster_title} is the dominant structural pressure cluster under the selected LawPolicy")
        } else {
            "no dominant structural pressure cluster was measured under the selected LawPolicy".to_string()
        },
        "whyItMatters": "The useful reading is not a flat count: prioritize places where law axes, spectrum hotspots, coverage blockers, repair candidates, and operation preconditions overlap.",
        "coveragePosture": if coverage_gap_count > 0 {
            "coverage gaps qualify zero/flatness/repair-safety claims; measured pressure localization remains usable"
        } else {
            "no coverage blocker was recorded for the selected coverage universe"
        },
        "repairPosture": if repair_candidate_count > 0 {
            "repair candidates exist, but their preconditions and transfer risks must be reviewed before implementation"
        } else {
            "no repair candidate was emitted for this packet"
        }
    })
}

#[derive(Debug, Default)]
struct ArchitectureInsightCluster {
    concern: String,
    pressure_score: i64,
    nonzero_axis_refs: BTreeSet<String>,
    hotspot_refs: BTreeSet<String>,
    repair_refs: BTreeSet<String>,
    precondition_refs: BTreeSet<String>,
    coverage_gap_refs: BTreeSet<String>,
    detail_refs: BTreeSet<String>,
}

fn architecture_pressure_clusters(packet: &serde_json::Value) -> Vec<ArchitectureInsightCluster> {
    let mut clusters = BTreeMap::<String, ArchitectureInsightCluster>::new();
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);

    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        if i64_field(axis, "value", 0) == 0 {
            continue;
        }
        let text = architecture_signal_text(
            axis,
            &["signatureAxisId", "axisRef", "lawRef", "coverageStatus"],
            &[],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "nonzeroSignatureAxis",
                json_field(axis, "signatureAxisId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/signatureAxes/{index}"),
                i64_field(axis, "value", 1).max(1) * 100,
                coverage_refs_from_signal(axis),
            );
        }
    }

    for (index, hotspot) in array_items(spectrum, "topHotspots").into_iter().enumerate() {
        let text = architecture_signal_text(
            hotspot,
            &["hotspotId", "axisRef", "recommendedNextAction"],
            &[],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "spectrumHotspot",
                json_field(hotspot, "hotspotId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/architectureSpectrumReport/topHotspots/{index}"),
                i64_field(hotspot, "curvatureValue", 1).max(1) * 50,
                coverage_refs_from_signal(hotspot),
            );
        }
    }

    for (index, candidate) in array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
    {
        let text = architecture_signal_text(
            candidate,
            &[
                "repairOperationCandidateId",
                "operationKind",
                "evidenceBoundary",
            ],
            &[
                "expectedSignatureAxisEffects",
                "transferRisks",
                "targetObstructionRefs",
            ],
        );
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "repairCandidate",
                json_field(candidate, "repairOperationCandidateId")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/repairOperationCandidates/{index}"),
                75,
                coverage_refs_from_signal(candidate),
            );
        }
    }

    for (index, reading) in array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .enumerate()
    {
        let text = architecture_signal_text(
            reading,
            &[
                "operationRef",
                "operationKind",
                "readinessStatus",
                "recommendedNextAction",
            ],
            &[],
        );
        let precondition_score = (array_len(reading, "missingPreconditionRefs")
            + array_len(reading, "coverageGapRefs")
            + array_len(reading, "witnessGapRefs"))
        .max(1) as i64;
        for concern in concern_keys_for_text(&text) {
            record_architecture_signal(
                &mut clusters,
                concern,
                "operationPrecondition",
                json_field(reading, "operationRef")
                    .as_str()
                    .unwrap_or("unknown"),
                &format!("packet:/operationPreconditionReadinessReadings/{index}"),
                precondition_score * 10,
                coverage_refs_from_signal(reading),
            );
        }
    }

    let mut values = clusters.into_values().collect::<Vec<_>>();
    values.sort_by(|left, right| {
        right
            .pressure_score
            .cmp(&left.pressure_score)
            .then(left.concern.cmp(&right.concern))
    });
    values
}

fn record_architecture_signal(
    clusters: &mut BTreeMap<String, ArchitectureInsightCluster>,
    concern: &str,
    kind: &str,
    reference: &str,
    detail_ref: &str,
    score: i64,
    coverage_refs: BTreeSet<String>,
) {
    let cluster =
        clusters
            .entry(concern.to_string())
            .or_insert_with(|| ArchitectureInsightCluster {
                concern: concern.to_string(),
                ..ArchitectureInsightCluster::default()
            });
    cluster.pressure_score += score;
    match kind {
        "nonzeroSignatureAxis" => {
            cluster.nonzero_axis_refs.insert(reference.to_string());
        }
        "spectrumHotspot" => {
            cluster.hotspot_refs.insert(reference.to_string());
        }
        "repairCandidate" => {
            cluster.repair_refs.insert(reference.to_string());
        }
        "operationPrecondition" => {
            cluster.precondition_refs.insert(reference.to_string());
        }
        _ => {}
    }
    cluster.detail_refs.insert(detail_ref.to_string());
    cluster.coverage_gap_refs.extend(coverage_refs);
}

fn cluster_summaries(clusters: &[ArchitectureInsightCluster], limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        clusters
            .iter()
            .take(limit)
            .map(|cluster| {
                let (title, why, recommended_review) = concern_metadata(&cluster.concern);
                serde_json::json!({
                    "concern": cluster.concern,
                    "title": title,
                    "reading": why,
                    "pressureScore": cluster.pressure_score,
                    "signalCounts": {
                        "nonzeroAxisCount": cluster.nonzero_axis_refs.len(),
                        "spectrumHotspotCount": cluster.hotspot_refs.len(),
                        "repairCandidateCount": cluster.repair_refs.len(),
                        "operationPreconditionBlockerCount": cluster.precondition_refs.len(),
                        "coverageBlockerCount": cluster.coverage_gap_refs.len()
                    },
                    "recommendedReview": recommended_review,
                    "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
                })
            })
            .collect(),
    )
}

fn architecture_insight_cards(
    _packet: &serde_json::Value,
    clusters: &[ArchitectureInsightCluster],
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        clusters
            .iter()
            .take(limit)
            .enumerate()
            .map(|(index, cluster)| {
                let observed = observed_signal_sentences(cluster);
                let missing = insight_card_missing_evidence(cluster);
                let (claim, why_it_matters, next_validation) =
                    insight_card_language(&cluster.concern);
                serde_json::json!({
                    "cardId": format!("insight-card:{}", index + 1),
                    "concern": cluster.concern,
                    "claim": claim,
                    "whyItMatters": why_it_matters,
                    "aatEvidence": {
                        "nonzeroAxisRefs": limited_string_set_values(&cluster.nonzero_axis_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "spectrumHotspotRefs": limited_string_set_values(&cluster.hotspot_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "repairCandidateRefs": limited_string_set_values(&cluster.repair_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "operationPreconditionRefs": limited_string_set_values(&cluster.precondition_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1),
                        "coverageGapRefs": limited_string_set_values(&cluster.coverage_gap_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
                    },
                    "observedSignals": observed,
                    "missingEvidence": missing,
                    "notBlockedByGaps": "measured nonzero axes, spectrum hotspots, repair cues, and precondition blockers are usable review signals even when gaps block zero, global flatness, and repair-safety claims",
                    "blockedClaims": [
                        "global lawfulness or flatness",
                        "automatic repair safety",
                        "source extraction completeness"
                    ],
                    "nextValidation": next_validation,
                    "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT + 1)
                })
            })
            .collect(),
    )
}

fn insight_card_missing_evidence(cluster: &ArchitectureInsightCluster) -> serde_json::Value {
    limited_string_set_values(
        &cluster.coverage_gap_refs,
        ARCHITECTURE_INSIGHT_REF_LIMIT + 1,
    )
}

fn observed_signal_sentences(cluster: &ArchitectureInsightCluster) -> serde_json::Value {
    let mut signals = Vec::new();
    if !cluster.nonzero_axis_refs.is_empty()
        || !cluster.hotspot_refs.is_empty()
        || !cluster.repair_refs.is_empty()
    {
        signals.push(format!(
            "cluster combines {} nonzero axis ref(s), {} hotspot ref(s), {} repair cue(s), and {} precondition blocker ref(s)",
            cluster.nonzero_axis_refs.len(),
            cluster.hotspot_refs.len(),
            cluster.repair_refs.len(),
            cluster.precondition_refs.len()
        ));
    }
    serde_json::Value::Array(signals.into_iter().map(serde_json::Value::String).collect())
}

fn insight_card_language(concern: &str) -> (&'static str, &'static str, serde_json::Value) {
    match concern {
        "authorityTrustBoundary" => (
            "authority and trust checks should be reviewed as one boundary across provider ingress and tenant-scoped routes",
            "The packet shows authority, tenant, role, trust, and permission signals overlapping in the same architecture boundary; reviewing them separately can miss handoff failures.",
            serde_json::json!([
                "trace the selected routes from request identity to tenant or workspace scope",
                "compare provider trust evidence with route/session authority evidence",
                "decide which gaps must be resolved before making a zero or repair-safety claim"
            ]),
        ),
        "stateEffectLifecycle" => (
            "state/effect pressure is concentrated where durable status, retry, external effects, and finalization meet",
            "The relevant risk is not just an async implementation detail; it is the boundary where effect ordering and state-machine ownership must agree.",
            serde_json::json!([
                "review retry, idempotency, compensation, and terminal status evidence together",
                "check whether commit/enqueue or provider-effect paths have an explicit recovery story",
                "separate missing runtime traces from observed source-backed pressure"
            ]),
        ),
        "llmOutputGovernance" => (
            "LLM and generated-output pressure is a cross-boundary architecture property, not a single chat-agent concern",
            "Prompt/context validation, provider output, generated artifacts, and persistence gates appear together; treating them as isolated code paths weakens review.",
            serde_json::json!([
                "follow generated content from prompt inputs through provider response to persistence",
                "check output filtering and tenant/workspace authority at the persistence boundary",
                "collect provider response samples or runtime traces before claiming the boundary is safe"
            ]),
        ),
        "providerIntegrationBoundary" => (
            "external provider ingress participates in the same pressure as authority, output mediation, and retry/finalization",
            "Provider boundaries are carrying trust, authority, runtime, and effect-ordering assumptions at once, so credential or webhook review alone is too narrow.",
            serde_json::json!([
                "review webhook verification, credential scope, provider response evidence, and retry behavior together",
                "map provider-originated data into the paths that persist or generate downstream artifacts",
                "resolve provider policy and response-sample gaps before promoting absence to zero"
            ]),
        ),
        "layerContractBoundary" => (
            "layer/contract pressure is concentrated where API, service, repository, and schema responsibilities converge",
            "The packet points to boundary responsibilities that must preserve contracts across layers, not just files with many dependencies.",
            serde_json::json!([
                "compare API route contracts with service and repository ownership",
                "check whether schema, persistence, and dependency boundaries have one owner",
                "use source refs to distinguish boundary design pressure from mere surface size"
            ]),
        ),
        "sourceProjectionBoundary" => (
            "source-backed projection pressure means domain cohesion and evidence fidelity are part of the same review surface",
            "The useful question is whether the ArchMap projection preserved the coordinates needed for law-relative reading, not whether every missing atom is absent.",
            serde_json::json!([
                "review projection-lost families and forgotten coordinates before repair planning",
                "connect domain cohesion readings back to concrete source-backed atoms",
                "decide which expected-missing evidence is out of scope versus required for confidence"
            ]),
        ),
        _ => (
            "multiple structural readings overlap, but the selected policy did not label a narrower concern",
            "This still gives a review starting point, but the LawPolicy may need a more specific axis to turn the cluster into a sharper architectural claim.",
            serde_json::json!([
                "inspect the packet detail refs for the cluster",
                "decide whether a more specific LawPolicy axis should be introduced",
                "separate observed support from missing evidence before planning repair"
            ]),
        ),
    }
}

fn coverage_blocker_insights(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut blockers = BTreeMap::<String, CoverageBlockerInsight>::new();
    for gap in coverage_gap_refs(packet) {
        let blocker = blockers
            .entry(gap.clone())
            .or_insert_with(|| CoverageBlockerInsight::new(&gap));
        blocker
            .detail_refs
            .insert("packet:/flatnessReading/blockedByCoverageGaps".to_string());
        blocker
            .detail_refs
            .insert("packet:/architectureSpectrumReport/coverageGaps".to_string());
        blocker
            .detail_refs
            .insert("packet:/architectureHomotopyReport/coverageGaps".to_string());
    }
    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        for gap in coverage_refs_from_signal(axis) {
            blockers
                .entry(gap.clone())
                .or_insert_with(|| CoverageBlockerInsight::new(&gap))
                .axis_refs
                .insert(
                    json_field(axis, "signatureAxisId")
                        .as_str()
                        .unwrap_or("unknown")
                        .to_string(),
                );
            blockers
                .get_mut(&gap)
                .expect("coverage blocker exists")
                .detail_refs
                .insert(format!("packet:/signatureAxes/{index}"));
        }
    }
    for (index, candidate) in array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
    {
        for gap in coverage_refs_from_signal(candidate) {
            blockers
                .entry(gap.clone())
                .or_insert_with(|| CoverageBlockerInsight::new(&gap))
                .repair_refs
                .insert(
                    json_field(candidate, "repairOperationCandidateId")
                        .as_str()
                        .unwrap_or("unknown")
                        .to_string(),
                );
            blockers
                .get_mut(&gap)
                .expect("coverage blocker exists")
                .detail_refs
                .insert(format!("packet:/repairOperationCandidates/{index}"));
        }
    }

    let mut values = blockers.into_values().collect::<Vec<_>>();
    values.sort_by(|left, right| {
        right
            .impact_count()
            .cmp(&left.impact_count())
            .then(left.gap_ref.cmp(&right.gap_ref))
    });

    serde_json::json!({
        "coverageBlockerCount": values.len(),
        "items": values
            .into_iter()
            .take(limit)
            .map(|blocker| blocker.to_json())
            .collect::<Vec<_>>(),
        "recommendedReview": "resolve or explicitly accept the highest-impact gaps before reading selected axes as zero or planning repair safety",
        "packetRefs": packet_refs(&[
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}

#[derive(Debug)]
struct CoverageBlockerInsight {
    gap_ref: String,
    axis_refs: BTreeSet<String>,
    repair_refs: BTreeSet<String>,
    detail_refs: BTreeSet<String>,
}

impl CoverageBlockerInsight {
    fn new(gap_ref: &str) -> Self {
        Self {
            gap_ref: gap_ref.to_string(),
            axis_refs: BTreeSet::new(),
            repair_refs: BTreeSet::new(),
            detail_refs: BTreeSet::new(),
        }
    }

    fn impact_count(&self) -> usize {
        self.axis_refs.len() + self.repair_refs.len()
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "gapRef": self.gap_ref,
            "impactCount": self.impact_count(),
            "affectedAxisCount": self.axis_refs.len(),
            "affectedRepairCandidateCount": self.repair_refs.len(),
            "detailRefs": limited_string_set_values(&self.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
        })
    }
}

fn repair_planning_summary(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut candidates = array_items(packet, "repairOperationCandidates")
        .into_iter()
        .enumerate()
        .map(|(index, candidate)| {
            let missing_evidence_count = coverage_refs_from_signal(candidate).len()
                + array_len(candidate, "missingEvidence");
            let transfer_risk_count = array_len(candidate, "transferRisks");
            serde_json::json!({
                "ref": json_field(candidate, "repairOperationCandidateId"),
                "operationKind": json_field(candidate, "operationKind"),
                "targetObstructionCount": array_len(candidate, "targetObstructionRefs"),
                "expectedAxisEffectCount": array_len(candidate, "expectedSignatureAxisEffects"),
                "preconditionCount": array_len(candidate, "preconditions"),
                "coverageBlockerCount": coverage_refs_from_signal(candidate).len(),
                "transferRiskCount": transfer_risk_count,
                "missingEvidenceCount": missing_evidence_count,
                "readiness": if missing_evidence_count > 0 || transfer_risk_count > 0 {
                    "reviewPreconditionsBeforeImplementation"
                } else {
                    "candidateReadyForHumanSelection"
                },
                "detailRefs": detail_refs("repairOperationCandidates", &format!("/repairOperationCandidates/{index}"))
            })
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| {
        std::cmp::Reverse(
            candidate["missingEvidenceCount"]
                .as_u64()
                .unwrap_or_default()
                + candidate["transferRiskCount"].as_u64().unwrap_or_default(),
        )
    });
    serde_json::json!({
        "candidateCount": array_len(packet, "repairOperationCandidates"),
        "candidateOperations": candidates.into_iter().take(limit).collect::<Vec<_>>(),
        "operationDeltaCount": array_len(packet, "operationDeltas"),
        "recommendedReview": "check target obstruction, expected axis effects, missing evidence, and transfer risk before turning a candidate into an implementation task",
        "packetRefs": packet_refs(&["/repairOperationCandidates", "/operationDeltas"])
    })
}

fn architecture_read_next(clusters: &[ArchitectureInsightCluster]) -> serde_json::Value {
    let cluster = clusters.first();
    let mut items = Vec::new();
    if let Some(cluster) = cluster {
        items.push(serde_json::json!({
            "step": 1,
            "focus": concern_metadata(&cluster.concern).0,
            "reason": "start with the highest combined structural pressure; gaps qualify completeness, not the existence of this review signal",
            "detailRefs": limited_string_set_values(&cluster.detail_refs, ARCHITECTURE_INSIGHT_REF_LIMIT)
        }));
    }
    items.extend([
        serde_json::json!({
            "step": 2,
            "focus": "spectrum and selected law overlap",
            "reason": "spectrum hotspots and nonzero signature axes show where selected law pressure concentrates",
            "packetRefs": packet_refs(&["/architectureSpectrumReport/topHotspots", "/signatureAxes"])
        }),
        serde_json::json!({
            "step": 3,
            "focus": "coverage blockers",
            "reason": "use coverage gaps to qualify zero/flatness and choose confidence-upgrade evidence, not to discard structural pressure findings",
            "packetRefs": packet_refs(&[
                "/flatnessReading/blockedByCoverageGaps",
                "/architectureSpectrumReport/coverageGaps",
                "/architectureHomotopyReport/coverageGaps"
            ])
        }),
        serde_json::json!({
            "step": 4,
            "focus": "repair preconditions and transfer",
            "reason": "repair candidates are useful only after missing evidence, preconditions, and transferred obstruction risk are visible",
            "packetRefs": packet_refs(&["/repairOperationCandidates", "/operationPreconditionReadinessReadings", "/operationDeltas"])
        }),
    ]);
    serde_json::Value::Array(items)
}

fn architecture_signal_text(
    value: &serde_json::Value,
    scalar_fields: &[&str],
    array_fields: &[&str],
) -> String {
    let mut parts = Vec::new();
    for field in scalar_fields {
        if let Some(text) = value.get(field).and_then(serde_json::Value::as_str) {
            parts.push(text.to_string());
        }
    }
    for field in array_fields {
        parts.extend(string_array(value, field));
    }
    parts.join(" ")
}

fn concern_keys_for_text(text: &str) -> BTreeSet<&'static str> {
    let normalized = text.to_ascii_lowercase();
    let mut concerns = BTreeSet::new();
    if contains_any(
        &normalized,
        &[
            "authority",
            "permission",
            "tenant",
            "role",
            "jwt",
            "auth",
            "trust",
            "session",
            "rls",
            "token",
        ],
    ) {
        concerns.insert("authorityTrustBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "state",
            "status",
            "job",
            "retry",
            "idempot",
            "event",
            "effect",
            "commit",
            "flush",
            "compensation",
            "transition",
            "upload",
        ],
    ) {
        concerns.insert("stateEffectLifecycle");
    }
    if contains_any(
        &normalized,
        &[
            "prompt",
            "llm",
            "ai",
            "model",
            "provider output",
            "context",
            "embedding",
            "agent",
            "generated",
        ],
    ) {
        concerns.insert("llmOutputGovernance");
    }
    if contains_any(
        &normalized,
        &[
            "provider",
            "webhook",
            "slack",
            "zoom",
            "salesforce",
            "external",
            "ingress",
            "s3",
            "email",
        ],
    ) {
        concerns.insert("providerIntegrationBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "layer",
            "repository",
            "service",
            "api",
            "route",
            "contract",
            "schema",
            "dependency",
            "interface",
        ],
    ) {
        concerns.insert("layerContractBoundary");
    }
    if contains_any(
        &normalized,
        &[
            "source",
            "projection",
            "domain",
            "cohesion",
            "origin",
            "inventory",
            "atom",
        ],
    ) {
        concerns.insert("sourceProjectionBoundary");
    }
    if concerns.is_empty() {
        concerns.insert("generalStructuralPressure");
    }
    concerns
}

fn contains_any(value: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| value.contains(needle))
}

fn concern_metadata(concern: &str) -> (&'static str, &'static str, &'static str) {
    match concern {
        "authorityTrustBoundary" => (
            "authority / trust boundary",
            "authority, tenant, role, trust, and permission signals are overlapping in selected law, spectrum, and operation readings",
            "review route/session authority, tenant scope, trust handoff, and policy evidence together",
        ),
        "stateEffectLifecycle" => (
            "state / effect lifecycle",
            "state transitions, durable effects, retries, events, and status finalization are coupled with selected structural pressure",
            "review state machine ownership, effect ordering, retry/idempotency, and terminal status evidence together",
        ),
        "llmOutputGovernance" => (
            "LLM / output governance",
            "prompt, model, provider output, generated artifact, and persistence boundaries participate in the same pressure cluster",
            "review prompt/context validation, output filtering, persistence gates, and source-backed projection evidence together",
        ),
        "providerIntegrationBoundary" => (
            "provider integration boundary",
            "external provider ingress, webhook, credential, and response surfaces appear in the same structural pressure cluster",
            "review provider trust assumptions, webhook verification, credential policy, and provider response evidence together",
        ),
        "layerContractBoundary" => (
            "layer / contract boundary",
            "API, service, repository, schema, route, and dependency boundaries are carrying selected law pressure",
            "review layer responsibility, contract ownership, API/service/repository split, and schema dependency evidence together",
        ),
        "sourceProjectionBoundary" => (
            "source projection boundary",
            "source-backed domain identity, projection, Atom origin, and cohesion readings affect the same architecture surface",
            "review source inventory, domain projection, Atom origin closure, and projection fidelity together",
        ),
        _ => (
            "general structural pressure",
            "multiple structural readings overlap without a narrower concern label",
            "review the linked packet details and decide whether a more specific LawPolicy axis is needed",
        ),
    }
}

fn coverage_refs_from_signal(value: &serde_json::Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    for key in [
        "coverageGapRefs",
        "missingEvidence",
        "preconditions",
        "witnessGapRefs",
        "exactnessAssumptions",
    ] {
        collect_value_labels(array_items(value, key), &mut refs);
    }
    refs.into_iter()
        .filter(|reference| reference.starts_with("gap:") || reference.starts_with("coverage:"))
        .collect()
}

fn limited_string_set_values(values: &BTreeSet<String>, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        values
            .iter()
            .take(limit)
            .map(|value| serde_json::Value::String(value.clone()))
            .collect(),
    )
}

fn analysis_verdict(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    let nonzero_axis_count = array_len(flatness, "nonzeroSignatureAxisRefs");
    let hotspot_count = array_len(spectrum, "topHotspots");
    let recurrent_count = array_len(spectrum, "recurrentObstructions");
    let architectural_hole_count = array_len(homotopy, "unfilledLoops");
    let nonzero_holonomy_count = array_len(homotopy, "nonzeroHolonomyLoops");
    let coverage_gap_count = coverage_gap_refs(packet).len();

    let flatness_status = flatness
        .get("status")
        .and_then(serde_json::Value::as_str)
        .unwrap_or("unknownUnderSelectedPolicy");
    let flatness_verdict = if nonzero_axis_count > 0 {
        "nonflatUnderSelectedPolicy"
    } else if flatness_status.contains("flat") {
        "flatUnderSelectedPolicy"
    } else {
        "unknownUnderSelectedPolicy"
    };
    let pressure_detected = nonzero_axis_count > 0 || hotspot_count > 0 || recurrent_count > 0;
    let holes_detected = architectural_hole_count > 0 || nonzero_holonomy_count > 0;
    let quality_state = match (pressure_detected, holes_detected, coverage_gap_count > 0) {
        (true, true, _) => "pressureAndArchitecturalHolesDetected",
        (true, false, _) => "architecturePressureDetected",
        (false, true, _) => "architecturalHolesDetected",
        (false, false, true) => "coverageGapsDetected",
        (false, false, false) => "noMeasuredPressureDetected",
    };
    let actionability = if pressure_detected || holes_detected || coverage_gap_count > 0 {
        "reviewRequired"
    } else {
        "noImmediateReviewQueue"
    };
    let primary_conclusion = if nonzero_axis_count > 0 && architectural_hole_count > 0 {
        "selected law axes are nonzero and architectural holes were measured from the supplied ArchMap and LawPolicy"
    } else if nonzero_axis_count > 0 {
        "selected law axes are nonzero under the supplied ArchMap and LawPolicy"
    } else if architectural_hole_count > 0 {
        "architectural holes were measured from unfilled loops under the supplied ArchMap and LawPolicy"
    } else if coverage_gap_count > 0 {
        "coverage gaps block a zero reading under the supplied ArchMap and LawPolicy"
    } else {
        "no nonzero architecture pressure was measured under the supplied ArchMap and LawPolicy"
    };

    serde_json::json!({
        "flatness": flatness_verdict,
        "qualityState": quality_state,
        "primaryConclusion": primary_conclusion,
        "actionability": actionability,
        "readingMode": "measurementOverSuppliedArchMapAndLawPolicy"
    })
}

fn quality_measurement(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "selectedAxisCount": array_len(packet, "signatureAxes"),
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "zeroAxisCount": array_len(flatness, "zeroSignatureAxisRefs"),
        "spectrumHotspotCount": array_len(spectrum, "topHotspots"),
        "recurrentObstructionCount": array_len(spectrum, "recurrentObstructions"),
        "witnessClusterCount": array_len(spectrum, "topWitnessClusters"),
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "filledLoopCount": array_len(homotopy, "filledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "localCurvatureCellCount": array_len(homotopy, "topLocalCurvatureCells"),
        "part4SupportingDistanceCount": array_len(
            packet
                .get("part4DistanceFoundation")
                .unwrap_or(&serde_json::Value::Null),
            "supportingDistances"
        ),
        "atomDistanceReadingCount": array_len(packet, "atomDistanceReadings"),
        "configurationDistanceReadingCount": array_len(packet, "configurationDistanceReadings"),
        "signatureDistanceReadingCount": array_len(packet, "signatureDistanceReadings"),
        "operationDistanceReadingCount": array_len(packet, "operationDistanceReadings"),
        "curvatureMassReadingCount": array_len(packet, "curvatureMassReadings"),
        "homotopyDistanceReadingCount": array_len(packet, "homotopyDistanceReadings"),
        "representationMetricReadingCount": array_len(packet, "representationMetricReadings"),
        "transferBridgeCount": array_len(packet, "transferBridgeReadings"),
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "effectRelationPressureCount": array_len(packet, "effectRelationAlgebraReadings"),
        "synthesisBlockageCount": array_len(packet, "synthesisBlockageReadings"),
        "operationPreconditionBlockerCount": array_len(packet, "operationPreconditionReadinessReadings"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
}

fn distance_diagnosis(packet: &serde_json::Value) -> serde_json::Value {
    let foundation = packet
        .get("part4DistanceFoundation")
        .unwrap_or(&serde_json::Value::Null);
    let status_summary = json_field(foundation, "statusSummary");
    let signature_distance = array_items(packet, "signatureDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let operation_distance = array_items(packet, "operationDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let curvature_distance = array_items(packet, "curvatureMassReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let homotopy_distance = array_items(packet, "homotopyDistanceReadings")
        .into_iter()
        .next()
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    let diagnostic_scope = foundation
        .get("diagnosticScope")
        .unwrap_or(&serde_json::Value::Null);
    let blocked_count = status_summary
        .get("blockedCount")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();
    let measured_count = status_summary
        .get("measuredCount")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_default();

    serde_json::json!({
        "verdict": if blocked_count > 0 {
            "distanceBlockedByCoverageOrEvidence"
        } else if measured_count > 0 {
            "distanceMeasuredWithinPolicy"
        } else {
            "distanceNeedsEvaluatorEvidence"
        },
        "distanceStatusSummary": status_summary,
        "distanceProfileRef": json_field(
            foundation.get("profile").unwrap_or(&serde_json::Value::Null),
            "profileId"
        ),
        "measuredMovement": {
            "totalMeasuredDistance": compact_distance_value(&signature_distance, "totalMeasuredDistance"),
            "pathDrift": compact_distance_value(&signature_distance, "pathDrift"),
            "endpointDistance": compact_distance_value(&signature_distance, "endpointDistance")
        },
        "unmeasuredAxes": distance_diagnosis_unmeasured_axes(diagnostic_scope, &signature_distance),
        "topMovedAtoms": top_atom_distance_rows(packet, 6),
        "topMovedAxes": top_signature_axis_distance_rows(packet, 6),
        "safeMargin": compact_distance_value(&signature_distance, "safeRegionMargin"),
        "repairDistance": {
            "readingId": json_field(&operation_distance, "operationDistanceReadingId"),
            "operationRef": json_field(&operation_distance, "operationDeltaRef"),
            "operationDeltaRef": json_field(&operation_distance, "operationDeltaRef"),
            "operationKind": json_field(&operation_distance, "operationKind"),
            "operationCost": compact_distance_value(&operation_distance, "operationCost"),
            "targetDistanceDecrease": compact_distance_value(&operation_distance, "targetDistanceDecrease"),
            "sideEffectBound": compact_distance_value(&operation_distance, "sideEffectBound")
        },
        "curvatureDistance": {
            "readingId": json_field(&curvature_distance, "curvatureMassReadingId"),
            "profileRef": json_field(&curvature_distance, "profileRef"),
            "supportReadingRef": json_field(&curvature_distance, "supportReadingRef"),
            "curvatureMass": compact_distance_value(&curvature_distance, "curvatureMass"),
            "transportDistance": compact_distance_value(&curvature_distance, "transportDistance")
        },
        "homotopyDistance": {
            "readingId": json_field(&homotopy_distance, "homotopyDistanceReadingId"),
            "homotopyDistance": compact_distance_value(&homotopy_distance, "homotopyDistance"),
            "fillingCost": compact_distance_value(&homotopy_distance, "fillingCost"),
            "observationGapLowerBound": compact_distance_value(&homotopy_distance, "observationGapLowerBound")
        },
        "representationMetric": representation_metric_distance_rows(packet, 6),
        "detailRefs": [
            packet_ref("/part4DistanceFoundation"),
            packet_ref("/atomDistanceReadings"),
            packet_ref("/signatureDistanceReadings"),
            packet_ref("/operationDistanceReadings"),
            packet_ref("/curvatureMassReadings"),
            packet_ref("/homotopyDistanceReadings"),
            packet_ref("/representationMetricReadings")
        ],
        "distanceBoundary": "diagnostic distance is computed from Part IV evaluators over ArchMap + LawPolicy evidence; viewer layout distance is a separate visual projection and is not a diagnostic metric",
        "nonClaims": [
            "distance diagnosis is not a single architecture quality score",
            "blocked or unmeasured distance is not measured zero",
            "repair distance is not automatic repair safety",
            "representation metric does not certify global structural faithfulness"
        ]
    })
}

fn distance_diagnosis_unmeasured_axes(
    diagnostic_scope: &serde_json::Value,
    signature_distance: &serde_json::Value,
) -> serde_json::Value {
    let signature_axis_aliases = signature_axis_aliases(signature_distance);
    let measured_axis_refs = string_vec_from_value(diagnostic_scope, "measuredAxisRefs")
        .into_iter()
        .chain(string_vec_from_value(
            signature_distance,
            "measuredAxisRefs",
        ))
        .flat_map(|axis| canonical_axis_refs(&axis, &signature_axis_aliases))
        .collect::<BTreeSet<_>>();
    let unmeasured_axis_refs = string_vec_from_value(diagnostic_scope, "unmeasuredAxisRefs")
        .into_iter()
        .chain(string_vec_from_value(
            signature_distance,
            "unmeasuredAxisRefs",
        ))
        .chain(string_vec_from_value(
            signature_distance,
            "incomparableAxisRefs",
        ))
        .filter(|axis| {
            canonical_axis_refs(axis, &signature_axis_aliases)
                .into_iter()
                .all(|canonical| !measured_axis_refs.contains(&canonical))
        })
        .collect::<BTreeSet<_>>();
    json_string_array(unmeasured_axis_refs.into_iter())
}

fn signature_axis_aliases(
    signature_distance: &serde_json::Value,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut aliases = BTreeMap::<String, BTreeSet<String>>::new();
    for axis in array_items(signature_distance, "axisDistances") {
        let refs = ["signatureAxisRef", "axisRef", "lawRef"]
            .into_iter()
            .filter_map(|key| axis.get(key).and_then(serde_json::Value::as_str))
            .map(str::to_string)
            .collect::<BTreeSet<_>>();
        for axis_ref in &refs {
            aliases
                .entry(axis_ref.clone())
                .or_default()
                .extend(refs.iter().cloned());
        }
    }
    aliases
}

fn canonical_axis_refs(
    axis_ref: &str,
    aliases: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    aliases.get(axis_ref).cloned().unwrap_or_else(|| {
        let mut refs = BTreeSet::new();
        refs.insert(axis_ref.to_string());
        refs
    })
}

fn compact_distance_value(container: &serde_json::Value, key: &str) -> serde_json::Value {
    let value = container.get(key).unwrap_or(&serde_json::Value::Null);
    if value.is_null() {
        return serde_json::Value::Null;
    }
    serde_json::json!({
        "status": json_field(value, "status"),
        "measuredValue": json_field(value, "measuredValue"),
        "unit": json_field(value, "unit"),
        "provenanceRefSample": array_field_with_limit(value, "provenanceRefs", Some(3)),
        "coverageRefSample": array_field_with_limit(value, "coverageRefs", Some(3)),
        "blockerRefCount": array_len(value, "blockerRefs")
    })
}

fn top_atom_distance_rows(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut rows = array_items(packet, "atomDistanceReadings")
        .into_iter()
        .map(|reading| {
            let bundle = reading
                .get("atomLayoutDistanceBundle")
                .unwrap_or(&serde_json::Value::Null);
            serde_json::json!({
                "readingId": json_field(reading, "atomDistanceReadingId"),
                "sourceAtomRef": json_field(reading, "sourceAtomRef"),
                "targetAtomRef": json_field(reading, "targetAtomRef"),
                "bundle": compact_distance_value(reading, "atomLayoutDistanceBundle"),
                "statusRank": distance_status_rank(json_field(bundle, "status").as_str())
            })
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("statusRank")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(limit).collect())
}

fn top_signature_axis_distance_rows(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut rows = array_items(packet, "signatureDistanceReadings")
        .into_iter()
        .flat_map(|reading| array_items(reading, "axisDistances"))
        .filter(|axis| {
            axis.get("axisDistance")
                .and_then(|value| value.get("measuredValue"))
                .and_then(serde_json::Value::as_i64)
                .unwrap_or_default()
                > 0
        })
        .map(|axis| {
            let axis_distance = axis.get("axisDistance").unwrap_or(&serde_json::Value::Null);
            serde_json::json!({
                "signatureAxisRef": json_field(axis, "signatureAxisRef"),
                "axisRef": json_field(axis, "axisRef"),
                "rhoI": compact_distance_value(axis, "rhoI"),
                "axisDistance": compact_distance_value(axis, "axisDistance"),
                "coverageStatus": json_field(axis, "coverageStatus"),
                "sourceRefCount": array_len(axis, "sourceRefs"),
                "blockerRefCount": array_len(axis, "blockerRefs"),
                "statusRank": distance_status_rank(json_field(axis_distance, "status").as_str())
            })
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| {
        -row.get("statusRank")
            .and_then(serde_json::Value::as_i64)
            .unwrap_or_default()
    });
    serde_json::Value::Array(rows.into_iter().take(limit).collect())
}

fn representation_metric_distance_rows(
    packet: &serde_json::Value,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "representationMetricReadings")
            .into_iter()
            .take(limit)
            .map(|reading| {
                serde_json::json!({
                    "readingId": json_field(reading, "representationMetricReadingId"),
                    "representationFamily": json_field(reading, "representationFamily"),
                    "structuralDistance": compact_distance_value(reading, "structuralDistance"),
                    "analyticDistance": compact_distance_value(reading, "analyticDistance"),
                    "lipschitzStability": compact_distance_value(reading, "lipschitzStability"),
                    "biLipschitzFaithfulness": compact_distance_value(reading, "biLipschitzFaithfulness"),
                    "part4DistanceRefs": array_field_with_limit(reading, "part4DistanceRefs", Some(6))
                })
            })
            .collect(),
    )
}

fn distance_status_rank(status: Option<&str>) -> i64 {
    match status.unwrap_or_default() {
        "measured" => 50,
        "zero" => 40,
        "partial" => 35,
        "blocked" | "blockedByCoverageGap" => 30,
        "unmeasured" => 20,
        "unavailable" | "incomparable" | "infinite" => 10,
        _ => 0,
    }
}

fn measurement_status_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut measured = 0usize;
    let mut partial = 0usize;
    let mut proxy = 0usize;
    let mut unmeasured = 0usize;
    let mut blocked = 0usize;
    let mut schema_foundation_only = 0usize;

    for value in [
        json_field(packet, "architectureSpectrumReport"),
        json_field(packet, "architectureHomotopyReport"),
    ] {
        classify_measurement_status(
            json_field(&value, "measurementStatus").as_str(),
            &mut measured,
            &mut partial,
            &mut proxy,
            &mut unmeasured,
            &mut blocked,
            &mut schema_foundation_only,
        );
    }
    for family_key in ["monodromyReadingFamily", "boundaryHolonomyReadingFamily"] {
        let family = packet.get(family_key).unwrap_or(&serde_json::Value::Null);
        classify_measurement_status(
            json_field(family, "status").as_str(),
            &mut measured,
            &mut partial,
            &mut proxy,
            &mut unmeasured,
            &mut blocked,
            &mut schema_foundation_only,
        );
    }
    for array_key in [
        "curvatureSupportReadings",
        "curvatureTransferReadings",
        "fillerCandidateReadings",
        "architecturalHoleReadings",
        "homotopyHolonomyReadings",
        "stokesStyleReadings",
        "axisWiseMonodromyDefects",
        "amiAggregateReadings",
    ] {
        for item in array_items(packet, array_key) {
            classify_measurement_status(
                json_field(item, "measurementStatus").as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
            classify_measurement_status(
                json_field(&json_field(item, "readingBoundary"), "readingStrength").as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
        }
    }
    for item in array_items(packet, "representationStrengthReadings") {
        for field in [
            "zeroPreserving",
            "zeroReflecting",
            "obstructionPreserving",
            "obstructionReflecting",
            "aggregateZeroSafety",
            "cancellationRisk",
        ] {
            classify_measurement_status(
                json_field(item, field).as_str(),
                &mut measured,
                &mut partial,
                &mut proxy,
                &mut unmeasured,
                &mut blocked,
                &mut schema_foundation_only,
            );
        }
    }

    serde_json::json!({
        "measuredCount": measured,
        "partialCount": partial,
        "proxyCount": proxy,
        "unmeasuredCount": unmeasured,
        "blockedCount": blocked,
        "schemaFoundationOnlyCount": schema_foundation_only,
        "claimBoundary": "measured counts require evaluator/source refs; proxy and schema-only rows are not measured claims"
    })
}

#[allow(clippy::too_many_arguments)]
fn classify_measurement_status(
    value: Option<&str>,
    measured: &mut usize,
    partial: &mut usize,
    proxy: &mut usize,
    unmeasured: &mut usize,
    blocked: &mut usize,
    schema_foundation_only: &mut usize,
) {
    let Some(value) = value else {
        return;
    };
    let normalized = value.to_ascii_lowercase();
    if normalized == "measured" || normalized.starts_with("boundedmeasured") {
        *measured += 1;
    } else if normalized == "partial" {
        *partial += 1;
    } else if normalized == "schemafoundationonly" {
        *schema_foundation_only += 1;
    } else if normalized.contains("proxy") {
        *proxy += 1;
    } else if normalized.contains("unmeasured") {
        *unmeasured += 1;
    } else if normalized.contains("blocked") || normalized.contains("gap") {
        *blocked += 1;
    }
}

fn trend_counts(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "spectrumHotspotCount": array_len(spectrum, "topHotspots"),
        "recurrentObstructionCount": array_len(spectrum, "recurrentObstructions"),
        "bridgePressureCount": bridge_pressure_action_count(packet),
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "coverageGapCount": coverage_gap_refs(packet).len()
    })
}

const ACTION_QUEUE_HOTSPOT_LIMIT: usize = 8;
const ACTION_QUEUE_HOMOTOPY_LIMIT: usize = 4;
const ACTION_QUEUE_AXIS_LIMIT: usize = 8;
const ACTION_QUEUE_BRIDGE_LIMIT: usize = 4;

fn action_queue(packet: &serde_json::Value) -> serde_json::Value {
    let mut actions = Vec::new();
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);

    for (index, hotspot) in array_items(spectrum, "topHotspots")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOTSPOT_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "spectrumHotspot",
            "conclusion": "measuredPressureHotspot",
            "ref": json_field(hotspot, "hotspotId"),
            "axisRef": json_field(hotspot, "axisRef"),
            "score": json_field(hotspot, "curvatureValue"),
            "recommendedAction": json_field(hotspot, "recommendedNextAction"),
            "detailRefs": detail_refs("architectureSpectrumReport.topHotspots", &format!("/architectureSpectrumReport/topHotspots/{index}"))
        }));
    }
    for (index, loop_ref) in array_items(homotopy, "unfilledLoops")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOMOTOPY_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "architecturalHole",
            "conclusion": "unfilledLoopMeasured",
            "ref": loop_ref.clone(),
            "recommendedAction": "inspect packet loop detail and add contract, test, runtime, policy, or source-backed filler evidence",
            "detailRefs": detail_refs("architectureHomotopyReport.unfilledLoops", &format!("/architectureHomotopyReport/unfilledLoops/{index}"))
        }));
    }
    for (index, loop_ref) in array_items(homotopy, "nonzeroHolonomyLoops")
        .into_iter()
        .enumerate()
        .take(ACTION_QUEUE_HOMOTOPY_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "nonzeroHolonomy",
            "conclusion": "nonzeroSelectedAxisContinuationDistance",
            "ref": loop_ref.clone(),
            "recommendedAction": "compare selected path continuations in packet detail and decide whether the loop needs filler evidence or design change",
            "detailRefs": detail_refs("architectureHomotopyReport.nonzeroHolonomyLoops", &format!("/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"))
        }));
    }
    for (index, axis) in array_items(packet, "signatureAxes")
        .into_iter()
        .enumerate()
        .filter(|(_, axis)| i64_field(axis, "value", 0) != 0)
        .take(ACTION_QUEUE_AXIS_LIMIT)
    {
        actions.push(serde_json::json!({
            "kind": "nonzeroSignatureAxis",
            "conclusion": "nonzeroAxisUnderSelectedPolicy",
            "ref": json_field(axis, "signatureAxisId"),
            "lawRef": json_field(axis, "lawRef"),
            "score": json_field(axis, "value"),
            "coverageStatus": json_field(axis, "coverageStatus"),
            "sourceRefCount": ref_count(axis, "sourceRefs"),
            "missingEvidenceCount": array_len(axis, "missingEvidence"),
            "recommendedAction": "inspect packet detail for source refs and selected law witness support",
            "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}"))
        }));
    }
    for action in aat_observation_axis_actions(packet) {
        actions.push(action);
    }
    for bridge in bridge_pressure_actions(packet)
        .into_iter()
        .take(ACTION_QUEUE_BRIDGE_LIMIT)
    {
        actions.push(bridge);
    }

    serde_json::Value::Array(
        actions
            .into_iter()
            .enumerate()
            .map(|(index, mut action)| {
                if let Some(object) = action.as_object_mut() {
                    object.insert(
                        "priority".to_string(),
                        serde_json::Value::Number((index + 1).into()),
                    );
                }
                action
            })
            .collect(),
    )
}

fn aat_observation_axis_actions(packet: &serde_json::Value) -> Vec<serde_json::Value> {
    let mut actions = Vec::new();
    for (index, reading) in array_items(packet, "observationProjectionFidelityReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "projectionFidelityLoss",
            "conclusion": json_field(reading, "fidelityStatus"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "projectionLossAxes") + i64_field(reading, "forgottenCoordinateCount", 0).max(0) as usize,
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("observationProjectionFidelityReadings", &format!("/observationProjectionFidelityReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "atomOriginClosureDebtReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "atomOriginClosureDebt",
            "conclusion": json_field(reading, "closureStatus"),
            "ref": json_field(reading, "readingId"),
            "score": i64_field(reading, "derivedOrInferredAtomCount", 0).max(0) as usize
                + i64_field(reading, "expectedMissingAtomCount", 0).max(0) as usize,
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("atomOriginClosureDebtReadings", &format!("/atomOriginClosureDebtReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "effectRelationAlgebraReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "effectRelationPressure",
            "conclusion": json_field(reading, "effectOrderingPressure"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "unresolvedEffectRelations") + array_len(reading, "externalBoundaryRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("effectRelationAlgebraReadings", &format!("/effectRelationAlgebraReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "synthesisBlockageReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "synthesisBlockage",
            "conclusion": json_field(reading, "blockageStatus"),
            "ref": json_field(reading, "readingId"),
            "score": array_len(reading, "constraintRefs") + array_len(reading, "missingEvidenceRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("synthesisBlockageReadings", &format!("/synthesisBlockageReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "operationPreconditionReadiness",
            "conclusion": json_field(reading, "readinessStatus"),
            "ref": json_field(reading, "operationRef"),
            "score": array_len(reading, "missingPreconditionRefs") + array_len(reading, "coverageGapRefs") + array_len(reading, "witnessGapRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("operationPreconditionReadinessReadings", &format!("/operationPreconditionReadinessReadings/{index}"))
        }));
    }
    for (index, reading) in array_items(packet, "pathMultiplicityLossReadings")
        .into_iter()
        .enumerate()
    {
        actions.push(serde_json::json!({
            "kind": "pathMultiplicityLoss",
            "conclusion": json_field(reading, "multiplicityLossStatus"),
            "ref": json_field(reading, "readingId"),
            "score": i64_field(reading, "alternatePathPressure", 0).max(0) as usize + array_len(reading, "fanInBoundaryRefs"),
            "recommendedAction": json_field(reading, "recommendedNextAction"),
            "detailRefs": detail_refs("pathMultiplicityLossReadings", &format!("/pathMultiplicityLossReadings/{index}"))
        }));
    }
    actions
}

fn bridge_pressure_actions(packet: &serde_json::Value) -> Vec<serde_json::Value> {
    let mut actions = Vec::new();
    for (reading_index, reading) in array_items(packet, "transferBridgeReadings")
        .into_iter()
        .enumerate()
    {
        for (bridge_index, bridge) in array_items(reading, "bridgeAtomFamilies")
            .into_iter()
            .enumerate()
        {
            let review_risk = bridge
                .get("reviewRisk")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("");
            let bridge_score = i64_field(bridge, "bridgeScore", 0);
            if review_risk == "high" || bridge_score > 0 {
                let path = format!(
                    "/transferBridgeReadings/{reading_index}/bridgeAtomFamilies/{bridge_index}"
                );
                actions.push(serde_json::json!({
                    "kind": "bridgePressure",
                    "conclusion": "transferBridgePressure",
                    "ref": json_field(bridge, "bridgeId"),
                    "score": json_field(bridge, "bridgeScore"),
                    "reviewRisk": json_field(bridge, "reviewRisk"),
                    "recommendedAction": json_field(bridge, "recommendedBoundaryPreparation"),
                    "detailRefs": detail_refs("transferBridgeReadings.bridgeAtomFamilies", &path)
                }));
            }
        }
    }
    actions
}

fn axis_summary(packet: &serde_json::Value) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "selectedAxisCount": array_len(packet, "signatureAxes"),
        "nonzeroAxisCount": array_len(flatness, "nonzeroSignatureAxisRefs"),
        "zeroAxisCount": array_len(flatness, "zeroSignatureAxisRefs"),
        "nonzeroAxes": nonzero_axis_findings(packet, usize::MAX),
        "packetRefs": packet_refs(&["/signatureAxes", "/flatnessReading"])
    })
}

fn aat_observation_axis_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "projectionFidelityLossCount": array_len(packet, "observationProjectionFidelityReadings"),
        "atomOriginClosureDebtCount": array_len(packet, "atomOriginClosureDebtReadings"),
        "effectRelationPressureCount": array_len(packet, "effectRelationAlgebraReadings"),
        "synthesisBlockageCount": array_len(packet, "synthesisBlockageReadings"),
        "operationPreconditionReadinessCount": array_len(packet, "operationPreconditionReadinessReadings"),
        "pathMultiplicityLossCount": array_len(packet, "pathMultiplicityLossReadings"),
        "packetRefs": packet_refs(&[
            "/observationProjectionFidelityReadings",
            "/atomOriginClosureDebtReadings",
            "/effectRelationAlgebraReadings",
            "/synthesisBlockageReadings",
            "/operationPreconditionReadinessReadings",
            "/pathMultiplicityLossReadings"
        ])
    })
}

fn nonzero_axis_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "signatureAxes")
            .into_iter()
            .enumerate()
            .filter(|(_, axis)| i64_field(axis, "value", 0) != 0)
            .take(limit)
            .map(|(index, axis)| {
                serde_json::json!({
                    "ref": json_field(axis, "signatureAxisId"),
                    "lawRef": json_field(axis, "lawRef"),
                    "axisRef": json_field(axis, "axisRef"),
                    "score": json_field(axis, "value"),
                    "coverageStatus": json_field(axis, "coverageStatus"),
                    "missingEvidenceCount": array_len(axis, "missingEvidence"),
                    "sourceRefCount": ref_count(axis, "sourceRefs"),
                    "detailRefs": detail_refs("signatureAxes", &format!("/signatureAxes/{index}")),
                    "packetRefs": packet_refs(&[&format!("/signatureAxes/{index}")])
                })
            })
            .collect(),
    )
}

fn design_principle_summary(packet: &serde_json::Value) -> serde_json::Value {
    let mut status_counts = BTreeMap::<String, usize>::new();
    let items = array_items(packet, "designPrincipleReadings")
        .into_iter()
        .map(|reading| {
            let status = json_field(reading, "status")
                .as_str()
                .unwrap_or("unknown")
                .to_string();
            *status_counts.entry(status.clone()).or_default() += 1;
            serde_json::json!({
                "principle": json_field(reading, "principle"),
                "status": status,
                "witnessRuleRef": json_field(reading, "witnessRuleRef"),
                "witnessStatus": json_field(reading, "witnessStatus"),
                "evidenceRefCount": array_len(reading, "witnessEvidenceRefs"),
                "sourceRefCount": ref_count(reading, "sourceRefs"),
                "obstructionRefCount": array_len(reading, "obstructionRefs"),
                "recommendedNextAction": json_field(reading, "recommendedNextAction")
            })
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "statusCounts": status_counts,
        "items": items,
        "claimBoundary": "design principles are principle-specific witness readings, not static lint rules or theorem proofs"
    })
}

fn architectural_hole_summary(packet: &serde_json::Value) -> serde_json::Value {
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "architecturalHoleCount": array_len(homotopy, "unfilledLoops"),
        "nonzeroHolonomyLoopCount": array_len(homotopy, "nonzeroHolonomyLoops"),
        "localCurvatureCellCount": array_len(homotopy, "topLocalCurvatureCells"),
        "unfilledLoopExamples": loop_ref_findings(
            homotopy,
            "unfilledLoops",
            "/architectureHomotopyReport/unfilledLoops",
            "unfilledLoopMeasured",
            DOMINANT_FINDING_LIMIT
        ),
        "nonzeroHolonomyExamples": loop_ref_findings(
            homotopy,
            "nonzeroHolonomyLoops",
            "/architectureHomotopyReport/nonzeroHolonomyLoops",
            "nonzeroSelectedAxisContinuationDistance",
            DOMINANT_FINDING_LIMIT
        ),
        "packetRefs": packet_refs(&["/architectureHomotopyReport"])
    })
}

fn loop_ref_findings(
    container: &serde_json::Value,
    key: &str,
    base_path: &str,
    conclusion: &str,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(container, key)
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, item)| {
                let path = format!("{base_path}/{index}");
                serde_json::json!({
                    "ref": item.clone(),
                    "conclusion": conclusion,
                    "detailRefs": detail_refs(key, &path),
                    "packetRefs": packet_refs(&[&path])
                })
            })
            .collect(),
    )
}

fn bridge_summary(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "transferBridgeReadingCount": array_len(packet, "transferBridgeReadings"),
        "bridgePressureCount": bridge_pressure_action_count(packet),
        "bridgePressure": bridge_pressure_findings(packet, DOMINANT_FINDING_LIMIT),
        "packetRefs": packet_refs(&["/transferBridgeReadings"])
    })
}

fn bridge_pressure_action_count(packet: &serde_json::Value) -> usize {
    bridge_pressure_actions(packet).len()
}

fn bridge_pressure_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        bridge_pressure_actions(packet)
            .into_iter()
            .take(limit)
            .map(|mut item| {
                if let Some(object) = item.as_object_mut() {
                    object.remove("kind");
                    object.remove("priority");
                }
                item
            })
            .collect(),
    )
}

fn hotspot_findings(spectrum: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(spectrum, "topHotspots")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, hotspot)| {
                serde_json::json!({
                    "ref": json_field(hotspot, "hotspotId"),
                    "axisRef": json_field(hotspot, "axisRef"),
                    "score": json_field(hotspot, "curvatureValue"),
                    "coverageGapCount": array_len(hotspot, "coverageGapRefs"),
                    "recommendedAction": json_field(hotspot, "recommendedNextAction"),
                    "detailRefs": detail_refs("architectureSpectrumReport.topHotspots", &format!("/architectureSpectrumReport/topHotspots/{index}")),
                    "packetRefs": packet_refs(&[&format!("/architectureSpectrumReport/topHotspots/{index}")])
                })
            })
            .collect(),
    )
}

fn recurrent_obstruction_findings(spectrum: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(spectrum, "recurrentObstructions")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "modeRef"),
                    "conclusion": "recurrentObstructionSupport",
                    "reading": json_field(reading, "reading"),
                    "transferEdgeCount": array_len(reading, "transferEdgeRefs"),
                    "detailRefs": detail_refs("architectureSpectrumReport.recurrentObstructions", &format!("/architectureSpectrumReport/recurrentObstructions/{index}")),
                    "packetRefs": packet_refs(&[&format!("/architectureSpectrumReport/recurrentObstructions/{index}")])
                })
            })
            .collect(),
    )
}

fn projection_fidelity_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "observationProjectionFidelityReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "fidelityStatus"),
                    "forgottenCoordinateCount": json_field(reading, "forgottenCoordinateCount"),
                    "collisionCount": json_field(reading, "observationCollisionCount"),
                    "reflectionStatus": json_field(reading, "reflectionStatus"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("observationProjectionFidelityReadings", &format!("/observationProjectionFidelityReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/observationProjectionFidelityReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn atom_origin_closure_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "atomOriginClosureDebtReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "closureStatus"),
                    "sourceBackedAtomCount": json_field(reading, "sourceBackedAtomCount"),
                    "derivedOrInferredAtomCount": json_field(reading, "derivedOrInferredAtomCount"),
                    "expectedMissingAtomCount": json_field(reading, "expectedMissingAtomCount"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("atomOriginClosureDebtReadings", &format!("/atomOriginClosureDebtReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/atomOriginClosureDebtReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn effect_relation_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "effectRelationAlgebraReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "effectOrderingPressure"),
                    "requiredRelationCount": array_len(reading, "requiredEffectRelations"),
                    "unresolvedRelationCount": array_len(reading, "unresolvedEffectRelations"),
                    "externalBoundaryCount": array_len(reading, "externalBoundaryRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("effectRelationAlgebraReadings", &format!("/effectRelationAlgebraReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/effectRelationAlgebraReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn synthesis_blockage_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "synthesisBlockageReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "blockageStatus"),
                    "targetConstructionCount": array_len(reading, "targetConstructionRefs"),
                    "constraintCount": array_len(reading, "constraintRefs"),
                    "missingEvidenceCount": array_len(reading, "missingEvidenceRefs"),
                    "noSolutionCertificateStatus": json_field(reading, "noSolutionCertificateStatus"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("synthesisBlockageReadings", &format!("/synthesisBlockageReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/synthesisBlockageReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn operation_precondition_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "operationPreconditionReadinessReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "operationRef"),
                    "conclusion": json_field(reading, "readinessStatus"),
                    "operationKind": json_field(reading, "operationKind"),
                    "missingPreconditionCount": array_len(reading, "missingPreconditionRefs"),
                    "coverageGapCount": array_len(reading, "coverageGapRefs"),
                    "witnessGapCount": array_len(reading, "witnessGapRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("operationPreconditionReadinessReadings", &format!("/operationPreconditionReadinessReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/operationPreconditionReadinessReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn path_multiplicity_findings(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "pathMultiplicityLossReadings")
            .into_iter()
            .enumerate()
            .take(limit)
            .map(|(index, reading)| {
                serde_json::json!({
                    "ref": json_field(reading, "readingId"),
                    "conclusion": json_field(reading, "multiplicityLossStatus"),
                    "observedPathCount": json_field(reading, "observedPathCount"),
                    "alternatePathPressure": json_field(reading, "alternatePathPressure"),
                    "fanInBoundaryCount": array_len(reading, "fanInBoundaryRefs"),
                    "recommendedAction": json_field(reading, "recommendedNextAction"),
                    "detailRefs": detail_refs("pathMultiplicityLossReadings", &format!("/pathMultiplicityLossReadings/{index}")),
                    "packetRefs": packet_refs(&[&format!("/pathMultiplicityLossReadings/{index}")])
                })
            })
            .collect(),
    )
}

fn coverage_gap_summary(packet: &serde_json::Value) -> serde_json::Value {
    let refs = coverage_gap_refs(packet);
    serde_json::json!({
        "coverageGapCount": refs.len(),
        "gapRefs": json_string_array(refs.iter()),
        "packetRefs": packet_refs(&[
            "/flatnessReading/blockedByCoverageGaps",
            "/architectureSpectrumReport/coverageGaps",
            "/architectureHomotopyReport/coverageGaps"
        ])
    })
}
