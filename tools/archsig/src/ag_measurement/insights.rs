pub fn build_measurement_summary_v1(packet: &ArchSigMeasurementPacketV1) -> Value {
    let nonzero_count = packet
        .structural_verdict
        .iter()
        .filter(|verdict| verdict.verdict == "measured_nonzero")
        .count();
    let unmeasured_count = packet
        .structural_verdict
        .iter()
        .filter(|verdict| {
            matches!(
                verdict.verdict.as_str(),
                "unmeasured" | "unknown" | "not_computed"
            )
        })
        .count();
    let cech_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.cech-obstruction" && verdict.verdict == "measured_nonzero"
    });
    let cech_zero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.cech-obstruction" && verdict.verdict == "measured_zero"
    });
    let cech_cover_shape_excludes = packet.computed_invariants.iter().any(|invariant| {
        invariant["evaluator"] == "ag.cech-obstruction"
            && invariant["theorem12_4Discharge"]["coverShapeExcludesGluingObstruction"].as_bool()
                == Some(true)
    });
    let square_free_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.square-free-repair" && verdict.verdict == "measured_nonzero"
    });
    let repair_targets_identified = square_free_nonzero
        && packet.computed_invariants.iter().any(|invariant| {
            invariant["evaluator"] == "ag.square-free-repair"
                && invariant["alexanderDualRepair"]["minimalHittingSets"]
                    .as_array()
                    .is_some_and(|sets| !sets.is_empty())
        });
    let saga_non_gluing = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-boundary-membership"
            && verdict.verdict == "measured_nonzero"
    });
    let saga_class_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-class"
            && verdict.verdict == "measured_nonzero"
    });
    let saga_glues = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.saga-descent"
            && verdict.law == "saga.residual-boundary-membership"
            && verdict.verdict == "measured_zero"
    });
    let conclusion = if saga_class_nonzero {
        ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
    } else if saga_non_gluing {
        ARCHSIG_SAGA_MEASURED_NONGLUING_RESIDUAL
    } else if saga_glues {
        ARCHSIG_SAGA_REPAIR_GLUES_WITHIN_SELECTED_COMPLEX
    } else if cech_cover_shape_excludes {
        ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION
    } else if cech_nonzero {
        ARCHSIG_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
    } else if repair_targets_identified {
        ARCHSIG_REPAIR_TARGETS_IDENTIFIED
    } else if nonzero_count > 0 {
        ARCHSIG_MEASURED_AG_OBSTRUCTION_UNDER_PROFILE
    } else if cech_zero {
        ARCHSIG_NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE
    } else if unmeasured_count > 0 {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    } else if packet.structural_verdict.is_empty() {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    } else {
        ARCHSIG_AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE
    };
    let translation_rule = summary_translation_rule(conclusion);
    let translation_rule_table = ARCHSIG_ANALYSIS_CONCLUSION_CODES
        .iter()
        .filter(|candidate| {
            **candidate != ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
                || conclusion == ARCHSIG_MEASURED_NONGLUING_RESIDUAL_CLASS
        })
        .map(|conclusion| summary_translation_rule_json(&summary_translation_rule(conclusion)))
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-analysis-summary/v0.5.4",
        "conclusion": conclusion,
        "translationRule": active_summary_translation_rule_json(&translation_rule, packet),
        "translationRuleTable": translation_rule_table,
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": conclusion,
            "whatItMeans": if conclusion == ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION {
                "The selected cover shape and explicit restriction-surjectivity witnesses discharge the Stage 1 abelian cover-shape exclusion check."
            } else if conclusion == ARCHSIG_REPAIR_TARGETS_IDENTIFIED {
                "ArchSig identified combinatorial repair target supports from the selected square-free obstruction invariant."
            } else if cech_nonzero {
                "Local rules are not enough to explain the selected cover; ArchSig measured a cross-context glue mismatch."
            } else if nonzero_count > 0 {
                "Review the theoremRef-bearing structural verdict rows before reading any selected AG obstruction claim."
            } else if cech_zero {
                "No selected H1 glue mismatch was measured under the profile."
            } else if unmeasured_count > 0 {
                "ArchSig produced a profile-relative foundation result with unmeasured, unknown, or not_computed rows still visible."
            } else {
                "ArchSig produced a profile-relative foundation result for the selected measurement surface."
            },
            "whereToLookFirst": "See archsig-insight-report.json#/insightCards/0/evidence",
            "nextAction": "Open archsig-insight-brief.md or the viewer Insight Queue.",
            "boundary": if conclusion == ARCHSIG_REPAIR_TARGETS_IDENTIFIED {
                "Profile-relative. Principle 5.3 boundary: repair targets are combinatorial hitting-set supports, not automatic semantic repairs or operation semantics.".to_string()
            } else if conclusion == ARCHSIG_CECH_COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION {
                format!(
                    "Profile-relative abelian cover-shape statement. Non-abelian torsor, stacky descent, and gerbe obstructions are not excluded. {} assumptions declared. {} non-terminal rows.",
                    packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
                    unmeasured_count
                )
            } else {
                format!(
                    "Profile-relative. {} assumptions declared. {} non-terminal rows.",
                    packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
                    unmeasured_count
                )
            }
        },
        "measurementPacketSchema": packet.schema,
        "profileRef": packet.profile.profile_id,
        "insightArtifacts": {
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md",
            "viewerData": "archsig-atom-viewer-data.json"
        },
        "structuralVerdictSummary": {
            "rowCount": packet.structural_verdict.len(),
            "measuredNonzeroCount": nonzero_count,
            "unmeasuredCount": packet.structural_verdict.iter().filter(|row| row.verdict == "unmeasured").count(),
            "nonTerminalCount": unmeasured_count
        },
        "assumptionSummary": {
            "checkedCount": packet.assumptions.iter().filter(|row| row.status == "checked").count(),
            "assumedCount": packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
            "violatedCount": packet.assumptions.iter().filter(|row| row.status == "violated").count()
        },
        "nonConclusions": [
            "Summary conclusion is relative to MeasurementProfile and assumption ledger.",
            "Schema foundation rows do not claim completed AG invariant computation."
        ]
    })
}

pub fn build_insight_report_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
) -> Value {
    let boundary_digest = insight_boundary_digest(packet, summary);
    let insight_cards = insight_cards_v1(normalized, packet, summary);
    let action_queue = insight_action_queue_v1(&insight_cards);
    let gluing_geometry = gluing_geometry_projection_v1(normalized, packet);
    let viewer_visual_scenes =
        insight_viewer_visual_scenes_v1(normalized, packet, &insight_cards, &gluing_geometry);
    let guided_tours = insight_guided_tours_v1(&insight_cards);
    let copy_blocks = insight_copy_blocks_v1(normalized, &insight_cards, &boundary_digest);
    let omitted_detail_counts = insight_omitted_detail_counts_v1(normalized, &viewer_visual_scenes);
    let top_card = insight_cards.first().cloned().unwrap_or_else(|| {
        json!({
            "id": "insight:measurement-boundary:empty",
            "kind": "measurement_boundary",
            "severity": "info",
            "title": "Measurement boundary recorded",
            "oneLine": "ArchSig generated a bounded measurement projection under the selected profile.",
            "whyItMatters": "Reviewers can inspect the selected profile, assumptions, and artifact links before reading details.",
            "evidence": empty_insight_evidence(),
            "nextAction": {
                "label": "Inspect measurement boundary",
                "kind": "inspect",
                "targetRefs": ["boundary-digest:main"]
            },
            "viewerNavigation": {
                "sceneId": "boundary-assumption",
                "highlightRefs": empty_highlight_refs()
            },
            "tourRefs": ["tour:measurement-boundary:empty"],
            "rankingBasis": ["fallback boundary reading"],
            "nonClaims": ["This does not add a new measurement claim."]
        })
    });
    json!({
        "schema": "archsig-insight-report/v0.5.4",
        "reportId": format!("insight:{}", packet.packet_id),
        "sourcePacketRef": "archsig-measurement-packet.json",
        "generatedAt": "deterministic-run-artifact",
        "outputArtifacts": {
            "summaryRef": "archsig-analysis-summary.json",
            "briefRef": "archsig-insight-brief.md",
            "viewerDataRef": "archsig-atom-viewer-data.json"
        },
        "headline": {
            "conclusionCode": summary["conclusion"],
            "title": top_card["title"],
            "summary": top_card["oneLine"],
            "decisionState": insight_decision_state(&top_card),
            "primaryVerdictRefs": top_card["evidence"]["structuralVerdictRefs"],
            "boundaryDigestRef": "boundary-digest:main"
        },
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": summary["conclusion"],
            "whatItMeans": top_card["oneLine"],
            "whereToLookFirst": top_card["evidence"]["sourceRefs"],
            "nextAction": top_card["nextAction"]["label"],
            "boundary": boundary_digest["shortText"],
            "details": top_card["evidence"]
        },
        "insightCards": insight_cards,
        "actionQueue": action_queue,
        "boundaryDigest": boundary_digest,
        "omittedDetailCounts": omitted_detail_counts,
        "gluingGeometry": gluing_geometry,
        "viewerVisualScenes": viewer_visual_scenes,
        "guidedTours": guided_tours,
        "copyBlocks": copy_blocks,
        "rankingBasis": [
            "validation_failure",
            "measured_nonzero structural verdict",
            "not_computed due to violated assumption",
            "repair lower bound or minimal repair candidate",
            "policy conflict",
            "architecture debt mass analytic reading",
            "measurement boundary",
            "measured_zero confirmation"
        ],
        "claimValidation": {
            "measuredClaimsRequireStructuralVerdictRefs": true,
            "analyticReadingsDoNotPromoteLawfulOrUnlawful": true,
            "highSeverityInsightsRequireWhereRefs": true,
            "notComputedBlockersRequireReasonCode": true,
            "repairCandidatesRequireNonClaims": true,
            "theoremCandidatePromotionForbidden": true,
            "monodromyVerdictGenerated": false
        },
        "nonConclusions": [
            "Insight report is a projection of archsig-measurement-packet/v0.5.4 and does not generate new measurement claims.",
            "Repair candidates are next inspection cues, not automatic fixes.",
            "Viewer scenes are visual projections, not structural verdict derivations."
        ]
    })
}

pub fn build_insight_brief_v1(report: &Value) -> String {
    let mut lines = Vec::new();
    lines.push("# ArchSig Insight Brief".to_string());
    lines.push(String::new());
    lines.push("## Read this first".to_string());
    lines.push(format!(
        "Conclusion: {}",
        string_at(report, &["readThisFirst", "conclusion"])
    ));
    lines.push(String::new());
    lines.push("What it means:".to_string());
    lines.push(string_at(report, &["readThisFirst", "whatItMeans"]));
    lines.push(String::new());
    lines.push("Where to look first:".to_string());
    for item in string_array_at(report, &["readThisFirst", "whereToLookFirst"])
        .into_iter()
        .take(5)
    {
        lines.push(format!("- {item}"));
    }
    lines.push(String::new());
    lines.push("Next action:".to_string());
    lines.push(string_at(report, &["readThisFirst", "nextAction"]));
    lines.push(String::new());
    lines.push("Boundary:".to_string());
    lines.push(string_at(report, &["readThisFirst", "boundary"]));
    lines.push(String::new());
    lines.push("## Top insights".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .take(3)
    {
        lines.push(format!(
            "- {}: {}",
            string_field(card, "title"),
            string_field(card, "oneLine")
        ));
        lines.push(format!(
            "  Why this matters: {}",
            string_field(card, "whyItMatters")
        ));
    }
    lines.push(String::new());
    lines.push("## Where to look".to_string());
    for block in report["copyBlocks"]["sourceRefs"]
        .as_array()
        .into_iter()
        .flatten()
        .take(10)
    {
        lines.push(format!("- {}", block.as_str().unwrap_or_default()));
    }
    lines.push(String::new());
    lines.push("## Suggested next inspections".to_string());
    for action in report["actionQueue"]
        .as_array()
        .into_iter()
        .flatten()
        .take(8)
    {
        lines.push(format!(
            "- {}: {}",
            string_field(action, "title"),
            string_field(action, "reason")
        ));
    }
    lines.push(String::new());
    lines.push("## Repair candidates".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|card| string_field(card, "kind") == "minimal_repair_candidate")
    {
        lines.push(format!("- {}", string_field(card, "oneLine")));
        lines.push("  Boundary: This is a combinatorial repair candidate, not a semantic refactor guarantee.".to_string());
    }
    if !lines
        .last()
        .is_some_and(|line| line.starts_with("  Boundary"))
    {
        lines.push("- No measured repair candidate was promoted by this packet.".to_string());
    }
    lines.push(String::new());
    lines.push("## Measurement boundary".to_string());
    lines.push(string_at(report, &["boundaryDigest", "shortText"]));
    lines.push(format!(
        "- checked: {}",
        number_at(report, &["boundaryDigest", "checkedCount"])
    ));
    lines.push(format!(
        "- assumed: {}",
        number_at(report, &["boundaryDigest", "assumedCount"])
    ));
    lines.push(format!(
        "- blocking: {}",
        number_at(report, &["boundaryDigest", "blockingCount"])
    ));
    if report["omittedDetailCounts"].is_object() {
        lines.push("- omitted detail counts:".to_string());
        for key in [
            "omittedAtoms",
            "omittedEdges",
            "omittedContextMemberships",
            "omittedCoverOverlaps",
            "omittedSceneLayerObjects",
            "omittedLabels",
            "omittedSourceRefs",
        ] {
            lines.push(format!(
                "  - {key}: {}",
                number_at(report, &["omittedDetailCounts", key])
            ));
        }
    }
    lines.push(String::new());
    lines.push("## Artifact links".to_string());
    for key in ["summaryRef", "briefRef", "viewerDataRef"] {
        lines.push(format!(
            "- {}: {}",
            key,
            string_at(report, &["outputArtifacts", key])
        ));
    }
    lines.push(String::new());
    lines.push("## Raw technical details".to_string());
    lines.push(format!(
        "- source packet: {}",
        string_field(report, "sourcePacketRef")
    ));
    lines.push(
        "- theorem-candidate readings are analytic-only and are not structural conclusions."
            .to_string(),
    );
    lines.push("- holonomy-like visual modes are exploratory cover / restriction path views, not monodromy verdicts.".to_string());
    lines.push(String::new());
    lines.push("## LLM handoff".to_string());
    lines.push("Use the following ArchSig result as bounded evidence.".to_string());
    lines.push("Do not infer beyond the listed claims and boundaries.".to_string());
    lines.push(String::new());
    lines.push("Conclusion:".to_string());
    lines.push(string_at(report, &["readThisFirst", "conclusion"]));
    lines.push(String::new());
    lines.push("Top insights:".to_string());
    for card in report["insightCards"]
        .as_array()
        .into_iter()
        .flatten()
        .take(3)
    {
        lines.push(format!("- {}", string_field(card, "oneLine")));
    }
    lines.push(String::new());
    lines.push("Boundary:".to_string());
    lines.push(string_at(report, &["boundaryDigest", "shortText"]));
    lines.push(String::new());
    lines.push("Source refs:".to_string());
    for source_ref in string_array_at(report, &["copyBlocks", "sourceRefs"])
        .into_iter()
        .take(10)
    {
        lines.push(format!("- {source_ref}"));
    }
    lines.push(String::new());
    lines.join("\n")
}

fn insight_cards_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
) -> Vec<Value> {
    let mut cards = Vec::new();
    for row in &packet.structural_verdict {
        if row.evaluator == "ag.cech-obstruction" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:h1-glue-mismatch:001",
                "global_glue_mismatch",
                "high",
                "Global glue mismatch measured",
                "Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.",
                "This highlights architecture drift that can be invisible as a local law violation and gives reviewers a first seam to inspect.",
                row,
                packet,
                normalized,
                "Inspect mismatch support",
                "cech-h1-mismatch",
                vec![
                    "measured_nonzero structural verdict".to_string(),
                    "has context refs".to_string(),
                    "has next inspection action".to_string(),
                ],
                vec![
                    "Source extraction completeness is supplied by the ArchMap source-grounding contract; this card records the selected measurement result.".to_string(),
                    "Repair safety is evaluated by the selected repair contract; this card records the measured support.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.cech-obstruction" && row.verdict == "measured_zero" {
            cards.push(insight_card(
                "insight:h1-glue-mismatch:zero",
                "no_measured_glue_mismatch",
                "info",
                "No measured H^1 glue mismatch under profile",
                "No selected-cover H^1 glue mismatch was measured under this profile.",
                "This lets reviewers distinguish a profile-relative zero result from unmeasured or unknown regions.",
                row,
                packet,
                normalized,
                "Inspect measurement boundary",
                "boundary-assumption",
                vec![
                    "measured_zero confirmation".to_string(),
                    "boundary digest remains visible".to_string(),
                ],
                vec![
                    "This card records a profile-relative zero result for the selected measurement surface.".to_string(),
                    "Unmeasured and unknown support remain represented by their own packet rows.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.square-free-repair" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:repair-candidate:001",
                "minimal_repair_candidate",
                "high",
                "Minimal repair candidate available",
                "Measured forbidden supports have a combinatorial hitting-set repair candidate.",
                "This gives refactor planning a concrete support set to inspect without claiming an automatic semantic repair.",
                row,
                packet,
                normalized,
                "Compare repair candidate with forbidden supports",
                "repair-dual",
                vec![
                    "repair candidate".to_string(),
                    "lower-bound language".to_string(),
                    "non-claim required".to_string(),
                ],
                vec![
                    "This is a combinatorial repair candidate evaluated under the selected support contract.".to_string(),
                    "Repair safety is a result of the selected repair evaluation contract; this card records the candidate support.".to_string(),
                ],
            ));
        } else if row.evaluator == "ag.law-conflict-tor" && row.verdict == "measured_nonzero" {
            cards.push(insight_card(
                "insight:policy-conflict:001",
                "policy_conflict",
                "high",
                "Policy conflict measured",
                "Selected law universes have a measured Tor conflict class in the common ambient.",
                "This points reviewers to the witness/context where policy choices structurally collide.",
                row,
                packet,
                normalized,
                "Inspect policy conflict witness",
                "law-conflict-tor",
                vec!["policy conflict".to_string(), "measured_nonzero structural verdict".to_string()],
                vec!["Compatible refactors are evaluated by the selected comparison contract; this card records the computed compatibility result.".to_string()],
            ));
        } else if row.verdict == "not_computed" {
            cards.push(insight_card(
                &format!("insight:not-computed:{}", slug(&row.evaluator)),
                "not_computed_blocker",
                "high",
                "Measurement blocked by reason code",
                &format!(
                    "{} did not compute because {}.",
                    row.evaluator, row.verdict_data.method_status
                ),
                "The blocked reason belongs in the Decision Bar so reviewers do not mistake an empty scene for absence of conflict.",
                row,
                packet,
                normalized,
                "Inspect blocking reason",
                if row.evaluator == "ag.law-conflict-tor" {
                    "law-conflict-tor"
                } else {
                    "boundary-assumption"
                },
                vec![
                    "not_computed due to reason code".to_string(),
                    row.verdict_data.method_status.clone(),
                ],
                vec!["This is not a measured zero result.".to_string()],
            ));
        }
    }
    if packet
        .analytic_readings
        .iter()
        .any(|reading| reading.evaluator == "ag.sheaf-laplacian")
    {
        cards.push(analytic_insight_card(
            "insight:architecture-debt-mass:001",
            "architecture_debt_mass",
            "medium",
            "Architecture debt field available",
            "Harmonic mass and flatness distance are available as analytic readings.",
            "This supports debt inspection as an analytic field while keeping lawful/unlawful verdicts separate.",
            packet,
            normalized,
            "Inspect Hodge debt field",
            "hodge-debt-field",
            vec!["architecture debt mass / analytic reading".to_string()],
            vec![
                "Near-flat is not lawful.".to_string(),
                "Analytic readings do not generate structural verdicts.".to_string(),
            ],
        ));
    }
    if packet
        .assumptions
        .iter()
        .any(|assumption| assumption.status != "checked")
        || summary["structuralVerdictSummary"]["nonTerminalCount"]
            .as_u64()
            .unwrap_or(0)
            > 0
    {
        cards.push(analytic_insight_card(
            "insight:measurement-boundary:001",
            "measurement_boundary",
            "medium",
            "Measurement boundary recorded",
            "Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.",
            "This tells reviewers exactly where the conclusion is profile-relative and where it is blocked or unmeasured.",
            packet,
            normalized,
            "Inspect measurement boundary",
            "boundary-assumption",
            vec!["measurement boundary".to_string(), "unknown states remain visible".to_string()],
            vec!["Boundary visibility is not a negative conclusion by itself.".to_string()],
        ));
    }
    cards.sort_by(|left, right| {
        insight_rank(right)
            .cmp(&insight_rank(left))
            .then_with(|| string_field(left, "id").cmp(&string_field(right, "id")))
    });
    cards
}

fn insight_card(
    id: &str,
    kind: &str,
    severity: &str,
    title: &str,
    one_line: &str,
    why_it_matters: &str,
    row: &AgStructuralVerdictV1,
    packet: &ArchSigMeasurementPacketV1,
    normalized: &NormalizedArchMapV2,
    next_action: &str,
    scene_id: &str,
    ranking_basis: Vec<String>,
    non_claims: Vec<String>,
) -> Value {
    let refs = insight_refs_for_row(normalized, packet, row);
    let structural_verdict_ref = structural_verdict_ref(row);
    let sample_refs = insight_sample_refs(normalized);
    let evidence_resolution_status = if refs.3.is_empty() && refs.4.is_empty() && refs.5.is_empty()
    {
        "boundary_only"
    } else {
        "resolved_from_packet_support"
    };
    json!({
        "id": id,
        "kind": kind,
        "severity": severity,
        "title": title,
        "oneLine": one_line,
        "whyItMatters": why_it_matters,
        "evidence": {
            "structuralVerdictRefs": [structural_verdict_ref],
            "computedInvariantRefs": refs.0,
            "analyticReadingRefs": refs.1,
            "assumptionRefs": refs.2,
            "sourceRefs": refs.3,
            "atomRefs": refs.4,
            "contextRefs": refs.5,
            "coverRefs": [packet.profile.cover_ref.clone()],
            "evaluatorRefs": [row.evaluator.clone()],
            "evidenceResolutionStatus": evidence_resolution_status
        },
        "sampleRefs": sample_refs,
        "nextAction": {
            "label": next_action,
            "kind": if kind == "minimal_repair_candidate" { "repair_candidate" } else { "next_inspection" },
            "targetRefs": refs.6
        },
        "viewerNavigation": {
            "sceneId": scene_id,
            "highlightRefs": {
                "atomRefs": refs.4,
                "contextRefs": refs.5,
                "sourceRefs": refs.3
            }
        },
        "tourRefs": [format!("tour:{}", id.trim_start_matches("insight:"))],
        "rankingBasis": ranking_basis,
        "nonClaims": non_claims
    })
}

fn analytic_insight_card(
    id: &str,
    kind: &str,
    severity: &str,
    title: &str,
    one_line: &str,
    why_it_matters: &str,
    packet: &ArchSigMeasurementPacketV1,
    normalized: &NormalizedArchMapV2,
    next_action: &str,
    scene_id: &str,
    ranking_basis: Vec<String>,
    non_claims: Vec<String>,
) -> Value {
    let source_refs = top_source_refs(normalized);
    let atom_refs = top_atom_refs(normalized);
    let context_refs = top_context_refs(normalized);
    let sample_refs = insight_sample_refs(normalized);
    json!({
        "id": id,
        "kind": kind,
        "severity": severity,
        "title": title,
        "oneLine": one_line,
        "whyItMatters": why_it_matters,
        "evidence": {
            "structuralVerdictRefs": [],
            "computedInvariantRefs": invariant_refs(packet),
            "analyticReadingRefs": analytic_reading_refs(packet),
            "assumptionRefs": assumption_refs(packet),
            "sourceRefs": source_refs,
            "atomRefs": atom_refs,
            "contextRefs": context_refs,
            "coverRefs": [packet.profile.cover_ref.clone()],
            "evaluatorRefs": evaluator_refs(packet),
            "evidenceResolutionStatus": "analytic_or_boundary_summary"
        },
        "sampleRefs": sample_refs,
        "nextAction": {
            "label": next_action,
            "kind": "next_inspection",
            "targetRefs": ["boundary-digest:main"]
        },
        "viewerNavigation": {
            "sceneId": scene_id,
            "highlightRefs": {
                "atomRefs": atom_refs,
                "contextRefs": context_refs,
                "sourceRefs": source_refs
            }
        },
        "tourRefs": [format!("tour:{}", id.trim_start_matches("insight:"))],
        "rankingBasis": ranking_basis,
        "nonClaims": non_claims
    })
}

fn insight_boundary_digest(packet: &ArchSigMeasurementPacketV1, summary: &Value) -> Value {
    let checked = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "checked")
        .count();
    let assumed = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "assumed")
        .count();
    let violated = packet
        .assumptions
        .iter()
        .filter(|assumption| assumption.status == "violated")
        .count();
    let unmeasured = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "unmeasured")
        .count();
    let unknown = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "unknown")
        .count();
    let not_computed = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "not_computed")
        .count();
    let blocking = violated + not_computed;
    json!({
        "id": "boundary-digest:main",
        "shortText": format!(
            "Profile-relative. {assumed} assumptions declared. {unmeasured} supports unmeasured. {unknown} unknown. {not_computed} not_computed."
        ),
        "profileRef": packet.profile.profile_id,
        "checkedCount": checked,
        "assumedCount": assumed,
        "violatedCount": violated,
        "unmeasuredCount": unmeasured,
        "unknownCount": unknown,
        "notComputedCount": not_computed,
        "blockingCount": blocking,
        "conclusionRef": summary["conclusion"],
        "checked": packet.assumptions.iter().filter(|row| row.status == "checked").map(assumption_row).collect::<Vec<_>>(),
        "assumed": packet.assumptions.iter().filter(|row| row.status == "assumed").map(assumption_row).collect::<Vec<_>>(),
        "blocking": packet.assumptions.iter().filter(|row| row.status == "violated").map(assumption_row).chain(packet.structural_verdict.iter().filter(|row| row.verdict == "not_computed").map(|row| json!({
            "kind": "not_computed",
            "evaluator": row.evaluator,
            "reasonCode": row.verdict_data.method_status,
            "reason": row.reason
        }))).collect::<Vec<_>>(),
        "nonClaims": [
            "Boundary digest qualifies where the conclusion applies; it does not add a new negative conclusion.",
            "Unmeasured, unknown, and not_computed are not measured zero."
        ]
    })
}

fn insight_omitted_detail_counts_v1(normalized: &NormalizedArchMapV2, scenes: &[Value]) -> Value {
    let atom_count = normalized.atoms.len();
    let context_memberships = normalized
        .atoms
        .iter()
        .map(|atom| atom.context_memberships.len())
        .sum::<usize>();
    let cover_overlaps = normalized
        .covers
        .iter()
        .map(|cover| cover.context_ids.len().saturating_sub(1))
        .sum::<usize>();
    let scene_layer_objects = scenes
        .iter()
        .flat_map(|scene| scene["layers"].as_array().into_iter().flatten())
        .count();
    json!({
        "omittedAtoms": if atom_count > 10_000 { atom_count.saturating_sub(10_000) } else { 0 },
        "omittedEdges": 0,
        "omittedContextMemberships": if context_memberships > 20_000 { context_memberships.saturating_sub(20_000) } else { 0 },
        "omittedCoverOverlaps": if cover_overlaps > 10_000 { cover_overlaps.saturating_sub(10_000) } else { 0 },
        "omittedSceneLayerObjects": if scene_layer_objects > 1_000 { scene_layer_objects.saturating_sub(1_000) } else { 0 },
        "omittedLabels": if atom_count > 10_000 { atom_count.saturating_sub(10_000) } else { 0 },
        "omittedSourceRefs": 0,
        "omittedReasons": [
            "large graph projection may aggregate background geometry",
            "top insight support and blocking reason objects are preserved before background objects",
            "viewer data remains a projection and does not embed raw source content"
        ]
    })
}

fn insight_action_queue_v1(cards: &[Value]) -> Vec<Value> {
    cards
        .iter()
        .enumerate()
        .map(|(index, card)| {
            let kind = if string_field(card, "kind") == "minimal_repair_candidate" {
                "repair_candidate"
            } else {
                "next_inspection"
            };
            json!({
                "id": format!("action:{}:{}", kind, index + 1),
                "kind": kind,
                "title": string_at(card, &["nextAction", "label"]),
                "reason": string_field(card, "oneLine"),
                "targetRefs": card["nextAction"]["targetRefs"],
                "expectedUserOutcome": if kind == "repair_candidate" {
                    "Decide whether this combinatorial candidate should seed a refactor plan."
                } else {
                    "Decide which measured support, boundary, or source ref to inspect next."
                },
                "nonClaims": card["nonClaims"]
            })
        })
        .collect()
}

fn insight_viewer_visual_scenes_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
    gluing_geometry: &Value,
) -> Vec<Value> {
    let overview_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &[
            "global_glue_mismatch",
            "minimal_repair_candidate",
            "policy_conflict",
            "not_computed_blocker",
            "architecture_debt_mass",
            "measurement_boundary",
            "confirmed_zero",
            "no_measured_glue_mismatch",
        ],
        true,
    );
    let cech_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &[
            "global_glue_mismatch",
            "confirmed_zero",
            "no_measured_glue_mismatch",
        ],
        false,
    );
    let obstruction_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["minimal_repair_candidate"],
        false,
    );
    let law_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["policy_conflict", "not_computed_blocker"],
        false,
    );
    let hodge_refs = scene_refs_for_kinds(
        normalized,
        packet,
        cards,
        &["architecture_debt_mass"],
        false,
    );
    let analytic_overlay_refs = analytic_overlay_scene_refs(packet, gluing_geometry);
    let period_stokes_refs = period_stokes_scene_refs(packet, gluing_geometry);
    let boundary_refs =
        scene_refs_for_kinds(normalized, packet, cards, &["measurement_boundary"], false);
    let source_refs = source_scene_refs(normalized, packet, cards);
    let has_glue_mismatch = cards
        .iter()
        .any(|card| string_field(card, "kind") == "global_glue_mismatch");
    let has_glue_zero = cards.iter().any(|card| {
        matches!(
            string_field(card, "kind").as_str(),
            "confirmed_zero" | "no_measured_glue_mismatch"
        )
    });
    let has_repair = cards
        .iter()
        .any(|card| string_field(card, "kind") == "minimal_repair_candidate");
    let has_policy_conflict = cards
        .iter()
        .any(|card| string_field(card, "kind") == "policy_conflict");
    let has_not_computed_blocker = cards
        .iter()
        .any(|card| string_field(card, "kind") == "not_computed_blocker");
    let has_debt = cards
        .iter()
        .any(|card| string_field(card, "kind") == "architecture_debt_mass");
    let has_analytic_overlay =
        !string_array_at(&analytic_overlay_refs, &["overlayRefs"]).is_empty();
    let has_period_stokes = gluing_geometry["periodStokes"]["activeMeterCount"]
        .as_u64()
        .unwrap_or_default()
        > 0;
    let scenes = vec![
        scene_v1(
            "overview",
            "overview_constellation",
            "Overview",
            "Which insight should I inspect first?",
            (
                "source locality / module neighborhood",
                "architecture layer or atom family rank",
                "insight priority / measured severity",
            ),
            "top_insight_beacon",
            "beacon",
            "topInsightBeacon",
            "selected insight support",
            &overview_refs,
            overview_color_role(cards),
            "sphere",
            "thick_glowing_line",
            true,
        ),
        scene_v1(
            "site-cover",
            "finite_poset_site",
            "Site / Cover",
            "What finite site and cover did ArchSig measure?",
            (
                "source neighborhood",
                "poset rank",
                "coverage density or context size",
            ),
            "context_patch",
            "patch",
            "contextPatch",
            "context and cover membership",
            &overview_refs,
            "checked",
            "translucent_patch",
            "arrow",
            true,
        ),
        scene_v1(
            "cech-gluing",
            "cover_gluing",
            "Cover & Gluing",
            "Where does local structure fail to glue globally?",
            (
                "context neighborhood / source locality",
                "context rank / restriction depth",
                "gluing mismatch intensity",
            ),
            "overlap_seam",
            "ribbon",
            "cechMismatchSeam",
            "overlap seam and gluing mismatch",
            &cech_refs,
            if has_glue_mismatch {
                "measured_nonzero"
            } else {
                "measured_zero"
            },
            "ribbon",
            "thick_glowing_line",
            has_glue_mismatch || has_glue_zero,
        ),
        scene_v1(
            "cech-h1-mismatch",
            "cech_h1_mismatch",
            "H1 Mismatch",
            "Which mismatch class remains after local explanations?",
            (
                "cover overlap support",
                "cochain / coboundary role",
                "H1 mismatch weight",
            ),
            "cocycle_ribbon",
            "ribbon",
            "cechMismatchSeam",
            "cocycle representative support",
            &cech_refs,
            if has_glue_mismatch {
                "measured_nonzero"
            } else {
                "measured_zero"
            },
            "ribbon",
            "thick_glowing_line",
            has_glue_mismatch || has_glue_zero,
        ),
        scene_v1(
            "obstruction",
            "forbidden_support",
            "Obstruction",
            "Which atom combinations form forbidden support?",
            (
                "atom support neighborhood",
                "law family",
                "obstruction intensity",
            ),
            "forbidden_support_cage",
            "cage",
            "forbiddenSupportCage",
            "minimal forbidden support",
            &obstruction_refs,
            "measured_nonzero",
            "cage",
            "broken_line",
            has_repair,
        ),
        with_scene_non_claims(
            scene_v1(
                "repair-dual",
                "repair_dual",
                "Repair",
                "Which candidate support intersects measured obstructions?",
                ("forbidden support", "candidate set", "lower-bound pressure"),
                "repair_candidate_cut",
                "cut",
                "repairCandidateCut",
                "minimal repair hitting set; not automatic repair",
                &obstruction_refs,
                "repair_candidate",
                "cut",
                "arrow",
                has_repair,
            ),
            &[
                "This is a combinatorial repair candidate under the selected support contract.",
                "Repair safety is evaluated by the selected repair contract; this scene records the candidate support.",
            ],
        ),
        scene_v1(
            "law-conflict-tor",
            "law_conflict",
            "Law Conflict",
            "Which law universe conflict is loaded on which witness?",
            (
                "law universe A",
                "common ambient / blocker",
                "law universe B",
            ),
            "law_conflict_bridge",
            "bridge",
            "lawConflictBridge",
            if has_not_computed_blocker {
                "no_common_ambient blocker or not_computed reason code"
            } else {
                "common ambient conflict witness"
            },
            &law_refs,
            if has_not_computed_blocker {
                "not_computed"
            } else if has_policy_conflict {
                "measured_nonzero"
            } else {
                "not_applicable"
            },
            "wall",
            "broken_line",
            has_policy_conflict || has_not_computed_blocker,
        ),
        scene_v1(
            "hodge-debt-field",
            "hodge_debt_field",
            "Hodge Debt Field",
            "Where is analytic architecture debt mass concentrated?",
            (
                "support locality",
                "harmonic / exact component",
                "debt mass / flatness distance",
            ),
            "analytic_debt_field",
            "field",
            "hodgeDebtField",
            "harmonic mass analytic reading",
            &hodge_refs,
            "analytic_reading",
            "heat",
            "contour",
            has_debt,
        ),
        with_scene_non_claims(
            scene_v1(
                "analytic-overlay",
                "analytic_overlay",
                "Analytic Overlay",
                "Which measured analytic readings can be inspected without promoting them to verdicts?",
                (
                    "analytic source family",
                    "selected cover or support stratum",
                    "reading magnitude / proxy height",
                ),
                "analytic_overlay_lane",
                "overlay",
                "analyticOverlay",
                "packet analytic reading overlay; no new structural verdict",
                &analytic_overlay_refs,
                "analytic_reading",
                "heat",
                "contour",
                has_analytic_overlay,
            ),
            &[
                "Analytic overlays are packet projections only; they do not create structural verdicts.",
                "Near-flat or low proxy values are not measured_zero lawfulness.",
            ],
        ),
        with_scene_non_claims(
            scene_v1(
                "period-stokes",
                "period_stokes_meter",
                "Period Stokes Meter",
                "Does the supplied finite period audit close under the selected coefficient reading?",
                (
                    "period cycle basis",
                    "form / chain audit pair",
                    "Stokes residual magnitude",
                ),
                "period_stokes_meter",
                "meter",
                "periodStokesMeter",
                "M9 Stokes audit meter; modelRelative finite-period reading",
                &period_stokes_refs,
                if has_period_stokes {
                    "analytic_reading"
                } else {
                    "not_applicable"
                },
                "ring",
                "flow_arc",
                has_period_stokes,
            ),
            &[
                "Period Stokes meter is modelRelative to the supplied finite period model.",
                "Period arcs and audit residuals are packet projections; the viewer creates no new structural verdict.",
            ],
        ),
        boundary_scene_v1(&boundary_refs),
        scene_v1(
            "source-evidence",
            "source_evidence",
            "Source Evidence",
            "Which source refs ground this insight?",
            (
                "path / directory neighborhood",
                "symbol / file depth",
                "evidence role",
            ),
            "source_node",
            "node",
            "sourceNode",
            "copyable source refs",
            &source_refs,
            "source_evidence",
            "node",
            "thin_line",
            !string_array_at(&source_refs, &["sourceRefs"]).is_empty(),
        ),
    ];
    scenes
        .into_iter()
        .map(|scene| attach_gluing_scene_geometry(scene, gluing_geometry))
        .collect()
}

fn attach_gluing_scene_geometry(mut scene: Value, gluing_geometry: &Value) -> Value {
    let scene_id = string_field(&scene, "sceneId");
    let geometry_refs = match scene_id.as_str() {
        "site-cover" | "cech-gluing" => json!({
            "nerveRef": "gluingGeometry.nerve",
            "projectionObjectKinds": ["nerveVertex", "nerveEdge", "nerveTriangle"]
        }),
        "cech-h1-mismatch" => json!({
            "cocycleRibbonRef": "gluingGeometry.cocycleRibbon",
            "projectionObjectKinds": ["cocycleRibbon", "holonomyLikeGapMarker"]
        }),
        "obstruction" => json!({
            "forbiddenCagesRef": "gluingGeometry.forbiddenCages",
            "projectionObjectKinds": ["forbiddenSupportCage", "simplexEdge"]
        }),
        "repair-dual" => json!({
            "repairMorphsRef": "gluingGeometry.repairMorphs",
            "projectionObjectKinds": ["repairMorphPath", "lowerBoundMarker"]
        }),
        "hodge-debt-field" => json!({
            "locusFieldRef": "gluingGeometry.locusField",
            "spectrumLandscapeRef": "gluingGeometry.spectrumLandscape",
            "projectionObjectKinds": [
                "curvatureHeightField",
                "blockedUnmeasuredRegion",
                "spectrumLawfulPlain",
                "spectrumLocalDeviationPeak",
                "spectrumProxyRidge"
            ]
        }),
        "analytic-overlay" => json!({
            "analyticOverlayBundleRef": "gluingGeometry.analyticOverlayBundle",
            "projectionObjectKinds": [
                "periodPairingMatrixOverlay",
                "transferCostOverlay",
                "spectralGapOverlay",
                "curvatureHotspotOverlay",
                "singularityConcentrationOverlay"
            ]
        }),
        "period-stokes" => json!({
            "periodStokesRef": "gluingGeometry.periodStokes",
            "projectionObjectKinds": [
                "periodStokesCycleArc",
                "periodStokesAuditMeter",
                "periodStokesResidualFlux"
            ]
        }),
        _ => json!({
            "projectionObjectKinds": []
        }),
    };
    scene["gluingGeometryRefs"] = geometry_refs;
    scene["axisMappingImplemented"] = json!(true);
    scene["axisMetricBindings"] = json!({
        "x": "xValue",
        "y": "yValue",
        "z": "zValue",
        "fallbackBlend": 0.35,
        "source": "renderer sceneAxisPosition reads these metric keys from each gluing geometry object"
    });
    scene["projectionBoundary"] = json!(
        "Scene geometry is a bounded projection of archsig-measurement-packet/v0.5.4 and archsig-insight-report/v0.5.4; it does not create a new structural verdict."
    );
    scene["visualEncodingLegend"] = visual_encoding_legend_v1();
    if scene_id == "cech-h1-mismatch" {
        let mut non_claims = string_array_at(&scene, &["nonClaims"]);
        non_claims.push(
            "Holonomy-like ribbon closure is an exploratory restriction-path view, not a monodromy verdict."
                .to_string(),
        );
        scene["nonClaims"] = json!(non_claims);
    }
    if scene_id == "repair-dual" {
        let mut non_claims = string_array_at(&scene, &["nonClaims"]);
        non_claims.push(
            "Repair morph animation shows lower-bound movement only; it is not an automatic repair."
                .to_string(),
        );
        scene["nonClaims"] = json!(non_claims);
    }
    if scene_id == "hodge-debt-field"
        && gluing_geometry["locusField"]["blockedRegions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    {
        scene["visualEncodings"][0]["textRole"] = json!(
            "curvature support field; blocked/unmeasured remains visibly separate from measured-zero"
        );
    }
    scene
}

fn analytic_overlay_scene_refs(
    packet: &ArchSigMeasurementPacketV1,
    gluing_geometry: &Value,
) -> Value {
    let overlays = gluing_geometry["analyticOverlayBundle"]["overlays"]
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let overlay_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["overlayId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let analytic_reading_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["sourceReadingRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let invariant_refs = overlays
        .iter()
        .filter_map(|overlay| overlay["sourceInvariantRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    json!({
        "overlayRefs": overlay_refs,
        "analyticReadingRefs": analytic_reading_refs,
        "invariantRefs": invariant_refs,
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": []
    })
}

fn period_stokes_scene_refs(packet: &ArchSigMeasurementPacketV1, gluing_geometry: &Value) -> Value {
    let meters = gluing_geometry["periodStokes"]["meters"]
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let meter_refs = meters
        .iter()
        .filter_map(|meter| meter["meterId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let invariant_refs = meters
        .iter()
        .filter_map(|meter| meter["sourceInvariantRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let structural_verdict_refs = meters
        .iter()
        .filter_map(|meter| meter["structuralVerdictRef"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    json!({
        "meterRefs": meter_refs,
        "invariantRefs": invariant_refs,
        "structuralVerdictRefs": structural_verdict_refs,
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": []
    })
}

fn visual_encoding_legend_v1() -> Value {
    json!([
        {
            "channel": "color",
            "meaning": "measurement state",
            "values": {
                "measured_nonzero": "amber obstruction or mismatch support",
                "measured_zero": "teal selected-support zero",
                "not_computed": "red blocker",
                "unmeasured": "gray unmeasured region",
                "analytic_reading": "blue analytic reading lane; never promoted to structural zero",
                "repair_candidate": "violet lower-bound repair candidate"
            }
        },
        {
            "channel": "shape",
            "meaning": "geometry object kind",
            "values": {
                "triangle": "packet cover triple simplex face",
                "ribbon": "Cech support path with closure gap marker",
                "cage": "minimal forbidden support simplex",
                "morph": "repair candidate lower-bound path",
                "glyph": "atom fiber/carrier/valence/semantic-anchor encoding"
            }
        },
        {
            "channel": "line",
            "meaning": "claim boundary",
            "values": {
                "solid": "measured or checked relation",
                "dashed": "blocked/unmeasured boundary",
                "thick": "top insight support"
            }
        },
        {
            "channel": "opacity",
            "meaning": "projection confidence",
            "values": {
                "opaque": "source-backed selected support",
                "translucent": "context or omitted background projection"
            }
        },
        {
            "channel": "thickness",
            "meaning": "support priority",
            "values": {
                "thick": "top insight or nonzero support",
                "thin": "orientation or background relation"
            }
        }
    ])
}

fn gluing_geometry_projection_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
) -> Value {
    let selected_contexts = selected_cover_contexts(normalized, &packet.profile);
    let cech_edges = cech_edges(normalized, &selected_contexts);
    let cover_nerve_projection = packet
        .computed_invariants
        .iter()
        .find_map(|invariant| invariant.get("coverNerveProjection").cloned())
        .unwrap_or_else(|| {
            empty_cover_nerve_projection_v1(
                &packet.profile.cover_ref,
                "missing packet coverNerveProjection; viewer does not infer cover triangles",
            )
        });
    let cover_nerve_projection =
        project_h2_coherence_to_cover_nerve(cover_nerve_projection, packet);
    let cover = normalized.covers.iter().find(|cover| {
        cover.normalized_cover_id == packet.profile.cover_ref
            || cover.source_cover_id == packet.profile.cover_ref
    });
    let cover_refs = cover
        .map(|cover| cover.source_refs.clone())
        .unwrap_or_default();
    let nonzero_edges = cech_edges
        .iter()
        .filter(|edge| edge.value > 0 || !edge.support_atom_refs.is_empty())
        .collect::<Vec<_>>();
    let class_nonzero = packet
        .computed_invariants
        .iter()
        .find_map(|invariant| {
            invariant
                .get("observedCocycle")
                .and_then(|cocycle| cocycle.get("classNonzero"))
                .and_then(Value::as_bool)
        })
        .unwrap_or(false);
    let cocycle_support_atom_refs = nonzero_edges
        .iter()
        .flat_map(|edge| edge.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let forbidden_cages = forbidden_cage_projection(normalized, packet);
    let repair_morphs = repair_morph_projection(normalized, packet, &forbidden_cages);
    let locus_field = locus_field_projection(packet);
    let atom_glyphs = atom_glyph_projection(normalized);
    let analytic_overlay_bundle = analytic_overlay_bundle_projection(packet);
    let period_stokes = period_stokes_projection(packet);
    let spectrum_landscape = spectrum_landscape_projection(packet);
    let triangle_count = cover_nerve_projection["faces"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let field_row_count = locus_field["fieldRows"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let blocked_region_count = locus_field["blockedRegions"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let zero_region_count = locus_field["measuredZeroRegions"]
        .as_array()
        .map(Vec::len)
        .unwrap_or_default();
    let atom_glyph_total_count = normalized.atoms.len();
    let analytic_overlay_count = analytic_overlay_bundle["rawOverlayCount"]
        .as_u64()
        .unwrap_or_default() as usize;
    let period_stokes_meter_count =
        period_stokes["rawMeterCount"].as_u64().unwrap_or_default() as usize;
    let spectrum_cell_count = spectrum_landscape["rawCellCount"]
        .as_u64()
        .unwrap_or_default() as usize;
    let cocycle_support_edge_count = nonzero_edges.len();
    let cocycle_support_edges = nonzero_edges
        .iter()
        .take(GLUING_COCYCLE_EDGE_RENDER_LIMIT)
        .map(|edge| {
            json!({
                "edgeId": edge.edge_id,
                "sourceContextRef": edge.source_context,
                "targetContextRef": edge.target_context,
                "value": edge.value,
                "supportAtomRefs": edge.support_atom_refs
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-viewer-gluing-geometry/v0.5.4",
        "sourcePacketRef": "archsig-measurement-packet.json",
        "sourceInsightReportRef": "archsig-insight-report.json",
        "projectionBoundary": "This geometry translates measured packet and ArchMap cover support into viewer objects. It adds no structural verdict or monodromy verdict; H2 coherence color appears only when projected from ag.coherence-obstruction packet verdicts.",
        "nerve": {
            "coverRef": packet.profile.cover_ref,
            "sourceRefs": cover_refs,
            "vertices": cover_nerve_projection["vertices"],
            "edges": cover_nerve_projection["edges"],
            "triangles": cover_nerve_projection["faces"],
            "triangleSource": cover_nerve_projection["faceSource"],
            "h2CoherenceVisualized": cover_nerve_projection["h2CoherenceVisualized"]
        },
        "cocycleRibbon": {
            "supportAtomRefs": cocycle_support_atom_refs,
            "supportEdges": cocycle_support_edges,
            "closureGapEncoding": {
                "kind": "holonomyLikeGapMarker",
                "visible": class_nonzero && !nonzero_edges.is_empty(),
                "lineRole": "thick_glowing_dashed_seam",
                "source": "observedCocycle.classNonzero plus representative support from packet",
                "nonClaim": "Exploratory restriction-path closure gap only; monodromy verdict is not generated."
            }
        },
        "locusField": locus_field,
        "forbiddenCages": forbidden_cages,
        "repairMorphs": repair_morphs,
        "atomGlyphs": atom_glyphs,
        "analyticOverlayBundle": analytic_overlay_bundle,
        "periodStokes": period_stokes,
        "spectrumLandscape": spectrum_landscape,
        "visualEncodingLegend": visual_encoding_legend_v1(),
        "renderLimits": {
            "nerveTriangles": GLUING_TRIANGLE_RENDER_LIMIT,
            "cocycleSupportEdges": GLUING_COCYCLE_EDGE_RENDER_LIMIT,
            "curvatureFieldRows": GLUING_FIELD_ROW_RENDER_LIMIT,
            "curvatureRegions": GLUING_REGION_RENDER_LIMIT,
            "forbiddenCages": GLUING_CAGE_RENDER_LIMIT,
            "repairMorphs": GLUING_MORPH_RENDER_LIMIT,
            "atomGlyphs": GLUING_ATOM_GLYPH_RENDER_LIMIT,
            "analyticOverlays": ANALYTIC_OVERLAY_RENDER_LIMIT,
            "periodStokesMeters": PERIOD_STOKES_METER_RENDER_LIMIT,
            "spectrumCells": GLUING_FIELD_ROW_RENDER_LIMIT
        },
        "omittedGeometryCounts": {
            "nerveTriangles": triangle_count.saturating_sub(GLUING_TRIANGLE_RENDER_LIMIT),
            "cocycleSupportEdges": cocycle_support_edge_count.saturating_sub(GLUING_COCYCLE_EDGE_RENDER_LIMIT),
            "curvatureFieldRows": field_row_count.saturating_sub(GLUING_FIELD_ROW_RENDER_LIMIT),
            "measuredZeroRegions": zero_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "blockedRegions": blocked_region_count.saturating_sub(GLUING_REGION_RENDER_LIMIT),
            "forbiddenCages": forbidden_cages.len().saturating_sub(GLUING_CAGE_RENDER_LIMIT),
            "repairMorphs": repair_morphs.len().saturating_sub(GLUING_MORPH_RENDER_LIMIT),
            "atomGlyphs": atom_glyph_total_count.saturating_sub(GLUING_ATOM_GLYPH_RENDER_LIMIT),
            "analyticOverlays": analytic_overlay_count.saturating_sub(ANALYTIC_OVERLAY_RENDER_LIMIT),
            "periodStokesMeters": period_stokes_meter_count.saturating_sub(PERIOD_STOKES_METER_RENDER_LIMIT),
            "spectrumCells": spectrum_cell_count.saturating_sub(GLUING_FIELD_ROW_RENDER_LIMIT)
        },
        "nonClaims": [
            "No H2 coherence failure is visualized by this projection.",
            "Holonomy-like ribbon display is not a monodromy verdict.",
            "Repair morphs are lower-bound inspection aids, not automatic repairs."
        ]
    })
}

fn context_atom_refs(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &[String],
) -> BTreeMap<String, Vec<String>> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    normalized
        .contexts
        .iter()
        .filter(|context| selected.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().take(24).cloned().collect(),
            )
        })
        .collect()
}

fn forbidden_cage_projection(
    _normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
) -> Vec<Value> {
    let mut cages = Vec::new();
    for invariant in &packet.computed_invariants {
        let generators = invariant["obstructionIdeal"]["generators"]
            .as_array()
            .into_iter()
            .flatten();
        for generator in generators {
            let support_atom_refs = string_array_at(generator, &["supportAtomRefs"]);
            let support_variables = string_array_at(generator, &["support"]);
            // Declared support variables do not create measured geometry. A
            // cage is projected only when the packet carries observed atom
            // references for that generator.
            if support_atom_refs.is_empty() {
                continue;
            }
            let generator_id = string_field(generator, "generatorId");
            cages.push(json!({
                "cageId": format!("forbidden-cage:{generator_id}"),
                "atomRefs": support_atom_refs,
                "supportVariables": support_variables,
                "sourceInvariantRef": invariant["invariantId"],
                "sourceGeneratorRef": generator_id,
                "shapeRole": "cage",
                "lineRole": "broken_line",
                "source": "packet obstructionIdeal.generators[].supportAtomRefs/support"
            }));
        }
    }
    cages
}

fn repair_morph_projection(
    _normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    forbidden_cages: &[Value],
) -> Vec<Value> {
    if forbidden_cages.is_empty() {
        return Vec::new();
    }
    let lower_bound_readings = packet
        .analytic_readings
        .iter()
        .filter(|reading| {
            reading.reading_id.contains("repair")
                || reading.evaluator.contains("support-transfer")
                || reading.value.to_string().contains("lower-bound")
        })
        .collect::<Vec<_>>();
    let repair_candidates = packet
        .computed_invariants
        .iter()
        .flat_map(|invariant| {
            invariant["alexanderDualRepair"]["minimalHittingSets"]
                .as_array()
                .into_iter()
                .flatten()
                .enumerate()
                .map(|(index, hitting_set)| {
                    json!({
                        "candidateId": format!("{}:repair-candidate:{index}", string_field(invariant, "invariantId")),
                        "sourceInvariantRef": invariant["invariantId"],
                        "supportVariables": hitting_set
                            .as_array()
                            .into_iter()
                            .flatten()
                            .filter_map(Value::as_str)
                            .map(ToOwned::to_owned)
                            .collect::<Vec<_>>()
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    repair_candidates
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| {
            let candidate_variables = string_array_at(candidate, &["supportVariables"]);
            let related_cages = related_forbidden_cages(forbidden_cages, candidate);
            if related_cages.is_empty() {
                return None;
            }
            let from_cage_ref = related_cages
                .get(index % related_cages.len().max(1))
                .or_else(|| related_cages.first())
                .cloned()?;
            let from_atom_refs = related_cages
                .iter()
                .filter_map(|cage_id| {
                    forbidden_cages
                        .iter()
                        .find(|cage| cage["cageId"] == *cage_id)
                })
                .flat_map(|cage| string_array_at(cage, &["atomRefs"]))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            Some(json!({
                "morphId": format!("repair-morph:{}", string_field(candidate, "candidateId")),
                "fromCageRef": from_cage_ref,
                "fromCageRefs": related_cages,
                "fromAtomRefs": from_atom_refs,
                "toCandidateRef": candidate["candidateId"],
                "supportVariables": candidate_variables,
                "sourceInvariantRef": candidate["sourceInvariantRef"],
                "lowerBoundReadingRefs": lower_bound_readings
                    .iter()
                    .map(|reading| reading.reading_id.clone())
                    .take(8)
                    .collect::<Vec<_>>(),
                "animationRole": "continuous_morph_lower_bound",
                "samplePhase": index,
                "nonClaim": "not automatic repair"
            }))
        })
        .collect()
}

fn analytic_overlay_bundle_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut period_pairing = Vec::new();
    let mut transfer_cost = Vec::new();
    let mut spectral_gap = Vec::new();
    let mut curvature_hotspot = Vec::new();

    for reading in &packet.analytic_readings {
        let reading_kind = string_at(&reading.value, &["readingKind"]);
        match reading_kind.as_str() {
            "strict-period-pairing@1" => {
                period_pairing.push(json!({
                    "overlayId": format!("overlay:period-pairing:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "period_pairing_matrix",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "forms": reading.value["forms"].clone(),
                    "cycleBasis": reading.value["cycleBasis"].clone(),
                    "periodPairingMatrix": reading.value["periodPairingMatrix"].clone(),
                    "nonClaim": reading.value["nonConclusion"].clone(),
                    "projectionBoundary": "modelRelative period landscape; not a structural verdict"
                }));
            }
            "support-localized-transfer@1" => {
                transfer_cost.push(json!({
                    "overlayId": format!("overlay:transfer-cost:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "wasserstein_transfer_cost",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "repairPaths": reading.value["repairPaths"].clone(),
                    "transferTargets": reading.value["transferTargets"].clone(),
                    "transferMeasurementPairing": reading.value["transferMeasurementPairing"].clone(),
                    "transferResidue": reading.value["transferResidue"].clone(),
                    "wassersteinTransferCost": reading.value["wassersteinTransferCost"].clone(),
                    "nonClaim": "Wasserstein transfer cost is a supplied finite support-localized analytic reading under the selected cost model; it records a local transport cost.",
                    "projectionBoundary": reading.value["nonConclusion"].clone()
                }));
            }
            "graph-laplacian-hodge-proxy@1" => {
                spectral_gap.push(json!({
                    "overlayId": format!("overlay:spectral-gap:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "spectral_gap_proxy",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "cells": reading.value["cells"].clone(),
                    "spectralGap": reading.value["spectralGap"].clone(),
                    "harmonicMass": reading.value["harmonicMass"].clone(),
                    "distanceToFlatness": reading.value["distanceToFlatness"].clone(),
                    "nonClaim": "spectralGap is a finite graph-Laplacian proxy eigenvalue, not L1 and not measured_zero lawfulness.",
                    "projectionBoundary": reading.value["nonConclusion"].clone()
                }));
            }
            "curvature-transfer-perron-hotspot@1" => {
                curvature_hotspot.push(json!({
                    "overlayId": format!("overlay:curvature-hotspot:{}", stable_ref_segment(&reading.reading_id)),
                    "overlayKind": "curvature_spectrum_hotspot",
                    "sourceReadingRef": reading.reading_id,
                    "sourceEvaluator": reading.evaluator,
                    "sourceReadingKind": reading_kind,
                    "sourceRegime": reading.regime,
                    "colorRole": "analytic_reading",
                    "hotspots": reading.value["hotspots"].clone(),
                    "nonClaim": reading.value["nonConclusion"].clone(),
                    "projectionBoundary": "hotspot projection is gated by the landed theorem-candidate reading; it creates no structural verdict"
                }));
            }
            _ => {}
        }
    }

    let singularity_concentration = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.law-conflict-tor")
        .flat_map(|invariant| {
            invariant["lawConflicts"]
                .as_array()
                .into_iter()
                .flatten()
                .enumerate()
                .map(|(index, conflict)| {
                    let shared_support = string_array_at(conflict, &["sharedSupport"]);
                    json!({
                        "overlayId": format!(
                            "overlay:singularity-concentration:{}:{index}",
                            stable_ref_segment(&string_field(invariant, "invariantId"))
                        ),
                        "overlayKind": "singularity_concentration",
                        "sourceInvariantRef": invariant["invariantId"],
                        "sourceEvaluator": invariant["evaluator"],
                        "colorRole": "analytic_reading",
                        "stratumRef": if shared_support.is_empty() {
                            format!("law-conflict-stratum:{index}")
                        } else {
                            format!("law-conflict-stratum:{}", shared_support.join("+"))
                        },
                        "sharedSupport": shared_support,
                        "multidegree": conflict["multidegree"].clone(),
                        "commonAmbient": invariant["commonAmbient"].clone(),
                        "concentrationCount": 1,
                        "deformationRegime": "not_provided",
                        "nonClaim": "singularity concentration is a selected LawConflict_1 count projection only; deformation regime is not provided and this is not object size or repair difficulty."
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let raw_overlay_count = period_pairing.len()
        + transfer_cost.len()
        + spectral_gap.len()
        + curvature_hotspot.len()
        + singularity_concentration.len();

    period_pairing.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    transfer_cost.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    spectral_gap.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    curvature_hotspot.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);
    let mut singularity_concentration = singularity_concentration;
    singularity_concentration.truncate(ANALYTIC_OVERLAY_RENDER_LIMIT);

    let overlays = period_pairing
        .iter()
        .chain(transfer_cost.iter())
        .chain(spectral_gap.iter())
        .chain(curvature_hotspot.iter())
        .chain(singularity_concentration.iter())
        .take(ANALYTIC_OVERLAY_RENDER_LIMIT)
        .cloned()
        .collect::<Vec<_>>();

    json!({
        "schema": "archsig-analytic-overlay-bundle/v0.5.4",
        "allowlist": [
            "strict-period-pairing@1",
            "support-localized-transfer@1",
            "graph-laplacian-hodge-proxy@1",
            "curvature-transfer-perron-hotspot@1",
            "ag.law-conflict-tor/lawConflicts"
        ],
        "colorRole": "analytic_reading",
        "rawOverlayCount": raw_overlay_count,
        "projectionBoundary": "This bundle projects existing packet analytic readings and computed invariants into the viewer; it creates no structural verdict and never promotes analytic values to measured_zero.",
        "periodPairingOverlays": period_pairing,
        "transferCostOverlays": transfer_cost,
        "spectralGapOverlays": spectral_gap,
        "curvatureHotspotOverlays": curvature_hotspot,
        "singularityConcentrationOverlays": singularity_concentration,
        "overlays": overlays,
        "nonClaims": [
            "Period overlays are model-relative.",
            "Transfer cost overlays are finite support-localized readings, not global repair safety.",
            "Spectral gap overlays are proxy eigenvalues and are not structural lawfulness.",
            "Curvature hotspot overlays are theorem-candidate projections.",
            "Singularity concentration has deformationRegime=not_provided and is not a size or difficulty score."
        ]
    })
}

fn period_stokes_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let structural_verdict = packet
        .structural_verdict
        .iter()
        .find(|row| row.evaluator == "ag.period-stokes-audit");
    let structural_verdict_ref = structural_verdict.map(structural_verdict_ref);
    let structural_verdict_value = structural_verdict
        .map(|row| row.verdict.clone())
        .unwrap_or_else(|| "not_computed".to_string());
    let meters = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.period-stokes-audit")
        .take(PERIOD_STOKES_METER_RENDER_LIMIT)
        .enumerate()
        .map(|(index, invariant)| {
            let cycle_basis = string_array_at(invariant, &["cycleBasis"]);
            let forms = string_array_at(invariant, &["forms"]);
            let pairs = invariant["stokesAudit"]["pairs"]
                .as_array()
                .cloned()
                .unwrap_or_default();
            let audit_status = invariant["stokesAudit"]["status"]
                .as_str()
                .unwrap_or("unknown");
            let has_model = !cycle_basis.is_empty() && !pairs.is_empty();
            let meter_status = if audit_status == "checked" || audit_status == "residual_nonzero" {
                "structural_audit_projected"
            } else if audit_status == "unknown" && !cycle_basis.is_empty() {
                "analytic_only"
            } else if !has_model {
                "silent"
            } else {
                "analytic_only"
            };
            json!({
                "meterId": format!(
                    "period-stokes-meter:{}:{index}",
                    stable_ref_segment(&string_field(invariant, "invariantId"))
                ),
                "sourceInvariantRef": invariant["invariantId"],
                "sourceEvaluator": "ag.period-stokes-audit",
                "structuralVerdictRef": structural_verdict_ref.clone(),
                "structuralVerdict": structural_verdict_value.clone(),
                "meterStatus": meter_status,
                "auditStatus": audit_status,
                "colorRole": "analytic_reading",
                "modelRelative": true,
                "selectedCoverRef": invariant["selectedCoverRef"],
                "coefficient": invariant["coefficient"],
                "forms": forms,
                "cycleBasis": cycle_basis,
                "periodPairingMatrix": invariant["periodPairingMatrix"],
                "stokesAudit": invariant["stokesAudit"],
                "pairCount": pairs.len(),
                "maxAbsoluteResidual": invariant["stokesAudit"]["maxAbsoluteResidual"],
                "nonzeroPairCount": invariant["stokesAudit"]["nonzeroPairCount"],
                "nonClaim": "Stokes audit meter is modelRelative to the supplied finite period model; it visualizes packet audit residuals and creates no new structural verdict.",
                "projectionBoundary": "periodStokes projection carries M9 packet values only; analytic period arcs are not absolute periods and not lawfulness verdicts"
            })
        })
        .collect::<Vec<_>>();
    let active_meter_count = meters
        .iter()
        .filter(|meter| meter["meterStatus"] == "structural_audit_projected")
        .count();
    let raw_meter_count = packet
        .computed_invariants
        .iter()
        .filter(|invariant| invariant["evaluator"] == "ag.period-stokes-audit")
        .count();
    json!({
        "schema": "archsig-period-stokes-meter/v0.5.4",
        "sourceEvaluator": "ag.period-stokes-audit",
        "sourceAnalyticReadingKind": "strict-period-pairing@1",
        "colorRole": "analytic_reading",
        "modelRelative": true,
        "rawMeterCount": raw_meter_count,
        "activeMeterCount": active_meter_count,
        "meterCount": meters.len(),
        "meters": meters,
        "projectionBoundary": "This projection renders M9 Stokes audit values in the viewer; it does not create or modify structural verdict rows.",
        "nonClaims": [
            "Period arcs are modelRelative to the supplied finite period model.",
            "The meter reads packet stokesAudit pairs; it is not an absolute period invariant.",
            "Unknown or model-missing audits remain analytic-only or silent, never green structural closure."
        ]
    })
}

fn spectrum_landscape_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let hodge_reading = packet.analytic_readings.iter().find(|reading| {
        string_at(&reading.value, &["readingKind"]) == "graph-laplacian-hodge-proxy@1"
    });
    let hotspot_reading = packet.analytic_readings.iter().find(|reading| {
        string_at(&reading.value, &["readingKind"]) == "curvature-transfer-perron-hotspot@1"
    });
    let Some(reading) = hodge_reading else {
        return json!({
            "schema": "archsig-spectrum-landscape/v0.5.4",
            "status": "silent",
            "measurementStatus": "not_projected",
            "colorRole": "analytic_reading",
            "rawCellCount": 0,
            "cells": [],
            "hotspots": [],
            "projectionBoundary": "No M10 graph-laplacian-hodge-proxy reading is present; viewer remains silent and creates no structural verdict."
        });
    };
    let cells = string_array_at(&reading.value, &["cells"]);
    let cochain = reading.value["cochain"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let transfer_rows = reading.value["curvatureTransferSpectrum"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let transfer_by_cell = transfer_rows
        .iter()
        .filter_map(|row| {
            Some((
                string_field(row, "cell"),
                row["curvature"].as_f64().unwrap_or(0.0),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let cell_rows = cells
        .iter()
        .take(GLUING_FIELD_ROW_RENDER_LIMIT)
        .enumerate()
        .map(|(index, cell)| {
            let cochain_value = cochain.get(index).and_then(Value::as_f64).unwrap_or(0.0);
            let curvature = transfer_by_cell.get(cell).copied().unwrap_or(0.0);
            json!({
                "cellRef": cell,
                "axisRef": format!("spectrum-axis:{cell}"),
                "cochainValue": round_f64(cochain_value),
                "signedCurvature": round_f64(curvature),
                "plainRole": if cochain_value.abs() < 1.0e-9 {
                    "lawful_plain_measured_zero"
                } else {
                    "local_deviation"
                },
                "deterministicIndex": index,
                "colorRole": "analytic_reading",
                "measurementStatus": "proxy",
                "notLegacyStatusField": true
            })
        })
        .collect::<Vec<_>>();
    let hotspot_rows = hotspot_reading
        .map(|reading| {
            reading.value["hotspots"]
                .as_array()
                .into_iter()
                .flatten()
                .take(GLUING_FIELD_ROW_RENDER_LIMIT)
                .enumerate()
                .map(|(index, hotspot)| {
                    json!({
                        "hotspotId": format!(
                            "spectrum-hotspot:{}:{index}",
                            stable_ref_segment(&reading.reading_id)
                        ),
                        "cellRef": string_field(hotspot, "cell"),
                        "axisRef": format!("spectrum-axis:{}", string_field(hotspot, "cell")),
                        "hotspotWeight": hotspot["hotspotWeight"].clone(),
                        "status": "needsReview",
                        "measurementStatus": "proxy",
                        "colorRole": "analytic_reading",
                        "sourceReadingRef": reading.reading_id,
                        "sourceRegime": reading.regime,
                        "localDeviationSecondary": true
                    })
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let spectral_radius_value = reading
        .value
        .get("spectralRadius")
        .or_else(|| reading.value.get("spectralGap"))
        .cloned()
        .unwrap_or(Value::Null);
    let spectral_radius_numeric = spectrum_numeric_value(&spectral_radius_value);

    json!({
        "schema": "archsig-spectrum-landscape/v0.5.4",
        "status": "needsReview",
        "measurementStatus": "proxy",
        "sourceReadingRef": reading.reading_id,
        "sourceEvaluator": reading.evaluator,
        "sourceReadingKind": "graph-laplacian-hodge-proxy@1",
        "hotspotReadingRef": hotspot_reading.map(|reading| reading.reading_id.clone()),
        "hotspotReadingKind": hotspot_reading.map(|_| "curvature-transfer-perron-hotspot@1"),
        "selectedCoverRef": reading.value["selectedCoverRef"].clone(),
        "colorRole": "analytic_reading",
        "rawCellCount": cells.len(),
        "cells": cell_rows,
        "hotspots": hotspot_rows,
        "spectralGap": reading.value["spectralGap"].clone(),
        "spectralRadius": spectral_radius_value,
        "spectralRadiusNumeric": spectral_radius_numeric.map(round_f64),
        "axisPlacement": "axisRef-deterministic",
        "forbiddenFieldRefs": ["legacy-schema052-curvature-status"],
        "nonClaim": "Spectrum landscape is an analytic proxy reading; lawful plain and hotspots are not structural verdicts.",
        "projectionBoundary": "spectrumLandscape carries M10/M14 packet readings only; no legacy v0 status field is read and no structural verdict is created."
    })
}

fn spectrum_numeric_value(value: &Value) -> Option<f64> {
    value
        .as_f64()
        .or_else(|| value.as_str().and_then(|text| text.parse::<f64>().ok()))
        .filter(|value| value.is_finite())
}

fn related_forbidden_cages(forbidden_cages: &[Value], candidate: &Value) -> Vec<String> {
    let source_invariant = string_field(candidate, "sourceInvariantRef");
    let candidate_variables = string_array_at(candidate, &["supportVariables"])
        .into_iter()
        .collect::<BTreeSet<_>>();
    let mut related = forbidden_cages
        .iter()
        .filter(|cage| {
            cage["sourceInvariantRef"] == source_invariant
                && string_array_at(cage, &["supportVariables"])
                    .into_iter()
                    .any(|variable| candidate_variables.contains(&variable))
        })
        .filter_map(|cage| cage["cageId"].as_str().map(ToOwned::to_owned))
        .collect::<Vec<_>>();
    if related.is_empty() {
        related = forbidden_cages
            .iter()
            .filter(|cage| cage["sourceInvariantRef"] == source_invariant)
            .filter_map(|cage| cage["cageId"].as_str().map(ToOwned::to_owned))
            .collect();
    }
    related
}

fn locus_field_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut field_rows = packet
        .structural_verdict
        .iter()
        .enumerate()
        .filter(|(_, row)| row.evaluator.contains("curvature") || row.law.contains("curvature"))
        .map(|(index, row)| {
            json!({
                "fieldId": format!("curvature-field:{index}:{}", row.evaluator),
                "status": row.verdict,
                "height": if row.verdict == "measured_nonzero" { 1 } else { 0 },
                "colorRole": match row.verdict.as_str() {
                    "measured_nonzero" => "measured_nonzero",
                    "measured_zero" => "measured_zero",
                    "not_computed" => "not_computed",
                    "unmeasured" => "unmeasured",
                    _ => "unknown"
                },
                "source": "structural verdict curvature row"
            })
        })
        .collect::<Vec<_>>();
    field_rows.extend(analytic_locus_field_rows(packet));
    let blocked_regions = packet
        .structural_verdict
        .iter()
        .filter(|row| {
            matches!(
                row.verdict.as_str(),
                "unmeasured" | "unknown" | "not_computed"
            )
        })
        .map(|row| {
            json!({
                "regionId": format!("blocked-region:{}", row.evaluator),
                "status": row.verdict,
                "shapeRole": "blocked_unmeasured_region",
                "source": "non-terminal packet verdict"
            })
        })
        .collect::<Vec<_>>();
    let measured_zero_regions = packet
        .structural_verdict
        .iter()
        .filter(|row| row.verdict == "measured_zero")
        .map(|row| {
            json!({
                "regionId": format!("measured-zero-region:{}", row.evaluator),
                "status": row.verdict,
                "shapeRole": "smooth_measured_zero_patch",
                "source": "selected-support zero packet verdict"
            })
        })
        .collect::<Vec<_>>();
    json!({
        "fieldRows": field_rows,
        "measuredZeroRegions": measured_zero_regions,
        "blockedRegions": blocked_regions
    })
}

fn analytic_locus_field_rows(packet: &ArchSigMeasurementPacketV1) -> Vec<Value> {
    let mut rows = Vec::new();
    for reading in &packet.analytic_readings {
        let reading_kind = string_at(&reading.value, &["readingKind"]);
        if reading_kind != "graph-laplacian-hodge-proxy@1" {
            continue;
        }
        let harmonic_mass = reading.value["harmonicMass"].as_f64().unwrap_or(0.0);
        let distance_to_flatness = reading.value["distanceToFlatness"].as_f64().unwrap_or(0.0);
        let mass_height = harmonic_mass.max(distance_to_flatness);
        rows.push(json!({
            "fieldId": format!("curvature-mass:{}", reading.reading_id),
            "status": "analytic_reading",
            "height": round_f64(mass_height),
            "harmonicMass": round_f64(harmonic_mass),
            "distanceToFlatness": round_f64(distance_to_flatness),
            "colorRole": "analytic_reading",
            "sourceReadingRef": reading.reading_id,
            "source": "analytic reading harmonicMass / distanceToFlatness"
        }));
        for (index, transfer) in reading.value["curvatureTransferSpectrum"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
        {
            let curvature = transfer["curvature"].as_f64().unwrap_or(0.0);
            rows.push(json!({
                "fieldId": format!("curvature-support:{}:{index}", reading.reading_id),
                "status": "analytic_reading",
                "height": round_f64(curvature.abs()),
                "signedCurvature": round_f64(curvature),
                "cellRef": string_field(transfer, "cell"),
                "harmonicMass": round_f64(harmonic_mass),
                "distanceToFlatness": round_f64(distance_to_flatness),
                "colorRole": "analytic_reading",
                "sourceReadingRef": reading.reading_id,
                "source": "analytic reading curvatureTransferSpectrum support / mass"
            }));
        }
    }
    rows
}

fn atom_glyph_projection(normalized: &NormalizedArchMapV2) -> Vec<Value> {
    normalized
        .atoms
        .iter()
        .take(GLUING_ATOM_GLYPH_RENDER_LIMIT)
        .map(|atom| {
            let semantic_anchor_missing =
                atom.subject.is_empty() || atom.source_refs.is_empty() || atom.axis == "unknown";
            json!({
                "atomRef": atom.normalized_atom_id,
                "fiber": atom.atom_kind,
                "carrier": atom.subject,
                "valence": atom.context_memberships.len(),
                "semanticAnchor": if semantic_anchor_missing { "blocked_missing_anchor" } else { "source_backed" },
                "shapeRole": if semantic_anchor_missing { "blocked_anchor_glyph" } else { "structured_atom_glyph" },
                "fiberShapeRole": format!("fiber_shape:{}", atom.atom_kind),
                "carrierColorRole": format!("carrier_color:{}", slug(&atom.subject)),
                "sizeRole": "valence",
                "colorRole": if semantic_anchor_missing { "not_computed" } else { "source_evidence" }
            })
        })
        .collect()
}

fn overview_color_role(cards: &[Value]) -> &'static str {
    let top_kind = cards.first().map(|card| string_field(card, "kind"));
    match top_kind.as_deref() {
        Some("global_glue_mismatch")
        | Some("minimal_repair_candidate")
        | Some("policy_conflict") => "measured_nonzero",
        Some("no_measured_glue_mismatch") | Some("confirmed_zero") => "measured_zero",
        Some("not_computed_blocker") => "not_computed",
        Some("architecture_debt_mass") => "analytic_reading",
        Some("measurement_boundary") => "unknown",
        _ => "checked",
    }
}

fn scene_refs_for_kinds(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
    kinds: &[&str],
    include_samples: bool,
) -> Value {
    let kind_set = kinds.iter().copied().collect::<BTreeSet<_>>();
    let mut insight_refs = Vec::new();
    let mut atom_refs = BTreeSet::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();

    for card in cards
        .iter()
        .filter(|card| kind_set.contains(string_field(card, "kind").as_str()))
    {
        insight_refs.push(string_field(card, "id"));
        for atom_ref in string_array_at(card, &["evidence", "atomRefs"]) {
            atom_refs.insert(atom_ref);
        }
        for context_ref in string_array_at(card, &["evidence", "contextRefs"]) {
            context_refs.insert(context_ref);
        }
        for source_ref in string_array_at(card, &["evidence", "sourceRefs"]) {
            source_refs.insert(source_ref);
        }
    }

    if include_samples {
        atom_refs.extend(top_atom_refs(normalized));
        context_refs.extend(top_context_refs(normalized));
        source_refs.extend(top_source_refs(normalized));
    }

    json!({
        "insightRefs": insight_refs,
        "atomRefs": atom_refs.into_iter().take(24).collect::<Vec<_>>(),
        "contextRefs": context_refs.into_iter().take(16).collect::<Vec<_>>(),
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": source_refs.into_iter().take(20).collect::<Vec<_>>()
    })
}

fn source_scene_refs(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    cards: &[Value],
) -> Value {
    let mut insight_refs = Vec::new();
    let mut atom_refs = BTreeSet::new();
    let mut context_refs = BTreeSet::new();
    let mut source_refs = BTreeSet::new();
    for card in cards
        .iter()
        .filter(|card| !string_array_at(card, &["evidence", "sourceRefs"]).is_empty())
    {
        insight_refs.push(string_field(card, "id"));
        for atom_ref in string_array_at(card, &["evidence", "atomRefs"]) {
            atom_refs.insert(atom_ref);
        }
        for context_ref in string_array_at(card, &["evidence", "contextRefs"]) {
            context_refs.insert(context_ref);
        }
        for source_ref in string_array_at(card, &["evidence", "sourceRefs"]) {
            source_refs.insert(source_ref);
        }
    }
    if source_refs.is_empty() {
        source_refs.extend(top_source_refs(normalized));
    }
    json!({
        "insightRefs": insight_refs,
        "atomRefs": atom_refs.into_iter().take(24).collect::<Vec<_>>(),
        "contextRefs": context_refs.into_iter().take(16).collect::<Vec<_>>(),
        "coverRefs": [packet.profile.cover_ref.clone()],
        "sourceRefs": source_refs.into_iter().take(20).collect::<Vec<_>>()
    })
}

fn scene_v1(
    scene_id: &str,
    kind: &str,
    title: &str,
    user_question: &str,
    axis: (&str, &str, &str),
    layer_kind: &str,
    geometry_role: &str,
    click_target_kind: &str,
    text_role: &str,
    primary_refs: &Value,
    color_role: &str,
    shape_role: &str,
    line_role: &str,
    active: bool,
) -> Value {
    json!({
        "sceneId": scene_id,
        "kind": kind,
        "title": title,
        "sceneStatus": if active { "active" } else { "not_active_for_packet" },
        "userQuestion": user_question,
        "axisMapping": { "x": axis.0, "y": axis.1, "z": axis.2 },
        "primaryRefs": primary_refs,
        "layers": [{
            "layerId": format!("layer:{scene_id}:{layer_kind}"),
            "kind": layer_kind,
            "geometryRole": geometry_role,
            "encodingRef": format!("encoding:{scene_id}:main"),
            "clickTargetKind": click_target_kind,
            "refs": primary_refs,
            "omissionPolicy": if active { "preserve_for_top_insight" } else { "omittable_background" },
            "animationPurpose": if active { "navigation" } else { "orientation" }
        }],
        "visualEncodings": [{
            "encodingId": format!("encoding:{scene_id}:main"),
            "colorRole": if active { color_role } else { "not_applicable" },
            "shapeRole": shape_role,
            "lineRole": line_role,
            "textRole": if active { text_role.to_string() } else { format!("not active for this packet: {text_role}") }
        }],
        "boundaryDigestRef": "boundary-digest:main"
    })
}

fn with_scene_non_claims(mut scene: Value, non_claims: &[&str]) -> Value {
    scene["nonClaims"] = json!(non_claims);
    scene
}

fn boundary_scene_v1(primary_refs: &Value) -> Value {
    let states = [
        (
            "checked",
            "checked_boundary_surface",
            "surface",
            "boundaryChecked",
            "checked evidence boundary",
            "checked",
            "solid_surface",
            "thin_line",
        ),
        (
            "assumed",
            "assumed_boundary_surface",
            "surface",
            "boundaryAssumed",
            "assumed profile boundary",
            "assumed",
            "translucent_surface",
            "thin_line",
        ),
        (
            "unknown",
            "unknown_boundary_region",
            "region",
            "boundaryUnknown",
            "unknown unresolved region",
            "unknown",
            "grey_region",
            "broken_line",
        ),
        (
            "unmeasured",
            "unmeasured_boundary_fog",
            "fog",
            "boundaryUnmeasured",
            "unmeasured support",
            "unmeasured",
            "fog",
            "dotted_line",
        ),
        (
            "not_computed",
            "not_computed_blocking_wall",
            "wall",
            "boundaryNotComputed",
            "not_computed blocker reason",
            "not_computed",
            "blocking_wall",
            "broken_line",
        ),
        (
            "violated",
            "violated_boundary",
            "broken_boundary",
            "boundaryViolated",
            "violated assumption",
            "violated",
            "red_broken_boundary",
            "broken_line",
        ),
    ];
    json!({
        "sceneId": "boundary-assumption",
        "kind": "boundary_assumption",
        "title": "Boundary",
        "sceneStatus": "active",
        "userQuestion": "Which regions are checked, assumed, unknown, unmeasured, not_computed, or violated?",
        "axisMapping": {
            "x": "input contract",
            "y": "assumption status",
            "z": "blocker intensity"
        },
        "primaryRefs": primary_refs,
        "layers": states.iter().map(|(state, layer_kind, geometry_role, click_target_kind, _, _, _, _)| json!({
            "layerId": format!("layer:boundary-assumption:{state}"),
            "kind": layer_kind,
            "boundaryState": state,
            "geometryRole": geometry_role,
            "encodingRef": format!("encoding:boundary-assumption:{state}"),
            "clickTargetKind": click_target_kind,
            "refs": primary_refs,
            "omissionPolicy": "preserve_for_top_insight",
            "animationPurpose": "navigation"
        })).collect::<Vec<_>>(),
        "visualEncodings": states.iter().map(|(state, _, _, _, text_role, color_role, shape_role, line_role)| json!({
            "encodingId": format!("encoding:boundary-assumption:{state}"),
            "boundaryState": state,
            "colorRole": color_role,
            "shapeRole": shape_role,
            "lineRole": line_role,
            "textRole": text_role
        })).collect::<Vec<_>>(),
        "boundaryDigestRef": "boundary-digest:main",
        "nonClaims": [
            "Boundary states qualify the selected measurement profile; they are not inferred source facts.",
            "Unmeasured, unknown, not_computed, and violated states are not measured zero."
        ]
    })
}

fn insight_guided_tours_v1(cards: &[Value]) -> Vec<Value> {
    cards
        .iter()
        .map(|card| {
            let tour_id = format!("tour:{}", string_field(card, "id").trim_start_matches("insight:"));
            json!({
                "tourId": tour_id,
                "title": string_field(card, "title"),
                "insightRefs": [string_field(card, "id")],
                "steps": [
                    {
                        "sceneId": "site-cover",
                        "caption": "These contexts form the selected cover.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": card["viewerNavigation"]["sceneId"],
                        "caption": "This scene highlights the measured support or blocker.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": "source-evidence",
                        "caption": "These source refs ground the insight.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    },
                    {
                        "sceneId": "boundary-assumption",
                        "caption": "This boundary explains what is checked, assumed, unknown, unmeasured, or not_computed.",
                        "highlightRefs": card["viewerNavigation"]["highlightRefs"]
                    }
                ]
            })
        })
        .collect()
}

fn insight_copy_blocks_v1(
    normalized: &NormalizedArchMapV2,
    cards: &[Value],
    boundary_digest: &Value,
) -> Value {
    let mut source_refs = cards
        .iter()
        .flat_map(|card| string_array_at(card, &["evidence", "sourceRefs"]))
        .chain(top_source_refs(normalized))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    source_refs.truncate(20);
    json!({
        "sourceRefs": source_refs,
        "llmHandoff": {
            "instruction": "Use the following ArchSig result as bounded evidence. Do not infer beyond the listed claims and boundaries.",
            "boundary": boundary_digest["shortText"],
            "topInsights": cards.iter().take(3).map(|card| string_field(card, "oneLine")).collect::<Vec<_>>()
        }
    })
}

fn insight_refs_for_row(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> (
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
    Vec<String>,
) {
    let row_invariants = invariant_values_for_row(packet, row);
    let mut packet_atom_refs = collect_packet_refs_from_values(
        &row_invariants,
        &[
            "supportAtomRefs",
            "mismatchSupportRefs",
            "witnessSupportRefs",
            "atomRefs",
            "atomRef",
        ],
    );
    packet_atom_refs.extend(atom_refs_for_row(normalized, row));
    let atom_refs = normalize_atom_refs(normalized, packet_atom_refs);
    let mut context_refs = context_refs_for_atoms(normalized, &atom_refs);
    context_refs.extend(normalize_context_refs(
        normalized,
        collect_packet_refs_from_values(
            &row_invariants,
            &[
                "contextRefs",
                "contextRef",
                "selectedContexts",
                "sourceContext",
                "targetContext",
            ],
        ),
    ));
    context_refs = sorted_truncated(context_refs, 8);
    let mut source_refs = source_refs_for_atoms(normalized, &atom_refs);
    source_refs.extend(
        collect_packet_refs_from_values(&row_invariants, &["sourceRefs", "sourceRef"])
            .into_iter()
            .map(|source_ref| sanitize_source_ref(&source_ref)),
    );
    source_refs = sorted_truncated(source_refs, 10);
    let mut target_refs = atom_refs.clone();
    target_refs.extend(context_refs.clone());
    if target_refs.is_empty() {
        target_refs.push(structural_verdict_ref(row));
    }
    (
        invariant_refs_for_values(&row_invariants),
        analytic_reading_refs_for_row(packet, row),
        assumption_refs(packet),
        source_refs,
        atom_refs,
        context_refs,
        target_refs,
    )
}

fn atom_refs_for_row(normalized: &NormalizedArchMapV2, row: &AgStructuralVerdictV1) -> Vec<String> {
    let evaluator_hint = evaluator_hint(&row.evaluator);
    let refs = normalized
        .atoms
        .iter()
        .filter(|atom| {
            evaluator_hint
                .is_some_and(|hint| atom.axis.contains(hint) || atom.predicate.contains(hint))
                || row
                    .verdict_data
                    .cert_ref
                    .as_deref()
                    .is_some_and(|cert| cert.contains(&atom.source_atom_id))
        })
        .map(|atom| atom.normalized_atom_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.into_iter().take(12).collect()
}

fn context_refs_for_atoms(normalized: &NormalizedArchMapV2, atom_refs: &[String]) -> Vec<String> {
    let atoms = atom_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut refs = normalized
        .contexts
        .iter()
        .filter(|context| {
            context
                .atom_ids
                .iter()
                .any(|atom| atoms.contains(atom.as_str()))
        })
        .map(|context| context.normalized_context_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.truncate(8);
    refs
}

fn source_refs_for_atoms(normalized: &NormalizedArchMapV2, atom_refs: &[String]) -> Vec<String> {
    let atoms = atom_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut refs = normalized
        .atoms
        .iter()
        .filter(|atom| atoms.contains(atom.normalized_atom_id.as_str()))
        .flat_map(|atom| {
            atom.source_refs
                .iter()
                .map(|source_ref| sanitize_source_ref(source_ref))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    refs.truncate(10);
    refs
}

fn structural_verdict_ref(row: &AgStructuralVerdictV1) -> String {
    format!(
        "structuralVerdict/{}/{}/{}",
        stable_ref_segment(&row.evaluator),
        stable_ref_segment(&row.law),
        stable_ref_segment(&row.verdict_data.method_status)
    )
}

fn stable_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect::<String>()
        .trim_matches('-')
        .to_string()
}

fn evaluator_hint(evaluator: &str) -> Option<&'static str> {
    if evaluator.contains("cech") {
        Some("cech")
    } else if evaluator.contains("square-free") || evaluator.contains("square_free") {
        Some("square")
    } else if evaluator.contains("tor") {
        Some("tor")
    } else if evaluator.contains("laplacian") {
        Some("laplacian")
    } else if evaluator.contains("period") {
        Some("period")
    } else if evaluator.contains("transfer") {
        Some("transfer")
    } else {
        None
    }
}

fn invariant_values_for_row(
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> Vec<Value> {
    let cert_invariant = row
        .verdict_data
        .cert_ref
        .as_deref()
        .and_then(|cert_ref| cert_ref.strip_prefix("computedInvariants/"));
    let hint = evaluator_hint(&row.evaluator);
    packet
        .computed_invariants
        .iter()
        .filter(|value| {
            let invariant_id = value["invariantId"].as_str().unwrap_or_default();
            cert_invariant.is_some_and(|cert| cert == invariant_id)
                || value["evaluator"].as_str() == Some(row.evaluator.as_str())
                || hint.is_some_and(|hint| invariant_id.contains(hint))
        })
        .cloned()
        .collect()
}

fn invariant_refs_for_values(values: &[Value]) -> Vec<String> {
    values
        .iter()
        .filter_map(|value| value["invariantId"].as_str())
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn analytic_reading_refs_for_row(
    packet: &ArchSigMeasurementPacketV1,
    row: &AgStructuralVerdictV1,
) -> Vec<String> {
    packet
        .analytic_readings
        .iter()
        .filter(|reading| {
            reading.evaluator == row.evaluator
                || reading.structural_verdict_ref.as_deref() == row.verdict_data.cert_ref.as_deref()
                || evaluator_hint(&row.evaluator)
                    .is_some_and(|hint| reading.reading_id.contains(hint))
        })
        .map(|reading| reading.reading_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn collect_packet_refs_from_values(values: &[Value], keys: &[&str]) -> Vec<String> {
    let key_set = keys.iter().copied().collect::<BTreeSet<_>>();
    let mut refs = BTreeSet::new();
    for value in values {
        collect_packet_refs(value, &key_set, &mut refs);
    }
    refs.into_iter().collect()
}

fn collect_packet_refs(value: &Value, keys: &BTreeSet<&str>, refs: &mut BTreeSet<String>) {
    match value {
        Value::Object(object) => {
            for (key, nested) in object {
                if keys.contains(key.as_str()) {
                    collect_strings(nested, refs);
                }
                collect_packet_refs(nested, keys, refs);
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_packet_refs(item, keys, refs);
            }
        }
        _ => {}
    }
}

fn collect_strings(value: &Value, refs: &mut BTreeSet<String>) {
    match value {
        Value::String(value) => {
            refs.insert(value.clone());
        }
        Value::Array(items) => {
            for item in items {
                collect_strings(item, refs);
            }
        }
        _ => {}
    }
}

fn normalize_atom_refs(normalized: &NormalizedArchMapV2, refs: Vec<String>) -> Vec<String> {
    let by_source = normalized
        .atoms
        .iter()
        .map(|atom| {
            (
                atom.source_atom_id.as_str(),
                atom.normalized_atom_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let normalized_ids = normalized
        .atoms
        .iter()
        .map(|atom| atom.normalized_atom_id.as_str())
        .collect::<BTreeSet<_>>();
    refs.into_iter()
        .filter_map(|atom_ref| {
            if normalized_ids.contains(atom_ref.as_str()) {
                Some(atom_ref)
            } else {
                by_source.get(atom_ref.as_str()).cloned()
            }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn normalize_context_refs(normalized: &NormalizedArchMapV2, refs: Vec<String>) -> Vec<String> {
    let by_source = normalized
        .contexts
        .iter()
        .map(|context| {
            (
                context.source_context_id.as_str(),
                context.normalized_context_id.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let normalized_ids = normalized
        .contexts
        .iter()
        .map(|context| context.normalized_context_id.as_str())
        .collect::<BTreeSet<_>>();
    refs.into_iter()
        .filter_map(|context_ref| {
            if normalized_ids.contains(context_ref.as_str()) {
                Some(context_ref)
            } else {
                by_source.get(context_ref.as_str()).cloned()
            }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(8)
        .collect()
}

fn sorted_truncated(refs: Vec<String>, limit: usize) -> Vec<String> {
    refs.into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(limit)
        .collect()
}

fn sanitize_source_ref(source_ref: &str) -> String {
    if is_local_or_private_source_ref(source_ref) {
        "source-ref:redacted-local-path".to_string()
    } else {
        source_ref.to_string()
    }
}

fn is_local_or_private_source_ref(source_ref: &str) -> bool {
    source_ref.starts_with("file:")
        || source_ref.starts_with('/')
        || source_ref.starts_with("~/")
        || source_ref.starts_with("../")
        || source_ref.contains("/../")
        || source_ref.contains('\\')
        || [
            "docs/",
            "tools/",
            "src/",
            "tests/",
            "research/",
            "Formal/",
            "paper/",
            "website/",
            "outreach/",
        ]
        .iter()
        .any(|prefix| source_ref.starts_with(prefix))
        || looks_like_windows_drive_path(source_ref)
        || has_hidden_path_segment(source_ref)
}

fn looks_like_windows_drive_path(source_ref: &str) -> bool {
    let bytes = source_ref.as_bytes();
    bytes.len() >= 3
        && bytes[0].is_ascii_alphabetic()
        && bytes[1] == b':'
        && matches!(bytes[2], b'/' | b'\\')
}

fn has_hidden_path_segment(source_ref: &str) -> bool {
    source_ref
        .split(['/', '\\'])
        .any(|segment| segment.starts_with('.') && segment != "." && segment != "..")
}

fn invariant_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .computed_invariants
        .iter()
        .filter_map(|value| value["invariantId"].as_str())
        .map(ToOwned::to_owned)
        .take(12)
        .collect()
}

fn analytic_reading_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .analytic_readings
        .iter()
        .map(|reading| reading.reading_id.clone())
        .take(12)
        .collect()
}

fn assumption_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .assumptions
        .iter()
        .map(|assumption| assumption.theorem_ref.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn evaluator_refs(packet: &ArchSigMeasurementPacketV1) -> Vec<String> {
    packet
        .structural_verdict
        .iter()
        .map(|row| row.evaluator.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn top_atom_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .map(|atom| atom.normalized_atom_id.clone())
        .take(8)
        .collect()
}

fn top_context_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .contexts
        .iter()
        .map(|context| context.normalized_context_id.clone())
        .take(8)
        .collect()
}

fn top_source_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .flat_map(|atom| {
            atom.source_refs
                .iter()
                .map(|source_ref| sanitize_source_ref(source_ref))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .take(12)
        .collect()
}

fn insight_sample_refs(normalized: &NormalizedArchMapV2) -> Value {
    json!({
        "atomRefs": top_atom_refs(normalized),
        "contextRefs": top_context_refs(normalized),
        "sourceRefs": top_source_refs(normalized),
        "note": "Sample refs support orientation only; measured insight evidence is listed under evidence."
    })
}

fn assumption_row(row: &AgAssumptionLedgerEntryV1) -> Value {
    json!({
        "theoremRef": row.theorem_ref,
        "assumption": row.assumption,
        "status": row.status,
        "checkedBy": row.checked_by,
        "assumedBy": row.assumed_by
    })
}

fn insight_rank(card: &Value) -> usize {
    match string_field(card, "kind").as_str() {
        "validation_failure" => 800,
        "global_glue_mismatch" => 700,
        "not_computed_blocker" => 650,
        "repair_lower_bound" | "minimal_repair_candidate" => 600,
        "policy_conflict" => 500,
        "architecture_debt_mass" => 400,
        "no_measured_glue_mismatch" => 300,
        "measurement_boundary" => 200,
        _ => 100,
    }
}

fn insight_decision_state(card: &Value) -> &'static str {
    match string_field(card, "severity").as_str() {
        "high" => "needs_attention",
        "medium" => "review_boundary",
        _ => "informational",
    }
}

fn empty_insight_evidence() -> Value {
    json!({
        "structuralVerdictRefs": [],
        "computedInvariantRefs": [],
        "analyticReadingRefs": [],
        "assumptionRefs": [],
        "sourceRefs": [],
        "atomRefs": [],
        "contextRefs": [],
        "coverRefs": [],
        "evaluatorRefs": []
    })
}

fn empty_highlight_refs() -> Value {
    json!({
        "atomRefs": [],
        "contextRefs": [],
        "sourceRefs": []
    })
}

fn string_field(value: &Value, field: &str) -> String {
    value[field].as_str().unwrap_or_default().to_string()
}

fn string_at(value: &Value, path: &[&str]) -> String {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current
        .as_str()
        .map(ToOwned::to_owned)
        .unwrap_or_else(|| current.to_string())
}

fn number_at(value: &Value, path: &[&str]) -> u64 {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current.as_u64().unwrap_or(0)
}

fn string_array_at(value: &Value, path: &[&str]) -> Vec<String> {
    let mut current = value;
    for key in path {
        current = &current[*key];
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str().map(ToOwned::to_owned))
        .collect()
}

fn slug(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
}
