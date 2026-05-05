use std::collections::{BTreeMap, BTreeSet};

use crate::repair_rule::static_repair_rule_registry;
use crate::schema_versioning::feature_report_schema_compatibility_metadata;
use crate::theorem_precondition::build_theorem_precondition_check_report;
use crate::{
    AirClaim, AirDocumentV0, AirEvidence, AirRelation, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    FeatureExtensionReportV0, FeatureReportArchitectureSummary, FeatureReportCoverageGap,
    FeatureReportEdgeRef, FeatureReportEvidenceRef, FeatureReportGeneratedPatchOperation,
    FeatureReportGeneratedPatchReviewWarning, FeatureReportGeneratedPatchSummary,
    FeatureReportInput, FeatureReportInterpretedExtension, FeatureReportInvariant,
    FeatureReportObstructionWitness, FeatureReportRepairSuggestion, FeatureReportReviewSummary,
    FeatureReportRuntimeSummary, FeatureReportSemanticDiagramSummary,
    FeatureReportSemanticNonfillabilityWitnessSummary, FeatureReportSemanticPathSummary,
    RepairRuleV0, TheoremPreconditionCheck,
};

pub fn build_feature_extension_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> FeatureExtensionReportV0 {
    let claim_by_id: BTreeMap<String, &AirClaim> = document
        .claims
        .iter()
        .map(|claim| (claim.claim_id.clone(), claim))
        .collect();
    let evidence_by_id: BTreeMap<String, &AirEvidence> = document
        .evidence
        .iter()
        .map(|evidence| (evidence.evidence_id.clone(), evidence))
        .collect();

    let preserved_invariants = feature_report_preserved_invariants(document);
    let changed_invariants = feature_report_changed_invariants(document);
    let introduced_obstruction_witnesses =
        feature_report_obstruction_witnesses(document, &claim_by_id, &evidence_by_id);
    let coverage_gaps = feature_report_coverage_gaps(document);
    let split_status = feature_report_split_status(
        document,
        &preserved_invariants,
        &changed_invariants,
        &introduced_obstruction_witnesses,
    );
    let theorem_package_refs = feature_report_theorem_package_refs(document);
    let theorem_precondition_report = build_theorem_precondition_check_report(document, input_path);
    let discharged_assumptions = feature_report_discharged_assumptions(document);
    let undischarged_assumptions =
        feature_report_undischarged_assumptions(document, &theorem_precondition_report.checks);
    let unsupported_constructs = feature_report_unsupported_constructs(&coverage_gaps);
    let repair_suggestions =
        feature_report_repair_suggestions(&introduced_obstruction_witnesses, &coverage_gaps);
    let non_conclusions = feature_report_non_conclusions(document, &split_status, &coverage_gaps);
    let measured_axes = document
        .signature
        .axes
        .iter()
        .filter(|axis| axis.measured)
        .map(|axis| axis.axis.clone())
        .collect();
    let unmeasured_axes = document
        .signature
        .axes
        .iter()
        .filter(|axis| !axis.measured)
        .map(|axis| axis.axis.clone())
        .collect();
    let runtime_summary = feature_report_runtime_summary(document, &coverage_gaps);
    let generated_patch_summary = feature_report_generated_patch_summary(document, &evidence_by_id);
    let complexity_transfer_candidates =
        feature_report_complexity_transfer_candidates(&generated_patch_summary.review_warnings);
    let semantic_path_summary = feature_report_semantic_path_summary(
        document,
        &coverage_gaps,
        &claim_by_id,
        &evidence_by_id,
    );
    let schema_compatibility = feature_report_schema_compatibility_metadata(
        &coverage_gaps,
        &undischarged_assumptions,
        &runtime_summary,
        &semantic_path_summary,
        &non_conclusions,
    );

    FeatureExtensionReportV0 {
        schema_version: FEATURE_EXTENSION_REPORT_SCHEMA_VERSION.to_string(),
        schema_compatibility: Some(schema_compatibility),
        input: FeatureReportInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        architecture_id: document.architecture_id.clone(),
        revision: document.revision.clone(),
        feature: document.feature.clone(),
        review_summary: FeatureReportReviewSummary {
            split_status: split_status.clone(),
            claim_classification: feature_report_claim_classification(&split_status),
            top_witnesses: introduced_obstruction_witnesses
                .iter()
                .take(3)
                .map(|witness| witness.kind.clone())
                .collect(),
            required_action: feature_report_required_action(
                &split_status,
                &introduced_obstruction_witnesses,
                &coverage_gaps,
                &runtime_summary,
                &theorem_precondition_report.checks,
            ),
        },
        architecture_summary: FeatureReportArchitectureSummary {
            component_count: document.components.len(),
            relation_count: document.relations.len(),
            static_relation_count: count_air_relations(document, "static"),
            runtime_relation_count: count_air_relations(document, "runtime"),
            policy_relation_count: count_air_relations(document, "policy"),
            semantic_diagram_count: document.semantic_diagrams.len(),
            measured_axes,
            unmeasured_axes,
        },
        runtime_summary,
        interpreted_extension: FeatureReportInterpretedExtension {
            embedding_claim_ref: document.extension.embedding_claim_ref.clone(),
            feature_view_claim_ref: document.extension.feature_view_claim_ref.clone(),
            interaction_claim_refs: document.extension.interaction_claim_refs.clone(),
            split_claim_ref: document.extension.split_claim_ref.clone(),
            added_components: document
                .components
                .iter()
                .filter(|component| component.lifecycle == "added")
                .map(|component| component.id.clone())
                .collect(),
            changed_components: document
                .components
                .iter()
                .filter(|component| component.lifecycle == "changed")
                .map(|component| component.id.clone())
                .collect(),
            added_relations: document
                .relations
                .iter()
                .filter(|relation| relation.lifecycle == "added")
                .map(|relation| relation.id.clone())
                .collect(),
        },
        generated_patch_summary,
        split_status,
        preserved_invariants,
        changed_invariants,
        introduced_obstruction_witnesses,
        eliminated_obstruction_witnesses: Vec::new(),
        complexity_transfer_candidates,
        semantic_path_summary,
        theorem_package_refs,
        theorem_precondition_summary: theorem_precondition_report.summary,
        theorem_precondition_checks: theorem_precondition_report.checks,
        discharged_assumptions,
        undischarged_assumptions,
        coverage_gaps,
        unsupported_constructs,
        repair_suggestions,
        empirical_annotations: vec![
            "Feature Extension Report v0 combines static split evidence with measured runtime exposure when available".to_string(),
            "runtimePropagation is reported as runtime exposure radius, not blast radius".to_string(),
            "Runtime formal claims require coverage, projection, exactness, and theorem preconditions".to_string(),
        ],
        non_conclusions,
    }
}

fn feature_report_semantic_path_summary(
    document: &AirDocumentV0,
    coverage_gaps: &[FeatureReportCoverageGap],
    claim_by_id: &BTreeMap<String, &AirClaim>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> FeatureReportSemanticPathSummary {
    let semantic_layer = document
        .coverage
        .layers
        .iter()
        .find(|layer| layer.layer == "semantic");
    let semantic_claims: Vec<&AirClaim> = document
        .claims
        .iter()
        .filter(|claim| {
            claim.subject_ref.contains("semantic")
                || claim.subject_ref == "signature.projectionSoundnessViolation"
                || document
                    .semantic_diagrams
                    .iter()
                    .any(|diagram| diagram.filler_claim_ref.as_ref() == Some(&claim.claim_id))
                || document
                    .nonfillability_witnesses
                    .iter()
                    .any(|witness| witness.claim_ref == claim.claim_id)
        })
        .collect();
    let mut non_conclusions = BTreeSet::new();
    non_conclusions.insert("global semantic flatness is not concluded".to_string());
    non_conclusions
        .insert("absence of semantic witnesses is not evidence of commutation".to_string());
    if semantic_layer
        .map(|layer| layer.measurement_boundary == "unmeasured")
        .unwrap_or(true)
    {
        non_conclusions.insert("unmeasured semantic layer is not measuredZero".to_string());
    }
    for claim in &semantic_claims {
        for conclusion in &claim.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }

    FeatureReportSemanticPathSummary {
        path_count: document.architecture_paths.len(),
        diagram_count: document.semantic_diagrams.len(),
        nonfillability_witness_count: document.nonfillability_witnesses.len(),
        representative_path_ids: document
            .architecture_paths
            .iter()
            .take(3)
            .map(|path| path.path_id.clone())
            .collect(),
        representative_diagram_ids: document
            .semantic_diagrams
            .iter()
            .take(3)
            .map(|diagram| diagram.id.clone())
            .collect(),
        representative_nonfillability_witness_ids: document
            .nonfillability_witnesses
            .iter()
            .take(3)
            .map(|witness| witness.witness_id.clone())
            .collect(),
        measurement_boundary: semantic_layer
            .map(|layer| layer.measurement_boundary.clone())
            .unwrap_or_else(|| "unmeasured".to_string()),
        measured_axes: semantic_layer
            .map(|layer| layer.measured_axes.clone())
            .unwrap_or_default(),
        unmeasured_axes: semantic_layer
            .map(|layer| layer.unmeasured_axes.clone())
            .unwrap_or_else(|| vec!["semanticDiagramCommutation".to_string()]),
        evidence_kinds: feature_report_semantic_evidence_kinds(&semantic_claims, evidence_by_id),
        diagrams: feature_report_semantic_diagram_summaries(document, claim_by_id, evidence_by_id),
        nonfillability_witnesses: feature_report_semantic_nonfillability_summaries(
            document,
            claim_by_id,
            evidence_by_id,
        ),
        extraction_scope: semantic_layer
            .map(|layer| layer.extraction_scope.clone())
            .unwrap_or_default(),
        exactness_assumptions: semantic_layer
            .map(|layer| layer.exactness_assumptions.clone())
            .unwrap_or_default(),
        unsupported_constructs: semantic_layer
            .map(|layer| layer.unsupported_constructs.clone())
            .unwrap_or_default(),
        missing_preconditions: feature_report_semantic_missing_preconditions(&semantic_claims),
        coverage_gaps: coverage_gaps
            .iter()
            .filter(|gap| gap.layer == "semantic")
            .flat_map(|gap| {
                let mut gaps = vec![format!("semantic layer is {}", gap.measurement_boundary)];
                gaps.extend(
                    gap.unmeasured_axes
                        .iter()
                        .map(|axis| format!("semantic axis unmeasured: {axis}")),
                );
                gaps.extend(
                    gap.unsupported_constructs
                        .iter()
                        .map(|construct| format!("semantic unsupported: {construct}")),
                );
                gaps
            })
            .collect(),
        claim_refs: semantic_claims
            .iter()
            .map(|claim| claim.claim_id.clone())
            .collect(),
        claim_classifications: semantic_claims
            .iter()
            .map(|claim| claim.claim_classification.clone())
            .collect(),
        non_conclusions: non_conclusions.into_iter().collect(),
    }
}

fn feature_report_semantic_diagram_summaries(
    document: &AirDocumentV0,
    claim_by_id: &BTreeMap<String, &AirClaim>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportSemanticDiagramSummary> {
    document
        .semantic_diagrams
        .iter()
        .map(|diagram| {
            let claims = feature_report_semantic_diagram_claims(document, &diagram.id, claim_by_id);
            FeatureReportSemanticDiagramSummary {
                diagram_id: diagram.id.clone(),
                lhs_path_ref: diagram.lhs_path_ref.clone(),
                rhs_path_ref: diagram.rhs_path_ref.clone(),
                equivalence: diagram.equivalence.clone(),
                filler_claim_ref: diagram.filler_claim_ref.clone(),
                nonfillability_witness_refs: diagram.nonfillability_witness_refs.clone(),
                observation_refs: diagram.observation_refs.clone(),
                evidence: feature_report_evidence_refs(&diagram.evidence_refs, evidence_by_id),
                claim_refs: claims.iter().map(|claim| claim.claim_id.clone()).collect(),
                claim_classifications: claims
                    .iter()
                    .map(|claim| claim.claim_classification.clone())
                    .collect(),
                theorem_reference: feature_report_claim_theorem_refs(&claims),
                missing_preconditions: feature_report_claim_missing_preconditions(&claims),
                non_conclusions: feature_report_claims_non_conclusions(&claims),
            }
        })
        .collect()
}

fn feature_report_semantic_nonfillability_summaries(
    document: &AirDocumentV0,
    claim_by_id: &BTreeMap<String, &AirClaim>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportSemanticNonfillabilityWitnessSummary> {
    document
        .nonfillability_witnesses
        .iter()
        .map(|witness| {
            let claim = claim_by_id.get(&witness.claim_ref).copied();
            FeatureReportSemanticNonfillabilityWitnessSummary {
                witness_id: witness.witness_id.clone(),
                diagram_ref: witness.diagram_ref.clone(),
                witness_kind: witness.witness_kind.clone(),
                claim_ref: witness.claim_ref.clone(),
                evidence: feature_report_evidence_refs(&witness.evidence_refs, evidence_by_id),
                theorem_reference: claim
                    .map(|claim| claim.theorem_refs.clone())
                    .unwrap_or_default(),
                claim_level: claim
                    .map(|claim| claim.claim_level.clone())
                    .unwrap_or_else(|| "tooling".to_string()),
                claim_classification: claim
                    .map(|claim| claim.claim_classification.clone())
                    .unwrap_or_else(|| "measured".to_string()),
                measurement_boundary: claim
                    .map(|claim| claim.measurement_boundary.clone())
                    .unwrap_or_else(|| "measuredNonzero".to_string()),
                missing_preconditions: claim
                    .map(|claim| claim.missing_preconditions.clone())
                    .unwrap_or_default(),
                non_conclusions: feature_report_claim_non_conclusions(claim),
            }
        })
        .collect()
}

fn feature_report_semantic_diagram_claims<'a>(
    document: &'a AirDocumentV0,
    diagram_id: &str,
    claim_by_id: &BTreeMap<String, &'a AirClaim>,
) -> Vec<&'a AirClaim> {
    let diagram = document
        .semantic_diagrams
        .iter()
        .find(|diagram| diagram.id == diagram_id);
    let mut claim_ids = BTreeSet::new();
    if let Some(diagram) = diagram {
        if let Some(claim_ref) = &diagram.filler_claim_ref {
            claim_ids.insert(claim_ref.clone());
        }
        for witness_ref in &diagram.nonfillability_witness_refs {
            if let Some(witness) = document
                .nonfillability_witnesses
                .iter()
                .find(|witness| witness.witness_id == *witness_ref)
            {
                claim_ids.insert(witness.claim_ref.clone());
            }
        }
    }

    let subject_ref = format!("semantic.diagram.{diagram_id}");
    let mut claims: Vec<&AirClaim> = document
        .claims
        .iter()
        .filter(|claim| claim.subject_ref == subject_ref || claim.subject_ref.contains(diagram_id))
        .collect();
    for claim_id in claim_ids {
        if let Some(claim) = claim_by_id.get(&claim_id).copied() {
            if !claims
                .iter()
                .any(|existing| existing.claim_id == claim.claim_id)
            {
                claims.push(claim);
            }
        }
    }
    claims
}

fn feature_report_claim_theorem_refs(claims: &[&AirClaim]) -> Vec<String> {
    let mut theorem_refs = BTreeSet::new();
    for claim in claims {
        for theorem_ref in &claim.theorem_refs {
            theorem_refs.insert(theorem_ref.clone());
        }
    }
    theorem_refs.into_iter().collect()
}

fn feature_report_claim_missing_preconditions(claims: &[&AirClaim]) -> Vec<String> {
    let mut missing = BTreeSet::new();
    for claim in claims {
        for precondition in &claim.missing_preconditions {
            missing.insert(format!("{}: {}", claim.claim_id, precondition));
        }
    }
    missing.into_iter().collect()
}

fn feature_report_claims_non_conclusions(claims: &[&AirClaim]) -> Vec<String> {
    let mut non_conclusions = BTreeSet::new();
    for claim in claims {
        for conclusion in &claim.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }
    non_conclusions.into_iter().collect()
}

fn feature_report_semantic_evidence_kinds(
    semantic_claims: &[&AirClaim],
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<String> {
    let mut kinds = BTreeSet::new();
    for claim in semantic_claims {
        for evidence_ref in &claim.evidence_refs {
            if let Some(evidence) = evidence_by_id.get(evidence_ref) {
                kinds.insert(evidence.kind.clone());
            }
        }
    }
    kinds.into_iter().collect()
}

fn feature_report_semantic_missing_preconditions(semantic_claims: &[&AirClaim]) -> Vec<String> {
    let mut missing = BTreeSet::new();
    for claim in semantic_claims {
        for precondition in &claim.missing_preconditions {
            missing.insert(format!("{}: {}", claim.claim_id, precondition));
        }
    }
    missing.into_iter().collect()
}

fn feature_report_generated_patch_summary(
    document: &AirDocumentV0,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> FeatureReportGeneratedPatchSummary {
    let ai_session = document.feature.ai_session.as_ref();
    let generated_patch_artifact_ids: BTreeSet<String> = document
        .artifacts
        .iter()
        .filter(|artifact| artifact.kind == "generated_patch")
        .map(|artifact| artifact.artifact_id.clone())
        .collect();
    let generated_patch_evidence_ids: BTreeSet<String> = document
        .evidence
        .iter()
        .filter(|evidence| {
            evidence.kind == "generated_patch"
                || evidence
                    .artifact_ref
                    .as_ref()
                    .map(|artifact_ref| generated_patch_artifact_ids.contains(artifact_ref))
                    .unwrap_or(false)
        })
        .map(|evidence| evidence.evidence_id.clone())
        .collect();
    let evidence_refs: Vec<String> = generated_patch_evidence_ids.iter().cloned().collect();
    let mut non_conclusions = BTreeSet::new();
    non_conclusions.insert(
        "generated patch summary is traceability evidence, not a proof or measurement claim"
            .to_string(),
    );
    non_conclusions
        .insert("AI generated status is not evidence for architecture lawfulness".to_string());
    non_conclusions
        .insert("AI generated status is not evidence against architecture lawfulness".to_string());
    non_conclusions.insert(
        "generated patch summary identifies architecture extension locations, not patch size"
            .to_string(),
    );
    non_conclusions.insert(
        "AI-generated hidden interaction candidates are conservative review signals, not measured obstruction witnesses"
            .to_string(),
    );
    non_conclusions.insert(
        "complexity transfer warnings are review signals, not obstruction measurements".to_string(),
    );
    let is_ai_session = document.feature.source == "ai_session";
    let generated_patch = ai_session
        .and_then(|session| session.generated_patch)
        .unwrap_or(false)
        || !generated_patch_artifact_ids.is_empty();

    FeatureReportGeneratedPatchSummary {
        is_ai_session,
        generated_patch,
        human_reviewed: ai_session.and_then(|session| session.human_reviewed),
        provider: ai_session.and_then(|session| session.provider.clone()),
        model: ai_session.and_then(|session| session.model.clone()),
        prompt_ref: ai_session.and_then(|session| session.prompt_ref.clone()),
        artifact_refs: generated_patch_artifact_ids.into_iter().collect(),
        evidence: feature_report_evidence_refs(&evidence_refs, evidence_by_id),
        operations: feature_report_generated_patch_operations(
            document,
            &generated_patch_evidence_ids,
            evidence_by_id,
        ),
        review_warnings: feature_report_generated_patch_review_warnings(
            document,
            is_ai_session && generated_patch,
            &generated_patch_evidence_ids,
            evidence_by_id,
        ),
        non_conclusions: non_conclusions.into_iter().collect(),
    }
}

fn feature_report_generated_patch_review_warnings(
    document: &AirDocumentV0,
    enabled: bool,
    generated_patch_evidence_ids: &BTreeSet<String>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportGeneratedPatchReviewWarning> {
    if !enabled {
        return Vec::new();
    }

    let mut warnings = Vec::new();
    for relation in &document.relations {
        if !feature_report_relation_in_generated_patch_context(
            document,
            relation,
            generated_patch_evidence_ids,
        ) || feature_report_obstructing_relation(document, relation)
        {
            continue;
        }
        let Some(review_signal) =
            feature_report_hidden_interaction_review_signal(document, relation, evidence_by_id)
        else {
            continue;
        };
        let evidence_refs =
            feature_report_relation_warning_evidence_refs(relation, generated_patch_evidence_ids);
        warnings.push(FeatureReportGeneratedPatchReviewWarning {
            warning_id: format!(
                "warning-{}-hidden-interaction-candidate",
                stable_id_fragment(&relation.id)
            ),
            warning_kind: "hidden_interaction_candidate".to_string(),
            classification: "conservative_review_signal".to_string(),
            review_signal,
            measurement_boundary: "unmeasured".to_string(),
            components: relation
                .from_component
                .iter()
                .chain(relation.to_component.iter())
                .cloned()
                .collect(),
            relations: vec![FeatureReportEdgeRef {
                relation_id: relation.id.clone(),
                from: relation.from_component.clone(),
                to: relation.to_component.clone(),
                kind: relation.kind.clone(),
            }],
            operation_refs: feature_report_relation_operation_refs(
                document,
                relation,
                generated_patch_evidence_ids,
            ),
            evidence: feature_report_evidence_refs(&evidence_refs, evidence_by_id),
            non_conclusions: vec![
                "hidden interaction candidate is not a measured hidden_interaction witness"
                    .to_string(),
                "candidate requires human review or measured policy/runtime/semantic evidence"
                    .to_string(),
            ],
        });
    }

    if let Some(warning) = feature_report_complexity_transfer_review_warning(
        document,
        generated_patch_evidence_ids,
        evidence_by_id,
    ) {
        warnings.push(warning);
    }

    warnings
}

fn feature_report_relation_in_generated_patch_context(
    document: &AirDocumentV0,
    relation: &AirRelation,
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> bool {
    relation.lifecycle == "added"
        || relation.lifecycle == "changed"
        || relation
            .evidence_refs
            .iter()
            .any(|evidence_ref| generated_patch_evidence_ids.contains(evidence_ref))
        || document
            .operation_trace
            .operations
            .iter()
            .any(|operation| operation.contains(&relation.id))
}

fn feature_report_hidden_interaction_review_signal(
    _document: &AirDocumentV0,
    relation: &AirRelation,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Option<String> {
    let mut haystack = vec![
        relation.id.as_str(),
        relation.layer.as_str(),
        relation.kind.as_str(),
    ]
    .join(" ");
    if let Some(extraction_rule) = &relation.extraction_rule {
        haystack.push(' ');
        haystack.push_str(extraction_rule);
    }
    if let Some(protected_by) = &relation.protected_by {
        haystack.push(' ');
        haystack.push_str(protected_by);
    }
    for component in relation
        .from_component
        .iter()
        .chain(relation.to_component.iter())
    {
        haystack.push(' ');
        haystack.push_str(component);
    }
    for evidence_ref in &relation.evidence_refs {
        if let Some(evidence) = evidence_by_id.get(evidence_ref) {
            for text in [
                Some(evidence.kind.as_str()),
                evidence.path.as_deref(),
                evidence.symbol.as_deref(),
                evidence.rule_id.as_deref(),
            ]
            .into_iter()
            .flatten()
            {
                haystack.push(' ');
                haystack.push_str(text);
            }
        }
    }
    let haystack = haystack.to_ascii_lowercase();
    if haystack.contains("policy_bypass") || haystack.contains("policy bypass") {
        Some("AI-generated patch contains a policy bypass candidate".to_string())
    } else if haystack.contains("cache") {
        Some("AI-generated patch contains a cache access candidate".to_string())
    } else if haystack.contains("implicit_state")
        || haystack.contains("implicit state")
        || haystack.contains("state_sharing")
        || haystack.contains("state sharing")
        || haystack.contains("internal")
    {
        Some("AI-generated patch contains an implicit state sharing candidate".to_string())
    } else if haystack.contains("adapter") {
        Some("AI-generated patch contains an adapter boundary candidate".to_string())
    } else {
        None
    }
}

fn feature_report_relation_warning_evidence_refs(
    relation: &AirRelation,
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> Vec<String> {
    let mut refs: BTreeSet<String> = generated_patch_evidence_ids.clone();
    refs.extend(relation.evidence_refs.iter().cloned());
    refs.into_iter().collect()
}

fn feature_report_relation_operation_refs(
    document: &AirDocumentV0,
    relation: &AirRelation,
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> Vec<String> {
    document
        .operation_trace
        .operations
        .iter()
        .filter(|operation| {
            operation.contains(&relation.id)
                || generated_patch_evidence_ids
                    .iter()
                    .any(|evidence_ref| operation.contains(evidence_ref))
        })
        .cloned()
        .collect()
}

fn feature_report_complexity_transfer_review_warning(
    document: &AirDocumentV0,
    generated_patch_evidence_ids: &BTreeSet<String>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Option<FeatureReportGeneratedPatchReviewWarning> {
    let relation_complexity_axis = document
        .signature
        .axes
        .iter()
        .find(|axis| axis.axis == "relationComplexity");
    let has_relation_complexity_signal = relation_complexity_axis.is_some()
        || document.claims.iter().any(|claim| {
            claim.subject_ref.contains("relationComplexity")
                || claim.predicate.contains("relation complexity")
        })
        || document
            .operation_trace
            .operations
            .iter()
            .any(|operation| operation.contains("relationComplexity"));
    if !has_relation_complexity_signal {
        return None;
    }

    let generated_relations: Vec<&AirRelation> = document
        .relations
        .iter()
        .filter(|relation| {
            feature_report_relation_in_generated_patch_context(
                document,
                relation,
                generated_patch_evidence_ids,
            )
        })
        .collect();
    if generated_relations.is_empty() {
        return None;
    }

    let mut evidence_refs = generated_patch_evidence_ids.clone();
    for relation in &generated_relations {
        evidence_refs.extend(relation.evidence_refs.iter().cloned());
    }
    let operation_refs: Vec<String> = document
        .operation_trace
        .operations
        .iter()
        .filter(|operation| {
            operation.contains("relationComplexity")
                || generated_relations
                    .iter()
                    .any(|relation| operation.contains(&relation.id))
                || operation.contains("generated_patch")
        })
        .cloned()
        .collect();
    let relation_ids: Vec<String> = generated_relations
        .iter()
        .map(|relation| relation.id.clone())
        .collect();

    Some(FeatureReportGeneratedPatchReviewWarning {
        warning_id: "warning-ai-generated-relation-complexity-transfer".to_string(),
        warning_kind: "complexity_transfer_warning".to_string(),
        classification: "conservative_review_signal".to_string(),
        review_signal: if relation_complexity_axis
            .and_then(|axis| axis.value)
            .unwrap_or_default()
            > 0
        {
            "relationComplexity is nonzero in an AI-generated patch context".to_string()
        } else {
            "changed generated-patch relations may transfer complexity across boundaries"
                .to_string()
        },
        measurement_boundary: relation_complexity_axis
            .map(|axis| axis.measurement_boundary.clone())
            .unwrap_or_else(|| "unmeasured".to_string()),
        components: generated_relations
            .iter()
            .flat_map(|relation| {
                relation
                    .from_component
                    .iter()
                    .chain(relation.to_component.iter())
            })
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        relations: generated_relations
            .iter()
            .map(|relation| FeatureReportEdgeRef {
                relation_id: relation.id.clone(),
                from: relation.from_component.clone(),
                to: relation.to_component.clone(),
                kind: relation.kind.clone(),
            })
            .collect(),
        operation_refs,
        evidence: feature_report_evidence_refs(
            &evidence_refs.into_iter().collect::<Vec<_>>(),
            evidence_by_id,
        ),
        non_conclusions: vec![
            "complexity transfer warning is not a measured obstruction witness".to_string(),
            format!(
                "changed relation candidates are review targets: {}",
                relation_ids.join(", ")
            ),
        ],
    })
}

fn feature_report_complexity_transfer_candidates(
    review_warnings: &[FeatureReportGeneratedPatchReviewWarning],
) -> Vec<String> {
    review_warnings
        .iter()
        .filter(|warning| warning.warning_kind == "complexity_transfer_warning")
        .map(|warning| {
            let relation_ids = warning
                .relations
                .iter()
                .map(|relation| relation.relation_id.clone())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{}: {} ({}, relations: {})",
                warning.warning_id, warning.review_signal, warning.classification, relation_ids
            )
        })
        .collect()
}

fn feature_report_generated_patch_operations(
    document: &AirDocumentV0,
    generated_patch_evidence_ids: &BTreeSet<String>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportGeneratedPatchOperation> {
    document
        .operation_trace
        .operations
        .iter()
        .filter(|operation_ref| {
            operation_ref.contains("generated_patch")
                || generated_patch_evidence_ids
                    .iter()
                    .any(|evidence_id| operation_ref.contains(evidence_id))
                || document.artifacts.iter().any(|artifact| {
                    artifact.kind == "generated_patch"
                        && operation_ref.contains(&artifact.artifact_id)
                })
        })
        .map(|operation_ref| {
            let added_components = feature_report_generated_patch_operation_components(
                document,
                operation_ref,
                generated_patch_evidence_ids,
            );
            let added_relations = feature_report_generated_patch_operation_relations(
                document,
                operation_ref,
                generated_patch_evidence_ids,
            );
            let policy_touches = feature_report_generated_patch_policy_touches(
                document,
                operation_ref,
                &added_relations,
            );
            let operation_evidence_refs = feature_report_generated_patch_operation_evidence_refs(
                document,
                &added_components,
                &added_relations,
                generated_patch_evidence_ids,
            );

            FeatureReportGeneratedPatchOperation {
                operation_ref: operation_ref.clone(),
                added_components,
                added_relations,
                policy_touches,
                evidence: feature_report_evidence_refs(&operation_evidence_refs, evidence_by_id),
            }
        })
        .collect()
}

fn feature_report_generated_patch_operation_components(
    document: &AirDocumentV0,
    operation_ref: &str,
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> Vec<String> {
    document
        .components
        .iter()
        .filter(|component| {
            component.lifecycle == "added"
                && (operation_ref.contains(&component.id)
                    || component
                        .evidence_refs
                        .iter()
                        .any(|evidence_ref| generated_patch_evidence_ids.contains(evidence_ref)))
        })
        .map(|component| component.id.clone())
        .collect()
}

fn feature_report_generated_patch_operation_relations(
    document: &AirDocumentV0,
    operation_ref: &str,
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> Vec<FeatureReportEdgeRef> {
    document
        .relations
        .iter()
        .filter(|relation| {
            relation.lifecycle == "added"
                && (operation_ref.contains(&relation.id)
                    || relation
                        .evidence_refs
                        .iter()
                        .any(|evidence_ref| generated_patch_evidence_ids.contains(evidence_ref)))
        })
        .map(|relation| FeatureReportEdgeRef {
            relation_id: relation.id.clone(),
            from: relation.from_component.clone(),
            to: relation.to_component.clone(),
            kind: relation.kind.clone(),
        })
        .collect()
}

fn feature_report_generated_patch_policy_touches(
    document: &AirDocumentV0,
    operation_ref: &str,
    added_relations: &[FeatureReportEdgeRef],
) -> Vec<String> {
    let mut policy_touches = BTreeSet::new();
    for relation in &document.relations {
        if relation.layer == "policy"
            && added_relations
                .iter()
                .any(|added| added.relation_id == relation.id)
        {
            policy_touches.insert(format!("policy relation: {}", relation.id));
        }
    }
    if operation_ref.contains("policy") {
        for policy_ref in document
            .policies
            .laws
            .iter()
            .chain(document.policies.boundaries.iter())
            .chain(document.policies.allowed_edges.iter())
            .chain(document.policies.forbidden_edges.iter())
            .chain(document.policies.abstraction_rules.iter())
            .chain(document.policies.protection_rules.iter())
        {
            if operation_ref.contains(policy_ref) {
                policy_touches.insert(policy_ref.clone());
            }
        }
    }
    policy_touches.into_iter().collect()
}

fn feature_report_generated_patch_operation_evidence_refs(
    document: &AirDocumentV0,
    added_components: &[String],
    added_relations: &[FeatureReportEdgeRef],
    generated_patch_evidence_ids: &BTreeSet<String>,
) -> Vec<String> {
    let mut evidence_refs = generated_patch_evidence_ids.clone();
    for component in &document.components {
        if added_components.contains(&component.id) {
            evidence_refs.extend(component.evidence_refs.iter().cloned());
        }
    }
    for relation in &document.relations {
        if added_relations
            .iter()
            .any(|added| added.relation_id == relation.id)
        {
            evidence_refs.extend(relation.evidence_refs.iter().cloned());
        }
    }
    evidence_refs.into_iter().collect()
}

fn feature_report_runtime_summary(
    document: &AirDocumentV0,
    coverage_gaps: &[FeatureReportCoverageGap],
) -> FeatureReportRuntimeSummary {
    let runtime_axis = document
        .signature
        .axes
        .iter()
        .find(|axis| axis.axis == "runtimePropagation");
    let runtime_layer = document
        .coverage
        .layers
        .iter()
        .find(|layer| layer.layer == "runtime");
    let runtime_claims: Vec<&AirClaim> = document
        .claims
        .iter()
        .filter(|claim| claim.subject_ref == "signature.runtimePropagation")
        .collect();
    let measured = runtime_axis
        .map(|axis| axis.measured && axis.value.is_some())
        .unwrap_or(false);
    let runtime_propagation = runtime_axis.and_then(|axis| axis.value);

    let mut non_conclusions = BTreeSet::new();
    non_conclusions
        .insert("runtimePropagation is an exposure radius, not runtime blast radius".to_string());
    non_conclusions
        .insert("runtimePropagation is not policy-aware runtime propagation".to_string());
    non_conclusions
        .insert("measured runtime witness is not a formal runtime zero bridge claim".to_string());
    if !measured {
        non_conclusions
            .insert("runtimePropagation null is UNMEASURED, not runtime risk zero".to_string());
    } else if runtime_propagation == Some(0) {
        non_conclusions.insert(
            "runtimePropagation = 0 needs coverage, projection, exactness, and theorem preconditions before a formal claim".to_string(),
        );
    }
    for claim in runtime_claims.iter().copied() {
        for conclusion in &claim.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
        for missing in &claim.missing_preconditions {
            non_conclusions.insert(format!("missing runtime precondition: {missing}"));
        }
    }

    FeatureReportRuntimeSummary {
        relation_count: count_air_relations(document, "runtime"),
        measurement_boundary: runtime_axis
            .map(|axis| axis.measurement_boundary.clone())
            .or_else(|| runtime_layer.map(|layer| layer.measurement_boundary.clone()))
            .unwrap_or_else(|| "unmeasured".to_string()),
        runtime_propagation,
        interpretation: if measured {
            "runtimePropagation is measured runtime exposure radius over the projected 0/1 runtime graph"
                .to_string()
        } else {
            "runtimePropagation is UNMEASURED; runtime risk zero is not concluded".to_string()
        },
        measured_axes: runtime_layer
            .map(|layer| layer.measured_axes.clone())
            .unwrap_or_default(),
        unmeasured_axes: runtime_layer
            .map(|layer| layer.unmeasured_axes.clone())
            .unwrap_or_else(|| vec!["runtimePropagation".to_string()]),
        projection_rule: runtime_layer.and_then(|layer| layer.projection_rule.clone()),
        extraction_scope: runtime_layer
            .map(|layer| layer.extraction_scope.clone())
            .unwrap_or_default(),
        exactness_assumptions: runtime_layer
            .map(|layer| layer.exactness_assumptions.clone())
            .unwrap_or_default(),
        coverage_gaps: coverage_gaps
            .iter()
            .filter(|gap| gap.layer == "runtime")
            .flat_map(|gap| {
                gap.unmeasured_axes
                    .iter()
                    .map(|axis| format!("runtime axis unmeasured: {axis}"))
                    .chain(
                        gap.unsupported_constructs
                            .iter()
                            .map(|construct| format!("runtime unsupported construct: {construct}")),
                    )
            })
            .collect(),
        claim_refs: runtime_claims
            .iter()
            .map(|claim| claim.claim_id.clone())
            .collect(),
        claim_classifications: runtime_claims
            .iter()
            .map(|claim| claim.claim_classification.clone())
            .collect(),
        non_conclusions: non_conclusions.into_iter().collect(),
    }
}

fn feature_report_preserved_invariants(document: &AirDocumentV0) -> Vec<FeatureReportInvariant> {
    document
        .signature
        .axes
        .iter()
        .filter(|axis| {
            axis.measured
                && axis.value == Some(0)
                && axis.measurement_boundary == "measuredZero"
                && static_report_axis(&axis.axis)
        })
        .map(|axis| FeatureReportInvariant {
            invariant: format!("{} preserved", axis.axis),
            axis: axis.axis.clone(),
            value: axis.value,
            measurement_boundary: axis.measurement_boundary.clone(),
            evidence_refs: feature_report_axis_evidence_refs(document, &axis.axis),
            claim_refs: feature_report_axis_claim_refs(document, &axis.axis),
        })
        .collect()
}

fn feature_report_changed_invariants(document: &AirDocumentV0) -> Vec<FeatureReportInvariant> {
    document
        .signature
        .axes
        .iter()
        .filter(|axis| {
            axis.measured && axis.value.unwrap_or_default() != 0 && static_report_axis(&axis.axis)
        })
        .map(|axis| FeatureReportInvariant {
            invariant: format!("{} changed", axis.axis),
            axis: axis.axis.clone(),
            value: axis.value,
            measurement_boundary: axis.measurement_boundary.clone(),
            evidence_refs: feature_report_axis_evidence_refs(document, &axis.axis),
            claim_refs: feature_report_axis_claim_refs(document, &axis.axis),
        })
        .collect()
}

fn feature_report_obstruction_witnesses(
    document: &AirDocumentV0,
    claim_by_id: &BTreeMap<String, &AirClaim>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportObstructionWitness> {
    let mut witnesses = Vec::new();
    for relation in &document.relations {
        if !feature_report_obstructing_relation(document, relation) {
            continue;
        }
        let claim = feature_report_relation_claim(document, relation);
        let kind = feature_report_relation_witness_kind(document, relation);
        witnesses.push(FeatureReportObstructionWitness {
            witness_id: format!("witness-{}", stable_id_fragment(&relation.id)),
            layer: relation.layer.clone(),
            kind: kind.clone(),
            extension_role: feature_report_witness_roles(&kind),
            extension_classification: feature_report_witness_classification(&kind),
            components: relation
                .from_component
                .iter()
                .chain(relation.to_component.iter())
                .cloned()
                .collect(),
            edges: vec![FeatureReportEdgeRef {
                relation_id: relation.id.clone(),
                from: relation.from_component.clone(),
                to: relation.to_component.clone(),
                kind: relation.kind.clone(),
            }],
            paths: Vec::new(),
            diagrams: Vec::new(),
            nonfillability_witness_ref: None,
            operation: Some("feature_addition".to_string()),
            evidence: feature_report_evidence_refs(&relation.evidence_refs, evidence_by_id),
            theorem_reference: claim
                .map(|claim| claim.theorem_refs.clone())
                .unwrap_or_default(),
            claim_level: claim
                .map(|claim| claim.claim_level.clone())
                .unwrap_or_else(|| "tooling".to_string()),
            claim_classification: claim
                .map(|claim| claim.claim_classification.clone())
                .unwrap_or_else(|| "measured".to_string()),
            measurement_boundary: claim
                .map(|claim| claim.measurement_boundary.clone())
                .unwrap_or_else(|| "measuredNonzero".to_string()),
            non_conclusions: feature_report_claim_non_conclusions(claim),
            repair_candidates: feature_report_witness_repairs(&kind),
        });
    }

    for witness in &document.nonfillability_witnesses {
        let claim = claim_by_id.get(&witness.claim_ref).copied();
        witnesses.push(FeatureReportObstructionWitness {
            witness_id: witness.witness_id.clone(),
            layer: "semantic".to_string(),
            kind: witness.witness_kind.clone(),
            extension_role: vec!["invariant_not_preserved".to_string()],
            extension_classification: vec!["fillingFailure".to_string()],
            components: Vec::new(),
            edges: Vec::new(),
            paths: feature_report_semantic_witness_path_refs(document, &witness.diagram_ref),
            diagrams: vec![witness.diagram_ref.clone()],
            nonfillability_witness_ref: Some(witness.witness_id.clone()),
            operation: Some("feature_addition".to_string()),
            evidence: feature_report_evidence_refs(&witness.evidence_refs, evidence_by_id),
            theorem_reference: claim
                .map(|claim| claim.theorem_refs.clone())
                .unwrap_or_default(),
            claim_level: claim
                .map(|claim| claim.claim_level.clone())
                .unwrap_or_else(|| "tooling".to_string()),
            claim_classification: claim
                .map(|claim| claim.claim_classification.clone())
                .unwrap_or_else(|| "measured".to_string()),
            measurement_boundary: claim
                .map(|claim| claim.measurement_boundary.clone())
                .unwrap_or_else(|| "measuredNonzero".to_string()),
            non_conclusions: feature_report_claim_non_conclusions(claim),
            repair_candidates: vec![
                "add or repair semantic diagram evidence".to_string(),
                "choose an explicit contract for the non-commuting paths".to_string(),
            ],
        });
    }

    witnesses
}

fn feature_report_semantic_witness_path_refs(
    document: &AirDocumentV0,
    diagram_ref: &str,
) -> Vec<String> {
    document
        .semantic_diagrams
        .iter()
        .find(|diagram| diagram.id == diagram_ref)
        .map(|diagram| vec![diagram.lhs_path_ref.clone(), diagram.rhs_path_ref.clone()])
        .unwrap_or_default()
}

fn feature_report_coverage_gaps(document: &AirDocumentV0) -> Vec<FeatureReportCoverageGap> {
    document
        .coverage
        .layers
        .iter()
        .filter(|layer| {
            layer.measurement_boundary == "unmeasured"
                || !layer.unmeasured_axes.is_empty()
                || !layer.unsupported_constructs.is_empty()
        })
        .map(|layer| FeatureReportCoverageGap {
            layer: layer.layer.clone(),
            measurement_boundary: if layer.measurement_boundary == "unmeasured" {
                "UNMEASURED".to_string()
            } else {
                layer.measurement_boundary.clone()
            },
            unmeasured_axes: layer.unmeasured_axes.clone(),
            unsupported_constructs: layer.unsupported_constructs.clone(),
            non_conclusions: vec![format!("{} layer is not concluded", layer.layer)],
        })
        .collect()
}

fn feature_report_split_status(
    document: &AirDocumentV0,
    preserved_invariants: &[FeatureReportInvariant],
    changed_invariants: &[FeatureReportInvariant],
    introduced_obstruction_witnesses: &[FeatureReportObstructionWitness],
) -> String {
    if !introduced_obstruction_witnesses.is_empty() || !changed_invariants.is_empty() {
        return "non_split".to_string();
    }
    if !preserved_invariants.is_empty() || feature_report_has_static_measurement(document) {
        return "split".to_string();
    }
    if document
        .coverage
        .layers
        .iter()
        .any(|layer| matches!(layer.layer.as_str(), "static" | "policy"))
    {
        "unknown".to_string()
    } else {
        "unmeasured".to_string()
    }
}

fn feature_report_theorem_package_refs(document: &AirDocumentV0) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for claim in &document.claims {
        for theorem_ref in &claim.theorem_refs {
            refs.insert(theorem_ref.clone());
        }
    }
    refs.into_iter().collect()
}

fn feature_report_discharged_assumptions(document: &AirDocumentV0) -> Vec<String> {
    let mut assumptions = BTreeSet::new();
    for claim in &document.claims {
        if claim.missing_preconditions.is_empty()
            && matches!(
                claim.claim_classification.as_str(),
                "measured" | "proved" | "assumed"
            )
        {
            for assumption in claim
                .required_assumptions
                .iter()
                .chain(claim.coverage_assumptions.iter())
                .chain(claim.exactness_assumptions.iter())
            {
                assumptions.insert(assumption.clone());
            }
        }
    }
    assumptions.into_iter().collect()
}

fn feature_report_undischarged_assumptions(
    document: &AirDocumentV0,
    theorem_checks: &[TheoremPreconditionCheck],
) -> Vec<String> {
    let mut assumptions = BTreeSet::new();
    for claim in &document.claims {
        for assumption in claim
            .missing_preconditions
            .iter()
            .chain(claim.required_assumptions.iter())
            .chain(claim.coverage_assumptions.iter())
            .chain(claim.exactness_assumptions.iter())
        {
            if !claim.missing_preconditions.is_empty() || claim.claim_classification == "unmeasured"
            {
                assumptions.insert(assumption.clone());
            }
        }
    }
    for check in theorem_checks {
        if check.result == "warn" {
            for precondition in &check.missing_preconditions {
                assumptions.insert(format!("{}: {}", check.claim_id, precondition));
            }
        }
    }
    assumptions.into_iter().collect()
}

fn feature_report_unsupported_constructs(
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<String> {
    let mut unsupported = BTreeSet::new();
    for gap in coverage_gaps {
        for construct in &gap.unsupported_constructs {
            unsupported.insert(format!("{}: {}", gap.layer, construct));
        }
    }
    unsupported.into_iter().collect()
}

fn feature_report_repair_suggestions(
    witnesses: &[FeatureReportObstructionWitness],
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<FeatureReportRepairSuggestion> {
    let registry = static_repair_rule_registry();
    let mut suggestions = BTreeMap::new();
    for witness in witnesses {
        let matching_rules: Vec<&RepairRuleV0> = registry
            .rules
            .iter()
            .filter(|rule| rule.target_witness_kind == witness.kind)
            .collect();
        if matching_rules.is_empty() {
            for repair in &witness.repair_candidates {
                let suggestion = feature_report_manual_witness_repair_suggestion(witness, repair);
                suggestions.insert(suggestion.suggestion_id.clone(), suggestion);
            }
        } else {
            for rule in matching_rules {
                let suggestion = feature_report_rule_repair_suggestion(witness, rule);
                suggestions.insert(suggestion.suggestion_id.clone(), suggestion);
            }
        }
    }
    for gap in coverage_gaps {
        if gap.measurement_boundary == "UNMEASURED" {
            let suggestion = feature_report_coverage_gap_repair_suggestion(gap);
            suggestions.insert(suggestion.suggestion_id.clone(), suggestion);
        }
    }
    suggestions.into_values().collect()
}

fn feature_report_rule_repair_suggestion(
    witness: &FeatureReportObstructionWitness,
    rule: &RepairRuleV0,
) -> FeatureReportRepairSuggestion {
    FeatureReportRepairSuggestion {
        suggestion_id: format!(
            "repair-suggestion-{}-{}",
            stable_id_fragment(&witness.witness_id),
            stable_id_fragment(&rule.repair_rule_id)
        ),
        repair_rule_id: Some(rule.repair_rule_id.clone()),
        source_witness_refs: vec![witness.witness_id.clone()],
        source_coverage_gap_refs: Vec::new(),
        target_witness_kind: rule.target_witness_kind.clone(),
        proposed_operation: rule.proposed_operation.clone(),
        required_preconditions: rule.required_preconditions.clone(),
        expected_effect: rule.expected_effect.clone(),
        preserved_invariants: rule.preserved_invariants.clone(),
        possible_side_effects: rule.possible_side_effects.clone(),
        proof_obligation_refs: rule.proof_obligation_refs.clone(),
        patch_strategy: rule.patch_strategy.clone(),
        confidence: rule.confidence.clone(),
        traceability: vec![
            format!("witness:{}", witness.witness_id),
            format!("repairRule:{}", rule.repair_rule_id),
            format!("measurementBoundary:{}", witness.measurement_boundary),
        ],
        non_conclusions: rule.non_conclusions.clone(),
    }
}

fn feature_report_manual_witness_repair_suggestion(
    witness: &FeatureReportObstructionWitness,
    repair: &str,
) -> FeatureReportRepairSuggestion {
    FeatureReportRepairSuggestion {
        suggestion_id: format!(
            "repair-suggestion-{}-{}",
            stable_id_fragment(&witness.witness_id),
            stable_id_fragment(repair)
        ),
        repair_rule_id: None,
        source_witness_refs: vec![witness.witness_id.clone()],
        source_coverage_gap_refs: Vec::new(),
        target_witness_kind: witness.kind.clone(),
        proposed_operation: "manual".to_string(),
        required_preconditions: vec![
            "referenced witness evidence has been reviewed".to_string(),
            "selected measurement boundary is unchanged".to_string(),
        ],
        expected_effect: "reduce".to_string(),
        preserved_invariants: Vec::new(),
        possible_side_effects: vec![
            "manual repair can transfer complexity to another measured or unmeasured axis"
                .to_string(),
        ],
        proof_obligation_refs: witness.theorem_reference.clone(),
        patch_strategy: "manual".to_string(),
        confidence: "low".to_string(),
        traceability: vec![
            format!("witness:{}", witness.witness_id),
            format!("repairCandidate:{repair}"),
            format!("measurementBoundary:{}", witness.measurement_boundary),
        ],
        non_conclusions: feature_report_repair_non_conclusions(),
    }
}

fn feature_report_coverage_gap_repair_suggestion(
    gap: &FeatureReportCoverageGap,
) -> FeatureReportRepairSuggestion {
    let gap_ref = format!("coverage-gap-{}", stable_id_fragment(&gap.layer));
    FeatureReportRepairSuggestion {
        suggestion_id: format!("repair-suggestion-{gap_ref}"),
        repair_rule_id: None,
        source_witness_refs: Vec::new(),
        source_coverage_gap_refs: vec![gap_ref.clone()],
        target_witness_kind: "coverage_gap".to_string(),
        proposed_operation: "manual".to_string(),
        required_preconditions: vec![
            format!("{} layer evidence source is available", gap.layer),
            "unsupported constructs are reported instead of discharged".to_string(),
        ],
        expected_effect: "translate".to_string(),
        preserved_invariants: Vec::new(),
        possible_side_effects: vec![
            "adding evidence can reveal new obstruction witnesses".to_string(),
            "coverage improvement does not by itself remove existing obstructions".to_string(),
        ],
        proof_obligation_refs: Vec::new(),
        patch_strategy: "manual".to_string(),
        confidence: "low".to_string(),
        traceability: vec![
            gap_ref,
            format!("layer:{}", gap.layer),
            format!("measurementBoundary:{}", gap.measurement_boundary),
        ],
        non_conclusions: feature_report_repair_non_conclusions(),
    }
}

fn feature_report_repair_non_conclusions() -> Vec<String> {
    vec![
        "repair success is not concluded".to_string(),
        "all obstruction removal is not concluded".to_string(),
        "global flatness preservation is not concluded".to_string(),
        "empirical cost improvement is not concluded".to_string(),
    ]
}

fn feature_report_non_conclusions(
    document: &AirDocumentV0,
    split_status: &str,
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<String> {
    let mut non_conclusions = BTreeSet::new();
    non_conclusions.insert("tooling report is not a Lean proof".to_string());
    non_conclusions.insert("absence of unmeasured witnesses is not concluded".to_string());
    if split_status == "split" {
        non_conclusions.insert("static split does not conclude runtime flatness".to_string());
        non_conclusions.insert("static split does not conclude semantic flatness".to_string());
    }
    for gap in coverage_gaps {
        non_conclusions.insert(format!(
            "{} layer is {}",
            gap.layer, gap.measurement_boundary
        ));
        for conclusion in &gap.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }
    for claim in &document.claims {
        for conclusion in &claim.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }
    non_conclusions.into_iter().collect()
}

fn feature_report_required_action(
    split_status: &str,
    witnesses: &[FeatureReportObstructionWitness],
    coverage_gaps: &[FeatureReportCoverageGap],
    runtime_summary: &FeatureReportRuntimeSummary,
    theorem_checks: &[TheoremPreconditionCheck],
) -> String {
    if theorem_checks.iter().any(|check| {
        check.resolved_claim_classification == "BLOCKED_FORMAL_CLAIM"
            && check
                .missing_preconditions
                .iter()
                .any(|precondition| precondition.contains("AI session human review"))
    }) {
        return "complete human review before promoting AI-generated formal claims".to_string();
    }
    if split_status == "non_split" && !witnesses.is_empty() {
        return "review introduced obstruction witnesses before treating the feature as split"
            .to_string();
    }
    if runtime_summary.runtime_propagation.unwrap_or_default() > 0 {
        return "review measured runtime exposure radius separately from static split evidence"
            .to_string();
    }
    if !runtime_summary.coverage_gaps.is_empty() {
        return "add runtime edge evidence before treating runtime risk as zero".to_string();
    }
    match split_status {
        "split" if !coverage_gaps.is_empty() => {
            "review static split together with UNMEASURED coverage gaps".to_string()
        }
        "split" => "review preserved static invariants".to_string(),
        "unmeasured" => {
            "add static or policy evidence before classifying the extension".to_string()
        }
        _ => {
            "review coverage and theorem preconditions before classifying the extension".to_string()
        }
    }
}

fn feature_report_claim_classification(split_status: &str) -> String {
    match split_status {
        "split" | "non_split" => "MEASURED".to_string(),
        "unmeasured" => "UNMEASURED".to_string(),
        _ => "UNKNOWN".to_string(),
    }
}

fn feature_report_obstructing_relation(document: &AirDocumentV0, relation: &AirRelation) -> bool {
    let extraction_rule = relation.extraction_rule.as_deref().unwrap_or_default();
    relation.layer == "policy"
        || extraction_rule.contains("hidden")
        || relation.kind.contains("hidden")
        || document.policies.forbidden_edges.iter().any(|edge| {
            relation
                .from_component
                .as_ref()
                .zip(relation.to_component.as_ref())
                .map(|(from, to)| edge.contains(from) && edge.contains(to))
                .unwrap_or(false)
        })
}

fn feature_report_relation_witness_kind(
    document: &AirDocumentV0,
    relation: &AirRelation,
) -> String {
    let extraction_rule = relation.extraction_rule.as_deref().unwrap_or_default();
    if extraction_rule.contains("hidden")
        || relation.kind.contains("hidden")
        || document
            .policies
            .forbidden_edges
            .iter()
            .any(|edge| edge.contains("hiddenInteraction"))
    {
        "hidden_interaction".to_string()
    } else if relation.layer == "policy" {
        "policy_violation".to_string()
    } else {
        "invariant_not_preserved".to_string()
    }
}

fn feature_report_witness_roles(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec![
            "hidden_interaction".to_string(),
            "invariant_not_preserved".to_string(),
        ],
        "policy_violation" => vec![
            "embedding_broken".to_string(),
            "invariant_not_preserved".to_string(),
        ],
        _ => vec!["invariant_not_preserved".to_string()],
    }
}

fn feature_report_witness_classification(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec!["interaction".to_string()],
        "policy_violation" => vec!["liftingFailure".to_string()],
        _ => vec!["residualCoverageGap".to_string()],
    }
}

fn feature_report_witness_repairs(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec![
            "route the dependency through a declared interface".to_string(),
            "move direct internal-state access behind a feature port".to_string(),
        ],
        "policy_violation" => vec![
            "move the dependency behind an allowed boundary".to_string(),
            "update policy only if the architecture law intentionally changed".to_string(),
        ],
        _ => vec!["add evidence or refactor the obstructing relation".to_string()],
    }
}

fn feature_report_relation_claim<'a>(
    document: &'a AirDocumentV0,
    relation: &AirRelation,
) -> Option<&'a AirClaim> {
    document
        .claims
        .iter()
        .find(|claim| claim.subject_ref == relation.id)
        .or_else(|| {
            document.claims.iter().find(|claim| {
                !claim.evidence_refs.is_empty()
                    && claim
                        .evidence_refs
                        .iter()
                        .any(|evidence_ref| relation.evidence_refs.contains(evidence_ref))
            })
        })
}

fn feature_report_claim_non_conclusions(claim: Option<&AirClaim>) -> Vec<String> {
    let mut non_conclusions = claim
        .map(|claim| claim.non_conclusions.clone())
        .unwrap_or_default();
    non_conclusions.push("witness is not a formal theorem claim".to_string());
    non_conclusions
}

fn feature_report_evidence_refs(
    refs: &[String],
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportEvidenceRef> {
    refs.iter()
        .map(|evidence_ref| {
            let evidence = evidence_by_id.get(evidence_ref).copied();
            FeatureReportEvidenceRef {
                evidence_ref: evidence_ref.clone(),
                kind: evidence.map(|evidence| evidence.kind.clone()),
                artifact_ref: evidence.and_then(|evidence| evidence.artifact_ref.clone()),
                path: evidence.and_then(|evidence| evidence.path.clone()),
                symbol: evidence.and_then(|evidence| evidence.symbol.clone()),
                rule_id: evidence.and_then(|evidence| evidence.rule_id.clone()),
            }
        })
        .collect()
}

fn feature_report_axis_evidence_refs(document: &AirDocumentV0, axis: &str) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for claim in &document.claims {
        if claim.subject_ref == format!("signature.{axis}") {
            for evidence_ref in &claim.evidence_refs {
                refs.insert(evidence_ref.clone());
            }
        }
    }
    refs.into_iter().collect()
}

fn feature_report_axis_claim_refs(document: &AirDocumentV0, axis: &str) -> Vec<String> {
    document
        .claims
        .iter()
        .filter(|claim| claim.subject_ref == format!("signature.{axis}"))
        .map(|claim| claim.claim_id.clone())
        .collect()
}

fn feature_report_has_static_measurement(document: &AirDocumentV0) -> bool {
    document.coverage.layers.iter().any(|layer| {
        matches!(layer.layer.as_str(), "static" | "policy")
            && layer.measurement_boundary != "unmeasured"
    }) || document
        .signature
        .axes
        .iter()
        .any(|axis| axis.measured && static_report_axis(&axis.axis))
}

fn static_report_axis(axis: &str) -> bool {
    matches!(
        axis,
        "boundaryViolationCount"
            | "abstractionViolationCount"
            | "projectionSoundnessViolation"
            | "lspViolationCount"
            | "hasCycle"
            | "sccMaxSize"
            | "maxDepth"
            | "fanoutRisk"
            | "sccExcessSize"
            | "maxFanout"
            | "reachableConeSize"
            | "weightedSccRisk"
    )
}

fn count_air_relations(document: &AirDocumentV0, layer: &str) -> usize {
    document
        .relations
        .iter()
        .filter(|relation| relation.layer == layer)
        .count()
}

fn stable_id_fragment(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect()
}
