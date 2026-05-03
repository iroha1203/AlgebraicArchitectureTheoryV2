use std::collections::{BTreeMap, BTreeSet};

use crate::theorem_precondition::build_theorem_precondition_check_report;
use crate::{
    AirClaim, AirDocumentV0, AirEvidence, AirRelation, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    FeatureExtensionReportV0, FeatureReportArchitectureSummary, FeatureReportCoverageGap,
    FeatureReportEdgeRef, FeatureReportEvidenceRef, FeatureReportInput,
    FeatureReportInterpretedExtension, FeatureReportInvariant, FeatureReportObstructionWitness,
    FeatureReportReviewSummary, FeatureReportSemanticPathSummary,
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
    let undischarged_assumptions = feature_report_undischarged_assumptions(document);
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

    FeatureExtensionReportV0 {
        schema_version: FEATURE_EXTENSION_REPORT_SCHEMA_VERSION.to_string(),
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
        split_status,
        preserved_invariants,
        changed_invariants,
        introduced_obstruction_witnesses,
        eliminated_obstruction_witnesses: Vec::new(),
        complexity_transfer_candidates: Vec::new(),
        semantic_path_summary: FeatureReportSemanticPathSummary {
            path_count: document.architecture_paths.len(),
            diagram_count: document.semantic_diagrams.len(),
            nonfillability_witness_count: document.nonfillability_witnesses.len(),
        },
        theorem_package_refs,
        theorem_precondition_summary: theorem_precondition_report.summary,
        theorem_precondition_checks: theorem_precondition_report.checks,
        discharged_assumptions,
        undischarged_assumptions,
        coverage_gaps,
        unsupported_constructs,
        repair_suggestions,
        empirical_annotations: vec![
            "Feature Extension Report v0 is a static tooling report".to_string(),
            "Runtime and semantic conclusions require separate evidence".to_string(),
        ],
        non_conclusions,
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
            paths: Vec::new(),
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

fn feature_report_undischarged_assumptions(document: &AirDocumentV0) -> Vec<String> {
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
) -> Vec<String> {
    let mut suggestions = BTreeSet::new();
    for witness in witnesses {
        for repair in &witness.repair_candidates {
            suggestions.insert(repair.clone());
        }
    }
    for gap in coverage_gaps {
        if gap.measurement_boundary == "UNMEASURED" {
            suggestions.insert(format!(
                "add {} layer evidence before drawing global conclusions",
                gap.layer
            ));
        }
    }
    suggestions.into_iter().collect()
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
) -> String {
    match split_status {
        "non_split" if !witnesses.is_empty() => {
            "review introduced obstruction witnesses before treating the feature as split"
                .to_string()
        }
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
