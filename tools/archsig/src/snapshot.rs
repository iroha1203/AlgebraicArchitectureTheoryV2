use std::collections::{BTreeMap, BTreeSet};

use crate::dataset::{
    DATASET_DELTA_AXES, dataset_metric_status, dataset_signature_shape, delta_signature_signed,
    metric_delta_status, signature_value,
};
use crate::{
    AttributionCandidate, ComponentSetDelta, ComponentUniverseValidationReport, EXTRACTOR_NAME,
    EXTRACTOR_VERSION, Edge, EdgeSetDelta, EmpiricalDatasetInput, ExtractorRef, GitCommitRef,
    MetricDeltaStatus, PolicyViolation, PolicyViolationSetDelta, RULE_SET_VERSION,
    SIGNATURE_DIFF_REPORT_SCHEMA_VERSION, SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION, Sig0Document,
    SignatureAxisChange, SignatureDiffReportV0, SignatureSnapshot, SignatureSnapshotStoreRecordV0,
    SnapshotAnalysisMetadata, SnapshotArtifacts, SnapshotComparisonStatus, SnapshotDiffAttribution,
    SnapshotDiffEndpoint, SnapshotEvidenceDiff, SnapshotExtractorMetadata, SnapshotPolicyMetadata,
    SnapshotRecordInput, SnapshotValidationSummary, UnmeasuredAxisDelta,
};

pub fn build_signature_snapshot_record(
    document: &Sig0Document,
    validation_report: Option<&ComponentUniverseValidationReport>,
    input: SnapshotRecordInput,
) -> SignatureSnapshotStoreRecordV0 {
    let validation_summary =
        snapshot_validation_summary(validation_report, input.validation_report_path.clone());
    let mut exclusion_reasons = Vec::new();
    match validation_summary.result.as_str() {
        "fail" => exclusion_reasons.push("validationSummary.result = fail".to_string()),
        "not_run" => exclusion_reasons.push("validationSummary.result = not_run".to_string()),
        _ => {}
    }

    SignatureSnapshotStoreRecordV0 {
        schema_version: SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        revision: input.revision,
        scan: input.scan,
        extractor: SnapshotExtractorMetadata {
            name: EXTRACTOR_NAME.to_string(),
            version: EXTRACTOR_VERSION.to_string(),
            rule_set_version: RULE_SET_VERSION.to_string(),
            input_schema_version: document.schema_version.clone(),
        },
        policy: SnapshotPolicyMetadata {
            policy_id: document.policies.policy_id.clone(),
            schema_version: document.policies.schema_version.clone(),
            version: input.policy_version,
            source_path: input.policy_source_path.clone(),
            content_hash: input.policy_content_hash,
        },
        signature: dataset_signature_shape(document),
        metric_status: dataset_metric_status(document),
        validation_summary,
        artifacts: SnapshotArtifacts {
            extractor_output_path: input.extractor_output_path,
            validation_report_path: input.validation_report_path,
            policy_path: input.policy_source_path,
        },
        analysis_metadata: SnapshotAnalysisMetadata {
            excluded_from_primary_diff: !exclusion_reasons.is_empty(),
            exclusion_reasons,
            tags: input.tags,
            notes: input.notes,
        },
    }
}

pub fn build_signature_diff_report(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
    before_document: Option<&Sig0Document>,
    after_document: Option<&Sig0Document>,
    pr_metadata: &[EmpiricalDatasetInput],
) -> SignatureDiffReportV0 {
    let before_snapshot = store_record_signature_snapshot(before, "before");
    let after_snapshot = store_record_signature_snapshot(after, "after");
    let delta_signature_signed = delta_signature_signed(&before_snapshot, &after_snapshot);
    let metric_delta_status = metric_delta_status(&before_snapshot, &after_snapshot);
    let (worsened_axes, improved_axes, unchanged_axes, unmeasured_axes) =
        classify_axis_deltas(before, after, &metric_delta_status);
    let evidence_diff = snapshot_evidence_diff(before_document, after_document);
    let attribution = snapshot_diff_attribution(after, &evidence_diff, &worsened_axes, pr_metadata);

    SignatureDiffReportV0 {
        schema_version: SIGNATURE_DIFF_REPORT_SCHEMA_VERSION.to_string(),
        before: snapshot_diff_endpoint(before),
        after: snapshot_diff_endpoint(after),
        comparison_status: snapshot_comparison_status(before, after),
        delta_signature_signed,
        metric_delta_status,
        worsened_axes,
        improved_axes,
        unchanged_axes,
        unmeasured_axes,
        evidence_diff,
        attribution,
    }
}

fn snapshot_validation_summary(
    report: Option<&ComponentUniverseValidationReport>,
    report_path: Option<String>,
) -> SnapshotValidationSummary {
    match report {
        Some(report) => SnapshotValidationSummary {
            schema_version: Some(report.schema_version.clone()),
            result: report.summary.result.clone(),
            universe_mode: Some(report.universe_mode.clone()),
            failed_check_count: Some(report.summary.failed_check_count),
            warning_check_count: Some(report.summary.warning_check_count),
            not_measured_check_count: Some(report.summary.not_measured_check_count),
            report_path,
        },
        None => SnapshotValidationSummary {
            schema_version: None,
            result: "not_run".to_string(),
            universe_mode: None,
            failed_check_count: None,
            warning_check_count: None,
            not_measured_check_count: None,
            report_path: None,
        },
    }
}

fn store_record_signature_snapshot(
    record: &SignatureSnapshotStoreRecordV0,
    role: &str,
) -> SignatureSnapshot {
    SignatureSnapshot {
        commit: GitCommitRef {
            sha: record.revision.sha.clone(),
            role: role.to_string(),
        },
        extractor: ExtractorRef {
            name: record.extractor.name.clone(),
            version: record.extractor.version.clone(),
            rule_set_version: record.extractor.rule_set_version.clone(),
            policy_version: record.policy.policy_id.clone(),
        },
        signature: record.signature.clone(),
        metric_status: record.metric_status.clone(),
    }
}

fn snapshot_diff_endpoint(record: &SignatureSnapshotStoreRecordV0) -> SnapshotDiffEndpoint {
    SnapshotDiffEndpoint {
        repository: record.repository.clone(),
        revision: record.revision.clone(),
        validation_result: record.validation_summary.result.clone(),
        extractor_version: record.extractor.version.clone(),
        rule_set_version: record.extractor.rule_set_version.clone(),
        policy_id: record.policy.policy_id.clone(),
    }
}

fn snapshot_comparison_status(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
) -> SnapshotComparisonStatus {
    let mut reasons = Vec::new();
    if !matches!(before.validation_summary.result.as_str(), "pass" | "warn") {
        reasons.push(format!(
            "before validationSummary.result = {}",
            before.validation_summary.result
        ));
    }
    if !matches!(after.validation_summary.result.as_str(), "pass" | "warn") {
        reasons.push(format!(
            "after validationSummary.result = {}",
            after.validation_summary.result
        ));
    }
    if before.extractor.name != after.extractor.name {
        reasons.push("extractor.name differs".to_string());
    }
    if before.extractor.version != after.extractor.version {
        reasons.push("extractor.version differs".to_string());
    }
    if before.extractor.rule_set_version != after.extractor.rule_set_version {
        reasons.push("extractor.ruleSetVersion differs".to_string());
    }
    if before.policy.policy_id != after.policy.policy_id {
        reasons.push("policy.policyId differs".to_string());
    }
    if before.policy.version != after.policy.version {
        reasons.push("policy.version differs".to_string());
    }

    SnapshotComparisonStatus {
        primary_diff_eligible: reasons.is_empty(),
        reasons,
    }
}

fn classify_axis_deltas(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
    status: &BTreeMap<String, MetricDeltaStatus>,
) -> (
    Vec<SignatureAxisChange>,
    Vec<SignatureAxisChange>,
    Vec<SignatureAxisChange>,
    Vec<UnmeasuredAxisDelta>,
) {
    let mut worsened = Vec::new();
    let mut improved = Vec::new();
    let mut unchanged = Vec::new();
    let mut unmeasured = Vec::new();

    for axis in DATASET_DELTA_AXES {
        let axis_status = status
            .get(axis)
            .expect("metric delta status exists for every dataset delta axis");
        let before_value = signature_value(axis, &before.signature);
        let after_value = signature_value(axis, &after.signature);
        if !axis_status.comparable {
            unmeasured.push(UnmeasuredAxisDelta {
                axis: axis.to_string(),
                reason: axis_status.reason.clone(),
                before_measured: axis_status.before_measured,
                after_measured: axis_status.after_measured,
            });
            continue;
        }

        let before_value = before_value.expect("comparable before value exists");
        let after_value = after_value.expect("comparable after value exists");
        let change = SignatureAxisChange {
            axis: axis.to_string(),
            before: before_value,
            after: after_value,
            delta: after_value - before_value,
        };
        match change.delta.cmp(&0) {
            std::cmp::Ordering::Greater => worsened.push(change),
            std::cmp::Ordering::Less => improved.push(change),
            std::cmp::Ordering::Equal => unchanged.push(change),
        }
    }

    (worsened, improved, unchanged, unmeasured)
}

fn snapshot_evidence_diff(
    before: Option<&Sig0Document>,
    after: Option<&Sig0Document>,
) -> SnapshotEvidenceDiff {
    let (before, after) = match (before, after) {
        (Some(before), Some(after)) => (before, after),
        _ => {
            return SnapshotEvidenceDiff {
                available: false,
                unavailable_reason: Some(
                    "before and after ArchSig JSON are required for component / edge evidence diff"
                        .to_string(),
                ),
                component_delta: None,
                edge_delta: None,
                policy_violation_delta: None,
            };
        }
    };

    let before_components = before
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect::<BTreeSet<_>>();
    let after_components = after
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect::<BTreeSet<_>>();
    let before_edges = before.edges.iter().cloned().collect::<BTreeSet<_>>();
    let after_edges = after.edges.iter().cloned().collect::<BTreeSet<_>>();
    let before_policy_violations = before
        .policy_violations
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let after_policy_violations = after
        .policy_violations
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();

    SnapshotEvidenceDiff {
        available: true,
        unavailable_reason: None,
        component_delta: Some(ComponentSetDelta {
            before_count: before_components.len(),
            after_count: after_components.len(),
            delta: after_components.len() as i64 - before_components.len() as i64,
            added: set_added(&before_components, &after_components),
            removed: set_removed(&before_components, &after_components),
        }),
        edge_delta: Some(EdgeSetDelta {
            before_count: before_edges.len(),
            after_count: after_edges.len(),
            delta: after_edges.len() as i64 - before_edges.len() as i64,
            added: set_added(&before_edges, &after_edges),
            removed: set_removed(&before_edges, &after_edges),
        }),
        policy_violation_delta: Some(PolicyViolationSetDelta {
            before_count: before_policy_violations.len(),
            after_count: after_policy_violations.len(),
            delta: after_policy_violations.len() as i64 - before_policy_violations.len() as i64,
            added: set_added(&before_policy_violations, &after_policy_violations),
            removed: set_removed(&before_policy_violations, &after_policy_violations),
        }),
    }
}

fn set_added<T: Ord + Clone>(before: &BTreeSet<T>, after: &BTreeSet<T>) -> Vec<T> {
    after.difference(before).cloned().collect()
}

fn set_removed<T: Ord + Clone>(before: &BTreeSet<T>, after: &BTreeSet<T>) -> Vec<T> {
    before.difference(after).cloned().collect()
}

fn snapshot_diff_attribution(
    after: &SignatureSnapshotStoreRecordV0,
    evidence_diff: &SnapshotEvidenceDiff,
    worsened_axes: &[SignatureAxisChange],
    pr_metadata: &[EmpiricalDatasetInput],
) -> SnapshotDiffAttribution {
    let touched_components = touched_components_from_evidence_diff(evidence_diff);
    let worsened_axis_names = worsened_axes
        .iter()
        .map(|axis| axis.axis.clone())
        .collect::<Vec<_>>();
    let mut candidates = pr_metadata
        .iter()
        .map(|metadata| {
            attribution_candidate(
                after,
                evidence_diff,
                &touched_components,
                &worsened_axis_names,
                metadata,
            )
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| {
        right
            .confidence
            .partial_cmp(&left.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(left.id.cmp(&right.id))
    });

    let method = if pr_metadata.is_empty() {
        "none: PR metadata not provided".to_string()
    } else if touched_components.is_empty() {
        "pr-metadata: commit match and changed components; raw evidence diff unavailable or empty"
            .to_string()
    } else {
        "pr-metadata: commit match and changed-component overlap with added/removed evidence"
            .to_string()
    };

    let shared_worsened_axes = if candidates
        .iter()
        .filter(|candidate| candidate.confidence_level != "unknown")
        .count()
        > 1
    {
        worsened_axis_names
    } else {
        Vec::new()
    };

    SnapshotDiffAttribution {
        method,
        shared_worsened_axes,
        candidates,
    }
}

fn touched_components_from_evidence_diff(evidence_diff: &SnapshotEvidenceDiff) -> BTreeSet<String> {
    let mut components = BTreeSet::new();
    if let Some(component_delta) = &evidence_diff.component_delta {
        components.extend(component_delta.added.iter().cloned());
        components.extend(component_delta.removed.iter().cloned());
    }
    if let Some(edge_delta) = &evidence_diff.edge_delta {
        for edge in edge_delta.added.iter().chain(edge_delta.removed.iter()) {
            components.insert(edge.source.clone());
            components.insert(edge.target.clone());
        }
    }
    if let Some(policy_delta) = &evidence_diff.policy_violation_delta {
        for violation in policy_delta.added.iter().chain(policy_delta.removed.iter()) {
            components.insert(violation.source.clone());
            components.insert(violation.target.clone());
        }
    }
    components
}

fn attribution_candidate(
    after: &SignatureSnapshotStoreRecordV0,
    evidence_diff: &SnapshotEvidenceDiff,
    touched_components: &BTreeSet<String>,
    worsened_axes: &[String],
    metadata: &EmpiricalDatasetInput,
) -> AttributionCandidate {
    let changed_components = metadata.pr_metrics.changed_components.clone();
    let changed_set = changed_components.iter().cloned().collect::<BTreeSet<_>>();
    let overlap = changed_set
        .intersection(touched_components)
        .cloned()
        .collect::<Vec<_>>();
    let matched_edges = matched_edges_from_evidence_diff(evidence_diff, &changed_set);
    let matched_policy_violations =
        matched_policy_violations_from_evidence_diff(evidence_diff, &changed_set);
    let mut matched_components = overlap;
    matched_components.sort();
    matched_components.dedup();
    let mut confidence = 0.0;
    let mut reasons = Vec::new();

    if after.revision.sha == metadata.pull_request.head_commit {
        confidence += 0.35;
        reasons.push("after revision matches pullRequest.headCommit".to_string());
    }
    if metadata
        .pull_request
        .merge_commit
        .as_ref()
        .is_some_and(|merge_commit| after.revision.sha == *merge_commit)
    {
        confidence += 0.35;
        reasons.push("after revision matches pullRequest.mergeCommit".to_string());
    }
    if !matched_components.is_empty() {
        let denominator = touched_components.len().max(1) as f64;
        confidence += 0.35 * (matched_components.len() as f64 / denominator).min(1.0);
        reasons.push(format!(
            "changed components overlap with evidence diff: {}",
            matched_components.join(", ")
        ));
    }
    if !matched_edges.is_empty() {
        confidence += 0.15;
        reasons.push(format!(
            "changed components touch added/removed edges: {}",
            edge_labels(&matched_edges).join(", ")
        ));
    }
    if !matched_policy_violations.is_empty() {
        confidence += 0.15;
        reasons.push(format!(
            "changed components touch added/removed policy violations: {}",
            policy_violation_labels(&matched_policy_violations).join(", ")
        ));
    }
    if !worsened_axes.is_empty() && confidence > 0.0 {
        confidence += 0.10;
        reasons.push(format!(
            "signature worsened on axes: {}",
            worsened_axes.join(", ")
        ));
    }
    if reasons.is_empty() {
        reasons.push(
            "weak candidate: PR metadata provided but no commit or evidence overlap".to_string(),
        );
    }
    let confidence = round_confidence(confidence.min(0.95));

    AttributionCandidate {
        kind: "pullRequest".to_string(),
        id: format!("#{}", metadata.pull_request.number),
        confidence,
        confidence_level: confidence_level(confidence).to_string(),
        reasons,
        changed_components,
        matched_components,
        matched_edges,
        matched_policy_violations,
        affected_axes: if confidence > 0.0 {
            worsened_axes.to_vec()
        } else {
            Vec::new()
        },
    }
}

fn matched_edges_from_evidence_diff(
    evidence_diff: &SnapshotEvidenceDiff,
    changed_components: &BTreeSet<String>,
) -> Vec<Edge> {
    let Some(edge_delta) = &evidence_diff.edge_delta else {
        return Vec::new();
    };
    edge_delta
        .added
        .iter()
        .chain(edge_delta.removed.iter())
        .filter(|edge| {
            changed_components.contains(&edge.source) || changed_components.contains(&edge.target)
        })
        .cloned()
        .collect()
}

fn matched_policy_violations_from_evidence_diff(
    evidence_diff: &SnapshotEvidenceDiff,
    changed_components: &BTreeSet<String>,
) -> Vec<PolicyViolation> {
    let Some(policy_delta) = &evidence_diff.policy_violation_delta else {
        return Vec::new();
    };
    policy_delta
        .added
        .iter()
        .chain(policy_delta.removed.iter())
        .filter(|violation| {
            changed_components.contains(&violation.source)
                || changed_components.contains(&violation.target)
        })
        .cloned()
        .collect()
}

fn edge_labels(edges: &[Edge]) -> Vec<String> {
    edges
        .iter()
        .map(|edge| format!("{} -> {}", edge.source, edge.target))
        .collect()
}

fn policy_violation_labels(violations: &[PolicyViolation]) -> Vec<String> {
    violations
        .iter()
        .map(|violation| {
            format!(
                "{}:{} -> {}",
                violation.axis, violation.source, violation.target
            )
        })
        .collect()
}

fn confidence_level(confidence: f64) -> &'static str {
    if confidence >= 0.80 {
        "high"
    } else if confidence >= 0.50 {
        "medium"
    } else if confidence > 0.0 {
        "low"
    } else {
        "unknown"
    }
}

fn round_confidence(value: f64) -> f64 {
    (value * 100.0).round() / 100.0
}
