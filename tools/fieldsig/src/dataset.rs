use std::collections::BTreeMap;
use std::error::Error;

use crate::graph::Graph;
use crate::{
    ArchitectureSignatureV1DatasetShape, EMPIRICAL_DATASET_SCHEMA_VERSION, EXTRACTOR_NAME,
    EXTRACTOR_VERSION, EmpiricalDatasetInput, EmpiricalSignatureDatasetV0, ExtractorRef,
    GitCommitRef, MetricDeltaStatus, MetricStatus, NullableSignatureIntVector, RULE_SET_VERSION,
    Sig0Document, SignatureSnapshot, measured_status, unmeasured_status,
};

pub(crate) const DATASET_SIGNATURE_AXES: [&str; 16] = [
    "hasCycle",
    "sccMaxSize",
    "maxDepth",
    "fanoutRisk",
    "boundaryViolationCount",
    "abstractionViolationCount",
    "sccExcessSize",
    "maxFanout",
    "reachableConeSize",
    "weightedSccRisk",
    "projectionSoundnessViolation",
    "lspViolationCount",
    "nilpotencyIndex",
    "runtimePropagation",
    "relationComplexity",
    "empiricalChangeCost",
];

pub(crate) const DATASET_DELTA_AXES: [&str; 15] = [
    "hasCycle",
    "sccMaxSize",
    "maxDepth",
    "fanoutRisk",
    "boundaryViolationCount",
    "abstractionViolationCount",
    "sccExcessSize",
    "maxFanout",
    "reachableConeSize",
    "weightedSccRisk",
    "projectionSoundnessViolation",
    "lspViolationCount",
    "nilpotencyIndex",
    "runtimePropagation",
    "relationComplexity",
];

pub fn build_empirical_dataset(
    before: &Sig0Document,
    after: &Sig0Document,
    mut input: EmpiricalDatasetInput,
    after_commit_role: &str,
) -> Result<EmpiricalSignatureDatasetV0, Box<dyn Error>> {
    if !matches!(after_commit_role, "head" | "merge") {
        return Err(format!("unsupported after commit role: {after_commit_role}").into());
    }

    let before_snapshot = signature_snapshot(
        before,
        GitCommitRef {
            sha: input.pull_request.base_commit.clone(),
            role: "base".to_string(),
        },
    );
    let after_sha = match after_commit_role {
        "head" => input.pull_request.head_commit.clone(),
        "merge" => input
            .pull_request
            .merge_commit
            .clone()
            .ok_or("after commit role merge requires pullRequest.mergeCommit")?,
        _ => unreachable!("after commit role is checked above"),
    };
    let after_snapshot = signature_snapshot(
        after,
        GitCommitRef {
            sha: after_sha,
            role: after_commit_role.to_string(),
        },
    );
    let delta_signature_signed = delta_signature_signed(&before_snapshot, &after_snapshot);
    let metric_delta_status = metric_delta_status(&before_snapshot, &after_snapshot);

    input.analysis_metadata.signature_after_commit_role = after_commit_role.to_string();

    Ok(EmpiricalSignatureDatasetV0 {
        schema_version: EMPIRICAL_DATASET_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        pull_request: input.pull_request,
        signature_before: before_snapshot,
        signature_after: after_snapshot,
        delta_signature_signed,
        metric_delta_status,
        pr_metrics: input.pr_metrics,
        issue_incident_links: input.issue_incident_links,
        analysis_metadata: input.analysis_metadata,
    })
}

pub(crate) fn signature_snapshot(
    document: &Sig0Document,
    commit: GitCommitRef,
) -> SignatureSnapshot {
    let signature = dataset_signature_shape(document);
    SignatureSnapshot {
        commit,
        extractor: ExtractorRef {
            name: EXTRACTOR_NAME.to_string(),
            version: EXTRACTOR_VERSION.to_string(),
            rule_set_version: RULE_SET_VERSION.to_string(),
            policy_version: document.policies.policy_id.clone(),
        },
        metric_status: dataset_metric_status(document),
        signature,
    }
}

pub(crate) fn dataset_signature_shape(
    document: &Sig0Document,
) -> ArchitectureSignatureV1DatasetShape {
    let graph = Graph::from_components_and_edges(&document.components, &document.edges);
    let runtime_propagation = document
        .runtime_dependency_graph
        .as_ref()
        .map(|projection| {
            Graph::from_components_and_edges(&document.components, &projection.edges)
                .reachable_cone_size()
        });

    ArchitectureSignatureV1DatasetShape {
        has_cycle: document.signature.has_cycle,
        scc_max_size: document.signature.scc_max_size,
        max_depth: document.signature.max_depth,
        fanout_risk: document.signature.fanout_risk,
        boundary_violation_count: document.signature.boundary_violation_count,
        abstraction_violation_count: document.signature.abstraction_violation_count,
        scc_excess_size: document.signature.scc_max_size.saturating_sub(1),
        max_fanout: graph.max_fanout(),
        reachable_cone_size: graph.reachable_cone_size(),
        weighted_scc_risk: None,
        projection_soundness_violation: None,
        lsp_violation_count: None,
        nilpotency_index: None,
        runtime_propagation,
        relation_complexity: None,
        empirical_change_cost: None,
    }
}

pub(crate) fn dataset_metric_status(document: &Sig0Document) -> BTreeMap<String, MetricStatus> {
    let mut status = BTreeMap::new();
    for axis in DATASET_SIGNATURE_AXES {
        let axis_status = match axis {
            "hasCycle"
            | "sccMaxSize"
            | "maxDepth"
            | "fanoutRisk"
            | "boundaryViolationCount"
            | "abstractionViolationCount" => document
                .metric_status
                .get(axis)
                .cloned()
                .unwrap_or_else(|| {
                    unmeasured_status(format!("legacy data without metricStatus entry for {axis}"))
                }),
            "sccExcessSize" => measured_status("archsig:derived-scc-excess"),
            "maxFanout" => measured_status("archsig:import-graph"),
            "reachableConeSize" => measured_status("archsig:import-graph"),
            "weightedSccRisk" => unmeasured_status("weight rule set not provided".to_string()),
            "projectionSoundnessViolation" => {
                unmeasured_status("projection rule set not provided".to_string())
            }
            "lspViolationCount" => {
                unmeasured_status("observation rule set not provided".to_string())
            }
            "nilpotencyIndex" => unmeasured_status("matrix bridge output not provided".to_string()),
            "runtimePropagation" => {
                document
                    .metric_status
                    .get(axis)
                    .cloned()
                    .unwrap_or_else(|| {
                        unmeasured_status("runtime dependency graph not provided".to_string())
                    })
            }
            "relationComplexity" => {
                unmeasured_status("relation complexity observation not provided".to_string())
            }
            "empiricalChangeCost" => {
                unmeasured_status("empirical target variable not provided".to_string())
            }
            _ => unreachable!("all dataset axes are covered"),
        };
        status.insert(axis.to_string(), axis_status);
    }
    status
}

pub(crate) fn delta_signature_signed(
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> NullableSignatureIntVector {
    NullableSignatureIntVector {
        has_cycle: signed_delta("hasCycle", before, after),
        scc_max_size: signed_delta("sccMaxSize", before, after),
        max_depth: signed_delta("maxDepth", before, after),
        fanout_risk: signed_delta("fanoutRisk", before, after),
        boundary_violation_count: signed_delta("boundaryViolationCount", before, after),
        abstraction_violation_count: signed_delta("abstractionViolationCount", before, after),
        scc_excess_size: signed_delta("sccExcessSize", before, after),
        max_fanout: signed_delta("maxFanout", before, after),
        reachable_cone_size: signed_delta("reachableConeSize", before, after),
        weighted_scc_risk: signed_delta("weightedSccRisk", before, after),
        projection_soundness_violation: signed_delta("projectionSoundnessViolation", before, after),
        lsp_violation_count: signed_delta("lspViolationCount", before, after),
        nilpotency_index: signed_delta("nilpotencyIndex", before, after),
        runtime_propagation: signed_delta("runtimePropagation", before, after),
        relation_complexity: signed_delta("relationComplexity", before, after),
    }
}

pub(crate) fn metric_delta_status(
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> BTreeMap<String, MetricDeltaStatus> {
    DATASET_DELTA_AXES
        .iter()
        .map(|axis| ((*axis).to_string(), delta_status(axis, before, after)))
        .collect()
}

fn signed_delta(axis: &str, before: &SignatureSnapshot, after: &SignatureSnapshot) -> Option<i64> {
    let before_measured = is_measured(axis, &before.metric_status);
    let after_measured = is_measured(axis, &after.metric_status);
    if !before_measured || !after_measured {
        return None;
    }

    Some(signature_value(axis, &after.signature)? - signature_value(axis, &before.signature)?)
}

fn delta_status(
    axis: &str,
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> MetricDeltaStatus {
    let before_measured = is_measured(axis, &before.metric_status);
    let after_measured = is_measured(axis, &after.metric_status);
    let before_value = signature_value(axis, &before.signature);
    let after_value = signature_value(axis, &after.signature);
    let comparable =
        before_measured && after_measured && before_value.is_some() && after_value.is_some();
    let reason = if comparable {
        "measured before and after".to_string()
    } else {
        delta_unavailable_reason(
            axis,
            before_measured,
            after_measured,
            before_value.is_some(),
            after_value.is_some(),
            &before.metric_status,
            &after.metric_status,
        )
    };

    MetricDeltaStatus {
        comparable,
        reason,
        before_measured,
        after_measured,
    }
}

fn is_measured(axis: &str, metric_status: &BTreeMap<String, MetricStatus>) -> bool {
    metric_status
        .get(axis)
        .is_some_and(|status| status.measured)
}

pub(crate) fn signature_value(
    axis: &str,
    signature: &ArchitectureSignatureV1DatasetShape,
) -> Option<i64> {
    let value = match axis {
        "hasCycle" => Some(signature.has_cycle),
        "sccMaxSize" => Some(signature.scc_max_size),
        "maxDepth" => Some(signature.max_depth),
        "fanoutRisk" => Some(signature.fanout_risk),
        "boundaryViolationCount" => Some(signature.boundary_violation_count),
        "abstractionViolationCount" => Some(signature.abstraction_violation_count),
        "sccExcessSize" => Some(signature.scc_excess_size),
        "maxFanout" => Some(signature.max_fanout),
        "reachableConeSize" => Some(signature.reachable_cone_size),
        "weightedSccRisk" => signature.weighted_scc_risk,
        "projectionSoundnessViolation" => signature.projection_soundness_violation,
        "lspViolationCount" => signature.lsp_violation_count,
        "nilpotencyIndex" => signature.nilpotency_index,
        "runtimePropagation" => signature.runtime_propagation,
        "relationComplexity" => signature.relation_complexity,
        _ => None,
    };
    value.map(|value| value as i64)
}

fn delta_unavailable_reason(
    axis: &str,
    before_measured: bool,
    after_measured: bool,
    before_value_present: bool,
    after_value_present: bool,
    before_status: &BTreeMap<String, MetricStatus>,
    after_status: &BTreeMap<String, MetricStatus>,
) -> String {
    let mut reasons = Vec::new();
    if !before_measured {
        reasons.push(format!(
            "before: {}",
            metric_status_reason(axis, before_status)
        ));
    }
    if !after_measured {
        reasons.push(format!(
            "after: {}",
            metric_status_reason(axis, after_status)
        ));
    }
    if before_measured && !before_value_present {
        reasons.push("before signature value is null".to_string());
    }
    if after_measured && !after_value_present {
        reasons.push("after signature value is null".to_string());
    }
    reasons.join("; ")
}

fn metric_status_reason(axis: &str, metric_status: &BTreeMap<String, MetricStatus>) -> String {
    metric_status
        .get(axis)
        .and_then(|status| status.reason.clone())
        .unwrap_or_else(|| "metricStatus entry is missing".to_string())
}

#[cfg(test)]
mod tests {
    use crate::EMPIRICAL_DATASET_SCHEMA_VERSION;
    use crate::test_support::{dataset_input, sig0_document_for_edges};

    use super::build_empirical_dataset;

    #[test]
    fn builds_empirical_dataset_with_comparable_and_unmeasured_deltas() {
        let before = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B")],
        );
        let after = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B"), ("A", "C"), ("C", "D")],
        );

        let dataset = build_empirical_dataset(&before, &after, dataset_input(), "head")
            .expect("dataset builds");

        assert_eq!(dataset.schema_version, EMPIRICAL_DATASET_SCHEMA_VERSION);
        assert_eq!(dataset.signature_before.commit.sha, "base-sha");
        assert_eq!(dataset.signature_after.commit.role, "head");
        assert_eq!(dataset.delta_signature_signed.fanout_risk, Some(2));
        assert_eq!(dataset.delta_signature_signed.max_fanout, Some(1));
        assert_eq!(dataset.delta_signature_signed.reachable_cone_size, Some(2));
        assert_eq!(
            dataset.delta_signature_signed.boundary_violation_count,
            None
        );
        assert_eq!(dataset.signature_after.signature.weighted_scc_risk, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("weightedSccRisk")
                .expect("weighted status")
                .measured
        );
        assert_eq!(dataset.signature_after.signature.runtime_propagation, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let fanout_status = dataset
            .metric_delta_status
            .get("fanoutRisk")
            .expect("fanout delta status");
        assert!(fanout_status.comparable);
        assert!(fanout_status.before_measured);
        assert!(fanout_status.after_measured);

        let boundary_status = dataset
            .metric_delta_status
            .get("boundaryViolationCount")
            .expect("boundary delta status");
        assert!(!boundary_status.comparable);
        assert!(!boundary_status.before_measured);
        assert!(!boundary_status.after_measured);
        assert!(
            boundary_status
                .reason
                .contains("policy file not provided before")
                || boundary_status.reason.contains("policy file not provided")
        );
    }

    #[test]
    fn dataset_merge_role_uses_merge_commit() {
        let document = sig0_document_for_edges(vec![("A", "A.lean")], Vec::new());
        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "merge")
            .expect("dataset builds");

        assert_eq!(dataset.signature_after.commit.sha, "merge-sha");
        assert_eq!(
            dataset.analysis_metadata.signature_after_commit_role,
            "merge"
        );
    }
}
