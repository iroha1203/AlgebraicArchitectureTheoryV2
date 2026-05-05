use std::collections::{BTreeMap, BTreeSet};

use crate::dataset::{DATASET_SIGNATURE_AXES, dataset_metric_status, dataset_signature_shape};
use crate::schema_versioning::air_schema_compatibility_metadata;
use crate::{
    AIR_SCHEMA_VERSION, AirArtifact, AirClaim, AirComponent, AirCoverage, AirCoverageLayer,
    AirDocumentInput, AirDocumentV0, AirEvidence, AirExtension, AirFeature, AirIdPolicies,
    AirOperationTrace, AirPolicies, AirRelation, AirRevision, AirSignature, AirSignatureAxis,
    ArchitectureSignatureV1DatasetShape, COMPONENT_KIND, ComponentUniverseValidationReport,
    EMPIRICAL_DATASET_SCHEMA_VERSION, EXTRACTOR_NAME, Edge, EmpiricalDatasetInput, MetricStatus,
    PYTHON_COMPONENT_KIND, PYTHON_IMPORT_RULE_VERSION, RUNTIME_PROJECTION_RULE_VERSION,
    Sig0Document, SignatureDiffReportV0, unmeasured_status,
};

pub fn build_air_document(
    sig0: &Sig0Document,
    validation: Option<&ComponentUniverseValidationReport>,
    diff: Option<&SignatureDiffReportV0>,
    pr_metadata: Option<&EmpiricalDatasetInput>,
    input: AirDocumentInput,
) -> AirDocumentV0 {
    let signature = dataset_signature_shape(sig0);
    let metric_status = dataset_metric_status(sig0);
    let signature_axes = air_signature_axes(&signature, &metric_status);
    let component_lifecycle = air_component_lifecycle(diff);
    let static_extraction_rule = static_extraction_rule(sig0);
    let static_evidence_kind = static_evidence_kind(sig0);

    let mut artifacts = vec![AirArtifact {
        artifact_id: "artifact-sig0".to_string(),
        kind: "sig0".to_string(),
        schema_version: Some(sig0.schema_version.clone()),
        path: Some(input.sig0_path),
        content_hash: None,
        produced_by: Some(EXTRACTOR_NAME.to_string()),
    }];
    if let (Some(report), Some(path)) = (validation, input.validation_path) {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-validation".to_string(),
            kind: "validation".to_string(),
            schema_version: Some(report.schema_version.clone()),
            path: Some(path),
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if let (Some(report), Some(path)) = (diff, input.diff_path) {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-diff".to_string(),
            kind: "diff".to_string(),
            schema_version: Some(report.schema_version.clone()),
            path: Some(path),
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if input.pr_metadata_path.is_some() {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-pr-metadata".to_string(),
            kind: "pr_metadata".to_string(),
            schema_version: Some(EMPIRICAL_DATASET_SCHEMA_VERSION.to_string()),
            path: input.pr_metadata_path,
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if input.law_policy_path.is_some() {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-law-policy".to_string(),
            kind: "policy".to_string(),
            schema_version: sig0.policies.schema_version.clone(),
            path: input.law_policy_path,
            content_hash: None,
            produced_by: None,
        });
    }

    let mut evidence: Vec<AirEvidence> = artifacts
        .iter()
        .map(|artifact| AirEvidence {
            evidence_id: format!("evidence-{}-artifact", artifact.kind.replace('_', "-")),
            kind: artifact_evidence_kind(&artifact.kind),
            artifact_ref: Some(artifact.artifact_id.clone()),
            path: artifact.path.clone(),
            symbol: None,
            line: None,
            rule_id: artifact.schema_version.clone(),
            confidence: Some("high".to_string()),
        })
        .collect();
    let mut relations = Vec::new();
    let component_paths: BTreeMap<String, String> = sig0
        .components
        .iter()
        .map(|component| (component.id.clone(), component.path.clone()))
        .collect();
    for (index, edge) in sig0.edges.iter().enumerate() {
        let evidence_id = numbered_id("evidence-static", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: static_evidence_kind.clone(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: component_paths.get(&edge.source).cloned(),
            symbol: Some(edge.source.clone()),
            line: None,
            rule_id: Some(edge.evidence.clone()),
            confidence: Some("high".to_string()),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-static", index),
            layer: "static".to_string(),
            from_component: Some(edge.source.clone()),
            to_component: Some(edge.target.clone()),
            kind: edge.kind.clone(),
            lifecycle: relation_lifecycle(edge, diff),
            protected_by: None,
            extraction_rule: Some(static_extraction_rule.clone()),
            evidence_refs: vec![evidence_id],
        });
    }
    for (index, runtime) in sig0.runtime_edge_evidence.iter().enumerate() {
        let evidence_id = numbered_id("evidence-runtime", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "runtime_trace".to_string(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: Some(runtime.evidence_location.path.clone()),
            symbol: runtime.evidence_location.symbol.clone(),
            line: runtime.evidence_location.line,
            rule_id: Some(runtime.label.clone()),
            confidence: runtime.confidence.clone(),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-runtime", index),
            layer: "runtime".to_string(),
            from_component: Some(runtime.source.clone()),
            to_component: Some(runtime.target.clone()),
            kind: runtime_relation_kind(&runtime.label),
            lifecycle: "after".to_string(),
            protected_by: runtime.circuit_breaker_coverage.clone(),
            extraction_rule: Some(RUNTIME_PROJECTION_RULE_VERSION.to_string()),
            evidence_refs: vec![evidence_id],
        });
    }
    for (index, violation) in sig0.policy_violations.iter().enumerate() {
        let evidence_id = numbered_id("evidence-policy", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "policy_rule".to_string(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: None,
            symbol: None,
            line: None,
            rule_id: violation.relation_ids.as_ref().map(|ids| ids.join(",")),
            confidence: Some("high".to_string()),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-policy", index),
            layer: "policy".to_string(),
            from_component: Some(violation.source.clone()),
            to_component: Some(violation.target.clone()),
            kind: "policy_rule".to_string(),
            lifecycle: "after".to_string(),
            protected_by: None,
            extraction_rule: Some(violation.axis.clone()),
            evidence_refs: vec![evidence_id],
        });
    }

    let component_ids: BTreeSet<String> = sig0
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect();
    let mut components: Vec<AirComponent> = sig0
        .components
        .iter()
        .map(|component| AirComponent {
            id: component.id.clone(),
            kind: air_component_kind(sig0).to_string(),
            lifecycle: component_lifecycle
                .get(&component.id)
                .cloned()
                .unwrap_or_else(|| "after".to_string()),
            owner: None,
            evidence_refs: Vec::new(),
        })
        .collect();
    let external_targets: BTreeSet<String> = sig0
        .edges
        .iter()
        .filter(|edge| !component_ids.contains(&edge.target))
        .map(|edge| edge.target.clone())
        .collect();
    components.extend(external_targets.into_iter().map(|target| AirComponent {
        id: target,
        kind: "external-dependency".to_string(),
        lifecycle: "after".to_string(),
        owner: None,
        evidence_refs: Vec::new(),
    }));
    let claims = air_claims(&signature_axes);
    let interaction_claim_refs = air_interaction_claim_refs(&claims);
    let revision = air_revision(diff, pr_metadata);
    let feature = air_feature(pr_metadata);
    let coverage = AirCoverage {
        layers: air_coverage_layers(&signature_axes, sig0),
    };
    let schema_compatibility = air_schema_compatibility_metadata(&coverage, &claims);

    AirDocumentV0 {
        schema_version: AIR_SCHEMA_VERSION.to_string(),
        schema_compatibility: Some(schema_compatibility),
        architecture_id: sig0.root.clone(),
        ids: AirIdPolicies {
            component_id_policy: "sig0 component id".to_string(),
            relation_id_policy: "layer-prefixed stable ordinal".to_string(),
            evidence_id_policy: "layer-prefixed stable ordinal".to_string(),
            claim_id_policy: "axis-prefixed stable id".to_string(),
        },
        revision,
        feature,
        artifacts,
        evidence,
        components,
        relations,
        policies: AirPolicies {
            laws: sig0
                .policies
                .policy_id
                .iter()
                .map(|policy_id| format!("policy:{policy_id}"))
                .collect(),
            boundaries: sig0
                .policies
                .boundary_group_count
                .map(|count| vec![format!("boundary groups: {count}")])
                .unwrap_or_default(),
            allowed_edges: sig0.policies.boundary_allowed.clone(),
            forbidden_edges: sig0
                .policy_violations
                .iter()
                .map(|violation| {
                    format!(
                        "{}:{}->{}",
                        violation.axis, violation.source, violation.target
                    )
                })
                .collect(),
            abstraction_rules: sig0.policies.abstraction_allowed.clone(),
            protection_rules: Vec::new(),
        },
        semantic_diagrams: Vec::new(),
        architecture_paths: Vec::new(),
        homotopy_generators: Vec::new(),
        nonfillability_witnesses: Vec::new(),
        signature: AirSignature {
            axes: signature_axes.clone(),
        },
        coverage,
        claims,
        operation_trace: AirOperationTrace {
            operations: Vec::new(),
        },
        extension: AirExtension {
            embedding_claim_ref: Some("claim-extension-embedding".to_string()),
            feature_view_claim_ref: Some("claim-extension-feature-view".to_string()),
            interaction_claim_refs,
            split_claim_ref: None,
            split_status: "unmeasured".to_string(),
        },
    }
}

fn air_signature_axes(
    signature: &ArchitectureSignatureV1DatasetShape,
    metric_status: &BTreeMap<String, MetricStatus>,
) -> Vec<AirSignatureAxis> {
    DATASET_SIGNATURE_AXES
        .iter()
        .map(|axis| {
            let value = signature_axis_value(signature, axis).map(|value| value as i64);
            let status = metric_status.get(*axis).cloned().unwrap_or_else(|| {
                unmeasured_status(format!("missing metricStatus entry for {axis}"))
            });
            AirSignatureAxis {
                axis: (*axis).to_string(),
                value,
                measured: status.measured,
                measurement_boundary: measurement_boundary(&status, value),
                source: status.source,
                reason: status.reason,
            }
        })
        .collect()
}

fn signature_axis_value(
    signature: &ArchitectureSignatureV1DatasetShape,
    axis: &str,
) -> Option<usize> {
    match axis {
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
        "empiricalChangeCost" => signature.empirical_change_cost,
        _ => None,
    }
}

fn measurement_boundary(status: &MetricStatus, value: Option<i64>) -> String {
    if !status.measured {
        return "unmeasured".to_string();
    }
    match value {
        Some(0) => "measuredZero".to_string(),
        Some(_) => "measuredNonzero".to_string(),
        None => "unmeasured".to_string(),
    }
}

fn numbered_id(prefix: &str, index: usize) -> String {
    format!("{prefix}-{:04}", index + 1)
}

fn runtime_relation_kind(label: &str) -> String {
    match label {
        "http" | "grpc" | "queue" | "db" | "event" | "batch" => label.to_string(),
        label if label.contains("queue") => "queue".to_string(),
        label if label.contains("event") => "event".to_string(),
        label if label.contains("rpc") => "grpc".to_string(),
        label if label.contains("db") => "db".to_string(),
        _ => "call".to_string(),
    }
}

fn artifact_evidence_kind(kind: &str) -> String {
    match kind {
        "policy" => "policy_rule",
        "pr_metadata" => "pr_file",
        "diff" | "validation" | "sig0" => "observation_result",
        _ => "manual_annotation",
    }
    .to_string()
}

fn air_component_kind(sig0: &Sig0Document) -> &str {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => PYTHON_COMPONENT_KIND,
        COMPONENT_KIND => "module",
        other => other,
    }
}

fn static_extraction_rule(sig0: &Sig0Document) -> String {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => PYTHON_IMPORT_RULE_VERSION.to_string(),
        _ => "lean-import".to_string(),
    }
}

fn static_evidence_kind(sig0: &Sig0Document) -> String {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => "python_import".to_string(),
        _ => "source_location".to_string(),
    }
}

fn relation_lifecycle(edge: &Edge, diff: Option<&SignatureDiffReportV0>) -> String {
    let Some(diff) = diff else {
        return "after".to_string();
    };
    let Some(edge_delta) = &diff.evidence_diff.edge_delta else {
        return "after".to_string();
    };
    if edge_delta.added.iter().any(|added| added == edge) {
        "added".to_string()
    } else if edge_delta.removed.iter().any(|removed| removed == edge) {
        "removed".to_string()
    } else {
        "unchanged".to_string()
    }
}

fn air_component_lifecycle(diff: Option<&SignatureDiffReportV0>) -> BTreeMap<String, String> {
    let mut lifecycle = BTreeMap::new();
    if let Some(component_delta) =
        diff.and_then(|report| report.evidence_diff.component_delta.as_ref())
    {
        for component in &component_delta.added {
            lifecycle.insert(component.clone(), "added".to_string());
        }
        for component in &component_delta.removed {
            lifecycle.insert(component.clone(), "removed".to_string());
        }
    }
    lifecycle
}

fn air_revision(
    diff: Option<&SignatureDiffReportV0>,
    pr_metadata: Option<&EmpiricalDatasetInput>,
) -> AirRevision {
    if let Some(diff) = diff {
        return AirRevision {
            before: Some(diff.before.revision.sha.clone()),
            after: diff.after.revision.sha.clone(),
        };
    }
    if let Some(pr_metadata) = pr_metadata {
        return AirRevision {
            before: Some(pr_metadata.pull_request.base_commit.clone()),
            after: pr_metadata.pull_request.head_commit.clone(),
        };
    }
    AirRevision {
        before: None,
        after: "unknown".to_string(),
    }
}

fn air_feature(pr_metadata: Option<&EmpiricalDatasetInput>) -> AirFeature {
    if let Some(pr_metadata) = pr_metadata {
        AirFeature {
            feature_id: Some(format!("#{}", pr_metadata.pull_request.number)),
            title: None,
            description: Some(format!(
                "pull request by {} with {} changed files",
                pr_metadata.pull_request.author, pr_metadata.pr_metrics.changed_files
            )),
            source: "pr".to_string(),
            ai_session: None,
        }
    } else {
        AirFeature {
            feature_id: None,
            title: None,
            description: None,
            source: "unknown".to_string(),
            ai_session: None,
        }
    }
}

fn air_claims(signature_axes: &[AirSignatureAxis]) -> Vec<AirClaim> {
    let mut claims: Vec<AirClaim> = signature_axes
        .iter()
        .map(|axis| {
            let measured = axis.measured && axis.value.is_some();
            let mut missing_preconditions = Vec::new();
            let mut non_conclusions = vec![
                "tooling measurement is not a Lean proof".to_string(),
                "extractor output is not a complete ComponentUniverse proof".to_string(),
            ];
            if !measured {
                missing_preconditions.push(format!("{} is unmeasured", axis.axis));
                non_conclusions.push("placeholder zero is not measured zero".to_string());
            }
            AirClaim {
                claim_id: format!("claim-axis-{}", stable_id_fragment(&axis.axis)),
                subject_ref: format!("signature.{}", axis.axis),
                predicate: if measured {
                    "axis value measured by tooling".to_string()
                } else {
                    "axis is outside the current measurement boundary".to_string()
                },
                claim_level: "tooling".to_string(),
                claim_classification: if measured {
                    "measured".to_string()
                } else {
                    "unmeasured".to_string()
                },
                measurement_boundary: axis.measurement_boundary.clone(),
                theorem_refs: Vec::new(),
                evidence_refs: vec!["evidence-sig0-artifact".to_string()],
                required_assumptions: Vec::new(),
                coverage_assumptions: Vec::new(),
                exactness_assumptions: Vec::new(),
                missing_preconditions,
                non_conclusions,
            }
        })
        .collect();
    claims.push(AirClaim {
        claim_id: "claim-extension-embedding".to_string(),
        subject_ref: "extension.embedding".to_string(),
        predicate: "before architecture is embedded into after architecture only if diff evidence and theorem preconditions are discharged".to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: Vec::new(),
        required_assumptions: vec!["before/after component correspondence".to_string()],
        coverage_assumptions: vec!["static diff coverage".to_string()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["theorem precondition checker has not run".to_string()],
        non_conclusions: vec!["split extension is not concluded".to_string()],
    });
    claims.push(AirClaim {
        claim_id: "claim-extension-feature-view".to_string(),
        subject_ref: "extension.feature".to_string(),
        predicate: "feature-owned delta can be interpreted from PR metadata and diff evidence"
            .to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: Vec::new(),
        required_assumptions: vec!["PR-to-component attribution".to_string()],
        coverage_assumptions: vec!["diff evidence coverage".to_string()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["feature extension report has not run".to_string()],
        non_conclusions: vec!["feature quotient is not constructed".to_string()],
    });
    claims
}

fn air_interaction_claim_refs(claims: &[AirClaim]) -> Vec<String> {
    claims
        .iter()
        .filter(|claim| {
            claim.subject_ref == "signature.boundaryViolationCount"
                || claim.subject_ref == "signature.abstractionViolationCount"
                || claim.subject_ref == "signature.runtimePropagation"
        })
        .map(|claim| claim.claim_id.clone())
        .collect()
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

fn air_coverage_layers(
    signature_axes: &[AirSignatureAxis],
    sig0: &Sig0Document,
) -> Vec<AirCoverageLayer> {
    vec![
        air_coverage_layer(
            "static",
            signature_axes,
            &[
                "hasCycle",
                "sccMaxSize",
                "maxDepth",
                "fanoutRisk",
                "sccExcessSize",
                "maxFanout",
                "reachableConeSize",
            ],
            static_extraction_scope(sig0),
            static_exactness_assumptions(sig0),
            Some(static_extraction_rule(sig0)),
            static_unsupported_constructs(sig0),
        ),
        air_coverage_layer(
            "policy",
            signature_axes,
            &["boundaryViolationCount", "abstractionViolationCount"],
            vec!["policy file".to_string()],
            vec!["policy coverage depends on selector completeness".to_string()],
            None,
            Vec::new(),
        ),
        air_runtime_coverage_layer(signature_axes, sig0),
        air_unmeasured_coverage_layer(
            "semantic",
            vec![
                "lspViolationCount".to_string(),
                "projectionSoundnessViolation".to_string(),
            ],
        ),
        air_unmeasured_coverage_layer(
            "operation",
            vec![
                "relationComplexity".to_string(),
                "empiricalChangeCost".to_string(),
            ],
        ),
    ]
}

fn static_extraction_scope(sig0: &Sig0Document) -> Vec<String> {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => vec![
            "Python package-root module universe".to_string(),
            "static import graph from Python ast import/from nodes".to_string(),
        ],
        _ => vec!["Lean import graph".to_string()],
    }
}

fn static_exactness_assumptions(sig0: &Sig0Document) -> Vec<String> {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => vec![
            "python-import-graph-v0 observes static import and from-import syntax only".to_string(),
            "python-module ids are normalized relative to the configured package root".to_string(),
            "Python extractor output is tooling evidence, not a Lean ComponentUniverse completeness proof".to_string(),
        ],
        _ => Vec::new(),
    }
}

fn static_unsupported_constructs(sig0: &Sig0Document) -> Vec<String> {
    match sig0.component_kind.as_str() {
        PYTHON_COMPONENT_KIND => sig0
            .unsupported_constructs
            .iter()
            .map(|construct| {
                let location = construct
                    .line
                    .map(|line| format!("{}:{}", construct.path, line))
                    .unwrap_or_else(|| construct.path.clone());
                format!("{} at {}: {}", construct.kind, location, construct.reason)
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn air_coverage_layer(
    layer: &str,
    signature_axes: &[AirSignatureAxis],
    axes: &[&str],
    extraction_scope: Vec<String>,
    exactness_assumptions: Vec<String>,
    projection_rule: Option<String>,
    unsupported_constructs: Vec<String>,
) -> AirCoverageLayer {
    let mut measured_axes = Vec::new();
    let mut unmeasured_axes = Vec::new();
    let mut boundaries = Vec::new();
    for axis in axes {
        if let Some(signature_axis) = signature_axes
            .iter()
            .find(|signature_axis| signature_axis.axis == *axis)
        {
            boundaries.push(signature_axis.measurement_boundary.clone());
            if signature_axis.measured {
                measured_axes.push((*axis).to_string());
            } else {
                unmeasured_axes.push((*axis).to_string());
            }
        }
    }
    AirCoverageLayer {
        layer: layer.to_string(),
        measurement_boundary: combined_measurement_boundary(&boundaries),
        universe_refs: vec!["artifact-sig0".to_string()],
        measured_axes,
        unmeasured_axes,
        projection_rule,
        extraction_scope,
        exactness_assumptions,
        unsupported_constructs,
    }
}

fn air_runtime_coverage_layer(
    signature_axes: &[AirSignatureAxis],
    sig0: &Sig0Document,
) -> AirCoverageLayer {
    let Some(runtime_axis) = signature_axes
        .iter()
        .find(|signature_axis| signature_axis.axis == "runtimePropagation")
    else {
        return air_unmeasured_coverage_layer("runtime", vec!["runtimePropagation".to_string()]);
    };

    if sig0.runtime_dependency_graph.is_some() && runtime_axis.measured {
        return AirCoverageLayer {
            layer: "runtime".to_string(),
            measurement_boundary: runtime_axis.measurement_boundary.clone(),
            universe_refs: vec!["artifact-sig0".to_string()],
            measured_axes: vec!["runtimePropagation".to_string()],
            unmeasured_axes: Vec::new(),
            projection_rule: Some(RUNTIME_PROJECTION_RULE_VERSION.to_string()),
            extraction_scope: vec![
                "runtime edge evidence JSON".to_string(),
                "0/1 runtime dependency graph over measured component pairs".to_string(),
            ],
            exactness_assumptions: vec![
                "runtime-edge-projection-v0 maps each observed component pair to one runtime edge"
                    .to_string(),
                "runtime evidence component ids resolve inside the AIR component universe"
                    .to_string(),
            ],
            unsupported_constructs: Vec::new(),
        };
    }

    AirCoverageLayer {
        layer: "runtime".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        universe_refs: Vec::new(),
        measured_axes: Vec::new(),
        unmeasured_axes: vec!["runtimePropagation".to_string()],
        projection_rule: None,
        extraction_scope: Vec::new(),
        exactness_assumptions: Vec::new(),
        unsupported_constructs: vec!["runtime edge evidence not provided".to_string()],
    }
}

fn air_unmeasured_coverage_layer(layer: &str, unmeasured_axes: Vec<String>) -> AirCoverageLayer {
    AirCoverageLayer {
        layer: layer.to_string(),
        measurement_boundary: "unmeasured".to_string(),
        universe_refs: Vec::new(),
        measured_axes: Vec::new(),
        unmeasured_axes,
        projection_rule: None,
        extraction_scope: Vec::new(),
        exactness_assumptions: Vec::new(),
        unsupported_constructs: vec!["extractor not implemented for this layer".to_string()],
    }
}

fn combined_measurement_boundary(boundaries: &[String]) -> String {
    if boundaries.is_empty() || boundaries.iter().any(|boundary| boundary == "unmeasured") {
        "unmeasured".to_string()
    } else if boundaries
        .iter()
        .any(|boundary| boundary == "measuredNonzero")
    {
        "measuredNonzero".to_string()
    } else {
        "measuredZero".to_string()
    }
}
