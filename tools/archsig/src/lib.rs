use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
mod dataset;
mod extractor;
mod github;
mod graph;
mod policy;
mod relation_complexity;
mod runtime;
pub mod schema;
mod snapshot;

pub use dataset::build_empirical_dataset;
pub use extractor::{extract_sig0, extract_sig0_with_policy, extract_sig0_with_runtime};
pub use github::{build_pr_metadata_from_github_files, build_pr_metadata_from_github_values};
pub use relation_complexity::{
    extract_relation_complexity_observation, extract_relation_complexity_observation_from_file,
};
pub use schema::*;
pub use snapshot::{build_signature_diff_report, build_signature_snapshot_record};

use dataset::{DATASET_SIGNATURE_AXES, dataset_metric_status, dataset_signature_shape};

#[cfg(test)]
pub(crate) use extractor::{ParsedImport, parse_imports};
#[cfg(test)]
pub(crate) use graph::compute_signature;

pub fn validate_component_universe_report(
    document: &Sig0Document,
    input_path: &str,
    universe_mode: &str,
) -> Result<ComponentUniverseValidationReport, Box<dyn Error>> {
    if !matches!(universe_mode, "local-only" | "closed-with-external") {
        return Err(format!("unsupported universe mode: {universe_mode}").into());
    }

    let component_ids: BTreeSet<String> = document
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect();
    let local_roots = component_roots(&component_ids);
    let external_edges = external_edges(document, &component_ids, &local_roots);
    let local_edge_count = document
        .edges
        .iter()
        .filter(|edge| component_ids.contains(&edge.source) && component_ids.contains(&edge.target))
        .count();

    let mut checks = Vec::new();

    checks.push(check_schema_version(&document.schema_version));
    checks.push(check_component_id_nodup(&document.components));
    checks.push(check_component_path_nodup(&document.components));
    checks.push(check_edge_endpoint_resolved(
        &document.edges,
        &component_ids,
        &local_roots,
    ));
    checks.push(check_edge_closure_local(
        &document.edges,
        &component_ids,
        &local_roots,
    ));
    checks.push(check_external_edge_targets(&external_edges, universe_mode));
    checks.push(check_metric_status_complete(&document.metric_status));
    checks.push(check_metric_measured(
        "boundary-policy-status",
        "boundary violation metric is measured",
        "boundaryViolationCount",
        &document.metric_status,
    ));
    checks.push(check_metric_measured(
        "abstraction-policy-status",
        "abstraction violation metric is measured",
        "abstractionViolationCount",
        &document.metric_status,
    ));
    checks.push(validation_check(
        "extractor-warning-status",
        "extractor output has no warnings",
        "pass",
    ));

    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let not_measured_check_count = count_checks(&checks, "not_measured");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 || not_measured_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    let mut warnings = Vec::new();
    if universe_mode == "local-only" && !external_edges.is_empty() {
        warnings
            .push("local-only universe excludes external or synthetic import targets".to_string());
    }

    Ok(ComponentUniverseValidationReport {
        schema_version: VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ValidationInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            root: document.root.clone(),
            component_kind: document.component_kind.clone(),
        },
        universe_mode: universe_mode.to_string(),
        summary: ValidationSummary {
            result: result.to_string(),
            component_count: document.components.len(),
            local_edge_count,
            external_edge_count: external_edges.len(),
            failed_check_count,
            warning_check_count,
            not_measured_check_count,
        },
        checks,
        warnings,
    })
}

pub fn validate_air_document_report(
    document: &AirDocumentV0,
    input_path: &str,
    strict_measured_evidence: bool,
) -> AirValidationReport {
    let mut checks = Vec::new();

    checks.push(check_air_schema_version(&document.schema_version));
    checks.push(check_air_unique_ids(document));
    checks.push(check_air_artifact_refs(document));
    checks.push(check_air_component_refs(document));
    checks.push(check_air_evidence_refs(document));
    checks.push(check_air_claim_refs(document));
    checks.push(check_air_path_and_witness_refs(document));
    checks.push(check_air_coverage_universe_refs(document));
    checks.push(check_air_signature_measurement_boundary(document));
    checks.push(check_air_claim_measurement_boundary(document));
    checks.push(check_air_measured_claim_evidence(
        document,
        strict_measured_evidence,
    ));

    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };
    let warnings = checks
        .iter()
        .filter(|check| check.result == "warn")
        .filter_map(|check| check.reason.clone())
        .collect();

    AirValidationReport {
        schema_version: AIR_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: AirValidationInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        summary: AirValidationSummary {
            result: result.to_string(),
            component_count: document.components.len(),
            relation_count: document.relations.len(),
            evidence_count: document.evidence.len(),
            claim_count: document.claims.len(),
            failed_check_count,
            warning_check_count,
        },
        checks,
        warnings,
    }
}

pub fn static_theorem_package_registry() -> TheoremPackageRegistryV0 {
    TheoremPackageRegistryV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        scope: "static theorem package v0".to_string(),
        packages: vec![TheoremPackageMetadataV0 {
            package_id: "static-theorem-package-v0".to_string(),
            lean_entrypoint: "SelectedStaticSplitExtension".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            supported_subject_refs: vec![
                "extension.embedding".to_string(),
                "extension.feature".to_string(),
                "extension.split".to_string(),
                "signature.hasCycle".to_string(),
                "signature.projectionSoundnessViolation".to_string(),
                "signature.lspViolationCount".to_string(),
                "signature.boundaryViolationCount".to_string(),
                "signature.abstractionViolationCount".to_string(),
            ],
            supported_axes: vec![
                "hasCycle".to_string(),
                "projectionSoundnessViolation".to_string(),
                "lspViolationCount".to_string(),
                "boundaryViolationCount".to_string(),
                "abstractionViolationCount".to_string(),
            ],
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            required_assumptions: vec![
                "core edges are preserved".to_string(),
                "feature/core interactions factor through a declared interface".to_string(),
                "no new forbidden static edge is introduced".to_string(),
                "embedding policy is preserved".to_string(),
            ],
            coverage_assumptions: vec![
                "static dependency graph is inside the measured universe".to_string(),
                "policy selector covers the checked static edges".to_string(),
            ],
            exactness_assumptions: vec![
                "AIR component and relation identifiers match the Lean package parameters"
                    .to_string(),
            ],
            missing_preconditions: Vec::new(),
            non_conclusions: vec![
                "static theorem package does not conclude runtime flatness".to_string(),
                "static theorem package does not conclude semantic flatness".to_string(),
                "static theorem package does not prove extractor completeness".to_string(),
            ],
        }],
    }
}

pub fn build_theorem_precondition_check_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> TheoremPreconditionCheckReportV0 {
    let registry = static_theorem_package_registry();
    let checks = theorem_precondition_checks(document, &registry);
    let summary = theorem_precondition_check_summary(&checks, document.claims.len());

    TheoremPreconditionCheckReportV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        input: TheoremPreconditionCheckInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        registry,
        summary,
        checks,
    }
}

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
            kind: "source_location".to_string(),
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
            extraction_rule: Some("lean-import".to_string()),
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

    let components = sig0
        .components
        .iter()
        .map(|component| AirComponent {
            id: component.id.clone(),
            kind: "module".to_string(),
            lifecycle: component_lifecycle
                .get(&component.id)
                .cloned()
                .unwrap_or_else(|| "after".to_string()),
            owner: None,
            evidence_refs: Vec::new(),
        })
        .collect();
    let claims = air_claims(&signature_axes);
    let interaction_claim_refs = air_interaction_claim_refs(&claims);
    let revision = air_revision(diff, pr_metadata);
    let feature = air_feature(pr_metadata);

    AirDocumentV0 {
        schema_version: AIR_SCHEMA_VERSION.to_string(),
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
        coverage: AirCoverage {
            layers: air_coverage_layers(&signature_axes),
        },
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

fn theorem_precondition_checks(
    document: &AirDocumentV0,
    registry: &TheoremPackageRegistryV0,
) -> Vec<TheoremPreconditionCheck> {
    document
        .claims
        .iter()
        .map(|claim| theorem_precondition_check(claim, registry))
        .collect()
}

fn theorem_precondition_check(
    claim: &AirClaim,
    registry: &TheoremPackageRegistryV0,
) -> TheoremPreconditionCheck {
    let applicable_packages: Vec<&TheoremPackageMetadataV0> = registry
        .packages
        .iter()
        .filter(|package| theorem_package_applies_to_claim(package, claim))
        .collect();
    let known_refs: BTreeSet<String> = registry
        .packages
        .iter()
        .flat_map(|package| package.theorem_refs.iter().cloned())
        .collect();
    let unknown_theorem_refs: Vec<String> = claim
        .theorem_refs
        .iter()
        .filter(|theorem_ref| !known_refs.contains(theorem_ref.as_str()))
        .cloned()
        .collect();
    let applicable_package_refs = applicable_packages
        .iter()
        .map(|package| package.package_id.clone())
        .collect();

    let (resolved_claim_classification, result, reason) = if !unknown_theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim cites theorem refs outside the static theorem package registry".to_string(),
        )
    } else if claim.claim_classification == "measured" {
        (
            "MEASURED_WITNESS".to_string(),
            "pass".to_string(),
            "tooling measurement remains a measured witness, not a formal proved claim".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.missing_preconditions.is_empty()
    {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "missing preconditions block formal proved classification".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.theorem_refs.is_empty()
        && !applicable_packages.is_empty()
    {
        (
            "FORMAL_PROVED".to_string(),
            "pass".to_string(),
            "theorem refs are registered and missing preconditions are empty".to_string(),
        )
    } else if claim.claim_level == "formal" && claim.claim_classification == "proved" {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "formal proved claim needs registered theorem refs".to_string(),
        )
    } else if claim.claim_classification == "unmeasured" || !claim.missing_preconditions.is_empty()
    {
        (
            "UNMEASURED".to_string(),
            "warn".to_string(),
            "claim remains outside the measured theorem boundary".to_string(),
        )
    } else if applicable_packages.is_empty() && !claim.theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim has theorem refs but no applicable static theorem package".to_string(),
        )
    } else {
        (
            "TOOLING_CLAIM".to_string(),
            "pass".to_string(),
            "claim is reported at tooling level".to_string(),
        )
    };

    TheoremPreconditionCheck {
        claim_id: claim.claim_id.clone(),
        subject_ref: claim.subject_ref.clone(),
        applicable_package_refs,
        theorem_refs: claim.theorem_refs.clone(),
        unknown_theorem_refs,
        claim_level: claim.claim_level.clone(),
        input_claim_classification: claim.claim_classification.clone(),
        resolved_claim_classification,
        measurement_boundary: claim.measurement_boundary.clone(),
        required_assumptions: claim.required_assumptions.clone(),
        coverage_assumptions: claim.coverage_assumptions.clone(),
        exactness_assumptions: claim.exactness_assumptions.clone(),
        missing_preconditions: claim.missing_preconditions.clone(),
        non_conclusions: claim.non_conclusions.clone(),
        result,
        reason,
    }
}

fn theorem_precondition_check_summary(
    checks: &[TheoremPreconditionCheck],
    checked_claim_count: usize,
) -> TheoremPreconditionCheckSummary {
    let blocked_claim_count = checks
        .iter()
        .filter(|check| check.resolved_claim_classification == "BLOCKED_FORMAL_CLAIM")
        .count();
    let unknown_theorem_ref_count = checks
        .iter()
        .map(|check| check.unknown_theorem_refs.len())
        .sum();
    let result = if checks.iter().any(|check| check.result == "warn") {
        "warn"
    } else {
        "pass"
    };

    TheoremPreconditionCheckSummary {
        result: result.to_string(),
        checked_claim_count,
        applicable_claim_count: checks
            .iter()
            .filter(|check| !check.applicable_package_refs.is_empty())
            .count(),
        formal_proved_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "FORMAL_PROVED")
            .count(),
        measured_witness_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "MEASURED_WITNESS")
            .count(),
        blocked_claim_count,
        unmeasured_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "UNMEASURED")
            .count(),
        unknown_theorem_ref_count,
    }
}

fn theorem_package_applies_to_claim(package: &TheoremPackageMetadataV0, claim: &AirClaim) -> bool {
    let theorem_ref_matches = claim
        .theorem_refs
        .iter()
        .any(|theorem_ref| package.theorem_refs.contains(theorem_ref));
    let subject_matches = package
        .supported_subject_refs
        .iter()
        .any(|subject_ref| subject_ref == &claim.subject_ref);

    theorem_ref_matches || subject_matches
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

fn air_coverage_layers(signature_axes: &[AirSignatureAxis]) -> Vec<AirCoverageLayer> {
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
            vec!["Lean import graph".to_string()],
            Vec::new(),
        ),
        air_coverage_layer(
            "policy",
            signature_axes,
            &["boundaryViolationCount", "abstractionViolationCount"],
            vec!["policy file".to_string()],
            vec!["policy coverage depends on selector completeness".to_string()],
        ),
        air_coverage_layer(
            "runtime",
            signature_axes,
            &["runtimePropagation"],
            vec!["runtime edge evidence JSON".to_string()],
            vec![
                "runtime projection is a tooling observation, not telemetry completeness"
                    .to_string(),
            ],
        ),
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

fn air_coverage_layer(
    layer: &str,
    signature_axes: &[AirSignatureAxis],
    axes: &[&str],
    extraction_scope: Vec<String>,
    exactness_assumptions: Vec<String>,
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
        extraction_scope,
        exactness_assumptions,
        unsupported_constructs: Vec::new(),
    }
}

fn air_unmeasured_coverage_layer(layer: &str, unmeasured_axes: Vec<String>) -> AirCoverageLayer {
    AirCoverageLayer {
        layer: layer.to_string(),
        measurement_boundary: "unmeasured".to_string(),
        universe_refs: Vec::new(),
        measured_axes: Vec::new(),
        unmeasured_axes,
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

fn count_checks(checks: &[ValidationCheck], result: &str) -> usize {
    checks.iter().filter(|check| check.result == result).count()
}

fn validation_check(id: &str, title: &str, result: &str) -> ValidationCheck {
    ValidationCheck {
        id: id.to_string(),
        title: title.to_string(),
        result: result.to_string(),
        reason: None,
        count: None,
        examples: Vec::new(),
        metric: None,
        lean_boundary: None,
    }
}

fn check_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "schema-version-supported",
        "input schema version is supported",
        if schema_version == SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("unsupported schemaVersion: {schema_version}"));
    }
    check
}

fn check_component_id_nodup(components: &[Component]) -> ValidationCheck {
    let duplicate_ids = duplicates(components.iter().map(|component| component.id.as_str()));
    let mut check = validation_check(
        "component-id-nodup",
        "component ids are duplicate-free",
        if duplicate_ids.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    check.lean_boundary = Some("Nodup-like JSON evidence only".to_string());
    if !duplicate_ids.is_empty() {
        check.reason = Some("duplicate component ids found".to_string());
        check.count = Some(duplicate_ids.len());
        check.examples = duplicate_ids
            .into_iter()
            .take(5)
            .map(|component_id| ValidationExample {
                component_id: Some(component_id),
                path: None,
                source: None,
                target: None,
                evidence: None,
            })
            .collect();
    }
    check
}

fn check_component_path_nodup(components: &[Component]) -> ValidationCheck {
    let duplicate_paths = duplicates(components.iter().map(|component| component.path.as_str()));
    let mut check = validation_check(
        "component-path-nodup",
        "component paths are duplicate-free",
        if duplicate_paths.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !duplicate_paths.is_empty() {
        check.reason = Some("duplicate component paths found".to_string());
        check.count = Some(duplicate_paths.len());
        check.examples = duplicate_paths
            .into_iter()
            .take(5)
            .map(|path| ValidationExample {
                component_id: None,
                path: Some(path),
                source: None,
                target: None,
                evidence: None,
            })
            .collect();
    }
    check
}

fn check_edge_endpoint_resolved(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> ValidationCheck {
    let unresolved = unresolved_edges(edges, component_ids, local_roots);
    let mut check = validation_check(
        "edge-endpoint-resolved",
        "edge endpoints are local components or external nodes",
        if unresolved.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !unresolved.is_empty() {
        check.reason = Some("edge endpoint is not covered by the selected universe".to_string());
        check.count = Some(unresolved.len());
        check.examples = unresolved.into_iter().take(5).collect();
    }
    check
}

fn check_edge_closure_local(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> ValidationCheck {
    let open_edges: Vec<ValidationExample> = edges
        .iter()
        .filter(|edge| {
            component_ids.contains(&edge.source)
                && is_local_like(&edge.target, local_roots)
                && !component_ids.contains(&edge.target)
                && !is_module_root_target(&edge.target, component_ids, local_roots)
        })
        .map(edge_example)
        .collect();
    let mut check = validation_check(
        "edge-closure-local",
        "local dependency edges are closed over selected universe",
        if open_edges.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    check.lean_boundary = Some("edge-closedness candidate for local-only projection".to_string());
    if !open_edges.is_empty() {
        check.reason = Some("local-like dependency target is missing from components".to_string());
        check.count = Some(open_edges.len());
        check.examples = open_edges.into_iter().take(5).collect();
    }
    check
}

fn check_external_edge_targets(
    external_edges: &[ValidationExample],
    universe_mode: &str,
) -> ValidationCheck {
    let has_external_edges = !external_edges.is_empty();
    let result = if universe_mode == "local-only" && has_external_edges {
        "warn"
    } else {
        "pass"
    };
    let mut check = validation_check(
        "external-edge-targets",
        "external import targets are outside selected universe",
        result,
    );
    check.lean_boundary =
        Some("not a ComponentUniverse witness for the full import graph".to_string());
    if has_external_edges {
        check.count = Some(external_edges.len());
        check.examples = external_edges.iter().take(5).cloned().collect();
    }
    check
}

fn check_metric_status_complete(metric_status: &BTreeMap<String, MetricStatus>) -> ValidationCheck {
    let expected_axes = [
        "hasCycle",
        "sccMaxSize",
        "maxDepth",
        "fanoutRisk",
        "boundaryViolationCount",
        "abstractionViolationCount",
    ];
    let missing: Vec<&str> = expected_axes
        .iter()
        .copied()
        .filter(|axis| !metric_status.contains_key(*axis))
        .collect();
    let mut check = validation_check(
        "metric-status-complete",
        "signature axes have metric status entries",
        if missing.is_empty() { "pass" } else { "warn" },
    );
    if !missing.is_empty() {
        check.reason = Some(format!(
            "missing metricStatus entries: {}",
            missing.join(", ")
        ));
        check.count = Some(missing.len());
    }
    check
}

fn check_metric_measured(
    id: &str,
    title: &str,
    metric: &str,
    metric_status: &BTreeMap<String, MetricStatus>,
) -> ValidationCheck {
    let status = metric_status.get(metric);
    let measured = status.is_some_and(|status| status.measured);
    let mut check = validation_check(id, title, if measured { "pass" } else { "not_measured" });
    check.metric = Some(metric.to_string());
    if !measured {
        check.reason = Some(
            status
                .and_then(|status| status.reason.clone())
                .unwrap_or_else(|| "metricStatus entry is missing".to_string()),
        );
    }
    check
}

fn check_air_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "air-schema-version-supported",
        "AIR schema version is supported",
        if schema_version == AIR_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("unsupported schemaVersion: {schema_version}"));
    }
    check
}

fn check_air_unique_ids(document: &AirDocumentV0) -> ValidationCheck {
    let duplicate_examples: Vec<ValidationExample> = [
        (
            "artifact",
            duplicates(
                document
                    .artifacts
                    .iter()
                    .map(|artifact| artifact.artifact_id.as_str()),
            ),
        ),
        (
            "evidence",
            duplicates(
                document
                    .evidence
                    .iter()
                    .map(|evidence| evidence.evidence_id.as_str()),
            ),
        ),
        (
            "component",
            duplicates(
                document
                    .components
                    .iter()
                    .map(|component| component.id.as_str()),
            ),
        ),
        (
            "relation",
            duplicates(
                document
                    .relations
                    .iter()
                    .map(|relation| relation.id.as_str()),
            ),
        ),
        (
            "claim",
            duplicates(document.claims.iter().map(|claim| claim.claim_id.as_str())),
        ),
    ]
    .into_iter()
    .flat_map(|(kind, ids)| {
        ids.into_iter()
            .map(move |id| generic_validation_example(kind, &id, "duplicate id"))
    })
    .collect();

    let mut check = validation_check(
        "air-id-nodup",
        "AIR ids are duplicate-free within each reference namespace",
        if duplicate_examples.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !duplicate_examples.is_empty() {
        check.reason = Some("duplicate AIR ids found".to_string());
        check.count = Some(duplicate_examples.len());
        check.examples = duplicate_examples.into_iter().take(5).collect();
    }
    check
}

fn check_air_artifact_refs(document: &AirDocumentV0) -> ValidationCheck {
    let artifact_ids = air_artifact_ids(document);
    let unresolved: Vec<ValidationExample> = document
        .evidence
        .iter()
        .filter_map(|evidence| {
            let artifact_ref = evidence.artifact_ref.as_ref()?;
            (!artifact_ids.contains(artifact_ref)).then(|| {
                generic_validation_example(
                    &evidence.evidence_id,
                    artifact_ref,
                    "dangling artifact_ref",
                )
            })
        })
        .collect();

    air_ref_check(
        "air-artifact-refs-resolved",
        "evidence artifact refs resolve to AIR artifacts",
        unresolved,
    )
}

fn check_air_component_refs(document: &AirDocumentV0) -> ValidationCheck {
    let component_ids = air_component_ids(document);
    let mut unresolved = Vec::new();
    for relation in &document.relations {
        if let Some(component_ref) = &relation.from_component {
            if !component_ids.contains(component_ref) {
                unresolved.push(generic_validation_example(
                    &relation.id,
                    component_ref,
                    "dangling relation.from",
                ));
            }
        }
        if let Some(component_ref) = &relation.to_component {
            if !component_ids.contains(component_ref) {
                unresolved.push(generic_validation_example(
                    &relation.id,
                    component_ref,
                    "dangling relation.to",
                ));
            }
        }
    }

    air_ref_check(
        "air-component-refs-resolved",
        "relation component refs resolve to AIR components",
        unresolved,
    )
}

fn check_air_evidence_refs(document: &AirDocumentV0) -> ValidationCheck {
    let evidence_ids = air_evidence_ids(document);
    let mut unresolved = Vec::new();

    for component in &document.components {
        unresolved.extend(unresolved_refs(
            &component.id,
            "dangling component.evidence_refs",
            &component.evidence_refs,
            &evidence_ids,
        ));
    }
    for relation in &document.relations {
        unresolved.extend(unresolved_refs(
            &relation.id,
            "dangling relation.evidence_refs",
            &relation.evidence_refs,
            &evidence_ids,
        ));
    }
    for diagram in &document.semantic_diagrams {
        unresolved.extend(unresolved_refs(
            &diagram.id,
            "dangling semantic_diagram.evidence_refs",
            &diagram.evidence_refs,
            &evidence_ids,
        ));
    }
    for path in &document.architecture_paths {
        unresolved.extend(unresolved_refs(
            &path.path_id,
            "dangling architecture_path.evidence_refs",
            &path.evidence_refs,
            &evidence_ids,
        ));
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.evidence_refs",
            &generator.evidence_refs,
            &evidence_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        unresolved.extend(unresolved_refs(
            &witness.witness_id,
            "dangling nonfillability_witness.evidence_refs",
            &witness.evidence_refs,
            &evidence_ids,
        ));
    }
    for claim in &document.claims {
        unresolved.extend(unresolved_refs(
            &claim.claim_id,
            "dangling claim.evidence_refs",
            &claim.evidence_refs,
            &evidence_ids,
        ));
    }

    air_ref_check(
        "air-evidence-refs-resolved",
        "AIR evidence refs resolve to evidence objects",
        unresolved,
    )
}

fn check_air_claim_refs(document: &AirDocumentV0) -> ValidationCheck {
    let claim_ids = air_claim_ids(document);
    let mut unresolved = Vec::new();

    for diagram in &document.semantic_diagrams {
        if let Some(claim_ref) = &diagram.filler_claim_ref {
            if !claim_ids.contains(claim_ref) {
                unresolved.push(generic_validation_example(
                    &diagram.id,
                    claim_ref,
                    "dangling semantic_diagram.filler_claim_ref",
                ));
            }
        }
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.preserves_observation_claim_refs",
            &generator.preserves_observation_claim_refs,
            &claim_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        if !claim_ids.contains(&witness.claim_ref) {
            unresolved.push(generic_validation_example(
                &witness.witness_id,
                &witness.claim_ref,
                "dangling nonfillability_witness.claim_ref",
            ));
        }
    }
    unresolved.extend(optional_unresolved_ref(
        "extension.embedding_claim_ref",
        document.extension.embedding_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(optional_unresolved_ref(
        "extension.feature_view_claim_ref",
        document.extension.feature_view_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(optional_unresolved_ref(
        "extension.split_claim_ref",
        document.extension.split_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(unresolved_refs(
        "extension.interaction_claim_refs",
        "dangling extension.interaction_claim_refs",
        &document.extension.interaction_claim_refs,
        &claim_ids,
    ));

    air_ref_check(
        "air-claim-refs-resolved",
        "AIR claim refs resolve to claim objects",
        unresolved,
    )
}

fn check_air_path_and_witness_refs(document: &AirDocumentV0) -> ValidationCheck {
    let path_ids: BTreeSet<String> = document
        .architecture_paths
        .iter()
        .map(|path| path.path_id.clone())
        .collect();
    let diagram_ids: BTreeSet<String> = document
        .semantic_diagrams
        .iter()
        .map(|diagram| diagram.id.clone())
        .collect();
    let witness_ids: BTreeSet<String> = document
        .nonfillability_witnesses
        .iter()
        .map(|witness| witness.witness_id.clone())
        .collect();
    let mut unresolved = Vec::new();

    for diagram in &document.semantic_diagrams {
        if !path_ids.contains(&diagram.lhs_path_ref) {
            unresolved.push(generic_validation_example(
                &diagram.id,
                &diagram.lhs_path_ref,
                "dangling semantic_diagram.lhs_path_ref",
            ));
        }
        if !path_ids.contains(&diagram.rhs_path_ref) {
            unresolved.push(generic_validation_example(
                &diagram.id,
                &diagram.rhs_path_ref,
                "dangling semantic_diagram.rhs_path_ref",
            ));
        }
        unresolved.extend(unresolved_refs(
            &diagram.id,
            "dangling semantic_diagram.nonfillability_witness_refs",
            &diagram.nonfillability_witness_refs,
            &witness_ids,
        ));
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.diagram_refs",
            &generator.diagram_refs,
            &diagram_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        if !diagram_ids.contains(&witness.diagram_ref) {
            unresolved.push(generic_validation_example(
                &witness.witness_id,
                &witness.diagram_ref,
                "dangling nonfillability_witness.diagram_ref",
            ));
        }
    }

    air_ref_check(
        "air-path-witness-refs-resolved",
        "AIR path, diagram, and witness refs resolve",
        unresolved,
    )
}

fn check_air_coverage_universe_refs(document: &AirDocumentV0) -> ValidationCheck {
    let artifact_ids = air_artifact_ids(document);
    let unresolved: Vec<ValidationExample> = document
        .coverage
        .layers
        .iter()
        .flat_map(|layer| {
            unresolved_refs(
                &layer.layer,
                "dangling coverage.layers.universe_refs",
                &layer.universe_refs,
                &artifact_ids,
            )
        })
        .collect();
    air_ref_check(
        "air-coverage-universe-refs-resolved",
        "coverage universe refs resolve to artifacts",
        unresolved,
    )
}

fn check_air_signature_measurement_boundary(document: &AirDocumentV0) -> ValidationCheck {
    let valid_boundaries = [
        "measuredZero",
        "measuredNonzero",
        "unmeasured",
        "outOfScope",
    ];
    let mut invalid = Vec::new();

    for axis in &document.signature.axes {
        if !valid_boundaries.contains(&axis.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &axis.axis,
                &axis.measurement_boundary,
                "unsupported signature measurement_boundary",
            ));
            continue;
        }
        if !axis.measured {
            if !matches!(
                axis.measurement_boundary.as_str(),
                "unmeasured" | "outOfScope"
            ) {
                invalid.push(generic_validation_example(
                    &axis.axis,
                    &axis.measurement_boundary,
                    "unmeasured axis must use unmeasured or outOfScope boundary",
                ));
            }
            continue;
        }
        match axis.value {
            Some(0) => {
                if axis.measurement_boundary != "measuredZero" {
                    invalid.push(generic_validation_example(
                        &axis.axis,
                        &axis.measurement_boundary,
                        "zero measured axis must use measuredZero boundary",
                    ));
                }
            }
            Some(_) => {
                if axis.measurement_boundary != "measuredNonzero" {
                    invalid.push(generic_validation_example(
                        &axis.axis,
                        &axis.measurement_boundary,
                        "nonzero measured axis must use measuredNonzero boundary",
                    ));
                }
            }
            None => {
                invalid.push(generic_validation_example(
                    &axis.axis,
                    &axis.measurement_boundary,
                    "measured axis must carry a value",
                ));
            }
        }
    }

    for layer in &document.coverage.layers {
        if !valid_boundaries.contains(&layer.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &layer.layer,
                &layer.measurement_boundary,
                "unsupported coverage measurement_boundary",
            ));
        }
    }

    air_ref_check(
        "air-signature-boundary-compatible",
        "signature and coverage measurement boundaries are internally consistent",
        invalid,
    )
}

fn check_air_claim_measurement_boundary(document: &AirDocumentV0) -> ValidationCheck {
    let valid_boundaries = [
        "measuredZero",
        "measuredNonzero",
        "unmeasured",
        "outOfScope",
    ];
    let valid_classifications = [
        "proved",
        "measured",
        "assumed",
        "empirical",
        "unmeasured",
        "out_of_scope",
    ];
    let mut invalid = Vec::new();

    for claim in &document.claims {
        if !valid_boundaries.contains(&claim.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.measurement_boundary,
                "unsupported measurement_boundary",
            ));
        }
        if !valid_classifications.contains(&claim.claim_classification.as_str()) {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_classification,
                "unsupported claim_classification",
            ));
        }
        if claim.claim_classification == "measured"
            && !matches!(
                claim.measurement_boundary.as_str(),
                "measuredZero" | "measuredNonzero"
            )
        {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.measurement_boundary,
                "measured claim must use a measured boundary",
            ));
        }
        if matches!(
            claim.measurement_boundary.as_str(),
            "measuredZero" | "measuredNonzero"
        ) && claim.claim_classification == "unmeasured"
        {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_classification,
                "measured boundary cannot be classified as unmeasured",
            ));
        }
        if claim.claim_classification == "proved" && claim.claim_level != "formal" {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_level,
                "proved claim must be claim_level formal",
            ));
        }
        if claim.claim_classification == "proved" && !claim.missing_preconditions.is_empty() {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.missing_preconditions.join(", "),
                "proved claim has missing preconditions",
            ));
        }
    }

    air_ref_check(
        "air-claim-boundary-compatible",
        "claim classification is compatible with measurement boundary",
        invalid,
    )
}

fn check_air_measured_claim_evidence(
    document: &AirDocumentV0,
    strict_measured_evidence: bool,
) -> ValidationCheck {
    let missing_evidence: Vec<ValidationExample> = document
        .claims
        .iter()
        .filter(|claim| claim.claim_classification == "measured" && claim.evidence_refs.is_empty())
        .map(|claim| {
            generic_validation_example(
                &claim.claim_id,
                &claim.subject_ref,
                "measured claim has no evidence_refs",
            )
        })
        .collect();
    let mut check = validation_check(
        "air-measured-claims-have-evidence",
        "measured tooling claims are traceable to evidence",
        if missing_evidence.is_empty() {
            "pass"
        } else if strict_measured_evidence {
            "fail"
        } else {
            "warn"
        },
    );
    if !missing_evidence.is_empty() {
        check.reason = Some("measured claims without evidence refs found".to_string());
        check.count = Some(missing_evidence.len());
        check.examples = missing_evidence.into_iter().take(5).collect();
    }
    check
}

fn air_ref_check(id: &str, title: &str, unresolved: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if unresolved.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !unresolved.is_empty() {
        check.reason = Some("dangling or invalid AIR references found".to_string());
        check.count = Some(unresolved.len());
        check.examples = unresolved.into_iter().take(5).collect();
    }
    check
}

fn unresolved_refs(
    owner: &str,
    reason: &str,
    refs: &[String],
    valid_refs: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    refs.iter()
        .filter(|value| !valid_refs.contains(*value))
        .map(|value| generic_validation_example(owner, value, reason))
        .collect()
}

fn optional_unresolved_ref(
    owner: &str,
    value: Option<&String>,
    valid_refs: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    value
        .filter(|value| !valid_refs.contains(*value))
        .map(|value| generic_validation_example(owner, value, "dangling optional claim ref"))
        .into_iter()
        .collect()
}

fn air_artifact_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .artifacts
        .iter()
        .map(|artifact| artifact.artifact_id.clone())
        .collect()
}

fn air_evidence_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .evidence
        .iter()
        .map(|evidence| evidence.evidence_id.clone())
        .collect()
}

fn air_component_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect()
}

fn air_claim_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .claims
        .iter()
        .map(|claim| claim.claim_id.clone())
        .collect()
}

fn generic_validation_example(source: &str, target: &str, evidence: &str) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(source.to_string()),
        target: Some(target.to_string()),
        evidence: Some(evidence.to_string()),
    }
}

fn duplicates<'a>(values: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
        .into_iter()
        .filter_map(|(value, count)| (count > 1).then(|| value.to_string()))
        .collect()
}

fn component_roots(component_ids: &BTreeSet<String>) -> BTreeSet<String> {
    component_ids
        .iter()
        .filter_map(|id| id.split('.').next())
        .filter(|root| !root.is_empty())
        .map(str::to_string)
        .collect()
}

fn unresolved_edges(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    edges
        .iter()
        .filter(|edge| {
            edge.source.is_empty()
                || edge.target.is_empty()
                || (!component_ids.contains(&edge.source)
                    && is_local_like(&edge.source, local_roots)
                    && !is_module_root_target(&edge.source, component_ids, local_roots))
                || (!component_ids.contains(&edge.target)
                    && is_local_like(&edge.target, local_roots)
                    && !is_module_root_target(&edge.target, component_ids, local_roots))
        })
        .map(edge_example)
        .collect()
}

fn external_edges(
    document: &Sig0Document,
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    document
        .edges
        .iter()
        .filter(|edge| {
            (!component_ids.contains(&edge.source) && !is_local_like(&edge.source, local_roots))
                || is_module_root_target(&edge.source, component_ids, local_roots)
                || (!component_ids.contains(&edge.target)
                    && !is_local_like(&edge.target, local_roots))
                || is_module_root_target(&edge.target, component_ids, local_roots)
        })
        .map(edge_example)
        .collect()
}

fn is_local_like(component_id: &str, local_roots: &BTreeSet<String>) -> bool {
    component_id
        .split('.')
        .next()
        .is_some_and(|root| local_roots.contains(root))
}

fn is_module_root_target(
    component_id: &str,
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> bool {
    local_roots.contains(component_id)
        && !component_ids.contains(component_id)
        && component_ids.iter().any(|id| {
            id.strip_prefix(component_id)
                .is_some_and(|rest| rest.starts_with('.'))
        })
}

fn edge_example(edge: &Edge) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(edge.source.clone()),
        target: Some(edge.target.clone()),
        evidence: Some(edge.evidence.clone()),
    }
}

fn measured_status(source: &str) -> MetricStatus {
    MetricStatus {
        measured: true,
        reason: None,
        source: Some(source.to_string()),
    }
}

fn unmeasured_status(reason: String) -> MetricStatus {
    MetricStatus {
        measured: false,
        reason: Some(reason),
        source: None,
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn parses_leading_imports_only() {
        let source = r#"
-- comment
import Formal.Arch.Graph
import Formal.Arch.Signature -- inline comment

def x := 1
import Should.Not.Appear
"#;

        let imports = parse_imports(source);

        assert_eq!(
            imports,
            vec![
                ParsedImport {
                    module: "Formal.Arch.Graph".to_string(),
                    evidence: "import Formal.Arch.Graph".to_string(),
                },
                ParsedImport {
                    module: "Formal.Arch.Signature".to_string(),
                    evidence: "import Formal.Arch.Signature".to_string(),
                },
            ]
        );
    }

    #[test]
    fn theorem_check_keeps_measured_witness_out_of_formal_proved_claims() {
        let document = air_fixture_document("good_extension.json");
        let report = build_theorem_precondition_check_report(&document, "good_extension.json");

        assert_eq!(
            report.schema_version,
            THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.registry.scope, "static theorem package v0");
        assert!(report.registry.packages.iter().any(|package| {
            package.theorem_refs
                == vec![
                    "SelectedStaticSplitExtension".to_string(),
                    "CoreEdgesPreserved".to_string(),
                    "DeclaredInterfaceFactorization".to_string(),
                    "NoNewForbiddenStaticEdge".to_string(),
                    "EmbeddingPolicyPreserved".to_string(),
                ]
        }));

        let boundary_check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-boundary-zero")
            .expect("boundary claim is checked");
        assert_eq!(
            boundary_check.resolved_claim_classification,
            "MEASURED_WITNESS"
        );
        assert_eq!(report.summary.formal_proved_claim_count, 0);
        assert!(report.summary.measured_witness_count > 0);
    }

    #[test]
    fn theorem_check_blocks_formal_claims_with_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-blocked".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec!["SelectedStaticSplitExtension".to_string()],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: vec![
                "declared interface factorization not discharged".to_string(),
            ],
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-blocked")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "BLOCKED_FORMAL_CLAIM");
        assert_eq!(check.result, "warn");
        assert_eq!(report.summary.blocked_claim_count, 1);
        assert_eq!(report.summary.formal_proved_claim_count, 0);
    }

    #[test]
    fn theorem_check_accepts_registered_formal_claim_without_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-proved".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: Vec::new(),
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-proved")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(check.result, "pass");
        assert_eq!(report.summary.formal_proved_claim_count, 1);
    }

    #[test]
    fn extracts_minimal_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let document = extract_sig0(&root).expect("fixture extracts");

        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert_eq!(document.component_kind, COMPONENT_KIND);
        assert!(document.components.iter().any(|c| c.id == "Formal"));
        assert!(document.components.iter().any(|c| c.id == "Formal.Arch.B"));
        assert!(!document.components.iter().any(|c| c.id == "lakefile"));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "Formal.Arch.B"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "import"
                && edge.evidence == "import Formal.Arch.A"
        }));
        assert_eq!(document.signature.has_cycle, 0);
        assert_eq!(document.signature.scc_max_size, 1);
        assert_eq!(document.signature.fanout_risk, 3);
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("hasCycle")
                .expect("hasCycle status")
                .measured
        );
        assert!(
            !document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .reason
                .as_deref(),
            Some("policy file not provided")
        );
        assert!(document.policy_violations.is_empty());
        assert!(document.runtime_edge_evidence.is_empty());
        assert!(document.runtime_dependency_graph.is_none());
    }

    #[test]
    fn projects_runtime_edge_evidence_to_runtime_dependency_graph() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let runtime_edges = root.join("runtime_edges.json");
        let document =
            extract_sig0_with_runtime(&root, None, Some(&runtime_edges)).expect("fixture extracts");

        assert_eq!(document.runtime_edge_evidence.len(), 2);
        assert!(document.runtime_edge_evidence.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.label == "rpc"
                && edge.failure_mode.as_deref() == Some("timeout")
                && edge.timeout_budget.as_deref() == Some("250ms")
                && edge.retry_policy.as_deref() == Some("bounded-retry")
                && edge.circuit_breaker_coverage.as_deref() == Some("covered")
                && edge.confidence.as_deref() == Some("fixture")
                && edge.evidence_location.path == "runtime/routes.json"
        }));

        let projection = document
            .runtime_dependency_graph
            .as_ref()
            .expect("runtime projection");
        assert_eq!(projection.projection_rule, RUNTIME_PROJECTION_RULE_VERSION);
        assert_eq!(projection.edge_kind, "runtime");
        assert_eq!(projection.edges.len(), 2);
        assert!(projection.edges.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "runtime"
                && edge.evidence == "runtime edge evidence count: 1"
        }));
        assert!(
            document
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "head")
            .expect("dataset builds");
        assert_eq!(
            dataset.signature_after.signature.runtime_propagation,
            Some(2)
        );
        assert_eq!(dataset.delta_signature_signed.runtime_propagation, Some(0));
        assert!(
            dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime dataset status")
                .measured
        );
    }

    #[test]
    fn builds_relation_complexity_observation_from_candidate_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_candidates.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(
            observation.schema_version,
            RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION
        );
        assert_eq!(
            observation.measurement_universe.rule_set_version.as_deref(),
            Some(RELATION_COMPLEXITY_RULE_SET_VERSION)
        );
        assert_eq!(observation.workflow.id, "checkout-payment");
        assert_eq!(observation.counts.constraints, 1);
        assert_eq!(observation.counts.compensations, 1);
        assert_eq!(observation.counts.projections, 0);
        assert_eq!(observation.counts.failure_transitions, 1);
        assert_eq!(observation.counts.idempotency_requirements, 0);
        assert_eq!(observation.relation_complexity, 3);
        assert_eq!(observation.evidence.len(), 2);
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "constraint-1"
                && evidence.path == "src/billing/checkout.rs"
                && evidence.symbol.as_deref() == Some("CheckoutWorkflow::validate")
                && evidence.line == Some(42)
                && evidence.tags == vec!["constraints".to_string()]
                && evidence.ownership == "application-owned"
                && evidence.review_status == "candidate"
        }));
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "compensate-timeout"
                && evidence.tags
                    == vec![
                        "compensations".to_string(),
                        "failureTransitions".to_string(),
                    ]
                && evidence.ownership == "application-configured"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/framework/generated.rs"
                && evidence.reason == "ownership-not-counted:framework-generated"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout.rs"
                && evidence.reason == "unsupported-tags:notATag"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout_test.rs" && evidence.reason == "test-fixture"
        }));
    }

    #[test]
    fn relation_complexity_fixture_excludes_unsupported_framework() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_unsupported_framework.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(observation.relation_complexity, 0);
        assert!(observation.evidence.is_empty());
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/unsupported.rs"
                && evidence.reason == "unsupported-framework:unsupported-framework"
        }));
    }

    #[test]
    fn applies_policy_with_measured_zero_counts() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(
            document.policies.policy_id.as_deref(),
            Some("minimal-measured-zero")
        );
        assert_eq!(document.policies.boundary_group_count, Some(2));
        assert_eq!(document.policies.abstraction_relation_count, Some(1));
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .source
                .as_deref(),
            Some("policy:minimal-measured-zero")
        );
        assert!(document.policy_violations.is_empty());
    }

    #[test]
    fn counts_policy_violations_by_unique_dependency_edge() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_violations.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(document.signature.boundary_violation_count, 2);
        assert_eq!(document.signature.abstraction_violation_count, 1);
        assert!(
            document
                .policy_violations
                .iter()
                .any(|violation| violation.axis == "boundaryViolationCount"
                    && violation.source == "Formal"
                    && violation.target == "Formal.Arch.A")
        );
        assert!(document.policy_violations.iter().any(|violation| {
            violation.axis == "abstractionViolationCount"
                && violation.source == "Formal"
                && violation.target == "Formal.Arch.B"
                && violation
                    .relation_ids
                    .as_ref()
                    .is_some_and(|relations| relations == &vec!["formal-api".to_string()])
        }));
    }

    #[test]
    fn validates_minimal_fixture_with_tooling_boundary_warnings() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.schema_version, VALIDATION_REPORT_SCHEMA_VERSION);
        assert_eq!(report.universe_mode, DEFAULT_UNIVERSE_MODE);
        assert_eq!(report.summary.component_count, 3);
        assert_eq!(report.summary.local_edge_count, 3);
        assert_eq!(report.summary.external_edge_count, 0);
        assert_eq!(report.summary.failed_check_count, 0);
        assert_eq!(report.summary.warning_check_count, 0);
        assert_eq!(report.summary.not_measured_check_count, 0);
        assert_eq!(report.summary.result, "pass");
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "metric-status-complete" && check.result == "pass" })
        );
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "boundary-policy-status" && check.result == "pass" })
        );
        assert!(report.warnings.is_empty());
    }

    #[test]
    fn validation_report_detects_duplicate_and_uncovered_local_target() {
        let mut metric_status = BTreeMap::new();
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        let document = Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components: vec![
                Component {
                    id: "Formal".to_string(),
                    path: "Formal.lean".to_string(),
                },
                Component {
                    id: "Formal".to_string(),
                    path: "FormalDuplicate.lean".to_string(),
                },
            ],
            edges: vec![Edge {
                source: "Formal".to_string(),
                target: "Formal.Arch.Missing".to_string(),
                kind: "import".to_string(),
                evidence: "import Formal.Arch.Missing".to_string(),
            }],
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature: Signature {
                has_cycle: 0,
                scc_max_size: 1,
                max_depth: 1,
                fanout_risk: 1,
                boundary_violation_count: 0,
                abstraction_violation_count: 0,
            },
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        };

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.result, "fail");
        assert_eq!(report.summary.failed_check_count, 3);
        assert!(report.checks.iter().any(|check| {
            check.id == "component-id-nodup" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-endpoint-resolved" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-closure-local" && check.result == "fail" && check.count == Some(1)
        }));
    }

    #[test]
    fn validation_report_warns_about_external_targets_in_local_only_mode() {
        let mut document = extract_sig0(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/minimal")
                .as_path(),
        )
        .expect("fixture extracts");
        document.edges.push(Edge {
            source: "Formal".to_string(),
            target: "Mathlib.Data.List.Basic".to_string(),
            kind: "import".to_string(),
            evidence: "import Mathlib.Data.List.Basic".to_string(),
        });

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.external_edge_count, 1);
        assert!(report.checks.iter().any(|check| {
            check.id == "external-edge-targets" && check.result == "warn" && check.count == Some(1)
        }));
        assert_eq!(
            report.warnings,
            vec!["local-only universe excludes external or synthetic import targets".to_string()]
        );
    }

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

    #[test]
    fn detects_cycle_fixture_metrics() {
        let components = vec![
            Component {
                id: "A".to_string(),
                path: "A.lean".to_string(),
            },
            Component {
                id: "B".to_string(),
                path: "B.lean".to_string(),
            },
        ];
        let edges = vec![
            Edge {
                source: "A".to_string(),
                target: "B".to_string(),
                kind: "import".to_string(),
                evidence: "import B".to_string(),
            },
            Edge {
                source: "B".to_string(),
                target: "A".to_string(),
                kind: "import".to_string(),
                evidence: "import A".to_string(),
            },
        ];

        let signature = compute_signature(&components, &edges);

        assert_eq!(signature.has_cycle, 1);
        assert_eq!(signature.scc_max_size, 2);
        assert_eq!(signature.fanout_risk, 2);
    }

    fn sig0_document_for_edges(
        components: Vec<(&str, &str)>,
        edge_pairs: Vec<(&str, &str)>,
    ) -> Sig0Document {
        let components: Vec<Component> = components
            .into_iter()
            .map(|(id, path)| Component {
                id: id.to_string(),
                path: path.to_string(),
            })
            .collect();
        let edges: Vec<Edge> = edge_pairs
            .into_iter()
            .map(|(source, target)| Edge {
                source: source.to_string(),
                target: target.to_string(),
                kind: "import".to_string(),
                evidence: format!("import {target}"),
            })
            .collect();
        let signature = compute_signature(&components, &edges);
        let mut metric_status = BTreeMap::new();
        for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
            metric_status.insert(axis.to_string(), measured_status("archsig:import-graph"));
        }
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );

        Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components,
            edges,
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature,
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        }
    }

    fn air_fixture_document(fixture: &str) -> AirDocumentV0 {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/air")
            .join(fixture);
        let contents = std::fs::read_to_string(&path).expect("AIR fixture is readable");
        serde_json::from_str(&contents).expect("AIR fixture parses")
    }

    fn dataset_input() -> EmpiricalDatasetInput {
        EmpiricalDatasetInput {
            repository: RepositoryRef {
                owner: "example".to_string(),
                name: "service".to_string(),
                default_branch: "main".to_string(),
            },
            pull_request: PullRequestRef {
                number: 42,
                author: "alice".to_string(),
                created_at: "2026-04-01T00:00:00Z".to_string(),
                merged_at: Some("2026-04-02T00:00:00Z".to_string()),
                base_commit: "base-sha".to_string(),
                head_commit: "head-sha".to_string(),
                merge_commit: Some("merge-sha".to_string()),
                labels: vec!["feature".to_string()],
                is_bot_generated: false,
            },
            pr_metrics: PullRequestMetrics {
                changed_files: 2,
                changed_lines_added: 20,
                changed_lines_deleted: 5,
                changed_components: vec!["A".to_string(), "C".to_string()],
                review_comment_count: 1,
                review_thread_count: 1,
                review_round_count: 1,
                first_review_latency_hours: Some(2.0),
                approval_latency_hours: Some(6.0),
                merge_latency_hours: Some(12.0),
            },
            issue_incident_links: Vec::new(),
            analysis_metadata: AnalysisMetadata::default(),
        }
    }
}
