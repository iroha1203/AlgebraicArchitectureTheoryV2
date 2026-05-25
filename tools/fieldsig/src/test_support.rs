use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::graph::compute_signature;
use crate::{
    AirDocumentV0, AnalysisMetadata, COMPONENT_KIND, Component, Edge, EmpiricalDatasetInput,
    MetricStatus, Policies, PullRequestMetrics, PullRequestRef, RepositoryRef, SCHEMA_VERSION,
    Sig0Document, measured_status, unmeasured_status,
};

pub(crate) fn fixture_root() -> PathBuf {
    manifest_root().join("tests/fixtures/minimal")
}

pub(crate) fn air_fixture_document(fixture: &str) -> AirDocumentV0 {
    let path = manifest_root().join("tests/fixtures/air").join(fixture);
    let contents = std::fs::read_to_string(&path).expect("AIR fixture is readable");
    serde_json::from_str(&contents).expect("AIR fixture parses")
}

pub(crate) fn sig0_document_for_edges(
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
    insert_unmeasured_policy_status(&mut metric_status);

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
        unsupported_constructs: Vec::new(),
    }
}

pub(crate) fn insert_unmeasured_policy_status(metric_status: &mut BTreeMap<String, MetricStatus>) {
    metric_status.insert(
        "boundaryViolationCount".to_string(),
        unmeasured_status("policy file not provided".to_string()),
    );
    metric_status.insert(
        "abstractionViolationCount".to_string(),
        unmeasured_status("policy file not provided".to_string()),
    );
}

pub(crate) fn dataset_input() -> EmpiricalDatasetInput {
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

fn manifest_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}
