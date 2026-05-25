use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use serde::Deserialize;

use crate::{
    COMPONENT_KIND, Component, Edge, RUNTIME_EDGE_EVIDENCE_SCHEMA_VERSION,
    RUNTIME_PROJECTION_RULE_VERSION, RuntimeDependencyGraphProjection, RuntimeEdgeEvidence,
};

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RuntimeEdgeEvidenceFile {
    schema_version: String,
    component_id_kind: String,
    edges: Vec<RuntimeEdgeEvidence>,
}

pub(crate) fn read_runtime_edge_evidence(
    path: &Path,
    components: &[Component],
) -> Result<Vec<RuntimeEdgeEvidence>, Box<dyn Error>> {
    let source = fs::read_to_string(path)?;
    let file: RuntimeEdgeEvidenceFile = serde_json::from_str(&source)?;
    if file.schema_version != RUNTIME_EDGE_EVIDENCE_SCHEMA_VERSION {
        return Err(format!(
            "unsupported runtime edge evidence schemaVersion: {}",
            file.schema_version
        )
        .into());
    }
    if file.component_id_kind != COMPONENT_KIND {
        return Err(format!(
            "unsupported runtime edge evidence componentIdKind: {}",
            file.component_id_kind
        )
        .into());
    }

    let component_ids = local_component_ids(components);
    let mut edges = file.edges;
    for edge in &edges {
        validate_runtime_edge_evidence(edge, &component_ids)?;
    }
    edges.sort_by(|a, b| {
        a.source
            .cmp(&b.source)
            .then(a.target.cmp(&b.target))
            .then(a.label.cmp(&b.label))
            .then(a.evidence_location.path.cmp(&b.evidence_location.path))
            .then(a.evidence_location.line.cmp(&b.evidence_location.line))
            .then(a.evidence_location.symbol.cmp(&b.evidence_location.symbol))
    });
    Ok(edges)
}

fn validate_runtime_edge_evidence(
    edge: &RuntimeEdgeEvidence,
    component_ids: &BTreeSet<String>,
) -> Result<(), String> {
    if edge.source.is_empty() {
        return Err("runtime edge source must not be empty".to_string());
    }
    if edge.target.is_empty() {
        return Err("runtime edge target must not be empty".to_string());
    }
    if edge.label.is_empty() {
        return Err("runtime edge label must not be empty".to_string());
    }
    if edge.evidence_location.path.is_empty() {
        return Err("runtime edge evidenceLocation.path must not be empty".to_string());
    }
    if !component_ids.contains(&edge.source) {
        return Err(format!(
            "runtime edge source is outside component universe: {}",
            edge.source
        ));
    }
    if !component_ids.contains(&edge.target) {
        return Err(format!(
            "runtime edge target is outside component universe: {}",
            edge.target
        ));
    }
    Ok(())
}

pub(crate) fn project_runtime_dependency_graph(
    evidence: &[RuntimeEdgeEvidence],
) -> RuntimeDependencyGraphProjection {
    let mut by_pair: BTreeMap<(String, String), usize> = BTreeMap::new();
    for item in evidence {
        *by_pair
            .entry((item.source.clone(), item.target.clone()))
            .or_default() += 1;
    }

    let edges = by_pair
        .into_iter()
        .map(|((source, target), count)| Edge {
            source,
            target,
            kind: "runtime".to_string(),
            evidence: format!("runtime edge evidence count: {count}"),
        })
        .collect();

    RuntimeDependencyGraphProjection {
        projection_rule: RUNTIME_PROJECTION_RULE_VERSION.to_string(),
        edge_kind: "runtime".to_string(),
        edges,
    }
}

fn local_component_ids(components: &[Component]) -> BTreeSet<String> {
    components
        .iter()
        .map(|component| component.id.clone())
        .collect()
}
