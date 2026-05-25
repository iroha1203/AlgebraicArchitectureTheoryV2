use std::collections::BTreeMap;
use std::error::Error;
use std::ffi::OsStr;
use std::fs;
use std::path::{Component as PathComponent, Path, PathBuf};

use walkdir::{DirEntry, WalkDir};

use crate::graph::compute_signature;
use crate::policy::{PolicyFile, measure_abstraction, measure_boundary};
use crate::runtime::{project_runtime_dependency_graph, read_runtime_edge_evidence};
use crate::{
    COMPONENT_KIND, Component, Edge, MetricStatus, Policies, RUNTIME_PROJECTION_RULE_VERSION,
    SCHEMA_VERSION, Sig0Document, measured_status, unmeasured_status,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportEdge {
    source: String,
    target: String,
    evidence: String,
}

pub fn extract_sig0(root: &Path) -> Result<Sig0Document, Box<dyn Error>> {
    extract_sig0_with_policy(root, None)
}

pub fn extract_sig0_with_policy(
    root: &Path,
    policy_path: Option<&Path>,
) -> Result<Sig0Document, Box<dyn Error>> {
    extract_sig0_with_runtime(root, policy_path, None)
}

pub fn extract_sig0_with_runtime(
    root: &Path,
    policy_path: Option<&Path>,
    runtime_edges_path: Option<&Path>,
) -> Result<Sig0Document, Box<dyn Error>> {
    let root = root.to_path_buf();
    let mut components = Vec::new();
    let mut import_edges = Vec::new();

    for path in lean_files(&root)? {
        let relative_path = normalize_relative_path(&root, &path)?;
        let module_id = module_id_from_relative_path(&relative_path)?;
        components.push(Component {
            id: module_id.clone(),
            path: relative_path,
        });

        let source = fs::read_to_string(&path)?;
        for parsed_import in parse_imports(&source) {
            import_edges.push(ImportEdge {
                source: module_id.clone(),
                target: parsed_import.module,
                evidence: parsed_import.evidence,
            });
        }
    }

    components.sort_by(|a, b| a.id.cmp(&b.id).then(a.path.cmp(&b.path)));

    let edges = dedup_edges(import_edges);
    let mut signature = compute_signature(&components, &edges);

    let mut metric_status = BTreeMap::new();
    for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
        metric_status.insert(axis.to_string(), measured_status("archsig:import-graph"));
    }
    metric_status.insert(
        "boundaryViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some("policy file not provided".to_string()),
            source: None,
        },
    );
    metric_status.insert(
        "abstractionViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some("policy file not provided".to_string()),
            source: None,
        },
    );
    let mut policies = Policies {
        boundary_allowed: Vec::new(),
        abstraction_allowed: Vec::new(),
        policy_id: None,
        schema_version: None,
        boundary_group_count: None,
        abstraction_relation_count: None,
    };
    let mut policy_violations = Vec::new();

    if let Some(policy_path) = policy_path {
        let policy = PolicyFile::read(policy_path)?;
        policies = Policies {
            boundary_allowed: Vec::new(),
            abstraction_allowed: Vec::new(),
            policy_id: Some(policy.policy_id.clone()),
            schema_version: Some(policy.schema_version.clone()),
            boundary_group_count: policy
                .boundary
                .as_ref()
                .map(|boundary| boundary.groups.len()),
            abstraction_relation_count: policy
                .abstraction
                .as_ref()
                .map(|abstraction| abstraction.relations.len()),
        };
        let policy_source = format!("policy:{}", policy.policy_id);

        match policy.boundary.as_ref() {
            Some(boundary) => match measure_boundary(boundary, &components, &edges) {
                Ok((count, violations)) => {
                    signature.boundary_violation_count = count;
                    metric_status.insert(
                        "boundaryViolationCount".to_string(),
                        measured_status(&policy_source),
                    );
                    policy_violations.extend(violations);
                }
                Err(reason) => {
                    signature.boundary_violation_count = 0;
                    metric_status.insert(
                        "boundaryViolationCount".to_string(),
                        unmeasured_status(reason),
                    );
                }
            },
            None => {
                signature.boundary_violation_count = 0;
                metric_status.insert(
                    "boundaryViolationCount".to_string(),
                    unmeasured_status("boundary policy not provided".to_string()),
                );
            }
        }

        match policy.abstraction.as_ref() {
            Some(abstraction) => match measure_abstraction(abstraction, &components, &edges) {
                Ok((count, violations)) => {
                    signature.abstraction_violation_count = count;
                    metric_status.insert(
                        "abstractionViolationCount".to_string(),
                        measured_status(&policy_source),
                    );
                    policy_violations.extend(violations);
                }
                Err(reason) => {
                    signature.abstraction_violation_count = 0;
                    metric_status.insert(
                        "abstractionViolationCount".to_string(),
                        unmeasured_status(reason),
                    );
                }
            },
            None => {
                signature.abstraction_violation_count = 0;
                metric_status.insert(
                    "abstractionViolationCount".to_string(),
                    unmeasured_status("abstraction policy not provided".to_string()),
                );
            }
        }
    }

    let (runtime_edge_evidence, runtime_dependency_graph) =
        if let Some(runtime_edges_path) = runtime_edges_path {
            let evidence = read_runtime_edge_evidence(runtime_edges_path, &components)?;
            let projection = project_runtime_dependency_graph(&evidence);
            metric_status.insert(
                "runtimePropagation".to_string(),
                measured_status(RUNTIME_PROJECTION_RULE_VERSION),
            );
            (evidence, Some(projection))
        } else {
            (Vec::new(), None)
        };

    Ok(Sig0Document {
        schema_version: SCHEMA_VERSION.to_string(),
        root: root.display().to_string(),
        component_kind: COMPONENT_KIND.to_string(),
        components,
        edges,
        policies,
        signature,
        metric_status,
        policy_violations,
        runtime_edge_evidence,
        runtime_dependency_graph,
        unsupported_constructs: Vec::new(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParsedImport {
    pub(crate) module: String,
    pub(crate) evidence: String,
}

pub(crate) fn parse_imports(source: &str) -> Vec<ParsedImport> {
    let mut imports = Vec::new();

    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        let Some(rest) = trimmed.strip_prefix("import") else {
            break;
        };
        if !rest.starts_with(char::is_whitespace) {
            break;
        }

        let evidence = trimmed
            .split_once("--")
            .map(|(before_comment, _)| before_comment.trim())
            .unwrap_or(trimmed)
            .to_string();
        let import_body = evidence
            .strip_prefix("import")
            .map(str::trim)
            .unwrap_or_default();

        for module in import_body.split_whitespace() {
            imports.push(ParsedImport {
                module: module.to_string(),
                evidence: evidence.clone(),
            });
        }
    }

    imports
}

fn lean_files(root: &Path) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut files = Vec::new();
    for entry in WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|entry| !is_skipped_entry(root, entry))
    {
        let entry = entry?;
        if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("lean")) {
            files.push(entry.into_path());
        }
    }
    Ok(files)
}

fn is_skipped_entry(root: &Path, entry: &DirEntry) -> bool {
    let name = entry.file_name().to_string_lossy();
    if entry.file_type().is_file() {
        return name == "lakefile.lean";
    }

    if !entry.file_type().is_dir() {
        return false;
    }

    if matches!(name.as_ref(), ".git" | ".lake" | ".elan" | "target") {
        return true;
    }

    entry.path().parent() == Some(root) && name == "tools"
}

fn normalize_relative_path(root: &Path, path: &Path) -> Result<String, Box<dyn Error>> {
    let relative = path.strip_prefix(root)?;
    let mut parts = Vec::new();
    for component in relative.components() {
        match component {
            PathComponent::Normal(part) => parts.push(part.to_string_lossy().into_owned()),
            _ => return Err(format!("unsupported path component in {}", path.display()).into()),
        }
    }
    Ok(parts.join("/"))
}

fn module_id_from_relative_path(relative_path: &str) -> Result<String, Box<dyn Error>> {
    let Some(without_ext) = relative_path.strip_suffix(".lean") else {
        return Err(format!("Lean path does not end with .lean: {relative_path}").into());
    };
    Ok(without_ext.replace('/', "."))
}

fn dedup_edges(import_edges: Vec<ImportEdge>) -> Vec<Edge> {
    let mut by_pair: BTreeMap<(String, String), String> = BTreeMap::new();
    for edge in import_edges {
        by_pair
            .entry((edge.source, edge.target))
            .or_insert(edge.evidence);
    }

    by_pair
        .into_iter()
        .map(|((source, target), evidence)| Edge {
            source,
            target,
            kind: "import".to_string(),
            evidence,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::dataset::build_empirical_dataset;
    use crate::test_support::{dataset_input, fixture_root};
    use crate::{
        COMPONENT_KIND, RUNTIME_PROJECTION_RULE_VERSION, SCHEMA_VERSION, extractor::ParsedImport,
    };

    use super::{extract_sig0, extract_sig0_with_policy, extract_sig0_with_runtime, parse_imports};

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
    fn extracts_minimal_fixture() {
        let root = fixture_root();
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
    fn applies_policy_with_measured_zero_counts() {
        let root = fixture_root();
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
        let root = fixture_root();
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
    fn projects_runtime_edge_evidence_to_runtime_dependency_graph() {
        let root = fixture_root();
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
}
