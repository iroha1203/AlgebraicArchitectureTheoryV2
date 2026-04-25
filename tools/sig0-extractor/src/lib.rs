use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::ffi::OsStr;
use std::fs;
use std::path::{Component as PathComponent, Path, PathBuf};

use serde::{Deserialize, Serialize};
use walkdir::{DirEntry, WalkDir};

pub const SCHEMA_VERSION: &str = "sig0-extractor-v0";
pub const COMPONENT_KIND: &str = "lean-module";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Sig0Document {
    pub schema_version: String,
    pub root: String,
    pub component_kind: String,
    pub components: Vec<Component>,
    pub edges: Vec<Edge>,
    pub policies: Policies,
    pub signature: Signature,
    pub metric_status: BTreeMap<String, MetricStatus>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub policy_violations: Vec<PolicyViolation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Component {
    pub id: String,
    pub path: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edge {
    pub source: String,
    pub target: String,
    pub kind: String,
    pub evidence: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Policies {
    pub boundary_allowed: Vec<String>,
    pub abstraction_allowed: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub boundary_group_count: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub abstraction_relation_count: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Signature {
    pub has_cycle: usize,
    pub scc_max_size: usize,
    pub max_depth: usize,
    pub fanout_risk: usize,
    pub boundary_violation_count: usize,
    pub abstraction_violation_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetricStatus {
    pub measured: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyViolation {
    pub axis: String,
    pub source: String,
    pub target: String,
    pub evidence: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_group: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_group: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relation_ids: Option<Vec<String>>,
}

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
    })
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

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PolicyFile {
    schema_version: String,
    policy_id: String,
    component_id_kind: String,
    selector_semantics: String,
    boundary: Option<BoundaryPolicy>,
    abstraction: Option<AbstractionPolicy>,
}

impl PolicyFile {
    fn read(path: &Path) -> Result<Self, Box<dyn Error>> {
        let source = fs::read_to_string(path)?;
        let policy: PolicyFile = serde_json::from_str(&source)?;
        if policy.schema_version != "signature-policy-v0" {
            return Err(format!(
                "unsupported policy schemaVersion: {}",
                policy.schema_version
            )
            .into());
        }
        if policy.component_id_kind != COMPONENT_KIND {
            return Err(format!(
                "unsupported policy componentIdKind: {}",
                policy.component_id_kind
            )
            .into());
        }
        if policy.selector_semantics != "exact-or-prefix-star" {
            return Err(format!(
                "unsupported policy selectorSemantics: {}",
                policy.selector_semantics
            )
            .into());
        }
        Ok(policy)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct BoundaryPolicy {
    groups: Vec<BoundaryGroup>,
    allowed_dependencies: Vec<AllowedDependency>,
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct BoundaryGroup {
    id: String,
    components: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AllowedDependency {
    source_group: String,
    target_group: String,
    #[allow(dead_code)]
    reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AbstractionPolicy {
    relations: Vec<AbstractionRelation>,
    #[allow(dead_code)]
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AbstractionRelation {
    id: String,
    abstraction: String,
    clients: Vec<String>,
    implementations: Vec<String>,
    #[serde(default)]
    allowed_direct_implementation_dependencies: Vec<String>,
}

fn measure_boundary(
    boundary: &BoundaryPolicy,
    components: &[Component],
    edges: &[Edge],
) -> Result<(usize, Vec<PolicyViolation>), String> {
    if boundary.unmatched_component.as_deref() != Some("not-measured") {
        return Err("boundary.unmatchedComponent must be not-measured".to_string());
    }

    let component_ids = local_component_ids(components);
    let mut membership: BTreeMap<String, BTreeSet<String>> = component_ids
        .iter()
        .map(|id| (id.clone(), BTreeSet::new()))
        .collect();

    for group in &boundary.groups {
        if group.id.is_empty() {
            return Err("boundary group id must not be empty".to_string());
        }
        if group.components.is_empty() {
            return Err(format!(
                "boundary group {} has no component selectors",
                group.id
            ));
        }

        for selector in &group.components {
            let matches = resolve_selector(selector, &component_ids)?;
            if matches.is_empty() {
                return Err(format!(
                    "boundary selector did not match component: {selector}"
                ));
            }
            for component in matches {
                membership
                    .get_mut(&component)
                    .expect("component id came from local set")
                    .insert(group.id.clone());
            }
        }
    }

    let mut group_by_component = BTreeMap::new();
    for (component, groups) in membership {
        if groups.len() != 1 {
            return Err(format!(
                "boundary group membership is not unique for {component}"
            ));
        }
        group_by_component.insert(
            component,
            groups
                .into_iter()
                .next()
                .expect("exactly one boundary group"),
        );
    }

    let allowed: BTreeSet<(String, String)> = boundary
        .allowed_dependencies
        .iter()
        .map(|dependency| {
            (
                dependency.source_group.clone(),
                dependency.target_group.clone(),
            )
        })
        .collect();

    let mut violations = Vec::new();
    for edge in edges {
        if !component_ids.contains(&edge.source) || !component_ids.contains(&edge.target) {
            continue;
        }

        let source_group = group_by_component
            .get(&edge.source)
            .expect("local component has boundary group");
        let target_group = group_by_component
            .get(&edge.target)
            .expect("local component has boundary group");
        if allowed.contains(&(source_group.clone(), target_group.clone())) {
            continue;
        }

        violations.push(PolicyViolation {
            axis: "boundaryViolationCount".to_string(),
            source: edge.source.clone(),
            target: edge.target.clone(),
            evidence: edge.evidence.clone(),
            source_group: Some(source_group.clone()),
            target_group: Some(target_group.clone()),
            relation_ids: None,
        });
    }

    Ok((violations.len(), violations))
}

fn measure_abstraction(
    abstraction: &AbstractionPolicy,
    components: &[Component],
    edges: &[Edge],
) -> Result<(usize, Vec<PolicyViolation>), String> {
    if abstraction.relations.is_empty() {
        return Err("abstraction.relations must not be empty".to_string());
    }

    let component_ids = local_component_ids(components);
    let mut relation_components = Vec::new();
    for relation in &abstraction.relations {
        if relation.id.is_empty() {
            return Err("abstraction relation id must not be empty".to_string());
        }
        let clients = resolve_nonempty_selectors(
            &relation.clients,
            &component_ids,
            &format!("abstraction relation {} clients", relation.id),
        )?;
        let abstractions = resolve_selector(&relation.abstraction, &component_ids)?;
        if abstractions.is_empty() {
            return Err(format!(
                "abstraction relation {} abstraction selector did not match component: {}",
                relation.id, relation.abstraction
            ));
        }
        let implementations = resolve_nonempty_selectors(
            &relation.implementations,
            &component_ids,
            &format!("abstraction relation {} implementations", relation.id),
        )?;
        let allowed_direct = resolve_optional_selectors(
            &relation.allowed_direct_implementation_dependencies,
            &component_ids,
        )?;

        relation_components.push(ResolvedAbstractionRelation {
            id: relation.id.clone(),
            clients,
            implementations,
            allowed_direct,
        });
    }

    let mut violations = Vec::new();
    for edge in edges {
        if !component_ids.contains(&edge.source) || !component_ids.contains(&edge.target) {
            continue;
        }

        let relation_ids: Vec<String> = relation_components
            .iter()
            .filter(|relation| {
                relation.clients.contains(&edge.source)
                    && relation.implementations.contains(&edge.target)
                    && !relation.allowed_direct.contains(&edge.target)
            })
            .map(|relation| relation.id.clone())
            .collect();

        if relation_ids.is_empty() {
            continue;
        }

        violations.push(PolicyViolation {
            axis: "abstractionViolationCount".to_string(),
            source: edge.source.clone(),
            target: edge.target.clone(),
            evidence: edge.evidence.clone(),
            source_group: None,
            target_group: None,
            relation_ids: Some(relation_ids),
        });
    }

    Ok((violations.len(), violations))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedAbstractionRelation {
    id: String,
    clients: BTreeSet<String>,
    implementations: BTreeSet<String>,
    allowed_direct: BTreeSet<String>,
}

fn local_component_ids(components: &[Component]) -> BTreeSet<String> {
    components
        .iter()
        .map(|component| component.id.clone())
        .collect()
}

fn resolve_nonempty_selectors(
    selectors: &[String],
    component_ids: &BTreeSet<String>,
    label: &str,
) -> Result<BTreeSet<String>, String> {
    if selectors.is_empty() {
        return Err(format!("{label} selectors must not be empty"));
    }
    let resolved = resolve_optional_selectors(selectors, component_ids)?;
    if resolved.is_empty() {
        return Err(format!("{label} selectors did not match any component"));
    }
    Ok(resolved)
}

fn resolve_optional_selectors(
    selectors: &[String],
    component_ids: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    let mut resolved = BTreeSet::new();
    for selector in selectors {
        let matches = resolve_selector(selector, component_ids)?;
        if matches.is_empty() {
            return Err(format!("selector did not match component: {selector}"));
        }
        resolved.extend(matches);
    }
    Ok(resolved)
}

fn resolve_selector(
    selector: &str,
    component_ids: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    validate_selector(selector)?;
    if let Some(prefix) = selector.strip_suffix('*') {
        return Ok(component_ids
            .iter()
            .filter(|component| component.starts_with(prefix))
            .cloned()
            .collect());
    }

    Ok(component_ids
        .iter()
        .filter(|component| component.as_str() == selector)
        .cloned()
        .collect())
}

fn validate_selector(selector: &str) -> Result<(), String> {
    if selector.is_empty() {
        return Err("selector must not be empty".to_string());
    }

    let star_count = selector.chars().filter(|ch| *ch == '*').count();
    if star_count > 1 || (star_count == 1 && !selector.ends_with('*')) {
        return Err(format!("unsupported selector: {selector}"));
    }

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedImport {
    module: String,
    evidence: String,
}

fn parse_imports(source: &str) -> Vec<ParsedImport> {
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
    if !entry.file_type().is_dir() {
        return false;
    }

    let name = entry.file_name().to_string_lossy();
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

fn compute_signature(components: &[Component], edges: &[Edge]) -> Signature {
    let graph = Graph::from_components_and_edges(components, edges);
    let sccs = graph.strongly_connected_components();
    let has_cycle = sccs.iter().any(|scc| {
        scc.len() > 1
            || scc
                .first()
                .is_some_and(|node| graph.neighbors(node).iter().any(|target| target == node))
    });

    Signature {
        has_cycle: usize::from(has_cycle),
        scc_max_size: sccs.iter().map(Vec::len).max().unwrap_or(0),
        max_depth: graph.max_bounded_depth(),
        fanout_risk: graph.unique_edge_count(),
        boundary_violation_count: 0,
        abstraction_violation_count: 0,
    }
}

#[derive(Debug, Clone)]
struct Graph {
    nodes: BTreeSet<String>,
    adjacency: BTreeMap<String, BTreeSet<String>>,
}

impl Graph {
    fn from_components_and_edges(components: &[Component], edges: &[Edge]) -> Self {
        let mut nodes = BTreeSet::new();
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

        for component in components {
            nodes.insert(component.id.clone());
        }

        for edge in edges {
            nodes.insert(edge.source.clone());
            nodes.insert(edge.target.clone());
            adjacency
                .entry(edge.source.clone())
                .or_default()
                .insert(edge.target.clone());
        }

        for node in &nodes {
            adjacency.entry(node.clone()).or_default();
        }

        Self { nodes, adjacency }
    }

    fn neighbors(&self, node: &str) -> Vec<String> {
        self.adjacency
            .get(node)
            .map(|neighbors| neighbors.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn unique_edge_count(&self) -> usize {
        self.adjacency.values().map(BTreeSet::len).sum()
    }

    fn strongly_connected_components(&self) -> Vec<Vec<String>> {
        let mut visited = HashSet::new();
        let mut order = Vec::new();
        for node in &self.nodes {
            self.dfs_order(node, &mut visited, &mut order);
        }

        let reversed = self.reversed();
        let mut visited = HashSet::new();
        let mut sccs = Vec::new();
        for node in order.iter().rev() {
            if visited.contains(node) {
                continue;
            }
            let mut scc = Vec::new();
            reversed.dfs_collect(node, &mut visited, &mut scc);
            scc.sort();
            sccs.push(scc);
        }
        sccs
    }

    fn dfs_order(&self, node: &str, visited: &mut HashSet<String>, order: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        for neighbor in self.neighbors(node) {
            self.dfs_order(&neighbor, visited, order);
        }
        order.push(node.to_string());
    }

    fn dfs_collect(&self, node: &str, visited: &mut HashSet<String>, scc: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        scc.push(node.to_string());
        for neighbor in self.neighbors(node) {
            self.dfs_collect(&neighbor, visited, scc);
        }
    }

    fn reversed(&self) -> Self {
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for node in &self.nodes {
            adjacency.entry(node.clone()).or_default();
        }

        for (source, targets) in &self.adjacency {
            for target in targets {
                adjacency
                    .entry(target.clone())
                    .or_default()
                    .insert(source.clone());
            }
        }

        Self {
            nodes: self.nodes.clone(),
            adjacency,
        }
    }

    fn max_bounded_depth(&self) -> usize {
        let fuel = self.nodes.len();
        let mut memo = HashMap::new();
        self.nodes
            .iter()
            .map(|node| self.bounded_depth_from(node, fuel, &mut memo))
            .max()
            .unwrap_or(0)
    }

    fn bounded_depth_from(
        &self,
        node: &str,
        fuel: usize,
        memo: &mut HashMap<(String, usize), usize>,
    ) -> usize {
        if fuel == 0 {
            return 0;
        }

        let key = (node.to_string(), fuel);
        if let Some(depth) = memo.get(&key) {
            return *depth;
        }

        let depth = self
            .neighbors(node)
            .iter()
            .map(|target| self.bounded_depth_from(target, fuel - 1, memo) + 1)
            .max()
            .unwrap_or(0);
        memo.insert(key, depth);
        depth
    }
}

#[cfg(test)]
mod tests {
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
    fn extracts_minimal_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let document = extract_sig0(&root).expect("fixture extracts");

        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert_eq!(document.component_kind, COMPONENT_KIND);
        assert!(document.components.iter().any(|c| c.id == "Formal"));
        assert!(document.components.iter().any(|c| c.id == "Formal.Arch.B"));
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
}
