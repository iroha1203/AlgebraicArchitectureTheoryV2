use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::ffi::OsStr;
use std::path::{Component as PathComponent, Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use walkdir::{DirEntry, WalkDir};

use crate::graph::compute_signature;
use crate::{
    Component, Edge, MetricStatus, PYTHON_COMPONENT_KIND, PYTHON_IMPORT_RULE_VERSION, Policies,
    SCHEMA_VERSION, Sig0Document, measured_status, unmeasured_status,
};

const PYTHON_AST_SCRIPT: &str = r#"
import ast
import json
import sys

path = sys.argv[1]
with open(path, "r", encoding="utf-8") as handle:
    source = handle.read()
lines = source.splitlines()
tree = ast.parse(source, filename=path)

def evidence(node):
    lineno = getattr(node, "lineno", None)
    if lineno is None or lineno < 1 or lineno > len(lines):
        return ""
    return lines[lineno - 1].strip()

imports = []
unsupported = []
for node in ast.walk(tree):
    if isinstance(node, ast.Import):
        imports.append({
            "kind": "import",
            "module": "",
            "names": [alias.name for alias in node.names],
            "level": 0,
            "evidence": evidence(node),
        })
    elif isinstance(node, ast.ImportFrom):
        imports.append({
            "kind": "from",
            "module": node.module or "",
            "names": [alias.name for alias in node.names],
            "level": node.level,
            "evidence": evidence(node),
        })
    elif isinstance(node, ast.Call):
        func = node.func
        dynamic = isinstance(func, ast.Name) and func.id == "__import__"
        dynamic = dynamic or (
            isinstance(func, ast.Attribute)
            and func.attr == "import_module"
            and isinstance(func.value, ast.Name)
            and func.value.id == "importlib"
        )
        if dynamic:
            unsupported.append({
                "kind": "dynamic-import",
                "evidence": evidence(node),
            })

json.dump({"imports": imports, "unsupported": unsupported}, sys.stdout)
"#;

#[derive(Debug, Clone, PartialEq, Eq)]
struct PythonComponent {
    component: Component,
    is_package: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PythonImportEdge {
    source: String,
    target: String,
    evidence: String,
}

#[derive(Debug, Deserialize)]
struct PythonAstOutput {
    imports: Vec<PythonImport>,
    unsupported: Vec<PythonUnsupported>,
}

#[derive(Debug, Deserialize)]
struct PythonImport {
    kind: String,
    module: String,
    names: Vec<String>,
    level: usize,
    evidence: String,
}

#[derive(Debug, Deserialize)]
struct PythonUnsupported {
    kind: String,
    evidence: String,
}

pub fn extract_python_sig0(
    root: &Path,
    source_roots: &[PathBuf],
    package_roots: &[PathBuf],
) -> Result<Sig0Document, Box<dyn Error>> {
    let root = root.to_path_buf();
    let source_roots = normalize_roots(&root, source_roots);
    let package_roots = if package_roots.is_empty() {
        source_roots.clone()
    } else {
        normalize_roots(&root, package_roots)
    };

    let mut python_components = Vec::new();
    for path in python_files(&source_roots)? {
        let relative_path = normalize_relative_path(&root, &path)?;
        let (module_id, is_package) = python_module_id(&path, &package_roots)?;
        python_components.push(PythonComponent {
            component: Component {
                id: module_id,
                path: relative_path,
            },
            is_package,
        });
    }
    python_components.sort_by(|a, b| {
        a.component
            .id
            .cmp(&b.component.id)
            .then(a.component.path.cmp(&b.component.path))
    });

    let components: Vec<Component> = python_components
        .iter()
        .map(|component| component.component.clone())
        .collect();
    let component_ids: BTreeSet<String> = components
        .iter()
        .map(|component| component.id.clone())
        .collect();

    let mut import_edges = Vec::new();
    let mut unsupported = Vec::new();
    for python_component in &python_components {
        let path = root.join(&python_component.component.path);
        let parsed = parse_python_imports(&path)?;
        for import in parsed.imports {
            import_edges.extend(resolve_python_import(
                &python_component.component.id,
                python_component.is_package,
                &import,
                &component_ids,
            ));
        }
        unsupported.extend(parsed.unsupported);
    }

    let edges = dedup_edges(import_edges);
    let signature = compute_signature(&components, &edges);

    let mut metric_status = BTreeMap::new();
    for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
        metric_status.insert(
            axis.to_string(),
            measured_status(PYTHON_IMPORT_RULE_VERSION),
        );
    }
    metric_status.insert(
        "boundaryViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some(
                "Python policy measurement is tracked separately from import extraction"
                    .to_string(),
            ),
            source: None,
        },
    );
    metric_status.insert(
        "abstractionViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some(
                "Python policy measurement is tracked separately from import extraction"
                    .to_string(),
            ),
            source: None,
        },
    );
    metric_status.insert(
        "pythonDynamicImportCoverage".to_string(),
        if unsupported.is_empty() {
            unmeasured_status(
                "dynamic import, plugin loading, and framework convention coverage is outside python-import-graph-v0".to_string(),
            )
        } else {
            let first = unsupported
                .first()
                .map(|site| format!(" first {} evidence: {}", site.kind, site.evidence))
                .unwrap_or_default();
            unmeasured_status(format!(
                "{} unsupported dynamic import site(s) detected; not counted as measured zero.{first}",
                unsupported.len(),
            ))
        },
    );

    Ok(Sig0Document {
        schema_version: SCHEMA_VERSION.to_string(),
        root: root.display().to_string(),
        component_kind: PYTHON_COMPONENT_KIND.to_string(),
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
    })
}

fn normalize_roots(root: &Path, roots: &[PathBuf]) -> Vec<PathBuf> {
    if roots.is_empty() {
        return vec![root.to_path_buf()];
    }

    roots
        .iter()
        .map(|path| {
            if path.is_absolute() {
                path.clone()
            } else {
                root.join(path)
            }
        })
        .collect()
}

fn python_files(source_roots: &[PathBuf]) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut files = BTreeSet::new();
    for source_root in source_roots {
        for entry in WalkDir::new(source_root)
            .sort_by_file_name()
            .into_iter()
            .filter_entry(is_skipped_entry)
        {
            let entry = entry?;
            if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("py")) {
                files.insert(entry.into_path());
            }
        }
    }
    Ok(files.into_iter().collect())
}

fn is_skipped_entry(entry: &DirEntry) -> bool {
    let name = entry.file_name().to_string_lossy();
    if !entry.file_type().is_dir() {
        return true;
    }
    !matches!(
        name.as_ref(),
        ".git"
            | ".lake"
            | ".elan"
            | ".mypy_cache"
            | ".pytest_cache"
            | ".ruff_cache"
            | ".venv"
            | "__pycache__"
            | "target"
            | "venv"
    )
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

fn python_module_id(
    path: &Path,
    package_roots: &[PathBuf],
) -> Result<(String, bool), Box<dyn Error>> {
    let package_root = package_roots
        .iter()
        .filter(|package_root| path.starts_with(package_root))
        .max_by_key(|package_root| package_root.components().count())
        .ok_or_else(|| {
            format!(
                "Python source {} is not under any package root",
                path.display()
            )
        })?;
    let relative = path.strip_prefix(package_root)?;
    let mut parts: Vec<String> = relative
        .components()
        .map(|component| match component {
            PathComponent::Normal(part) => Ok(part.to_string_lossy().into_owned()),
            _ => Err(format!("unsupported path component in {}", path.display())),
        })
        .collect::<Result<_, _>>()?;
    let Some(file_name) = parts.pop() else {
        return Err(format!("Python source has no file name: {}", path.display()).into());
    };
    let Some(stem) = file_name.strip_suffix(".py") else {
        return Err(format!("Python source does not end with .py: {}", path.display()).into());
    };
    let is_package = stem == "__init__";
    if !is_package {
        parts.push(stem.to_string());
    }
    if parts.is_empty() {
        parts.push(stem.to_string());
    }
    Ok((parts.join("."), is_package))
}

fn parse_python_imports(path: &Path) -> Result<PythonAstOutput, Box<dyn Error>> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(PYTHON_AST_SCRIPT)
        .arg(path)
        .output()
        .map_err(|error| format!("python3 is required for Python import extraction: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "Python AST parse failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        )
        .into());
    }
    serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "Python AST output did not parse for {}: {error}",
            path.display()
        )
        .into()
    })
}

fn resolve_python_import(
    source: &str,
    is_package: bool,
    import: &PythonImport,
    component_ids: &BTreeSet<String>,
) -> Vec<PythonImportEdge> {
    match import.kind.as_str() {
        "import" => import
            .names
            .iter()
            .map(|name| PythonImportEdge {
                source: source.to_string(),
                target: name.clone(),
                evidence: import.evidence.clone(),
            })
            .collect(),
        "from" => {
            let prefix = resolve_from_prefix(source, is_package, import);
            import
                .names
                .iter()
                .map(|name| {
                    let target = resolve_from_target(prefix.as_deref(), name, component_ids);
                    PythonImportEdge {
                        source: source.to_string(),
                        target,
                        evidence: import.evidence.clone(),
                    }
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

fn resolve_from_prefix(source: &str, is_package: bool, import: &PythonImport) -> Option<String> {
    let absolute_module = (!import.module.is_empty()).then(|| import.module.clone());
    if import.level == 0 {
        return absolute_module;
    }

    let mut package_parts: Vec<&str> = source.split('.').collect();
    if !is_package {
        package_parts.pop();
    }
    let ascents = import.level.saturating_sub(1);
    if ascents > package_parts.len() {
        return absolute_module;
    }
    package_parts.truncate(package_parts.len() - ascents);

    let mut parts: Vec<String> = package_parts.into_iter().map(str::to_string).collect();
    if let Some(module) = absolute_module {
        parts.extend(module.split('.').map(str::to_string));
    }
    (!parts.is_empty()).then(|| parts.join("."))
}

fn resolve_from_target(
    prefix: Option<&str>,
    imported_name: &str,
    component_ids: &BTreeSet<String>,
) -> String {
    if imported_name == "*" {
        return prefix.unwrap_or(imported_name).to_string();
    }

    let candidate = prefix
        .filter(|prefix| !prefix.is_empty())
        .map(|prefix| format!("{prefix}.{imported_name}"))
        .unwrap_or_else(|| imported_name.to_string());
    if component_ids.contains(&candidate) {
        return candidate;
    }
    if let Some(prefix) = prefix.filter(|prefix| component_ids.contains(*prefix)) {
        return prefix.to_string();
    }
    prefix.unwrap_or(&candidate).to_string()
}

fn dedup_edges(import_edges: Vec<PythonImportEdge>) -> Vec<Edge> {
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
    use std::path::Path;

    use crate::{PYTHON_COMPONENT_KIND, python_extractor::extract_python_sig0};

    #[test]
    fn extracts_python_import_graph_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/python_imports");
        let document = extract_python_sig0(&root, &[Path::new("src").to_path_buf()], &[])
            .expect("python fixture extracts");

        assert_eq!(document.component_kind, PYTHON_COMPONENT_KIND);
        assert!(document.components.iter().any(|c| c.id == "app"));
        assert!(document.components.iter().any(|c| c.id == "app.service"));
        assert!(document.components.iter().any(|c| c.id == "app.util"));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "app.service"
                && edge.target == "app.util"
                && edge.evidence == "from . import util"
        }));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "app.service"
                && edge.target == "requests"
                && edge.evidence == "import requests as http"
        }));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "app.util" && edge.target == "json" && edge.evidence == "import json"
        }));
        assert_eq!(
            document
                .metric_status
                .get("pythonDynamicImportCoverage")
                .expect("dynamic import status")
                .measured,
            false
        );
        assert_eq!(document.signature.has_cycle, 0);
    }
}
