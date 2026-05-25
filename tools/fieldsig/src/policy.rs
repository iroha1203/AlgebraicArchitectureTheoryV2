use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use serde::Deserialize;

use crate::{COMPONENT_KIND, Component, Edge, PolicyViolation};

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct PolicyFile {
    pub(crate) schema_version: String,
    pub(crate) policy_id: String,
    component_id_kind: String,
    selector_semantics: String,
    pub(crate) boundary: Option<BoundaryPolicy>,
    pub(crate) abstraction: Option<AbstractionPolicy>,
}

impl PolicyFile {
    pub(crate) fn read(path: &Path) -> Result<Self, Box<dyn Error>> {
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
pub(crate) struct BoundaryPolicy {
    pub(crate) groups: Vec<BoundaryGroup>,
    allowed_dependencies: Vec<AllowedDependency>,
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub(crate) struct BoundaryGroup {
    pub(crate) id: String,
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
pub(crate) struct AbstractionPolicy {
    pub(crate) relations: Vec<AbstractionRelation>,
    #[allow(dead_code)]
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct AbstractionRelation {
    id: String,
    abstraction: String,
    clients: Vec<String>,
    implementations: Vec<String>,
    #[serde(default)]
    allowed_direct_implementation_dependencies: Vec<String>,
}

pub(crate) fn measure_boundary(
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

pub(crate) fn measure_abstraction(
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
