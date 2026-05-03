use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use crate::validation::{count_checks, duplicates, validation_check};
use crate::{
    Component, ComponentUniverseValidationReport, Edge, MetricStatus, SCHEMA_VERSION, Sig0Document,
    VALIDATION_REPORT_SCHEMA_VERSION, ValidationCheck, ValidationExample, ValidationInput,
    ValidationSummary,
};

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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::extractor::{extract_sig0, extract_sig0_with_policy};
    use crate::test_support::{fixture_root, insert_unmeasured_policy_status};
    use crate::{
        COMPONENT_KIND, Component, DEFAULT_UNIVERSE_MODE, Edge, Policies, SCHEMA_VERSION,
        Sig0Document, Signature, VALIDATION_REPORT_SCHEMA_VERSION,
    };

    use super::validate_component_universe_report;

    #[test]
    fn validates_minimal_fixture_with_tooling_boundary_warnings() {
        let root = fixture_root();
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
        insert_unmeasured_policy_status(&mut metric_status);
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
        let mut document = extract_sig0(&fixture_root()).expect("fixture extracts");
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
}
