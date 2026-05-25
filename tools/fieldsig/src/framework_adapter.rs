use std::collections::BTreeSet;

use crate::schema_versioning::air_schema_compatibility_metadata;
use crate::{
    AirArtifact, AirClaim, AirCoverageLayer, AirDocumentV0, AirEvidence, AirRelation,
    FRAMEWORK_ADAPTER_EVIDENCE_SCHEMA_VERSION, FrameworkAdapterEvidenceV0, PYTHON_COMPONENT_KIND,
};

pub fn attach_framework_adapter_evidence(
    document: &mut AirDocumentV0,
    adapter: &FrameworkAdapterEvidenceV0,
    path: String,
    index: usize,
) -> Result<(), String> {
    validate_framework_adapter_evidence(document, adapter)?;

    let artifact_id = format!("artifact-framework-adapter-{:04}", index + 1);
    document.artifacts.push(AirArtifact {
        artifact_id: artifact_id.clone(),
        kind: "framework_adapter".to_string(),
        schema_version: Some(adapter.schema_version.clone()),
        path: Some(path),
        content_hash: None,
        produced_by: Some(adapter.adapter_id.clone()),
    });
    document.evidence.push(AirEvidence {
        evidence_id: format!("evidence-framework-adapter-{:04}-artifact", index + 1),
        kind: "observation_result".to_string(),
        artifact_ref: Some(artifact_id.clone()),
        path: None,
        symbol: None,
        line: None,
        rule_id: Some(adapter.projection_rule.clone()),
        confidence: Some("high".to_string()),
    });

    for (route_index, route) in adapter.routes.iter().enumerate() {
        let evidence_id = format!(
            "evidence-framework-adapter-{:04}-route-{:04}",
            index + 1,
            route_index + 1
        );
        document.evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "framework_route".to_string(),
            artifact_ref: Some(artifact_id.clone()),
            path: Some(route.evidence_location.path.clone()),
            symbol: route.evidence_location.symbol.clone(),
            line: route.evidence_location.line,
            rule_id: Some(format!(
                "{} {} {}",
                adapter.projection_rule, route.method, route.route_path
            )),
            confidence: Some(route.confidence.clone()),
        });
        document.relations.push(AirRelation {
            id: format!(
                "relation-framework-adapter-{:04}-route-{:04}",
                index + 1,
                route_index + 1
            ),
            layer: "framework".to_string(),
            from_component: Some(route.source.clone()),
            to_component: route.target.clone(),
            kind: route.relation_kind.clone(),
            lifecycle: "after".to_string(),
            protected_by: None,
            extraction_rule: Some(adapter.projection_rule.clone()),
            evidence_refs: vec![evidence_id],
        });
    }

    document.coverage.layers.push(AirCoverageLayer {
        layer: "framework".to_string(),
        measurement_boundary: if adapter.routes.is_empty() {
            "unmeasured".to_string()
        } else {
            "measuredNonzero".to_string()
        },
        universe_refs: vec![artifact_id],
        measured_axes: if adapter.routes.is_empty() {
            Vec::new()
        } else {
            vec!["frameworkRouteBinding".to_string()]
        },
        unmeasured_axes: if adapter.routes.is_empty() {
            vec!["frameworkRouteBinding".to_string()]
        } else {
            Vec::new()
        },
        projection_rule: Some(adapter.projection_rule.clone()),
        extraction_scope: vec![format!(
            "{} framework adapter over {} components",
            adapter.framework, adapter.component_id_kind
        )],
        exactness_assumptions: adapter.exactness_assumptions.clone(),
        unsupported_constructs: adapter
            .unsupported_constructs
            .iter()
            .map(|construct| {
                let location = construct
                    .line
                    .map(|line| format!("{}:{line}", construct.path))
                    .unwrap_or_else(|| construct.path.clone());
                format!("{} at {}: {}", construct.kind, location, construct.reason)
            })
            .collect(),
    });

    document.claims.push(AirClaim {
        claim_id: format!("claim-framework-adapter-{:04}", index + 1),
        subject_ref: format!("framework.{}.routes", adapter.framework),
        predicate: "framework adapter route bindings are measured inside the fixture boundary"
            .to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: if adapter.routes.is_empty() {
            "unmeasured".to_string()
        } else {
            "measured".to_string()
        },
        measurement_boundary: if adapter.routes.is_empty() {
            "unmeasured".to_string()
        } else {
            "measuredNonzero".to_string()
        },
        theorem_refs: Vec::new(),
        evidence_refs: document
            .evidence
            .iter()
            .filter(|evidence| {
                evidence.evidence_id.starts_with(&format!(
                    "evidence-framework-adapter-{:04}-route-",
                    index + 1
                ))
            })
            .map(|evidence| evidence.evidence_id.clone())
            .collect(),
        required_assumptions: Vec::new(),
        coverage_assumptions: adapter.coverage_assumptions.clone(),
        exactness_assumptions: adapter.exactness_assumptions.clone(),
        missing_preconditions: Vec::new(),
        non_conclusions: adapter.non_conclusions.clone(),
    });
    document.schema_compatibility = Some(air_schema_compatibility_metadata(
        &document.coverage,
        &document.claims,
    ));

    Ok(())
}

fn validate_framework_adapter_evidence(
    document: &AirDocumentV0,
    adapter: &FrameworkAdapterEvidenceV0,
) -> Result<(), String> {
    if adapter.schema_version != FRAMEWORK_ADAPTER_EVIDENCE_SCHEMA_VERSION {
        return Err(format!(
            "unsupported framework adapter evidence schemaVersion: {}",
            adapter.schema_version
        ));
    }
    if adapter.adapter_id.is_empty() {
        return Err("framework adapter id must not be empty".to_string());
    }
    if adapter.framework.is_empty() {
        return Err("framework adapter framework must not be empty".to_string());
    }
    if adapter.source_language != "python" {
        return Err(format!(
            "unsupported framework adapter sourceLanguage: {}",
            adapter.source_language
        ));
    }
    if adapter.component_id_kind != PYTHON_COMPONENT_KIND {
        return Err(format!(
            "unsupported framework adapter componentIdKind: {}",
            adapter.component_id_kind
        ));
    }
    if adapter.projection_rule.is_empty() {
        return Err("framework adapter projectionRule must not be empty".to_string());
    }
    if adapter.coverage_assumptions.is_empty() {
        return Err("framework adapter coverageAssumptions must not be empty".to_string());
    }
    if adapter.exactness_assumptions.is_empty() {
        return Err("framework adapter exactnessAssumptions must not be empty".to_string());
    }
    if adapter.non_conclusions.is_empty() {
        return Err("framework adapter nonConclusions must not be empty".to_string());
    }

    let component_ids: BTreeSet<&str> = document
        .components
        .iter()
        .map(|component| component.id.as_str())
        .collect();
    for route in &adapter.routes {
        if route.route_id.is_empty() {
            return Err("framework route routeId must not be empty".to_string());
        }
        if route.source.is_empty() || !component_ids.contains(route.source.as_str()) {
            return Err(format!(
                "framework route source is outside component universe: {}",
                route.source
            ));
        }
        if let Some(target) = &route.target {
            if !component_ids.contains(target.as_str()) {
                return Err(format!(
                    "framework route target is outside component universe: {target}"
                ));
            }
        }
        if route.method.is_empty() {
            return Err("framework route method must not be empty".to_string());
        }
        if route.route_path.is_empty() {
            return Err("framework route path must not be empty".to_string());
        }
        if route.relation_kind.is_empty() {
            return Err("framework route relationKind must not be empty".to_string());
        }
        if route.confidence.is_empty() {
            return Err("framework route confidence must not be empty".to_string());
        }
        if route.evidence_location.path.is_empty() {
            return Err("framework route evidenceLocation.path must not be empty".to_string());
        }
    }

    Ok(())
}
