use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::{
    RELATION_COMPLEXITY_CANDIDATE_SCHEMA_VERSION, RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION,
    RELATION_COMPLEXITY_RULE_SET_VERSION, RelationComplexityCandidateFile,
    RelationComplexityComponents, RelationComplexityEvidence, RelationComplexityExcludedEvidence,
    RelationComplexityObservation,
};

pub fn extract_relation_complexity_observation_from_file(
    path: &Path,
) -> Result<RelationComplexityObservation, Box<dyn Error>> {
    let source = fs::read_to_string(path)?;
    let input: RelationComplexityCandidateFile = serde_json::from_str(&source)?;
    extract_relation_complexity_observation(input)
}

pub fn extract_relation_complexity_observation(
    mut input: RelationComplexityCandidateFile,
) -> Result<RelationComplexityObservation, Box<dyn Error>> {
    if input.schema_version != RELATION_COMPLEXITY_CANDIDATE_SCHEMA_VERSION {
        return Err(format!(
            "unsupported relation complexity candidate schemaVersion: {}",
            input.schema_version
        )
        .into());
    }

    input.measurement_universe.rule_set_version =
        Some(RELATION_COMPLEXITY_RULE_SET_VERSION.to_string());

    let mut excluded_evidence = input.excluded_evidence;
    let mut included_by_id: BTreeMap<String, RelationComplexityEvidence> = BTreeMap::new();
    let unsupported_frameworks =
        unsupported_relation_complexity_frameworks(&input.measurement_universe.frameworks);
    let framework_supported = input.measurement_universe.frameworks.is_empty()
        || input
            .measurement_universe
            .frameworks
            .iter()
            .any(|framework| relation_complexity_framework_supported(framework));
    let unsupported_reason = (!unsupported_frameworks.is_empty())
        .then(|| format!("unsupported-framework:{}", unsupported_frameworks.join(",")));

    let candidates = input
        .evidence
        .into_iter()
        .chain(input.evidence_candidates)
        .collect::<Vec<_>>();
    for mut candidate in candidates {
        validate_relation_complexity_candidate_shape(&candidate)?;

        if !framework_supported {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                unsupported_reason
                    .as_deref()
                    .expect("unsupported reason exists"),
            ));
            continue;
        }

        let ownership = candidate.ownership.as_str();
        if !matches!(ownership, "application-owned" | "application-configured") {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("ownership-not-counted:{ownership}"),
            ));
            continue;
        }

        if matches!(
            candidate.review_status.as_str(),
            "excluded" | "false-positive" | "rejected"
        ) {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("review-status-not-counted:{}", candidate.review_status),
            ));
            continue;
        }

        let mut unsupported_tags = Vec::new();
        candidate.tags = relation_complexity_tags(candidate.tags, &mut unsupported_tags);
        if !unsupported_tags.is_empty() {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("unsupported-tags:{}", unsupported_tags.join(",")),
            ));
        }
        if candidate.tags.is_empty() {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                "no-counted-relation-complexity-tags",
            ));
            continue;
        }

        included_by_id
            .entry(candidate.id.clone())
            .and_modify(|existing| {
                existing.tags = relation_complexity_tags(
                    existing
                        .tags
                        .iter()
                        .cloned()
                        .chain(candidate.tags.iter().cloned())
                        .collect(),
                    &mut Vec::new(),
                );
            })
            .or_insert(candidate);
    }

    let evidence: Vec<RelationComplexityEvidence> = included_by_id.into_values().collect();
    let counts = relation_complexity_counts(&evidence);
    let relation_complexity = counts.relation_complexity();

    Ok(RelationComplexityObservation {
        schema_version: RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        revision: input.revision,
        measurement_universe: input.measurement_universe,
        workflow: input.workflow,
        counts,
        relation_complexity,
        evidence,
        excluded_evidence,
    })
}

fn validate_relation_complexity_candidate_shape(
    candidate: &RelationComplexityEvidence,
) -> Result<(), String> {
    if candidate.id.is_empty() {
        return Err("relation complexity evidence id must not be empty".to_string());
    }
    if candidate.path.is_empty() {
        return Err(format!(
            "relation complexity evidence path must not be empty for {}",
            candidate.id
        ));
    }
    if candidate.ownership.is_empty() {
        return Err(format!(
            "relation complexity evidence ownership must not be empty for {}",
            candidate.id
        ));
    }
    if candidate.review_status.is_empty() {
        return Err(format!(
            "relation complexity evidence reviewStatus must not be empty for {}",
            candidate.id
        ));
    }
    Ok(())
}

fn relation_complexity_tags(tags: Vec<String>, unsupported_tags: &mut Vec<String>) -> Vec<String> {
    let mut supported = BTreeSet::new();
    let mut unsupported = BTreeSet::new();
    for tag in tags {
        if relation_complexity_tag_rank(&tag).is_some() {
            supported.insert(tag);
        } else {
            unsupported.insert(tag);
        }
    }
    unsupported_tags.extend(unsupported);

    let mut tags: Vec<String> = supported.into_iter().collect();
    tags.sort_by_key(|tag| relation_complexity_tag_rank(tag).expect("supported tag"));
    tags
}

fn relation_complexity_tag_rank(tag: &str) -> Option<usize> {
    match tag {
        "constraints" => Some(0),
        "compensations" => Some(1),
        "projections" => Some(2),
        "failureTransitions" => Some(3),
        "idempotencyRequirements" => Some(4),
        _ => None,
    }
}

fn relation_complexity_counts(
    evidence: &[RelationComplexityEvidence],
) -> RelationComplexityComponents {
    let mut counts = RelationComplexityComponents {
        constraints: 0,
        compensations: 0,
        projections: 0,
        failure_transitions: 0,
        idempotency_requirements: 0,
    };

    for item in evidence {
        let tags: BTreeSet<&str> = item.tags.iter().map(String::as_str).collect();
        for tag in tags {
            match tag {
                "constraints" => counts.constraints += 1,
                "compensations" => counts.compensations += 1,
                "projections" => counts.projections += 1,
                "failureTransitions" => counts.failure_transitions += 1,
                "idempotencyRequirements" => counts.idempotency_requirements += 1,
                _ => {}
            }
        }
    }

    counts
}

fn unsupported_relation_complexity_frameworks(frameworks: &[String]) -> Vec<String> {
    frameworks
        .iter()
        .filter(|framework| !relation_complexity_framework_supported(framework))
        .cloned()
        .collect()
}

fn relation_complexity_framework_supported(framework: &str) -> bool {
    matches!(
        framework,
        "generic-workflow" | "event-sourcing" | "saga" | "crud" | "lean-fixture"
    )
}

fn excluded_relation_complexity_evidence(
    evidence: &RelationComplexityEvidence,
    reason: &str,
) -> RelationComplexityExcludedEvidence {
    RelationComplexityExcludedEvidence {
        path: evidence.path.clone(),
        reason: reason.to_string(),
        symbol: evidence.symbol.clone(),
        line: evidence.line,
    }
}
