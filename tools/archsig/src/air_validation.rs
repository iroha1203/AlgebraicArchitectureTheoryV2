use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AIR_SCHEMA_VERSION, AIR_VALIDATION_REPORT_SCHEMA_VERSION, AirDocumentV0, AirValidationInput,
    AirValidationReport, AirValidationSummary, ValidationCheck, ValidationExample,
};

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
