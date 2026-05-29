use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ArchMapAtomicObservationSummary, ArchMapDocumentV0,
    ArchMapLeanPreservationChecklistEntry, ArchMapLeanPreservationVocabularyEntry,
    ArchMapSourceInventoryV0, ArchMapSourceRef, ArchMapValidationReportV0,
    ArchMapValidationSummary, ValidationCheck,
};

pub struct ArchMapSourceInventoryInput<'a> {
    pub path: &'a str,
    pub document: Option<&'a ArchMapSourceInventoryV0>,
    pub read_error: Option<String>,
}

pub fn validate_archmap_report(
    document: &ArchMapDocumentV0,
    input_path: &str,
    source_inventory: Option<ArchMapSourceInventoryInput<'_>>,
) -> ArchMapValidationReportV0 {
    let source_inventory_checks = vec![
        check_archmap_schema_version(&document.schema_version),
        check_source_inventory_boundary(document),
        check_source_inventory_artifact(document, source_inventory.as_ref()),
    ];
    let source_ref_checks = vec![
        check_source_refs(document),
        check_unique_observation_ids(document),
        check_projection_refs(document),
    ];
    let claim_boundary_checks = vec![
        check_measured_claim_evidence(document),
        check_missing_evidence_not_measured_zero(document),
        check_observation_status_boundary(document),
    ];
    let semantic_coverage_checks = vec![check_semantic_coverage(document)];
    let formal_promotion_guardrail_checks = vec![
        check_formal_promotion_guardrail(document),
        check_projection_separation(document),
    ];
    let atomic_observation_checks = vec![
        check_atom_observations(document),
        check_molecule_observations(document),
        check_semantic_observations(document),
        check_observation_gaps(document),
        check_concern_hints(document),
    ];
    let atomic_observation_summary = archmap_atomic_observation_summary(document);
    let responsibility_checks = vec![check_archmap_required_non_conclusions(document)];

    let all_checks = source_inventory_checks
        .iter()
        .chain(source_ref_checks.iter())
        .chain(claim_boundary_checks.iter())
        .chain(semantic_coverage_checks.iter())
        .chain(formal_promotion_guardrail_checks.iter())
        .chain(atomic_observation_checks.iter())
        .chain(responsibility_checks.iter())
        .cloned()
        .collect::<Vec<_>>();

    let failed_check_count = count_checks(&all_checks, "fail");
    let warning_check_count = count_checks(&all_checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    ArchMapValidationReportV0 {
        schema_version: ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        archmap_ref: input_path.to_string(),
        lean_preservation_vocabulary: archmap_lean_preservation_vocabulary(),
        lean_preservation_precondition_checklist: archmap_lean_preservation_checklist(document),
        source_inventory_checks,
        source_ref_checks,
        claim_boundary_checks,
        semantic_coverage_checks,
        formal_promotion_guardrail_checks,
        atomic_observation_checks,
        atomic_observation_summary,
        responsibility_checks,
        summary: ArchMapValidationSummary {
            result: result.to_string(),
            atom_observation_count: document.atom_observations.len(),
            molecule_observation_count: document.molecule_observations.len(),
            semantic_observation_count: document.semantic_observations.len(),
            observation_gap_count: document.observation_gaps.len(),
            failed_check_count,
            warning_check_count,
        },
        non_conclusions: archmap_non_conclusions(document),
    }
}

fn check_archmap_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-schema-version",
        "ArchMap uses the current Atom observation schema",
        if schema_version == ARCHMAP_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if schema_version != ARCHMAP_SCHEMA_VERSION {
        check.reason = Some(format!(
            "expected {ARCHMAP_SCHEMA_VERSION}, found {schema_version}"
        ));
    }
    check
}

fn check_source_inventory_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-source-inventory-boundary",
        "ArchMap declares bounded source inventory and observation scope",
        "pass",
    );
    let mut examples = Vec::new();
    if document.source_universe.included_refs.is_empty() {
        examples.push(generic_validation_example(
            "sourceUniverse.includedRefs",
            "empty",
            "source-grounded ArchMap needs at least one included source ref",
        ));
    }
    if document
        .source_universe
        .selection_boundary
        .trim()
        .is_empty()
    {
        examples.push(generic_validation_example(
            "sourceUniverse.selectionBoundary",
            "empty",
            "source selection boundary must be explicit",
        ));
    }
    if document.provenance.observation_boundary.trim().is_empty() {
        examples.push(generic_validation_example(
            "provenance.observationBoundary",
            "empty",
            "observation boundary must be explicit",
        ));
    }
    if !examples.is_empty() {
        check.result = "fail".to_string();
        check.examples = examples;
    }
    check
}

fn check_source_inventory_artifact(
    document: &ArchMapDocumentV0,
    source_inventory: Option<&ArchMapSourceInventoryInput<'_>>,
) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-source-inventory-artifact",
        "Optional source inventory sidecar is readable and matches the current schema",
        "pass",
    );
    let Some(input) = source_inventory else {
        check.reason =
            Some("no sourceInventoryRef supplied; sourceUniverse is used directly".to_string());
        return check;
    };
    if let Some(error) = &input.read_error {
        check.result = "fail".to_string();
        check.reason = Some(error.clone());
        check.examples = vec![generic_validation_example(
            "sourceInventoryRef.path",
            input.path,
            "source inventory sidecar could not be loaded",
        )];
        return check;
    }
    let Some(inventory) = input.document else {
        check.result = "fail".to_string();
        check.reason = Some("source inventory sidecar was requested but not available".to_string());
        return check;
    };
    if inventory.schema_version != ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION {
        check.result = "fail".to_string();
        check.examples.push(generic_validation_example(
            "sourceInventory.schemaVersion",
            &inventory.schema_version,
            "source inventory must use the current schema",
        ));
    }
    if inventory.root != document.source_universe.root {
        check.result = "warn".to_string();
        check.examples.push(generic_validation_example(
            "sourceInventory.root",
            &inventory.root,
            "source inventory root differs from ArchMap sourceUniverse.root",
        ));
    }
    check
}

fn check_source_refs(document: &ArchMapDocumentV0) -> ValidationCheck {
    let declared = declared_source_ref_ids(document);
    let mut examples = Vec::new();
    for (owner, refs) in observation_source_refs(document) {
        for source_ref in refs {
            if let Some(artifact_id) = &source_ref.artifact_id {
                if !declared.contains(artifact_id.as_str()) {
                    examples.push(generic_validation_example(
                        &owner,
                        artifact_id,
                        "observation references a source artifact outside sourceUniverse.includedRefs",
                    ));
                }
            }
        }
    }
    let mut check = validation_check(
        "archmap-source-refs-declared",
        "Observation source refs are declared in the source universe",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(examples.len());
    check.examples = examples;
    check
}

fn check_unique_observation_ids(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut ids = Vec::new();
    ids.extend(
        document
            .atom_observations
            .iter()
            .map(|observation| observation.atom_observation_id.as_str()),
    );
    ids.extend(
        document
            .molecule_observations
            .iter()
            .map(|observation| observation.molecule_observation_id.as_str()),
    );
    ids.extend(
        document
            .semantic_observations
            .iter()
            .map(|observation| observation.semantic_observation_id.as_str()),
    );
    ids.extend(
        document
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.as_str()),
    );
    ids.extend(
        document
            .concern_hints
            .iter()
            .map(|hint| hint.concern_hint_id.as_str()),
    );
    let duplicate_ids = duplicates(ids.into_iter());
    let mut check = validation_check(
        "archmap-observation-ids-unique",
        "Atom observation surface ids are unique",
        if duplicate_ids.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    check.examples = duplicate_ids
        .iter()
        .map(|id| generic_validation_example("observation id", id, "duplicate id"))
        .collect();
    check.count = Some(check.examples.len());
    check
}

fn check_projection_refs(document: &ArchMapDocumentV0) -> ValidationCheck {
    let projection_ids = document
        .projection_info
        .iter()
        .map(|projection| projection.projection_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for observation in &document.atom_observations {
        for projection_ref in &observation.projection_refs {
            if !projection_ids.contains(projection_ref.as_str()) {
                examples.push(generic_validation_example(
                    &observation.atom_observation_id,
                    projection_ref,
                    "atom observation references missing projectionInfo entry",
                ));
            }
        }
    }
    let mut check = validation_check(
        "archmap-projection-refs-declared",
        "Atom observation projection refs are declared in projectionInfo",
        if examples.is_empty() { "pass" } else { "warn" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_measured_claim_evidence(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for observation in &document.atom_observations {
        if observation.observation_status == "observed" && observation.source_refs.is_empty() {
            examples.push(generic_validation_example(
                &observation.atom_observation_id,
                "sourceRefs",
                "observed atom must carry source evidence",
            ));
        }
        if observation.evidence_boundary.trim().is_empty() {
            examples.push(generic_validation_example(
                &observation.atom_observation_id,
                "evidenceBoundary",
                "atom observation must keep evidence boundary explicit",
            ));
        }
    }
    for observation in &document.molecule_observations {
        if observation.observation_status == "observed"
            && observation.atom_observation_refs.is_empty()
        {
            examples.push(generic_validation_example(
                &observation.molecule_observation_id,
                "atomObservationRefs",
                "observed molecule must reference atom observations",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-measured-claims-have-evidence",
        "Observed ArchMap claims carry source or atom evidence",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_missing_evidence_not_measured_zero(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for gap in &document.observation_gaps {
        let joined = [
            gap.evidence_status.as_str(),
            gap.reason.as_str(),
            &gap.non_conclusions.join(" "),
        ]
        .join(" ")
        .to_ascii_lowercase();
        if gap.evidence_status == "measuredZero"
            || (joined.contains("measured zero") && !joined.contains("not measured zero"))
            || joined.contains("zero evidence")
            || joined.contains("no issue")
        {
            examples.push(generic_validation_example(
                &gap.gap_id,
                &gap.evidence_status,
                "missing evidence must remain an observation gap, not a measured-zero claim",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-observation-gaps-not-measured-zero",
        "Observation gaps are preserved separately from measured zero",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_observation_status_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for observation in &document.atom_observations {
        if is_promoted_truth_status(&observation.observation_status) {
            examples.push(generic_validation_example(
                &observation.atom_observation_id,
                &observation.observation_status,
                "Atom observations must not be promoted to formal truth",
            ));
        }
    }
    for observation in &document.semantic_observations {
        if is_promoted_truth_status(&observation.observation_status) {
            examples.push(generic_validation_example(
                &observation.semantic_observation_id,
                &observation.observation_status,
                "Semantic observations must not be promoted to formal truth",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-observation-status-boundary",
        "Observation statuses remain observational and bounded",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_semantic_coverage(document: &ArchMapDocumentV0) -> ValidationCheck {
    let atom_ids = atom_ids(document);
    let molecule_ids = molecule_ids(document);
    let mut examples = Vec::new();
    for observation in &document.semantic_observations {
        for atom_ref in &observation.atom_observation_refs {
            if !atom_ids.contains(atom_ref.as_str()) {
                examples.push(generic_validation_example(
                    &observation.semantic_observation_id,
                    atom_ref,
                    "semantic observation references missing atom observation",
                ));
            }
        }
        for molecule_ref in &observation.molecule_observation_refs {
            if !molecule_ids.contains(molecule_ref.as_str()) {
                examples.push(generic_validation_example(
                    &observation.semantic_observation_id,
                    molecule_ref,
                    "semantic observation references missing molecule observation",
                ));
            }
        }
    }
    let mut check = validation_check(
        "archmap-semantic-coverage",
        "Semantic observations reference declared atom or molecule observations",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_formal_promotion_guardrail(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for value in archmap_non_conclusions(document) {
        let lower = value.to_ascii_lowercase();
        if lower.contains("lean proof complete")
            || lower.contains("formal truth")
            || lower.contains("certified atom truth")
        {
            examples.push(generic_validation_example(
                "nonConclusions",
                &value,
                "ArchMap must not promote observations to formal proof",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-formal-promotion-guardrail",
        "ArchMap does not promote observations to Lean theorem evidence",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_projection_separation(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for projection in &document.projection_info {
        let reading = projection.reading.to_ascii_lowercase();
        if reading.contains("lawful")
            || reading.contains("zero curvature")
            || reading.contains("obstruction circuit")
        {
            examples.push(generic_validation_example(
                &projection.projection_id,
                &projection.reading,
                "projectionInfo must not construct law-relative ArchSig conclusions",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-projection-separation",
        "Projection info remains observation-derived and law-independent",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.examples = examples;
    check.count = Some(check.examples.len());
    check
}

fn check_atom_observations(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for observation in &document.atom_observations {
        if observation.atom_family.trim().is_empty()
            || observation.predicate.trim().is_empty()
            || observation.subject_ref.trim().is_empty()
            || observation.evidence_boundary.trim().is_empty()
        {
            examples.push(generic_validation_example(
                &observation.atom_observation_id,
                "atom observation fields",
                "atom observation requires family, predicate, subject, and evidence boundary",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-atom-observation-surface",
        "Atom observations use explicit source-grounded fields",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(document.atom_observations.len());
    check.examples = examples;
    check
}

fn check_molecule_observations(document: &ArchMapDocumentV0) -> ValidationCheck {
    let atom_ids = atom_ids(document);
    let mut examples = Vec::new();
    for observation in &document.molecule_observations {
        for atom_ref in &observation.atom_observation_refs {
            if !atom_ids.contains(atom_ref.as_str()) {
                examples.push(generic_validation_example(
                    &observation.molecule_observation_id,
                    atom_ref,
                    "molecule observation references missing atom observation",
                ));
            }
        }
    }
    let mut check = validation_check(
        "archmap-molecule-observation-surface",
        "Molecule observations are assembled from declared atom observations",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(document.molecule_observations.len());
    check.examples = examples;
    check
}

fn check_semantic_observations(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for observation in &document.semantic_observations {
        if observation.semantic_family.trim().is_empty()
            || observation.subject_ref.trim().is_empty()
            || observation.predicate.trim().is_empty()
            || observation.evidence_boundary.trim().is_empty()
        {
            examples.push(generic_validation_example(
                &observation.semantic_observation_id,
                "semantic observation fields",
                "semantic observation requires family, subject, predicate, and evidence boundary",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-semantic-observation-surface",
        "Semantic observations stay source-grounded and law-independent",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(document.semantic_observations.len());
    check.examples = examples;
    check
}

fn check_observation_gaps(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for gap in &document.observation_gaps {
        if gap.evidence_status.trim().is_empty() || gap.reason.trim().is_empty() {
            examples.push(generic_validation_example(
                &gap.gap_id,
                "observation gap fields",
                "observation gap requires evidence status and reason",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-observation-gap-surface",
        "Observation gaps explicitly preserve unavailable evidence",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(document.observation_gaps.len());
    check.examples = examples;
    check
}

fn check_concern_hints(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    for hint in &document.concern_hints {
        let combined = [
            hint.concern_family.as_str(),
            hint.analysis_boundary.as_str(),
            &hint.non_conclusions.join(" "),
        ]
        .join(" ")
        .to_ascii_lowercase();
        let analysis_boundary = hint.analysis_boundary.to_ascii_lowercase();
        if analysis_boundary.contains("promoted")
            || analysis_boundary.contains("candidate")
            || (combined.contains("obstruction circuit")
                && !combined.contains("not obstruction")
                && !combined.contains("not an obstruction"))
        {
            examples.push(generic_validation_example(
                &hint.concern_hint_id,
                &hint.concern_family,
                "concernHints are review cues and must not be promoted to obstruction circuits",
            ));
        }
    }
    let mut check = validation_check(
        "archmap-concern-hints-are-not-obstruction-circuits",
        "Concern hints remain review cues until ArchSig applies a LawPolicy",
        if examples.is_empty() { "pass" } else { "fail" },
    );
    check.count = Some(document.concern_hints.len());
    check.examples = examples;
    check
}

fn check_archmap_required_non_conclusions(document: &ArchMapDocumentV0) -> ValidationCheck {
    let required = [
        "ArchMap is not a Lean theorem proof",
        "ArchMap does not construct obstruction circuits",
        "ArchMap does not prove zero curvature",
        "ArchMap does not prove source completeness",
    ];
    let present = archmap_non_conclusions(document)
        .into_iter()
        .map(|value| value.to_ascii_lowercase())
        .collect::<Vec<_>>();
    let missing = required
        .iter()
        .filter(|required| {
            let required = required.to_ascii_lowercase();
            !present.iter().any(|value| value.contains(&required))
        })
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "archmap-required-non-conclusions",
        "ArchMap carries non-conclusions for proof, lawfulness, zero, and completeness",
        if missing.is_empty() { "pass" } else { "fail" },
    );
    check.examples = missing
        .iter()
        .map(|value| {
            generic_validation_example("nonConclusions", value, "required boundary missing")
        })
        .collect();
    check.count = Some(check.examples.len());
    check
}

fn archmap_atomic_observation_summary(
    document: &ArchMapDocumentV0,
) -> ArchMapAtomicObservationSummary {
    let observed_atom_count = document
        .atom_observations
        .iter()
        .filter(|observation| observation.observation_status == "observed")
        .count();
    let observed_molecule_count = document
        .molecule_observations
        .iter()
        .filter(|observation| observation.observation_status == "observed")
        .count();
    let promotable_atom_observation_count = document
        .atom_observations
        .iter()
        .filter(|observation| {
            observation.observation_status == "observed"
                && !observation.source_refs.is_empty()
                && !observation.evidence_boundary.trim().is_empty()
        })
        .count();
    let rejected_or_uncertain_observation_count = document
        .atom_observations
        .iter()
        .filter(|observation| {
            observation.observation_status != "observed" || !observation.uncertainty.is_empty()
        })
        .count()
        + document.observation_gaps.len();
    let lean_presentation_candidate_count = document
        .atom_observations
        .iter()
        .filter(|observation| observation.atom_family == "existence")
        .count();
    let sft_handoff_ref_count = document
        .source_universe
        .included_refs
        .iter()
        .filter(|source_ref| {
            source_ref.kind.contains("runtime")
                || source_ref.kind.contains("test")
                || source_ref.kind.contains("doc")
        })
        .count()
        + document.observation_gaps.len();

    ArchMapAtomicObservationSummary {
        atom_observation_count: document.atom_observations.len(),
        observed_atom_count,
        promotable_atom_observation_count,
        rejected_or_uncertain_observation_count,
        molecule_observation_count: document.molecule_observations.len(),
        observed_molecule_count,
        semantic_observation_count: document.semantic_observations.len(),
        concern_hint_count: document.concern_hints.len(),
        observation_gap_count: document.observation_gaps.len(),
        lean_presentation_candidate_count,
        sft_handoff_ref_count,
        zero_curvature_reading: if document.observation_gaps.is_empty() {
            "not computed; no observed gaps in this ArchMap".to_string()
        } else {
            "not computed; observation gaps block zero-curvature reflection".to_string()
        },
        promotion_boundary:
            "source-grounded Atom observations may guide Lean presentation, but are not proof"
                .to_string(),
        boundary: "summary counts current Atom observation fields only".to_string(),
        non_conclusions: archmap_non_conclusions(document),
    }
}

fn archmap_lean_preservation_vocabulary() -> Vec<ArchMapLeanPreservationVocabularyEntry> {
    vec![
        ArchMapLeanPreservationVocabularyEntry {
            vocabulary_id: "atomObservations".to_string(),
            archmap_selector: "atomObservations[]".to_string(),
            lean_package_field: "candidate Atom predicate evidence".to_string(),
            preservation_role: "source-grounded observation; not theorem evidence".to_string(),
            report_boundary:
                "Lean preservation requires separate formalization and proof obligations"
                    .to_string(),
        },
        ArchMapLeanPreservationVocabularyEntry {
            vocabulary_id: "moleculeObservations".to_string(),
            archmap_selector: "moleculeObservations[]".to_string(),
            lean_package_field: "candidate molecule presentation".to_string(),
            preservation_role: "observed grouping over atom observations".to_string(),
            report_boundary: "molecule observation is not minimality proof".to_string(),
        },
        ArchMapLeanPreservationVocabularyEntry {
            vocabulary_id: "observationGaps".to_string(),
            archmap_selector: "observationGaps[]".to_string(),
            lean_package_field: "coverage boundary".to_string(),
            preservation_role: "blocks measured-zero and proof promotion".to_string(),
            report_boundary: "gap is preserved as unavailable evidence".to_string(),
        },
    ]
}

fn archmap_lean_preservation_checklist(
    document: &ArchMapDocumentV0,
) -> Vec<ArchMapLeanPreservationChecklistEntry> {
    let mut entries = Vec::new();
    entries.push(ArchMapLeanPreservationChecklistEntry {
        checklist_id: "atom-observation-source-evidence".to_string(),
        lean_package_field: "Atom predicate candidate".to_string(),
        status: if document
            .atom_observations
            .iter()
            .all(|observation| !observation.source_refs.is_empty())
        {
            "ready-for-human-review"
        } else {
            "blocked"
        }
        .to_string(),
        candidate_sources: document
            .atom_observations
            .iter()
            .map(|observation| observation.atom_observation_id.clone())
            .collect(),
        blocking_reasons: document
            .atom_observations
            .iter()
            .filter(|observation| observation.source_refs.is_empty())
            .map(|observation| format!("{} has no sourceRefs", observation.atom_observation_id))
            .collect(),
        missing_evidence: document
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.clone())
            .collect(),
        coverage_boundary: "only observed source-backed atoms are candidates".to_string(),
        non_conclusions: archmap_non_conclusions(document),
    });
    entries.push(ArchMapLeanPreservationChecklistEntry {
        checklist_id: "observation-gap-boundary".to_string(),
        lean_package_field: "coverage assumption".to_string(),
        status: if document.observation_gaps.is_empty() {
            "no-gap-declared"
        } else {
            "gap-preserved"
        }
        .to_string(),
        candidate_sources: document
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.clone())
            .collect(),
        blocking_reasons: document
            .observation_gaps
            .iter()
            .map(|gap| format!("{}: {}", gap.gap_id, gap.reason))
            .collect(),
        missing_evidence: document
            .observation_gaps
            .iter()
            .map(|gap| gap.gap_id.clone())
            .collect(),
        coverage_boundary: "missing evidence is not measured zero".to_string(),
        non_conclusions: archmap_non_conclusions(document),
    });
    entries
}

fn archmap_non_conclusions(document: &ArchMapDocumentV0) -> Vec<String> {
    let mut values = vec![
        "ArchMap is not a Lean theorem proof".to_string(),
        "ArchMap does not construct obstruction circuits".to_string(),
        "ArchMap does not prove zero curvature".to_string(),
        "ArchMap does not prove source completeness".to_string(),
    ];
    values.extend(document.non_conclusions.clone());
    values.extend(document.provenance.non_conclusions.clone());
    values.extend(document.provenance.excluded_readings.clone());
    for observation in &document.atom_observations {
        values.extend(observation.non_conclusions.clone());
    }
    for observation in &document.molecule_observations {
        values.extend(observation.non_conclusions.clone());
    }
    for observation in &document.semantic_observations {
        values.extend(observation.non_conclusions.clone());
    }
    for gap in &document.observation_gaps {
        values.extend(gap.non_conclusions.clone());
    }
    for hint in &document.concern_hints {
        values.extend(hint.non_conclusions.clone());
    }
    let mut seen = BTreeSet::new();
    values
        .into_iter()
        .filter(|value| seen.insert(value.clone()))
        .collect()
}

fn declared_source_ref_ids(document: &ArchMapDocumentV0) -> BTreeSet<&str> {
    document
        .source_universe
        .included_refs
        .iter()
        .filter_map(|source_ref| source_ref.artifact_id.as_deref())
        .collect()
}

fn observation_source_refs(document: &ArchMapDocumentV0) -> Vec<(String, &[ArchMapSourceRef])> {
    let mut refs = Vec::new();
    for observation in &document.atom_observations {
        refs.push((
            format!(
                "atomObservations[{}].sourceRefs",
                observation.atom_observation_id
            ),
            observation.source_refs.as_slice(),
        ));
    }
    for observation in &document.molecule_observations {
        refs.push((
            format!(
                "moleculeObservations[{}].sourceRefs",
                observation.molecule_observation_id
            ),
            observation.source_refs.as_slice(),
        ));
    }
    for observation in &document.semantic_observations {
        refs.push((
            format!(
                "semanticObservations[{}].sourceRefs",
                observation.semantic_observation_id
            ),
            observation.source_refs.as_slice(),
        ));
    }
    for gap in &document.observation_gaps {
        refs.push((
            format!("observationGaps[{}].sourceRefs", gap.gap_id),
            gap.source_refs.as_slice(),
        ));
    }
    for hint in &document.concern_hints {
        refs.push((
            format!("concernHints[{}].sourceRefs", hint.concern_hint_id),
            hint.source_refs.as_slice(),
        ));
    }
    refs
}

fn atom_ids(document: &ArchMapDocumentV0) -> BTreeSet<&str> {
    document
        .atom_observations
        .iter()
        .map(|observation| observation.atom_observation_id.as_str())
        .collect()
}

fn molecule_ids(document: &ArchMapDocumentV0) -> BTreeSet<&str> {
    document
        .molecule_observations
        .iter()
        .map(|observation| observation.molecule_observation_id.as_str())
        .collect()
}

fn is_promoted_truth_status(status: &str) -> bool {
    matches!(
        status,
        "proved" | "certified" | "theorem" | "lawful" | "zeroCurvature"
    )
}
