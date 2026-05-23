use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AIR_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, AirArchitecturePath, AirArtifact, AirClaim,
    AirComponent, AirCoverage, AirCoverageLayer, AirDocumentV0, AirEvidence, AirExtension,
    AirFeature, AirIdPolicies, AirNonfillabilityWitness, AirOperationTrace, AirPolicies,
    AirRelation, AirRevision, AirSemanticDiagram, AirSignature, ArchMapConflict, ArchMapDocumentV0,
    ArchMapLeanPreservationChecklistEntry, ArchMapLeanPreservationVocabularyEntry, ArchMapMapItem,
    ArchMapSourceInventoryV0, ArchMapSourceRef, ArchMapValidationReportV0,
    ArchMapValidationSummary, Sig0Document, ValidationCheck,
};

pub struct ArchMapSourceInventoryInput<'a> {
    pub path: &'a str,
    pub document: Option<&'a ArchMapSourceInventoryV0>,
    pub read_error: Option<String>,
}

pub fn validate_archmap_report(
    document: &ArchMapDocumentV0,
    input_path: &str,
    sig0: Option<&Sig0Document>,
    source_inventory: Option<ArchMapSourceInventoryInput<'_>>,
) -> ArchMapValidationReportV0 {
    let source_inventory_checks = vec![
        check_archmap_schema_version(&document.schema_version),
        check_source_inventory_boundary(document),
        check_source_inventory_artifact(document, source_inventory.as_ref()),
    ];
    let mut source_ref_checks = vec![check_archmap_unique_map_item_ids(document)];
    source_ref_checks.push(check_source_refs(document));
    let claim_boundary_checks = vec![
        check_measured_claim_evidence(document),
        check_missing_evidence_not_measured_zero(document),
    ];
    let semantic_coverage_checks = vec![check_semantic_coverage(document)];
    let conflict_checks = vec![check_conflicts(document, sig0)];
    let formal_promotion_guardrail_checks = vec![check_formal_promotion_guardrail(document)];

    let mut all_checks = Vec::new();
    all_checks.append(&mut source_inventory_checks.clone());
    all_checks.extend(source_ref_checks.clone());
    all_checks.extend(claim_boundary_checks.clone());
    all_checks.extend(semantic_coverage_checks.clone());
    all_checks.extend(conflict_checks.clone());
    all_checks.extend(formal_promotion_guardrail_checks.clone());

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
        conflict_checks,
        formal_promotion_guardrail_checks,
        summary: ArchMapValidationSummary {
            result: result.to_string(),
            map_item_count: document.map_items.len(),
            conflict_count: explicit_and_derived_conflicts(document, sig0).len(),
            failed_check_count,
            warning_check_count,
        },
        non_conclusions: archmap_non_conclusions(document),
    }
}

pub fn build_air_from_archmap(
    document: &ArchMapDocumentV0,
    input_path: &str,
    sig0: Option<&Sig0Document>,
) -> AirDocumentV0 {
    let conflicts = explicit_and_derived_conflicts(document, sig0);
    let artifact_id = "artifact-archmap".to_string();
    let mut artifacts = vec![AirArtifact {
        artifact_id: artifact_id.clone(),
        kind: "archmap".to_string(),
        schema_version: Some(document.schema_version.clone()),
        path: Some(input_path.to_string()),
        content_hash: None,
        produced_by: document.generator.tool.clone(),
    }];
    if let Some(source_inventory_ref) = &document.source_inventory_ref {
        artifacts.push(AirArtifact {
            artifact_id: source_inventory_ref.artifact_id.clone(),
            kind: source_inventory_ref
                .kind
                .clone()
                .unwrap_or_else(|| "source_inventory".to_string()),
            schema_version: None,
            path: source_inventory_ref.path.clone(),
            content_hash: source_inventory_ref.content_hash.clone(),
            produced_by: document.generator.tool.clone(),
        });
    }

    let mut evidence = vec![AirEvidence {
        evidence_id: "evidence-archmap-artifact".to_string(),
        kind: "manual_annotation".to_string(),
        artifact_ref: Some(artifact_id.clone()),
        path: Some(input_path.to_string()),
        symbol: None,
        line: None,
        rule_id: Some(document.schema_version.clone()),
        confidence: Some("medium".to_string()),
    }];
    if let Some(source_inventory_ref) = &document.source_inventory_ref {
        evidence.push(AirEvidence {
            evidence_id: "evidence-archmap-source-inventory".to_string(),
            kind: "manual_annotation".to_string(),
            artifact_ref: Some(source_inventory_ref.artifact_id.clone()),
            path: source_inventory_ref.path.clone(),
            symbol: None,
            line: None,
            rule_id: Some(document.schema_version.clone()),
            confidence: Some("medium".to_string()),
        });
    }
    let mut source_evidence_ids = BTreeMap::new();
    for source_ref in all_source_refs(document) {
        let key = source_ref_key(source_ref);
        if source_evidence_ids.contains_key(&key) {
            continue;
        }
        let evidence_id = format!(
            "evidence-archmap-source-{:04}",
            source_evidence_ids.len() + 1
        );
        source_evidence_ids.insert(key, evidence_id.clone());
        evidence.push(AirEvidence {
            evidence_id,
            kind: "manual_annotation".to_string(),
            artifact_ref: Some(artifact_id.clone()),
            path: source_ref.path.clone(),
            symbol: source_ref.symbol.clone(),
            line: source_ref.line,
            rule_id: source_ref.section.clone(),
            confidence: Some("medium".to_string()),
        });
    }

    let mut components = Vec::new();
    let mut component_ids = BTreeSet::new();
    for item in &document.map_items {
        if item.mapping_kind == "object" {
            if let Some(id) = item.target_ref.id.clone() {
                if component_ids.insert(id.clone()) {
                    components.push(AirComponent {
                        id,
                        kind: "archmap-component".to_string(),
                        lifecycle: "after".to_string(),
                        owner: None,
                        evidence_refs: evidence_refs_for_item(item, &source_evidence_ids),
                    });
                }
            }
        }
    }
    for item in &document.map_items {
        for id in [&item.target_ref.from, &item.target_ref.to]
            .into_iter()
            .flatten()
        {
            if component_ids.insert(id.clone()) {
                components.push(AirComponent {
                    id: id.clone(),
                    kind: "archmap-component".to_string(),
                    lifecycle: "after".to_string(),
                    owner: None,
                    evidence_refs: evidence_refs_for_item(item, &source_evidence_ids),
                });
            }
        }
    }

    let mut relations = Vec::new();
    let mut claims = Vec::new();
    let mut architecture_paths = Vec::new();
    let mut semantic_diagrams = Vec::new();
    let mut nonfillability_witnesses = Vec::new();
    for (index, item) in document.map_items.iter().enumerate() {
        let claim_id = format!("claim-archmap-{}", item.map_item_id);
        let evidence_refs = evidence_refs_for_item(item, &source_evidence_ids);
        if (item.mapping_kind == "relation" || item.target_ref.kind == "air-relation")
            && item.target_ref.layer.as_deref() != Some("runtime")
        {
            if let (Some(from), Some(to)) = (&item.target_ref.from, &item.target_ref.to) {
                relations.push(AirRelation {
                    id: item
                        .target_ref
                        .id
                        .clone()
                        .unwrap_or_else(|| format!("relation-archmap-{:04}", index + 1)),
                    layer: item
                        .target_ref
                        .layer
                        .clone()
                        .unwrap_or_else(|| "semantic".to_string()),
                    from_component: Some(from.clone()),
                    to_component: Some(to.clone()),
                    kind: "archmap-relation".to_string(),
                    lifecycle: "after".to_string(),
                    protected_by: None,
                    extraction_rule: Some("archmap-v0-projection".to_string()),
                    evidence_refs: evidence_refs.clone(),
                });
            }
        }
        if item.mapping_kind == "semanticDiagram"
            || item.mapping_kind == "semanticCommutationClaim"
            || item.target_ref.kind == "semantic-diagram"
        {
            let lhs = item
                .target_ref
                .lhs_path_ref
                .clone()
                .unwrap_or_else(|| format!("path-{}-lhs", item.map_item_id));
            let rhs = item
                .target_ref
                .rhs_path_ref
                .clone()
                .unwrap_or_else(|| format!("path-{}-rhs", item.map_item_id));
            architecture_paths.push(AirArchitecturePath {
                path_id: lhs.clone(),
                source_state: item
                    .target_ref
                    .from
                    .clone()
                    .unwrap_or_else(|| "selected-source".to_string()),
                target_state: item
                    .target_ref
                    .to
                    .clone()
                    .unwrap_or_else(|| "selected-target".to_string()),
                steps: item.preserves.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
            architecture_paths.push(AirArchitecturePath {
                path_id: rhs.clone(),
                source_state: item
                    .target_ref
                    .from
                    .clone()
                    .unwrap_or_else(|| "selected-source".to_string()),
                target_state: item
                    .target_ref
                    .to
                    .clone()
                    .unwrap_or_else(|| "selected-target".to_string()),
                steps: item.forgets.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
            semantic_diagrams.push(AirSemanticDiagram {
                id: item
                    .target_ref
                    .id
                    .clone()
                    .unwrap_or_else(|| format!("diagram-{}", item.map_item_id)),
                lhs_path_ref: lhs,
                rhs_path_ref: rhs,
                equivalence: item
                    .target_ref
                    .equivalence
                    .clone()
                    .unwrap_or_else(|| item.measurement_boundary.clone()),
                filler_claim_ref: Some(claim_id.clone()),
                nonfillability_witness_refs: Vec::new(),
                observation_refs: evidence_refs.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
        }
        if item.mapping_kind == "nonfillabilityWitness"
            || item.target_ref.kind == "nonfillability-witness"
        {
            nonfillability_witnesses.push(AirNonfillabilityWitness {
                witness_id: item
                    .target_ref
                    .id
                    .clone()
                    .unwrap_or_else(|| format!("witness-{}", item.map_item_id)),
                diagram_ref: item
                    .target_ref
                    .subject_ref
                    .clone()
                    .unwrap_or_else(|| "diagram-unresolved".to_string()),
                witness_kind: "archmap-nonfillability-witness".to_string(),
                claim_ref: claim_id.clone(),
                evidence_refs: evidence_refs.clone(),
            });
        }
        claims.push(air_claim_from_item(item, claim_id, evidence_refs));
    }
    for conflict in &conflicts {
        claims.push(air_claim_from_conflict(conflict));
    }

    AirDocumentV0 {
        schema_version: AIR_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        architecture_id: document.architecture_id.clone(),
        ids: AirIdPolicies {
            component_id_policy: "archmap targetRef id/from/to".to_string(),
            relation_id_policy: "archmap targetRef id or stable ordinal".to_string(),
            evidence_id_policy: "archmap source ref stable ordinal".to_string(),
            claim_id_policy: "archmap mapItemId and conflict id".to_string(),
        },
        revision: AirRevision {
            before: None,
            after: document.generated_at.clone(),
        },
        feature: AirFeature {
            feature_id: Some(document.map_id.clone()),
            title: Some("ArchMap supplied JSON projection".to_string()),
            description: Some("AIR generated from supplied archmap-v0 artifact".to_string()),
            source: "manual".to_string(),
            ai_session: None,
        },
        artifacts,
        evidence,
        components,
        relations,
        policies: AirPolicies {
            laws: document
                .map_items
                .iter()
                .filter(|item| item.mapping_kind == "policyBoundary")
                .map(|item| item.map_item_id.clone())
                .collect(),
            boundaries: document.generation_boundary.scope.clone(),
            allowed_edges: Vec::new(),
            forbidden_edges: conflicts
                .iter()
                .filter(|conflict| conflict.category == "policy-disagreement")
                .map(|conflict| conflict.subject_ref.clone())
                .collect(),
            abstraction_rules: Vec::new(),
            protection_rules: Vec::new(),
        },
        semantic_diagrams,
        architecture_paths,
        homotopy_generators: Vec::new(),
        nonfillability_witnesses,
        signature: AirSignature {
            axes: archmap_signature_axes(document),
        },
        coverage: archmap_air_coverage(document, &conflicts),
        claims,
        operation_trace: AirOperationTrace {
            operations: Vec::new(),
        },
        extension: AirExtension {
            embedding_claim_ref: None,
            feature_view_claim_ref: None,
            interaction_claim_refs: Vec::new(),
            split_claim_ref: None,
            split_status: "unmeasured".to_string(),
        },
    }
}

fn check_archmap_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-schema-version-supported",
        "ArchMap schema version is supported",
        if schema_version == ARCHMAP_SCHEMA_VERSION {
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

fn check_source_inventory_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut missing = Vec::new();
    if document.source_universe.included_refs.is_empty() {
        missing.push(generic_validation_example(
            "sourceUniverse.includedRefs",
            "empty",
            "bounded source inventory must enumerate included refs",
        ));
    }
    if document
        .source_universe
        .selection_boundary
        .trim()
        .is_empty()
    {
        missing.push(generic_validation_example(
            "sourceUniverse.selectionBoundary",
            "empty",
            "source inventory selection boundary must be explicit",
        ));
    }
    if document.generation_boundary.non_conclusions.is_empty()
        && document.non_conclusions.is_empty()
    {
        missing.push(generic_validation_example(
            "generationBoundary.nonConclusions",
            "empty",
            "LLM generation boundary must preserve non-conclusions",
        ));
    }
    check_from_examples(
        "archmap-source-inventory-boundary",
        "Source inventory keeps included / excluded / unavailable / private boundary explicit",
        missing,
        "fail",
    )
}

fn check_source_inventory_artifact(
    document: &ArchMapDocumentV0,
    source_inventory: Option<&ArchMapSourceInventoryInput<'_>>,
) -> ValidationCheck {
    let Some(source_inventory_ref) = &document.source_inventory_ref else {
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            vec![generic_validation_example(
                "sourceInventoryRef",
                "missing",
                "source inventory artifact ref is absent; input boundary remains embedded only",
            )],
        );
    };

    let mut examples = Vec::new();
    let expected_path = source_inventory_ref.path.as_deref().unwrap_or_default();
    if expected_path.trim().is_empty() {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            "empty",
            "source inventory artifact path must be explicit",
        ));
    }

    let Some(source_inventory) = source_inventory else {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            expected_path,
            "source inventory artifact was not supplied to validation",
        ));
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            examples,
        );
    };

    if source_inventory.path != expected_path {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            source_inventory.path,
            "loaded source inventory path differs from ArchMap sourceInventoryRef.path",
        ));
    }
    if let Some(read_error) = &source_inventory.read_error {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            expected_path,
            read_error,
        ));
    }

    let Some(inventory) = source_inventory.document else {
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            examples,
        );
    };

    if inventory.schema_version != ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "sourceInventory.schemaVersion",
            &inventory.schema_version,
            "source inventory schema version is unsupported",
        ));
    }
    if inventory.root != document.source_universe.root {
        examples.push(generic_validation_example(
            "sourceInventory.root",
            &inventory.root,
            "source inventory root differs from ArchMap sourceUniverse.root",
        ));
    }
    if inventory.selection_boundary != document.source_universe.selection_boundary {
        examples.push(generic_validation_example(
            "sourceInventory.selectionBoundary",
            &inventory.selection_boundary,
            "source inventory selection boundary differs from ArchMap sourceUniverse",
        ));
    }

    compare_source_ref_sets(
        &mut examples,
        "includedRefs",
        &inventory.included_refs,
        &document.source_universe.included_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "excludedRefs",
        &inventory.excluded_refs,
        &document.source_universe.excluded_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "unavailableRefs",
        &inventory.unavailable_refs,
        &document.source_universe.unavailable_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "privateRefs",
        &inventory.private_refs,
        &document.source_universe.private_refs,
    );

    compare_artifact_ref_sets(
        &mut examples,
        "hashes",
        &inventory.hashes,
        &document.source_universe.hashes,
    );

    let mut check = warning_check_from_examples(
        "archmap-source-inventory-artifact",
        "Source inventory artifact ref is present and matches sourceUniverse",
        examples,
    );
    if check.result == "pass" {
        check.count = Some(
            inventory.included_refs.len()
                + inventory.excluded_refs.len()
                + inventory.unavailable_refs.len()
                + inventory.private_refs.len(),
        );
        check.reason = Some(
            "source inventory preserves included, excluded, unavailable, private, hash, and selection boundary categories"
                .to_string(),
        );
    }
    check
}

fn check_archmap_unique_map_item_ids(document: &ArchMapDocumentV0) -> ValidationCheck {
    let duplicate_ids = duplicates(
        document
            .map_items
            .iter()
            .map(|item| item.map_item_id.as_str()),
    );
    let examples = duplicate_ids
        .iter()
        .map(|id| generic_validation_example("mapItems[].mapItemId", id, "duplicate map item id"))
        .collect();
    check_from_examples(
        "archmap-map-item-ids-unique",
        "ArchMap map item ids are unique",
        examples,
        "fail",
    )
}

fn check_source_refs(document: &ArchMapDocumentV0) -> ValidationCheck {
    let included: BTreeSet<String> = document
        .source_universe
        .included_refs
        .iter()
        .map(source_ref_key)
        .collect();
    let examples: Vec<_> = document
        .map_items
        .iter()
        .flat_map(|item| {
            let included = &included;
            item.source_refs.iter().filter_map(move |source_ref| {
                let key = source_ref_key(source_ref);
                (!included.contains(&key)).then(|| {
                    generic_validation_example(
                        &format!("mapItems[{}].sourceRefs", item.map_item_id),
                        &key,
                        "source ref is outside includedRefs and is preserved as a dangling boundary",
                    )
                })
            })
        })
        .collect();
    check_from_examples(
        "archmap-source-refs-resolve",
        "Map item source refs resolve inside the selected source inventory",
        examples,
        "warn",
    )
}

fn check_measured_claim_evidence(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| item.claim_classification == "measured" && item.source_refs.is_empty())
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                &item.measurement_boundary,
                "measured ArchMap claim must cite source refs",
            )
        })
        .collect();
    check_from_examples(
        "archmap-measured-claims-have-evidence",
        "Measured ArchMap claims carry evidence refs",
        examples,
        "fail",
    )
}

fn check_missing_evidence_not_measured_zero(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| {
            item.measurement_boundary == "measuredZero" && !item.missing_evidence.is_empty()
        })
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                "measuredZero",
                "missing evidence cannot be rounded to measured zero",
            )
        })
        .collect();
    check_from_examples(
        "archmap-missing-evidence-not-measured-zero",
        "Missing evidence is not rounded to measured zero",
        examples,
        "fail",
    )
}

fn check_semantic_coverage(document: &ArchMapDocumentV0) -> ValidationCheck {
    let has_semantic_item = document.map_items.iter().any(|item| {
        item.mapping_kind.starts_with("semantic")
            || item.mapping_kind == "nonfillabilityWitness"
            || item.target_ref.layer.as_deref() == Some("semantic")
    });
    let semantic_recorded = document
        .coverage
        .measured_layers
        .iter()
        .chain(document.coverage.unmeasured_layers.iter())
        .chain(document.coverage.assumed_layers.iter())
        .any(|layer| layer == "semantic");
    let mut examples = Vec::new();
    if has_semantic_item && !semantic_recorded {
        examples.push(generic_validation_example(
            "coverage",
            "semantic",
            "semantic map items require measured, assumed, or unmeasured semantic coverage",
        ));
    }
    check_from_examples(
        "archmap-semantic-coverage-boundary",
        "Semantic coverage is explicit and is not inferred from absence",
        examples,
        "fail",
    )
}

fn check_conflicts(document: &ArchMapDocumentV0, sig0: Option<&Sig0Document>) -> ValidationCheck {
    let conflicts = explicit_and_derived_conflicts(document, sig0);
    let mut check = validation_check(
        "archmap-conflicts-preserved-as-review-cues",
        "ArchMap conflicts are preserved as review cues instead of resolved claims",
        if conflicts.is_empty() { "pass" } else { "warn" },
    );
    check.count = Some(conflicts.len());
    check.examples = conflicts
        .iter()
        .take(10)
        .map(|conflict| {
            generic_validation_example(
                &conflict.category,
                &conflict.subject_ref,
                &conflict.description,
            )
        })
        .collect();
    check
}

fn check_formal_promotion_guardrail(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| {
            matches!(item.claim_classification.as_str(), "proved" | "formal")
                && item.theorem_refs.is_empty()
        })
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                &item.claim_classification,
                "formal/proved claim requires theorem refs and is not inferred from LLM output",
            )
        })
        .collect();
    check_from_examples(
        "archmap-formal-promotion-guardrail",
        "LLM-authored claims are not promoted to formal/proved theorem claims",
        examples,
        "fail",
    )
}

fn check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
    failure_result: &str,
) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if examples.is_empty() {
            "pass"
        } else {
            failure_result
        },
    );
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

fn warning_check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    check_from_examples(id, title, examples, "warn")
}

fn compare_source_ref_sets(
    examples: &mut Vec<crate::ValidationExample>,
    field: &str,
    inventory_refs: &[ArchMapSourceRef],
    embedded_refs: &[ArchMapSourceRef],
) {
    let inventory_keys: BTreeSet<_> = inventory_refs.iter().map(source_ref_key).collect();
    let embedded_keys: BTreeSet<_> = embedded_refs.iter().map(source_ref_key).collect();
    for key in inventory_keys.difference(&embedded_keys) {
        examples.push(generic_validation_example(
            &format!("sourceInventory.{field}"),
            key,
            "source inventory ref is absent from embedded ArchMap sourceUniverse",
        ));
    }
    for key in embedded_keys.difference(&inventory_keys) {
        examples.push(generic_validation_example(
            &format!("sourceUniverse.{field}"),
            key,
            "embedded ArchMap sourceUniverse ref is absent from source inventory artifact",
        ));
    }
}

fn compare_artifact_ref_sets(
    examples: &mut Vec<crate::ValidationExample>,
    field: &str,
    inventory_refs: &[crate::ArchMapArtifactRef],
    embedded_refs: &[crate::ArchMapArtifactRef],
) {
    let inventory_keys: BTreeSet<_> = inventory_refs.iter().map(artifact_ref_key).collect();
    let embedded_keys: BTreeSet<_> = embedded_refs.iter().map(artifact_ref_key).collect();
    for key in inventory_keys.difference(&embedded_keys) {
        examples.push(generic_validation_example(
            &format!("sourceInventory.{field}"),
            key,
            "source inventory artifact hash is absent from embedded ArchMap sourceUniverse",
        ));
    }
    for key in embedded_keys.difference(&inventory_keys) {
        examples.push(generic_validation_example(
            &format!("sourceUniverse.{field}"),
            key,
            "embedded ArchMap sourceUniverse hash is absent from source inventory artifact",
        ));
    }
}

fn explicit_and_derived_conflicts(
    document: &ArchMapDocumentV0,
    sig0: Option<&Sig0Document>,
) -> Vec<ArchMapConflict> {
    let mut conflicts = document.conflicts.clone();
    conflicts.extend(document.map_items.iter().filter_map(|item| {
        item.conflict_category
            .as_ref()
            .map(|category| ArchMapConflict {
                conflict_id: format!("conflict-{}", item.map_item_id),
                category: category.clone(),
                subject_ref: item
                    .target_ref
                    .subject_ref
                    .clone()
                    .or_else(|| item.target_ref.id.clone())
                    .unwrap_or_else(|| item.map_item_id.clone()),
                description: format!("ArchMap item {} reports {}", item.map_item_id, category),
                source_refs: item.source_refs.clone(),
                non_conclusions: vec![
                    "conflict cue does not decide which source is correct".to_string(),
                ],
            })
    }));
    let included: BTreeSet<String> = document
        .source_universe
        .included_refs
        .iter()
        .map(source_ref_key)
        .collect();
    for item in &document.map_items {
        for source_ref in &item.source_refs {
            let key = source_ref_key(source_ref);
            if !included.contains(&key) {
                conflicts.push(ArchMapConflict {
                    conflict_id: format!("conflict-source-ref-dangling-{}", item.map_item_id),
                    category: "source-ref-dangling".to_string(),
                    subject_ref: key,
                    description: "map item cites a source ref outside sourceUniverse.includedRefs"
                        .to_string(),
                    source_refs: vec![source_ref.clone()],
                    non_conclusions: vec![
                        "dangling source ref is not measured zero".to_string(),
                        "validation does not infer source availability".to_string(),
                    ],
                });
            }
        }
    }
    if let Some(sig0) = sig0 {
        conflicts.extend(static_edge_conflicts(document, sig0));
    }
    unique_conflicts(conflicts)
}

fn static_edge_conflicts(
    document: &ArchMapDocumentV0,
    sig0: &Sig0Document,
) -> Vec<ArchMapConflict> {
    let static_edges: BTreeSet<(String, String)> = sig0
        .edges
        .iter()
        .map(|edge| (edge.source.clone(), edge.target.clone()))
        .collect();
    let archmap_edges: BTreeSet<(String, String)> = document
        .map_items
        .iter()
        .filter_map(|item| Some((item.target_ref.from.clone()?, item.target_ref.to.clone()?)))
        .collect();
    let mut conflicts = Vec::new();
    for (from, to) in archmap_edges.difference(&static_edges) {
        conflicts.push(ArchMapConflict {
            conflict_id: format!(
                "conflict-missing-static-edge-{}-{}",
                stable_id(from),
                stable_id(to)
            ),
            category: "missing-static-edge".to_string(),
            subject_ref: format!("{from}->{to}"),
            description: "ArchMap relation is not present in supplied Sig0 static edges"
                .to_string(),
            source_refs: Vec::new(),
            non_conclusions: vec![
                "semantic relation is not resolved by static extraction".to_string(),
            ],
        });
    }
    for (from, to) in static_edges.difference(&archmap_edges) {
        conflicts.push(ArchMapConflict {
            conflict_id: format!(
                "conflict-unexplained-static-edge-{}-{}",
                stable_id(from),
                stable_id(to)
            ),
            category: "unexplained-static-edge".to_string(),
            subject_ref: format!("{from}->{to}"),
            description: "Sig0 static edge has no ArchMap semantic explanation".to_string(),
            source_refs: Vec::new(),
            non_conclusions: vec![
                "unexplained static edge is a review cue, not a violation proof".to_string(),
            ],
        });
    }
    conflicts
}

fn unique_conflicts(conflicts: Vec<ArchMapConflict>) -> Vec<ArchMapConflict> {
    let mut seen = BTreeSet::new();
    conflicts
        .into_iter()
        .filter(|conflict| {
            seen.insert((
                conflict.category.clone(),
                conflict.subject_ref.clone(),
                conflict.description.clone(),
            ))
        })
        .collect()
}

fn archmap_air_coverage(
    document: &ArchMapDocumentV0,
    conflicts: &[ArchMapConflict],
) -> AirCoverage {
    let mut layers = Vec::new();
    for layer in ["static", "runtime", "semantic", "policy", "operation"] {
        let measured = document
            .coverage
            .measured_layers
            .iter()
            .any(|measured_layer| measured_layer == layer);
        let assumed = document
            .coverage
            .assumed_layers
            .iter()
            .any(|assumed_layer| assumed_layer == layer);
        let unmeasured = document
            .coverage
            .unmeasured_layers
            .iter()
            .any(|unmeasured_layer| unmeasured_layer == layer);
        let has_conflict = conflicts.iter().any(|conflict| {
            conflict.subject_ref.contains(layer) || conflict.category.contains(layer)
        });
        layers.push(AirCoverageLayer {
            layer: layer.to_string(),
            measurement_boundary: if measured {
                "measuredNonzero".to_string()
            } else {
                "unmeasured".to_string()
            },
            universe_refs: vec!["artifact-archmap".to_string()],
            measured_axes: measured
                .then(|| vec![format!("{layer}ArchMapCoverage")])
                .unwrap_or_default(),
            unmeasured_axes: if layer == "runtime" && !measured {
                vec!["runtimePropagation".to_string()]
            } else {
                (unmeasured || (!measured && !assumed) || assumed)
                    .then(|| vec![format!("{layer}ArchMapCoverage")])
                    .unwrap_or_default()
            },
            projection_rule: if layer == "runtime" && !measured {
                None
            } else {
                Some("archmap-v0-to-air-v0".to_string())
            },
            extraction_scope: vec![document.source_universe.selection_boundary.clone()],
            exactness_assumptions: vec![
                "ArchMap projection preserves claim boundary but does not prove semantic preservation"
                    .to_string(),
            ],
            unsupported_constructs: unsupported_constructs_for_layer(document, layer, has_conflict),
        });
    }
    AirCoverage { layers }
}

fn unsupported_constructs_for_layer(
    document: &ArchMapDocumentV0,
    layer: &str,
    has_conflict: bool,
) -> Vec<String> {
    let mut constructs = document.coverage.unsupported_constructs.clone();
    if layer == "runtime" && !document.coverage.measured_layers.iter().any(|l| l == layer) {
        constructs.extend(document.source_universe.known_blind_spots.clone());
    }
    if has_conflict {
        constructs.push(format!("{layer} conflict requires human review"));
    }
    constructs.sort();
    constructs.dedup();
    constructs
}

fn archmap_signature_axes(document: &ArchMapDocumentV0) -> Vec<crate::AirSignatureAxis> {
    let mut axes: Vec<_> = ["static", "runtime", "semantic", "policy"]
        .into_iter()
        .map(|layer| {
            let measured = document
                .coverage
                .measured_layers
                .iter()
                .any(|measured_layer| measured_layer == layer);
            crate::AirSignatureAxis {
                axis: format!("{layer}ArchMapCoverage"),
                value: measured.then_some(1),
                measured,
                measurement_boundary: if measured {
                    "measuredNonzero".to_string()
                } else {
                    "unmeasured".to_string()
                },
                source: Some("archmap-v0".to_string()),
                reason: (!measured).then(|| format!("{layer} layer is not measured by ArchMap")),
            }
        })
        .collect();
    axes.push(crate::AirSignatureAxis {
        axis: "runtimePropagation".to_string(),
        value: None,
        measured: false,
        measurement_boundary: "unmeasured".to_string(),
        source: Some("archmap-v0".to_string()),
        reason: Some("runtime traces are not supplied by ArchMap MVP fixture".to_string()),
    });
    axes
}

fn air_claim_from_item(
    item: &ArchMapMapItem,
    claim_id: String,
    evidence_refs: Vec<String>,
) -> AirClaim {
    AirClaim {
        claim_id,
        subject_ref: item
            .target_ref
            .subject_ref
            .clone()
            .or_else(|| item.target_ref.id.clone())
            .unwrap_or_else(|| item.map_item_id.clone()),
        predicate: item
            .target_ref
            .predicate
            .clone()
            .unwrap_or_else(|| format!("ArchMap {} mapping", item.mapping_kind)),
        claim_level: "tooling".to_string(),
        claim_classification: item.claim_classification.clone(),
        measurement_boundary: item.measurement_boundary.clone(),
        theorem_refs: item.theorem_refs.clone(),
        evidence_refs,
        required_assumptions: archmap_item_required_assumptions(item),
        coverage_assumptions: item.preserves.clone(),
        exactness_assumptions: item.forgets.clone(),
        missing_preconditions: item.missing_evidence.clone(),
        non_conclusions: archmap_item_non_conclusions(item),
    }
}

pub fn archmap_lean_preservation_vocabulary() -> Vec<ArchMapLeanPreservationVocabularyEntry> {
    vec![
        lean_vocabulary_entry(
            "archmap-object-preservation",
            "mappingKind=object or targetRef.kind=air-component",
            "ObjectPreservation",
            "selected ArchMap object candidate preserves a bounded Lean object field",
        ),
        lean_vocabulary_entry(
            "archmap-relation-preservation",
            "mappingKind=relation or targetRef.kind=air-relation",
            "RelationPreservation",
            "selected ArchMap relation candidate preserves a bounded Lean relation field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-diagram-preservation",
            "mappingKind=semanticDiagram or targetRef.kind=semantic-diagram",
            "SemanticDiagramPreservation",
            "selected semantic diagram candidate preserves a bounded diagram field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-commutation-preservation",
            "mappingKind=semanticCommutationClaim",
            "SemanticCommutationPreservation",
            "selected commutation claim candidate is tracked without proving commutation",
        ),
        lean_vocabulary_entry(
            "archmap-nonfillability-witness-preservation",
            "mappingKind=nonfillabilityWitness or targetRef.kind=nonfillability-witness",
            "NonfillabilityWitnessPreservation",
            "selected non-fillability witness candidate is preserved as review evidence",
        ),
        lean_vocabulary_entry(
            "archmap-law-policy-preservation",
            "mappingKind=policyBoundary or targetRef.layer=policy",
            "LawPolicyPreservation",
            "selected policy boundary candidate is tracked as supplied policy evidence",
        ),
        lean_vocabulary_entry(
            "archmap-flatness-precondition-preservation",
            "targetRef.subjectRef contains flatnessPrecondition or preserves contains flatness precondition boundary",
            "FlatnessPreconditionPreservation",
            "selected flatness precondition candidate is tracked without discharging flatness",
        ),
        lean_vocabulary_entry(
            "archmap-coverage-boundary",
            "coverage, missingEvidence, nonConclusions",
            "CoverageExactnessBoundary",
            "coverage gaps, exactness limits, missing evidence, and non-conclusions remain explicit",
        ),
    ]
}

pub fn archmap_lean_preservation_checklist(
    document: &ArchMapDocumentV0,
) -> Vec<ArchMapLeanPreservationChecklistEntry> {
    let mut entries: Vec<_> = document
        .map_items
        .iter()
        .map(|item| archmap_item_preservation_checklist_entry(document, item))
        .collect();
    entries.push(archmap_coverage_boundary_checklist_entry(document));
    entries.push(archmap_formal_promotion_guardrail_checklist_entry());
    entries
}

fn lean_vocabulary_entry(
    vocabulary_id: &str,
    archmap_selector: &str,
    lean_package_field: &str,
    preservation_role: &str,
) -> ArchMapLeanPreservationVocabularyEntry {
    ArchMapLeanPreservationVocabularyEntry {
        vocabulary_id: vocabulary_id.to_string(),
        archmap_selector: archmap_selector.to_string(),
        lean_package_field: lean_package_field.to_string(),
        preservation_role: preservation_role.to_string(),
        report_boundary:
            "tooling vocabulary records a preservation candidate; it is not a Lean proof witness"
                .to_string(),
    }
}

fn archmap_item_preservation_checklist_entry(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
) -> ArchMapLeanPreservationChecklistEntry {
    let lean_package_field = archmap_item_lean_package_field(item);
    let status = archmap_item_preservation_status(document, item, lean_package_field);
    let mut blocking_reasons = Vec::new();
    if !item.missing_evidence.is_empty() {
        blocking_reasons
            .push("missing evidence blocks preservation precondition discharge".to_string());
    }
    if status == "blockedByUnmeasuredCoverage" {
        blocking_reasons.push("unmeasured coverage remains a coverage gap".to_string());
    }
    if matches!(item.claim_classification.as_str(), "proved" | "formal")
        && item.theorem_refs.is_empty()
    {
        blocking_reasons.push(
            "formal promotion guardrail blocks theorem claim without theorem refs".to_string(),
        );
    }
    if lean_package_field == "OutOfScopeBoundary" {
        blocking_reasons
            .push("mapping kind is outside the ArchMapPreservationPackage vocabulary".to_string());
    }

    ArchMapLeanPreservationChecklistEntry {
        checklist_id: format!("archmap-preservation-{}", item.map_item_id),
        map_item_id: Some(item.map_item_id.clone()),
        lean_package_field: lean_package_field.to_string(),
        status: status.to_string(),
        candidate_sources: vec![
            format!("mappingKind={}", item.mapping_kind),
            format!("targetRef.kind={}", item.target_ref.kind),
        ],
        blocking_reasons,
        missing_evidence: item.missing_evidence.clone(),
        coverage_boundary: archmap_item_coverage_boundary(document, item),
        non_conclusions: archmap_item_non_conclusions(item),
    }
}

fn archmap_coverage_boundary_checklist_entry(
    document: &ArchMapDocumentV0,
) -> ArchMapLeanPreservationChecklistEntry {
    let mut blocking_reasons = Vec::new();
    if !document.coverage.unmeasured_layers.is_empty() {
        blocking_reasons.push(format!(
            "unmeasured layers remain: {}",
            document.coverage.unmeasured_layers.join(", ")
        ));
    }
    if !document.coverage.unsupported_constructs.is_empty() {
        blocking_reasons.push(format!(
            "unsupported constructs remain: {}",
            document.coverage.unsupported_constructs.join(", ")
        ));
    }
    ArchMapLeanPreservationChecklistEntry {
        checklist_id: "archmap-preservation-coverage-boundary".to_string(),
        map_item_id: None,
        lean_package_field: "CoverageExactnessBoundary".to_string(),
        status: if blocking_reasons.is_empty() {
            "candidate"
        } else {
            "blockedByUnmeasuredCoverage"
        }
        .to_string(),
        candidate_sources: vec!["coverage".to_string(), "nonConclusions".to_string()],
        blocking_reasons,
        missing_evidence: Vec::new(),
        coverage_boundary: format!(
            "measured=[{}]; unmeasured=[{}]; assumed=[{}]",
            document.coverage.measured_layers.join(", "),
            document.coverage.unmeasured_layers.join(", "),
            document.coverage.assumed_layers.join(", ")
        ),
        non_conclusions: archmap_non_conclusions(document),
    }
}

fn archmap_formal_promotion_guardrail_checklist_entry() -> ArchMapLeanPreservationChecklistEntry {
    ArchMapLeanPreservationChecklistEntry {
        checklist_id: "archmap-preservation-formal-promotion-guardrail".to_string(),
        map_item_id: None,
        lean_package_field: "FormalPromotionGuardrail".to_string(),
        status: "blockedByFormalPromotionGuardrail".to_string(),
        candidate_sources: vec![
            "archmap validation pass".to_string(),
            "AIR projection success".to_string(),
        ],
        blocking_reasons: vec![
            "validation and projection do not discharge ArchMapPreservationPackage fields"
                .to_string(),
        ],
        missing_evidence: vec!["Lean theorem witness not supplied by archmap-v0".to_string()],
        coverage_boundary:
            "formal promotion requires explicit Lean theorem refs and discharged preconditions"
                .to_string(),
        non_conclusions: vec![
            "ArchMap validation pass is not a Lean theorem proof".to_string(),
            "AIR projection success is not a semantic preservation proof".to_string(),
        ],
    }
}

fn archmap_item_lean_package_field(item: &ArchMapMapItem) -> &'static str {
    if item.mapping_kind == "object" || item.target_ref.kind == "air-component" {
        "ObjectPreservation"
    } else if item.mapping_kind == "relation" || item.target_ref.kind == "air-relation" {
        "RelationPreservation"
    } else if item.mapping_kind == "semanticCommutationClaim" {
        "SemanticCommutationPreservation"
    } else if item.mapping_kind == "semanticDiagram" || item.target_ref.kind == "semantic-diagram" {
        "SemanticDiagramPreservation"
    } else if item.mapping_kind == "nonfillabilityWitness"
        || item.target_ref.kind == "nonfillability-witness"
    {
        "NonfillabilityWitnessPreservation"
    } else if item.mapping_kind == "policyBoundary"
        || item.target_ref.layer.as_deref() == Some("policy")
    {
        "LawPolicyPreservation"
    } else if item
        .target_ref
        .subject_ref
        .as_deref()
        .is_some_and(|subject_ref| subject_ref.contains("flatnessPrecondition"))
        || item
            .preserves
            .iter()
            .any(|preserves| preserves.contains("flatness precondition"))
    {
        "FlatnessPreconditionPreservation"
    } else {
        "OutOfScopeBoundary"
    }
}

fn archmap_item_preservation_status(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
    lean_package_field: &str,
) -> &'static str {
    if lean_package_field == "OutOfScopeBoundary" {
        "notApplicableOutOfScope"
    } else if matches!(item.claim_classification.as_str(), "proved" | "formal")
        && item.theorem_refs.is_empty()
    {
        "blockedByFormalPromotionGuardrail"
    } else if !item.missing_evidence.is_empty() {
        "blockedByMissingEvidence"
    } else if item.claim_classification == "assumed" || !item.required_assumptions.is_empty() {
        "satisfiedBySuppliedAssumption"
    } else if archmap_item_has_unmeasured_coverage(document, item) {
        "blockedByUnmeasuredCoverage"
    } else {
        "candidate"
    }
}

fn archmap_item_has_unmeasured_coverage(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
) -> bool {
    item.measurement_boundary == "unmeasured"
        || item
            .target_ref
            .layer
            .as_ref()
            .is_some_and(|layer| document.coverage.unmeasured_layers.contains(layer))
}

fn archmap_item_coverage_boundary(document: &ArchMapDocumentV0, item: &ArchMapMapItem) -> String {
    let layer = item.target_ref.layer.as_deref().unwrap_or("unlayered");
    let layer_state = if document
        .coverage
        .measured_layers
        .iter()
        .any(|measured| measured == layer)
    {
        "measured"
    } else if document
        .coverage
        .assumed_layers
        .iter()
        .any(|assumed| assumed == layer)
    {
        "assumed"
    } else if document
        .coverage
        .unmeasured_layers
        .iter()
        .any(|unmeasured| unmeasured == layer)
    {
        "unmeasured"
    } else {
        "not listed"
    };
    format!(
        "layer={layer}; layerState={layer_state}; measurementBoundary={}",
        item.measurement_boundary
    )
}

fn archmap_item_required_assumptions(item: &ArchMapMapItem) -> Vec<String> {
    let mut required_assumptions = item.required_assumptions.clone();
    required_assumptions.push(format!(
        "ArchMapPreservationPackage.{} candidate",
        archmap_item_lean_package_field(item)
    ));
    required_assumptions.sort();
    required_assumptions.dedup();
    required_assumptions
}

fn air_claim_from_conflict(conflict: &ArchMapConflict) -> AirClaim {
    AirClaim {
        claim_id: format!("claim-{}", conflict.conflict_id),
        subject_ref: conflict.subject_ref.clone(),
        predicate: format!("ArchMap conflict review cue: {}", conflict.category),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: vec!["evidence-archmap-artifact".to_string()],
        required_assumptions: Vec::new(),
        coverage_assumptions: vec![conflict.description.clone()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["human review of conflicting evidence".to_string()],
        non_conclusions: conflict.non_conclusions.clone(),
    }
}

fn archmap_item_non_conclusions(item: &ArchMapMapItem) -> Vec<String> {
    let mut non_conclusions = item.non_conclusions.clone();
    non_conclusions.push("ArchMap item is not architecture ground truth".to_string());
    non_conclusions.push("ArchMap item does not prove semantic preservation".to_string());
    if item.claim_classification != "proved" {
        non_conclusions.push("LLM-authored mapping is not a Lean theorem".to_string());
    }
    non_conclusions.sort();
    non_conclusions.dedup();
    non_conclusions
}

fn archmap_non_conclusions(document: &ArchMapDocumentV0) -> Vec<String> {
    let mut non_conclusions = document.non_conclusions.clone();
    non_conclusions.extend(document.generation_boundary.non_conclusions.clone());
    non_conclusions.push("ArchMap validation does not prove architecture lawfulness".to_string());
    non_conclusions.push("ArchMap validation does not prove semantic completeness".to_string());
    non_conclusions.sort();
    non_conclusions.dedup();
    non_conclusions
}

fn evidence_refs_for_item(
    item: &ArchMapMapItem,
    source_evidence_ids: &BTreeMap<String, String>,
) -> Vec<String> {
    let mut refs: Vec<String> = item
        .source_refs
        .iter()
        .filter_map(|source_ref| {
            source_evidence_ids
                .get(&source_ref_key(source_ref))
                .cloned()
        })
        .collect();
    refs.extend(item.evidence_refs.clone());
    if refs.is_empty() {
        refs.push("evidence-archmap-artifact".to_string());
    }
    refs.sort();
    refs.dedup();
    refs
}

fn all_source_refs(document: &ArchMapDocumentV0) -> Vec<&ArchMapSourceRef> {
    document
        .source_universe
        .included_refs
        .iter()
        .chain(document.source_universe.excluded_refs.iter())
        .chain(document.source_universe.unavailable_refs.iter())
        .chain(document.source_universe.private_refs.iter())
        .chain(document.generation_boundary.excluded_refs.iter())
        .chain(document.generation_boundary.unavailable_refs.iter())
        .chain(document.generation_boundary.private_refs.iter())
        .chain(
            document
                .map_items
                .iter()
                .flat_map(|item| item.source_refs.iter()),
        )
        .collect()
}

fn source_ref_key(source_ref: &ArchMapSourceRef) -> String {
    if let Some(artifact_id) = &source_ref.artifact_id {
        return artifact_id.clone();
    }
    format!(
        "{}:{}:{}:{}:{}",
        source_ref.kind,
        source_ref.path.as_deref().unwrap_or(""),
        source_ref.symbol.as_deref().unwrap_or(""),
        source_ref
            .line
            .map(|line| line.to_string())
            .unwrap_or_default(),
        source_ref.section.as_deref().unwrap_or("")
    )
}

fn artifact_ref_key(artifact_ref: &crate::ArchMapArtifactRef) -> String {
    let mut parts = Vec::new();
    parts.push(format!("artifactId={}", artifact_ref.artifact_id));
    if let Some(kind) = &artifact_ref.kind {
        parts.push(format!("kind={kind}"));
    }
    if let Some(path) = &artifact_ref.path {
        parts.push(format!("path={path}"));
    }
    if let Some(content_hash) = &artifact_ref.content_hash {
        parts.push(format!("contentHash={content_hash}"));
    }
    parts.join("|")
}

fn stable_id(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect()
}
