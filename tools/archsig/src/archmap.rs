use std::collections::{BTreeMap, BTreeSet};

use crate::law_surface::LawSurfaceBindingVocabularyV1;
use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_V2_SCHEMA, AatAtomVocabularyEntryV1,
    AatAtomVocabularyPairV1, AatAtomVocabularyV1, ArchMapDocumentV2, ArchMapValidationReportV2,
    ArchMapValidationSummaryV2, LAW_SURFACE_BINDING_VOCABULARY_SCHEMA, ValidationCheck,
    ValidationExample, canonical_archmap_extraction_doctrine_ref_v2,
};

/// Splits a `src:<path>:<line>` citation into its file-level source id and
/// line number. Returns None when the ref has no trailing numeric segment.
pub fn source_ref_line_base(reference: &str) -> Option<(&str, u32)> {
    let (base, suffix) = reference.rsplit_once(':')?;
    if base.is_empty() || suffix.is_empty() {
        return None;
    }
    let line = suffix.parse::<u32>().ok()?;
    Some((base, line))
}

pub(crate) fn source_ref_resolves(document: &ArchMapDocumentV2, reference: &str) -> bool {
    document.sources.contains_key(reference)
        || source_ref_line_base(reference)
            .is_some_and(|(base, _)| document.sources.contains_key(base))
}

pub fn compare_archmap_v2_doctrine(
    left: &ArchMapDocumentV2,
    right: &ArchMapDocumentV2,
) -> serde_json::Value {
    let canonical = canonical_archmap_extraction_doctrine_ref_v2();
    let left_is_canonical = left.extraction_doctrine_ref == canonical;
    let right_is_canonical = right.extraction_doctrine_ref == canonical;
    if left_is_canonical && right_is_canonical {
        serde_json::json!({
            "status": "comparable",
            "reason": "fixed_tool_doctrine",
            "leftDoctrine": left.extraction_doctrine_ref.doctrine_id,
            "rightDoctrine": right.extraction_doctrine_ref.doctrine_id
        })
    } else {
        serde_json::json!({
            "status": "not_comparable",
            "reason": "invalid_fixed_doctrine",
            "leftDoctrine": left.extraction_doctrine_ref.doctrine_id,
            "rightDoctrine": right.extraction_doctrine_ref.doctrine_id,
            "leftCanonical": left_is_canonical,
            "rightCanonical": right_is_canonical
        })
    }
}

pub fn validate_archmap_v2_report(
    document: &ArchMapDocumentV2,
    input_path: &str,
) -> ArchMapValidationReportV2 {
    let checks = vec![
        check_archmap_v2_schema(&document.schema),
        check_archmap_v2_doctrine(document),
        check_archmap_v2_sources(document),
        check_archmap_v2_collection_shape(document),
        check_archmap_v2_atom_ids(document),
        check_archmap_v2_no_diagnostic_shortcuts(document),
        check_archmap_v2_atom_kind_vocabulary(document),
        check_archmap_v2_atom_axis_predicate_vocabulary(document),
        check_archmap_v2_binding_vocabulary(),
        check_archmap_v2_atom_shapes(document),
        check_archmap_v2_contexts(document),
        check_archmap_v2_covers(document),
    ];
    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    ArchMapValidationReportV2 {
        schema_version: "archmap-validation-report/v0.5.4".to_string(),
        archmap_ref: input_path.to_string(),
        input_schema: document.schema.clone(),
        checks,
        summary: ArchMapValidationSummaryV2 {
            result: result.to_string(),
            source_count: document.sources.len(),
            atom_count: document.atoms.len(),
            context_count: document.contexts.len(),
            cover_count: document.covers.len(),
            failed_check_count,
            warning_check_count,
        },
        non_conclusions: vec![
            "ArchMap v2 validation checks the finite poset site observation contract and supplies source-grounded observations for ArchSig measurement.".to_string(),
            "Contexts and covers are source-grounded observations; selected measurement coefficients, witnesses, and verdict predicates belong to MeasurementProfile.".to_string(),
        ],
    }
}

pub fn static_aat_atom_vocabulary_v1() -> AatAtomVocabularyV1 {
    let doctrine_ref = "aat-theory:atom-vocabulary";
    AatAtomVocabularyV1 {
        schema: AAT_ATOM_VOCABULARY_V1_SCHEMA.to_string(),
        vocabulary_id: "aat-atom-vocabulary:ag-archmap@1".to_string(),
        doctrine_ref: doctrine_ref.to_string(),
        required_doctrine_components: ["V", "Gamma", "R", "rho", "E", "N"]
            .into_iter()
            .map(str::to_string)
            .collect(),
        entries: [
            "component",
            "relation",
            "capability",
            "state",
            "effect",
            "authority",
            "contract",
            "semantic",
            "runtime",
        ]
        .into_iter()
        .map(|kind| AatAtomVocabularyEntryV1 {
            kind: kind.to_string(),
            doctrine_ref: doctrine_ref.to_string(),
            provenance_ref: doctrine_ref.to_string(),
        })
        .collect(),
        axis_predicate_pairs: canonical_aat_atom_axis_predicate_pairs(),
        allowed_non_ag_observation_axes: [
            "application",
            "boundary",
            "cover",
            "dataflow",
            "effect",
            "restriction",
            "runtime",
            "semantic",
            "specification",
            "state",
            "static",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
        non_conclusions: vec![
            "AAT atom vocabulary is the ArchSig input contract for token membership and canonical observation pairs.".to_string(),
            "Vocabulary lint computes token membership under the compiled AAT doctrine.".to_string(),
        ],
    }
}

fn canonical_aat_atom_axis_predicate_pairs() -> Vec<AatAtomVocabularyPairV1> {
    [
        (
            "boundary-residue",
            [
                "boundarySection",
                "patchClassification",
                "patchRole",
                "restrictionColumn",
            ]
            .as_slice(),
        ),
        (
            "cech",
            [
                "cocycleValue",
                "restrictionSurjectivityWitness",
                "sectionValue",
            ]
            .as_slice(),
        ),
        (
            "coherence",
            ["coherenceSection", "h2Section", "tripleSection"].as_slice(),
        ),
        (
            "laplacian",
            ["cellularBoundary", "cellularCochain"].as_slice(),
        ),
        (
            "period",
            ["boundaryPeriod", "dOmegaIntegral", "periodIntegral"].as_slice(),
        ),
        (
            "restriction-compatibility",
            ["restrictionIdealGenerator"].as_slice(),
        ),
        (
            "section-factorization",
            [
                "cooccurrence",
                "selectedSection",
                "support",
                "witnessAssignment",
            ]
            .as_slice(),
        ),
        ("square-free", ["cooccurrence", "support"].as_slice()),
        ("tor", ["commonAmbient", "lawIdealGenerator"].as_slice()),
        (
            "transfer",
            ["groundCost", "repairPath", "transferPairing"].as_slice(),
        ),
    ]
    .into_iter()
    .map(|(axis, predicates)| AatAtomVocabularyPairV1 {
        axis: axis.to_string(),
        predicates: predicates
            .iter()
            .map(|predicate| predicate.to_string())
            .collect(),
        provenance_ref: "aat-theory:atom-vocabulary".to_string(),
    })
    .collect()
}

pub fn static_aat_atom_binding_vocabulary_v1() -> LawSurfaceBindingVocabularyV1 {
    serde_json::from_str(include_str!(
        "schema/aat-law-surface-binding-vocabulary.json"
    ))
    .expect("canonical AAT atom binding vocabulary must be valid JSON")
}

fn check_archmap_v2_binding_vocabulary() -> ValidationCheck {
    let vocabulary = static_aat_atom_binding_vocabulary_v1();
    let required_axes = [
        "cech",
        "square-free",
        "section-factorization",
        "laplacian",
        "period",
        "transfer",
    ];
    let required_predicates = [
        "support",
        "cooccurrence",
        "sectionValue",
        "cellularCochain",
        "periodIntegral",
        "transferPairing",
    ];
    let required_pairs = [
        ("cech", "sectionValue"),
        ("square-free", "support"),
        ("square-free", "cooccurrence"),
        ("section-factorization", "support"),
        ("section-factorization", "cooccurrence"),
        ("laplacian", "cellularCochain"),
        ("period", "periodIntegral"),
        ("transfer", "transferPairing"),
    ];
    let mut examples = Vec::new();
    if vocabulary.schema != LAW_SURFACE_BINDING_VOCABULARY_SCHEMA {
        examples.push(generic_validation_example(
            "aatAtomBindingVocabulary.schema",
            &vocabulary.schema,
            "ArchSig ArchMap and law-surface validation use the v0.5.4 binding manifest",
        ));
    }
    for axis in required_axes {
        if !vocabulary.axes.iter().any(|item| item == axis) {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.axes",
                axis,
                "the shared binding manifest must retain every Stage 2 axis",
            ));
        }
    }
    for predicate in required_predicates {
        if !vocabulary.predicates.iter().any(|item| item == predicate) {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.predicates",
                predicate,
                "the shared binding manifest must retain every Stage 2 predicate",
            ));
        }
    }
    for axis in &vocabulary.axes {
        if !required_axes.contains(&axis.as_str()) {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.axes",
                axis,
                "the shared binding manifest must reject axes outside the Stage 2 contract",
            ));
        }
    }
    for duplicate in duplicates(vocabulary.axes.iter().map(String::as_str)) {
        examples.push(generic_validation_example(
            "aatAtomBindingVocabulary.axes",
            &duplicate,
            "the shared binding manifest must declare each axis once",
        ));
    }
    for predicate in &vocabulary.predicates {
        if !required_predicates.contains(&predicate.as_str()) {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.predicates",
                predicate,
                "the shared binding manifest must reject predicates outside the Stage 2 contract",
            ));
        }
    }
    for duplicate in duplicates(vocabulary.predicates.iter().map(String::as_str)) {
        examples.push(generic_validation_example(
            "aatAtomBindingVocabulary.predicates",
            &duplicate,
            "the shared binding manifest must declare each predicate once",
        ));
    }
    for (axis, predicate) in required_pairs {
        let present = vocabulary
            .axis_predicate_pairs
            .iter()
            .any(|pair| pair.axis == axis && pair.predicates.iter().any(|item| item == predicate));
        if !present {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.axisPredicatePairs",
                &format!("{axis}/{predicate}"),
                "the shared binding manifest must retain every Stage 2 pair",
            ));
        }
    }
    let mut pair_keys = BTreeSet::new();
    for pair in &vocabulary.axis_predicate_pairs {
        if pair.predicates.is_empty() {
            examples.push(generic_validation_example(
                "aatAtomBindingVocabulary.axisPredicatePairs[].predicates",
                &pair.axis,
                "the shared binding manifest must not declare an axis without predicates",
            ));
        }
        for predicate in &pair.predicates {
            if !pair_keys.insert((pair.axis.as_str(), predicate.as_str())) {
                examples.push(generic_validation_example(
                    "aatAtomBindingVocabulary.axisPredicatePairs",
                    &format!("{}/{}", pair.axis, predicate),
                    "the shared binding manifest must declare each pair once",
                ));
            }
            if !required_pairs.contains(&(pair.axis.as_str(), predicate.as_str())) {
                examples.push(generic_validation_example(
                    "aatAtomBindingVocabulary.axisPredicatePairs",
                    &format!("{}/{}", pair.axis, predicate),
                    "the shared binding manifest must reject pairs outside the Stage 2 contract",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-schema052-aat-binding-vocabulary",
        "ArchSig ArchMap and law-surface validation resolve one versioned binding manifest",
        examples,
    )
}

fn check_archmap_v2_schema(schema: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-schema052-schema",
        "ArchMap v2 uses the finite poset site schema discriminator",
        if schema == ARCHMAP_V2_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("expected {ARCHMAP_V2_SCHEMA}, found {schema}"));
    }
    check
}

fn check_archmap_v2_doctrine(document: &ArchMapDocumentV2) -> ValidationCheck {
    let canonical = canonical_archmap_extraction_doctrine_ref_v2();
    let mut examples = Vec::new();
    if document.extraction_doctrine_ref.doctrine_id != canonical.doctrine_id {
        examples.push(generic_validation_example(
            "extractionDoctrineRef.doctrineId",
            &document.extraction_doctrine_ref.doctrine_id,
            "ArchMap v2 uses the fixed AAT canonical doctrine",
        ));
    }
    if document.extraction_doctrine_ref.fingerprint != canonical.fingerprint {
        examples.push(generic_validation_example(
            "extractionDoctrineRef.fingerprint",
            &document.extraction_doctrine_ref.fingerprint,
            "ArchMap v2 uses the fixed AAT canonical doctrine fingerprint",
        ));
    }
    if document.extraction_doctrine_ref.components != canonical.components {
        examples.push(generic_validation_example(
            "extractionDoctrineRef.components",
            &document.extraction_doctrine_ref.components.join(","),
            "ArchMap v2 uses the fixed AAT canonical doctrine components",
        ));
    }
    check_from_examples(
        "archmap-schema052-extraction-doctrine-ref",
        "ArchMap v2 uses the fixed AAT canonical doctrine; authors do not select doctrine",
        examples,
    )
}

fn check_archmap_v2_sources(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    if document.sources.is_empty() {
        examples.push(generic_validation_example(
            "sources",
            "empty",
            "ArchMap v2 needs a source table for atom, context, and cover refs",
        ));
    }
    for (source_id, source) in &document.sources {
        if source_id.trim().is_empty() {
            examples.push(generic_validation_example(
                "sources",
                "empty",
                "source id must be non-empty",
            ));
        }
        if source.kind.trim().is_empty() {
            examples.push(generic_validation_example(
                "sources",
                source_id,
                "source kind must be non-empty",
            ));
        }
        if !source_has_locator(source) {
            examples.push(generic_validation_example(
                "sources",
                source_id,
                "source record must carry at least one non-empty locator: path, symbol, section, or traceId",
            ));
        }
        if let Some(parent) = source.source.as_deref() {
            if !document.sources.contains_key(parent) {
                examples.push(generic_validation_example(
                    source_id,
                    parent,
                    "source parent must resolve to sources",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-schema052-sources-resolve",
        "sources table is present and internally resolvable",
        examples,
    )
}

fn source_has_locator(source: &crate::ArchMapSource) -> bool {
    [
        source.path.as_deref(),
        source.symbol.as_deref(),
        source.section.as_deref(),
        source.trace_id.as_deref(),
    ]
    .into_iter()
    .flatten()
    .any(|value| !value.trim().is_empty())
}

fn check_archmap_v2_collection_shape(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    for (field, is_empty, requirement) in [
        (
            "atoms",
            document.atoms.is_empty(),
            "ArchMap v2 must contain at least one observed atom",
        ),
        (
            "contexts",
            document.contexts.is_empty(),
            "ArchMap v2 must contain at least one observed context",
        ),
        (
            "covers",
            document.covers.is_empty(),
            "ArchMap v2 must contain at least one observed cover",
        ),
    ] {
        if is_empty {
            examples.push(generic_validation_example(field, "empty", requirement));
        }
    }
    check_from_examples(
        "archmap-schema052-required-observation-collections",
        "ArchMap v2 declares non-empty atom, context, and cover observations",
        examples,
    )
}

fn check_archmap_v2_atom_ids(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        if atom.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "atoms[].id",
                "empty",
                "atom id must be non-empty",
            ));
        }
    }
    examples.extend(
        duplicates(document.atoms.iter().map(|atom| atom.id.as_str()))
            .into_iter()
            .map(|duplicate| {
                generic_validation_example("atoms[].id", &duplicate, "atom id must be unique")
            }),
    );
    check_from_examples(
        "archmap-schema052-atom-ids",
        "atom ids are non-empty and unique",
        examples,
    )
}

fn check_archmap_v2_no_diagnostic_shortcuts(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        let mut fields = vec![("id", atom.id.as_str())];
        if !atom.axis.trim().is_empty() {
            fields.push(("axis", atom.axis.as_str()));
        }
        if let Some(predicate) = atom.predicate.as_deref() {
            fields.push(("predicate", predicate));
        }
        for (field, value) in fields {
            if let Some(token) = diagnostic_shortcut_token(value) {
                examples.push(generic_validation_example(
                    &atom.id,
                    &format!("{field}:{token}"),
                    "ArchMap v2 observation fields must not pre-author diagnostic conclusions",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-schema052-no-diagnostic-shortcuts",
        "ArchMap v2 atom observation fields do not pre-author diagnostic conclusions",
        examples,
    )
}

fn diagnostic_shortcut_token(value: &str) -> Option<&'static str> {
    let parts = diagnostic_shortcut_parts(value);
    parts
        .iter()
        .find_map(|part| match part.as_str() {
            "mismatch" => Some("mismatch"),
            "obstruction" | "obstructive" => Some("obstruction"),
            "violation" | "violate" | "violated" | "violates" | "violating" => Some("violation"),
            "risk" | "risky" => Some("risk"),
            "debt" => Some("debt"),
            "unsafe" => Some("unsafe"),
            "safety" => Some("safety"),
            "lawful" => Some("lawful"),
            "nonzero" => Some("nonzero"),
            "failure" | "fail" | "failed" | "failing" => Some("failure"),
            _ => None,
        })
        .or_else(|| {
            parts
                .windows(2)
                .any(|window| window[0] == "non" && window[1] == "zero")
                .then_some("nonzero")
        })
}

fn diagnostic_shortcut_parts(value: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut previous_was_lower_or_digit = false;
    for character in value.chars() {
        if character.is_ascii_alphanumeric() {
            if character.is_ascii_uppercase() && previous_was_lower_or_digit && !current.is_empty()
            {
                parts.push(std::mem::take(&mut current));
            }
            current.push(character.to_ascii_lowercase());
            previous_was_lower_or_digit =
                character.is_ascii_lowercase() || character.is_ascii_digit();
        } else {
            if !current.is_empty() {
                parts.push(std::mem::take(&mut current));
            }
            previous_was_lower_or_digit = false;
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

fn check_archmap_v2_atom_kind_vocabulary(document: &ArchMapDocumentV2) -> ValidationCheck {
    let vocabulary = static_aat_atom_vocabulary_v1();
    let vocabulary_ref = vocabulary.vocabulary_id.as_str();
    let canonical_doctrine = canonical_archmap_extraction_doctrine_ref_v2();
    let canonical_components = canonical_doctrine
        .components
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let missing_components = vocabulary
        .required_doctrine_components
        .iter()
        .filter(|component| !canonical_components.contains(component.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let allowed = vocabulary
        .entries
        .iter()
        .map(|entry| entry.kind.as_str())
        .collect::<BTreeSet<_>>();
    let unknown_atoms = document
        .atoms
        .iter()
        .filter(|atom| !allowed.contains(atom.kind.as_str()))
        .collect::<Vec<_>>();
    let mut examples = Vec::new();
    if !missing_components.is_empty() {
        examples.push(ValidationExample {
            component_id: Some("fixedAatCanonicalDoctrine.components".to_string()),
            path: Some("fixedAatCanonicalDoctrine.components".to_string()),
            source: Some(canonical_doctrine.components.join(",")),
            target: Some(vocabulary_ref.to_string()),
            evidence: Some(format!(
                "fixed AAT canonical doctrine does not resolve required atom vocabulary components: {}",
                missing_components.join(",")
            )),
        });
    }
    examples.extend(unknown_atoms.iter().map(|atom| ValidationExample {
        component_id: Some(atom.id.clone()),
        path: Some("atoms[].kind".to_string()),
        source: Some(atom.kind.clone()),
        target: Some(vocabulary_ref.to_string()),
        evidence: Some("declared AAT atom vocabulary does not contain this token".to_string()),
    }));
    let mut check = check_from_examples(
        "archmap-schema052-atom-kind-vocabulary",
        "ATOMS_WITHIN_DECLARED_VOCABULARY: atom kinds are members of aat-atom-vocabulary/v1",
        examples,
    );
    check.metric = Some(vocabulary_ref.to_string());
    if check.result == "fail" {
        check.reason = Some(match (unknown_atoms.is_empty(), missing_components.is_empty()) {
            (false, true) => {
                "declared AAT atom vocabulary does not contain one or more atom kind tokens"
                    .to_string()
            }
            (true, false) => {
                "fixed AAT canonical doctrine does not resolve the declared atom vocabulary"
                    .to_string()
            }
            (false, false) => {
                "declared AAT atom vocabulary does not contain one or more atom kind tokens and the fixed AAT canonical doctrine does not resolve the vocabulary"
                    .to_string()
            }
            (true, true) => unreachable!("failed vocabulary check must have examples"),
        });
    }
    check
}

fn check_archmap_v2_atom_axis_predicate_vocabulary(
    document: &ArchMapDocumentV2,
) -> ValidationCheck {
    let vocabulary = static_aat_atom_vocabulary_v1();
    let allowed_pairs = vocabulary
        .axis_predicate_pairs
        .iter()
        .map(|pair| {
            (
                pair.axis.as_str(),
                pair.predicates
                    .iter()
                    .map(String::as_str)
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let allowed_non_ag_axes = vocabulary
        .allowed_non_ag_observation_axes
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for atom in &document.atoms {
        let Some(predicates) = allowed_pairs.get(atom.axis.as_str()) else {
            if !allowed_non_ag_axes.contains(atom.axis.as_str()) {
                examples.push(generic_validation_example(
                    &atom.id,
                    &atom.axis,
                    "ArchMap v2 atom axis must be in the compiled observation-axis vocabulary",
                ));
            } else if atom.predicate.as_deref().is_none_or(|predicate| {
                !canonical_non_ag_observation_predicate(atom.axis.as_str(), predicate)
            }) {
                examples.push(generic_validation_example(
                    &atom.id,
                    &format!(
                        "{}/{}",
                        atom.axis,
                        atom.predicate.as_deref().unwrap_or("<missing>")
                    ),
                    "ArchMap v2 non-AG atom axis/predicate pair must be in the compiled observation vocabulary",
                ));
            }
            continue;
        };
        let Some(predicate) = atom.predicate.as_deref() else {
            examples.push(generic_validation_example(
                &atom.id,
                "predicate",
                "ArchMap v2 atom predicate is required for a vocabulary-bound axis",
            ));
            continue;
        };
        if !predicates.contains(predicate) {
            examples.push(generic_validation_example(
                &atom.id,
                &format!("{}/{}", atom.axis, predicate),
                "ArchMap v2 atom axis/predicate pair must be in the compiled AAT AG measurement vocabulary",
            ));
        }
    }
    let mut check = check_from_examples(
        "archmap-schema052-atom-axis-predicate-vocabulary",
        "ArchMap v2 atom axis/predicate pairs are members of the compiled AAT AG measurement vocabulary",
        examples,
    );
    check.metric = Some(vocabulary.vocabulary_id);
    check
}

fn canonical_non_ag_observation_predicate(axis: &str, predicate: &str) -> bool {
    match axis {
        "application" => matches!(
            predicate,
            "authorizesPayment"
                | "evaluatesPolicyCatalog"
                | "placesOrder"
                | "plansShipment"
                | "reservesInventory"
        ),
        "boundary" => matches!(
            predicate,
            "catalogLookupBoundary"
                | "inventoryReservationBoundary"
                | "paymentAuthorizationBoundary"
                | "policyRuleCatalogBoundary"
        ),
        "cover" => predicate == "coSelectedInCover",
        "dataflow" => matches!(
            predicate,
            "appendsDomainEvent"
                | "booksCaptureFor"
                | "booksPricedOrderFrom"
                | "createsShipmentPlan"
                | "decrementsAvailableInventory"
                | "recordsAuthorization"
        ),
        "effect" => predicate == "effect",
        "restriction" => predicate == "dependsOn",
        "runtime" => matches!(
            predicate,
            "calls"
                | "component"
                | "concurrentReservationTrace"
                | "demoCheckoutTrace"
                | "presentsArchSigDemo"
        ),
        "semantic" => matches!(
            predicate,
            "commerceFulfillmentWorkflow"
                | "policyRuleSpecCatalog"
                | "reads"
                | "reconciliationResidue"
        ),
        "specification" => matches!(
            predicate,
            "authorizationKeyedByOrderId"
                | "hazmatUsesGroundCarrier"
                | "platformBoundIncludesPorts"
                | "rejectsEmptyOrder"
                | "requiresPositiveQuantity"
                | "reservationCarriesWarehouse"
        ),
        "state" => matches!(
            predicate,
            "OrderStatus" | "PaymentStatus" | "ReservationStatus" | "ShipmentStatus"
        ),
        "static" => matches!(
            predicate,
            "component"
                | "dependsOn"
                | "implements"
                | "tripleOverlapWitness"
                | "quadrupleOverlapWitness"
        ),
        _ => false,
    }
}

fn check_archmap_v2_atom_shapes(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        if atom.subject.trim().is_empty() {
            examples.push(generic_validation_example(
                &atom.id,
                "subject",
                "ArchMap v2 atom subject is required",
            ));
        }
        if atom.axis.trim().is_empty() {
            examples.push(generic_validation_example(
                &atom.id,
                "axis",
                "ArchMap v2 atom axis decoration is required",
            ));
        }
        append_source_ref_validation_examples(
            &mut examples,
            document,
            &atom.id,
            &atom.refs,
            "atom refs[]",
        );
    }
    check_from_examples(
        "archmap-schema052-atom-subject-axis-refs",
        "atoms carry subject / axis decorations and source refs resolve",
        examples,
    )
}

fn check_archmap_v2_contexts(document: &ArchMapDocumentV2) -> ValidationCheck {
    let atom_ids = document
        .atoms
        .iter()
        .map(|atom| atom.id.as_str())
        .collect::<BTreeSet<_>>();
    let context_ids = document
        .contexts
        .iter()
        .map(|context| context.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    examples.extend(
        duplicates(document.contexts.iter().map(|context| context.id.as_str()))
            .into_iter()
            .map(|duplicate| {
                generic_validation_example("contexts[].id", &duplicate, "context id must be unique")
            }),
    );
    for context in &document.contexts {
        if context.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "contexts[].id",
                "empty",
                "context id must be non-empty",
            ));
        }
        if context.atoms.is_empty() {
            examples.push(generic_validation_example(
                &context.id,
                "atoms",
                "context must observe an explicit atom subfamily",
            ));
        }
        for atom_ref in &context.atoms {
            if !atom_ids.contains(atom_ref.as_str()) {
                examples.push(generic_validation_example(
                    &context.id,
                    atom_ref,
                    "context atom ref must resolve to atoms",
                ));
            }
        }
        for context_ref in &context.restricts_to {
            if !context_ids.contains(context_ref.as_str()) {
                examples.push(generic_validation_example(
                    &context.id,
                    context_ref,
                    "context restriction target must resolve to contexts",
                ));
            }
            if context_ref == &context.id {
                examples.push(generic_validation_example(
                    &context.id,
                    context_ref,
                    "context restriction must be irreflexive in primary input",
                ));
            }
        }
        append_source_ref_validation_examples(
            &mut examples,
            document,
            &context.id,
            &context.refs,
            "context refs[]",
        );
    }
    let graph = document
        .contexts
        .iter()
        .map(|context| (context.id.as_str(), context.restricts_to.as_slice()))
        .collect::<BTreeMap<_, _>>();
    for context_id in graph.keys() {
        let mut path = Vec::new();
        if restriction_cycle_reaches(context_id, context_id, &graph, &mut path) {
            examples.push(generic_validation_example(
                "contexts[].restrictsTo",
                context_id,
                "context restriction relation must be acyclic to define a finite poset",
            ));
        }
    }
    check_from_examples(
        "archmap-schema052-context-poset-refs",
        "contexts form a finite source-grounded poset over atom subfamilies",
        examples,
    )
}

fn restriction_cycle_reaches<'a>(
    start: &'a str,
    current: &'a str,
    graph: &BTreeMap<&'a str, &'a [String]>,
    path: &mut Vec<&'a str>,
) -> bool {
    if path.contains(&current) {
        return false;
    }
    path.push(current);
    let reaches_start = graph.get(current).is_some_and(|targets| {
        targets
            .iter()
            .any(|target| target == start || restriction_cycle_reaches(start, target, graph, path))
    });
    path.pop();
    reaches_start
}

fn check_archmap_v2_covers(document: &ArchMapDocumentV2) -> ValidationCheck {
    let context_ids = document
        .contexts
        .iter()
        .map(|context| context.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    examples.extend(
        duplicates(document.covers.iter().map(|cover| cover.id.as_str()))
            .into_iter()
            .map(|duplicate| {
                generic_validation_example("covers[].id", &duplicate, "cover id must be unique")
            }),
    );
    for cover in &document.covers {
        if cover.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "covers[].id",
                "empty",
                "cover id must be non-empty",
            ));
        }
        if cover.contexts.is_empty() {
            examples.push(generic_validation_example(
                &cover.id,
                "contexts",
                "cover must select a finite context family",
            ));
        }
        for context_ref in &cover.contexts {
            if !context_ids.contains(context_ref.as_str()) {
                examples.push(generic_validation_example(
                    &cover.id,
                    context_ref,
                    "cover context ref must resolve to contexts",
                ));
            }
        }
        append_source_ref_validation_examples(
            &mut examples,
            document,
            &cover.id,
            &cover.refs,
            "cover refs[]",
        );
    }
    check_from_examples(
        "archmap-schema052-cover-refs",
        "covers select finite source-grounded context families",
        examples,
    )
}

fn append_source_ref_validation_examples(
    examples: &mut Vec<ValidationExample>,
    document: &ArchMapDocumentV2,
    owner: &str,
    refs: &[String],
    field: &str,
) {
    if refs.is_empty() {
        examples.push(generic_validation_example(
            owner,
            field,
            "observation rows must carry at least one source ref",
        ));
        return;
    }
    let mut seen = BTreeSet::new();
    for source_ref in refs {
        if source_ref.trim().is_empty() {
            examples.push(generic_validation_example(
                owner,
                field,
                "source refs must be non-empty strings",
            ));
        }
        if !seen.insert(source_ref.as_str()) {
            examples.push(generic_validation_example(
                owner,
                source_ref,
                "source refs must be unique within an observation row",
            ));
        }
        if !source_ref_resolves(document, source_ref) {
            examples.push(generic_validation_example(
                owner,
                source_ref,
                "source refs[] entry must resolve to sources",
            ));
        }
    }
}

fn check_from_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_aat_atom_vocabulary_has_provenance_refs() {
        let vocabulary = static_aat_atom_vocabulary_v1();
        let expected_kinds = [
            "component",
            "relation",
            "capability",
            "state",
            "effect",
            "authority",
            "contract",
            "semantic",
            "runtime",
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        let actual_kinds = vocabulary
            .entries
            .iter()
            .map(|entry| entry.kind.as_str())
            .collect::<BTreeSet<_>>();

        assert_eq!(vocabulary.schema, AAT_ATOM_VOCABULARY_V1_SCHEMA);
        assert_eq!(vocabulary.doctrine_ref, "aat-theory:atom-vocabulary");
        assert_eq!(actual_kinds, expected_kinds);
        assert_eq!(
            vocabulary.required_doctrine_components,
            ["V", "Gamma", "R", "rho", "E", "N"]
        );
        assert_eq!(
            vocabulary.allowed_non_ag_observation_axes,
            [
                "application",
                "boundary",
                "cover",
                "dataflow",
                "effect",
                "restriction",
                "runtime",
                "semantic",
                "specification",
                "state",
                "static",
            ]
        );
        assert!(vocabulary.entries.iter().all(|entry| {
            entry.doctrine_ref == "aat-theory:atom-vocabulary"
                && entry.provenance_ref == "aat-theory:atom-vocabulary"
        }));
        assert!(
            vocabulary
                .axis_predicate_pairs
                .iter()
                .all(|pair| { pair.provenance_ref == "aat-theory:atom-vocabulary" })
        );
        assert!(
            vocabulary
                .non_conclusions
                .iter()
                .any(|text| text.contains("token membership under the compiled AAT doctrine"))
        );
        assert!(
            vocabulary
                .non_conclusions
                .iter()
                .any(|text| text.contains("canonical observation pairs"))
        );
        let expected_pairs = BTreeMap::from([
            (
                "boundary-residue".to_string(),
                BTreeSet::from([
                    "boundarySection".to_string(),
                    "patchClassification".to_string(),
                    "patchRole".to_string(),
                    "restrictionColumn".to_string(),
                ]),
            ),
            (
                "cech".to_string(),
                BTreeSet::from([
                    "cocycleValue".to_string(),
                    "restrictionSurjectivityWitness".to_string(),
                    "sectionValue".to_string(),
                ]),
            ),
            (
                "coherence".to_string(),
                BTreeSet::from([
                    "coherenceSection".to_string(),
                    "h2Section".to_string(),
                    "tripleSection".to_string(),
                ]),
            ),
            (
                "laplacian".to_string(),
                BTreeSet::from([
                    "cellularBoundary".to_string(),
                    "cellularCochain".to_string(),
                ]),
            ),
            (
                "period".to_string(),
                BTreeSet::from([
                    "boundaryPeriod".to_string(),
                    "dOmegaIntegral".to_string(),
                    "periodIntegral".to_string(),
                ]),
            ),
            (
                "restriction-compatibility".to_string(),
                BTreeSet::from(["restrictionIdealGenerator".to_string()]),
            ),
            (
                "section-factorization".to_string(),
                BTreeSet::from([
                    "cooccurrence".to_string(),
                    "selectedSection".to_string(),
                    "support".to_string(),
                    "witnessAssignment".to_string(),
                ]),
            ),
            (
                "square-free".to_string(),
                BTreeSet::from(["cooccurrence".to_string(), "support".to_string()]),
            ),
            (
                "tor".to_string(),
                BTreeSet::from(["commonAmbient".to_string(), "lawIdealGenerator".to_string()]),
            ),
            (
                "transfer".to_string(),
                BTreeSet::from([
                    "groundCost".to_string(),
                    "repairPath".to_string(),
                    "transferPairing".to_string(),
                ]),
            ),
        ]);
        let actual_pairs = vocabulary
            .axis_predicate_pairs
            .iter()
            .map(|pair| {
                (
                    pair.axis.clone(),
                    pair.predicates.iter().cloned().collect::<BTreeSet<_>>(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(actual_pairs, expected_pairs);
        assert!(serde_json::to_value(&vocabulary).is_ok());
    }

    #[test]
    fn archmap_input_rejects_unknown_axis_predicate_pairs() {
        let document: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("canonical ArchMap fixture parses");
        let valid_report = validate_archmap_v2_report(&document, "fixture:archmap_v2.json");
        assert_eq!(
            valid_report
                .checks
                .iter()
                .find(|check| check.id == "archmap-schema052-atom-axis-predicate-vocabulary")
                .expect("axis/predicate check exists")
                .result,
            "pass"
        );

        let mut invalid_pair = document.clone();
        invalid_pair.atoms[0].axis = "cech".to_string();
        invalid_pair.atoms[0].predicate = Some("unregisteredPredicate".to_string());
        let invalid_pair_report =
            validate_archmap_v2_report(&invalid_pair, "fixture:invalid-pair.json");
        let invalid_pair_check = invalid_pair_report
            .checks
            .iter()
            .find(|check| check.id == "archmap-schema052-atom-axis-predicate-vocabulary")
            .expect("axis/predicate check exists");
        assert_eq!(invalid_pair_check.result, "fail");
        assert!(
            invalid_pair_check
                .examples
                .iter()
                .any(|example| example.target.as_deref() == Some("cech/unregisteredPredicate"))
        );

        let mut invalid_axis = document;
        invalid_axis.atoms[0].axis = "unregistered-axis".to_string();
        invalid_axis.atoms[0].predicate = Some("component".to_string());
        let invalid_axis_report =
            validate_archmap_v2_report(&invalid_axis, "fixture:invalid-axis.json");
        let invalid_axis_check = invalid_axis_report
            .checks
            .iter()
            .find(|check| check.id == "archmap-schema052-atom-axis-predicate-vocabulary")
            .expect("axis/predicate check exists");
        assert_eq!(invalid_axis_check.result, "fail");
        assert!(
            invalid_axis_check
                .examples
                .iter()
                .any(|example| example.target.as_deref() == Some("unregistered-axis"))
        );
    }

    #[test]
    fn archmap_input_requires_source_grounded_observation_rows() {
        let document: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("canonical ArchMap fixture parses");

        let mut invalid = document.clone();
        invalid.atoms[0].refs.clear();
        invalid.contexts[0].refs = vec!["src:checkout".to_string(), "src:checkout".to_string()];
        invalid.covers[0].refs.clear();
        let report = validate_archmap_v2_report(&invalid, "fixture:invalid-source-grounding.json");

        for check_id in [
            "archmap-schema052-atom-subject-axis-refs",
            "archmap-schema052-context-poset-refs",
            "archmap-schema052-cover-refs",
        ] {
            assert_eq!(
                report
                    .checks
                    .iter()
                    .find(|check| check.id == check_id)
                    .expect("source-grounding check exists")
                    .result,
                "fail",
                "{check_id} must reject absent or duplicate refs"
            );
        }
    }

    #[test]
    fn archmap_input_requires_a_source_locator_on_every_source_record() {
        let document: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("canonical ArchMap fixture parses");
        let mut invalid = document;
        let source = invalid
            .sources
            .get_mut("src:order")
            .expect("fixture source exists");
        source.path = None;
        source.symbol = None;
        source.section = None;
        source.trace_id = None;

        let report = validate_archmap_v2_report(&invalid, "fixture:invalid-source-locator.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.id == "archmap-schema052-sources-resolve")
            .expect("source check exists");
        assert_eq!(check.result, "fail");
        assert!(check.examples.iter().any(|example| {
            example.source.as_deref() == Some("sources")
                && example.target.as_deref() == Some("src:order")
                && example
                    .evidence
                    .as_deref()
                    .is_some_and(|reason| reason.contains("locator"))
        }));
    }

    #[test]
    fn non_ag_observation_predicates_cannot_pre_author_safety_conclusions() {
        let document: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("canonical ArchMap fixture parses");
        let mut invalid = document;
        invalid.atoms[0].axis = "runtime".to_string();
        invalid.atoms[0].predicate = Some("globalSafety".to_string());
        let report = validate_archmap_v2_report(&invalid, "fixture:invalid-safety-label.json");

        assert_eq!(
            report
                .checks
                .iter()
                .find(|check| check.id == "archmap-schema052-no-diagnostic-shortcuts")
                .expect("diagnostic shortcut check exists")
                .result,
            "fail"
        );
    }
}
