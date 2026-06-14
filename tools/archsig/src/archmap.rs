use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION,
    ARCHMAP_V1_SCHEMA, ARCHMAP_V2_SCHEMA, ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION,
    AatAtomVocabularyEntryV1, AatAtomVocabularyV1, ArchMapAtomV1, ArchMapAtomicObservationSummary,
    ArchMapDocumentV0, ArchMapDocumentV1, ArchMapDocumentV2, ArchMapLeanPreservationChecklistEntry,
    ArchMapLeanPreservationVocabularyEntry, ArchMapSourceInventoryV0, ArchMapSourceRef,
    ArchMapValidationReportV0, ArchMapValidationReportV1, ArchMapValidationReportV2,
    ArchMapValidationSummary, ArchMapValidationSummaryV1, ArchMapValidationSummaryV2,
    ValidationCheck, ValidationExample,
};

pub struct ArchMapSourceInventoryInput<'a> {
    pub path: &'a str,
    pub document: Option<&'a ArchMapSourceInventoryV0>,
    pub read_error: Option<String>,
}

pub fn compare_archmap_v2_doctrine(
    left: &ArchMapDocumentV2,
    right: &ArchMapDocumentV2,
) -> serde_json::Value {
    if left.extraction_doctrine_ref.fingerprint == right.extraction_doctrine_ref.fingerprint {
        serde_json::json!({
            "status": "comparable",
            "reason": "same_doctrine",
            "leftDoctrine": left.extraction_doctrine_ref.doctrine_id,
            "rightDoctrine": right.extraction_doctrine_ref.doctrine_id
        })
    } else {
        serde_json::json!({
            "status": "not_comparable",
            "reason": "cross_doctrine_not_comparable",
            "leftDoctrine": left.extraction_doctrine_ref.doctrine_id,
            "rightDoctrine": right.extraction_doctrine_ref.doctrine_id
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
        check_archmap_v2_atom_ids(document),
        check_archmap_v2_atom_kind_vocabulary(document),
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
        schema_version: "archmap-validation-report-v2".to_string(),
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
            "ArchMap v2 validation checks the finite poset site observation contract; it does not prove source extraction soundness, U-adequacy, architecture lawfulness, or Lean theorem discharge.".to_string(),
            "Contexts and covers are source-grounded observations; selected measurement coefficients, witnesses, and verdict predicates belong to MeasurementProfile.".to_string(),
        ],
    }
}

pub fn static_aat_atom_vocabulary_v1() -> AatAtomVocabularyV1 {
    let doctrine_ref = "docs/aat/mathematical_theory/part_1_atoms_objects_laws.md";
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
        non_conclusions: vec![
            "AAT atom vocabulary is an artifact-side authoring contract; it does not prove source extraction soundness or semantic correctness.".to_string(),
            "Vocabulary lint checks token membership only and does not decide whether a new atom kind should be added to the doctrine.".to_string(),
        ],
    }
}

fn check_archmap_v2_schema(schema: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-v2-schema",
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
    let mut examples = Vec::new();
    if document
        .extraction_doctrine_ref
        .doctrine_id
        .trim()
        .is_empty()
    {
        examples.push(generic_validation_example(
            "extractionDoctrineRef.doctrineId",
            "empty",
            "doctrine id must be non-empty",
        ));
    }
    if document
        .extraction_doctrine_ref
        .fingerprint
        .trim()
        .is_empty()
    {
        examples.push(generic_validation_example(
            "extractionDoctrineRef.fingerprint",
            "empty",
            "doctrine fingerprint must be non-empty",
        ));
    }
    check_from_examples(
        "archmap-v2-extraction-doctrine-ref",
        "ArchMap v2 declares the extraction doctrine fingerprint used for A8-relative determinism",
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
        if source.kind.trim().is_empty() {
            examples.push(generic_validation_example(
                "sources",
                source_id,
                "source kind must be non-empty",
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
        "archmap-v2-sources-resolve",
        "sources table is present and internally resolvable",
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
        "archmap-v2-atom-ids",
        "atom ids are non-empty and unique",
        examples,
    )
}

fn check_archmap_v2_atom_kind_vocabulary(document: &ArchMapDocumentV2) -> ValidationCheck {
    let vocabulary = static_aat_atom_vocabulary_v1();
    let vocabulary_ref = vocabulary.vocabulary_id.as_str();
    let declared_components = document
        .extraction_doctrine_ref
        .components
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let missing_components = vocabulary
        .required_doctrine_components
        .iter()
        .filter(|component| !declared_components.contains(component.as_str()))
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
            component_id: Some("extractionDoctrineRef.components".to_string()),
            path: Some("extractionDoctrineRef.components".to_string()),
            source: Some(document.extraction_doctrine_ref.components.join(",")),
            target: Some(vocabulary_ref.to_string()),
            evidence: Some(format!(
                "extraction doctrine does not resolve required AAT atom vocabulary components: {}",
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
        "archmap-v2-atom-kind-vocabulary",
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
                "extraction doctrine does not resolve the declared AAT atom vocabulary"
                    .to_string()
            }
            (false, false) => {
                "declared AAT atom vocabulary does not contain one or more atom kind tokens and the extraction doctrine does not resolve the vocabulary"
                    .to_string()
            }
            (true, true) => unreachable!("failed vocabulary check must have examples"),
        });
    }
    check
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
        for source_ref in &atom.refs {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &atom.id,
                    source_ref,
                    "atom refs[] entry must resolve to sources",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-v2-atom-subject-axis-refs",
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
        for source_ref in &context.refs {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &context.id,
                    source_ref,
                    "context refs[] entry must resolve to sources",
                ));
            }
        }
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
        "archmap-v2-context-poset-refs",
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
        for source_ref in &cover.refs {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &cover.id,
                    source_ref,
                    "cover refs[] entry must resolve to sources",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-v2-cover-refs",
        "covers select finite source-grounded context families",
        examples,
    )
}

pub fn validate_archmap_v1_report(
    document: &ArchMapDocumentV1,
    input_path: &str,
) -> ArchMapValidationReportV1 {
    let checks = vec![
        check_archmap_v1_schema(&document.schema),
        check_archmap_v1_sources(document),
        check_archmap_v1_atom_ids(document),
        check_archmap_v1_atom_kinds(document),
        check_archmap_v1_atom_shapes(document),
        check_archmap_v1_atom_predicates(document),
        check_archmap_v1_atom_refs(document),
        check_archmap_v1_molecule_refs(document),
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

    ArchMapValidationReportV1 {
        schema_version: "archmap-validation-report-v1".to_string(),
        archmap_ref: input_path.to_string(),
        input_schema: document.schema.clone(),
        checks,
        summary: ArchMapValidationSummaryV1 {
            result: result.to_string(),
            source_count: document.sources.len(),
            atom_count: document.atoms.len(),
            molecule_count: document.molecules.len(),
            failed_check_count,
            warning_check_count,
        },
        non_conclusions: vec![
            "ArchMap v1 validation checks the atom map contract; it does not prove architecture lawfulness, source completeness, Lean theorem discharge, or global semantic truth.".to_string(),
            "Missing atoms remain unavailable to evaluators; they are not measured zero.".to_string(),
        ],
    }
}

fn check_archmap_v1_schema(schema: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-v1-schema",
        "ArchMap v1 uses the atom-to-AAT schema discriminator",
        if schema == ARCHMAP_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("expected {ARCHMAP_V1_SCHEMA}, found {schema}"));
    }
    check
}

fn check_archmap_v1_sources(document: &ArchMapDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if document.sources.is_empty() {
        examples.push(generic_validation_example(
            "sources",
            "empty",
            "ArchMap v1 needs a source table for atom refs and source refs",
        ));
    }
    for (source_id, source) in &document.sources {
        if source.kind.trim().is_empty() {
            examples.push(generic_validation_example(
                "sources",
                source_id,
                "source kind must be non-empty",
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
        "archmap-v1-sources-resolve",
        "sources table is present and internally resolvable",
        examples,
    )
}

fn check_archmap_v1_atom_ids(document: &ArchMapDocumentV1) -> ValidationCheck {
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
        "archmap-v1-atom-ids",
        "atom ids are non-empty and unique",
        examples,
    )
}

fn check_archmap_v1_atom_kinds(document: &ArchMapDocumentV1) -> ValidationCheck {
    let examples = document
        .atoms
        .iter()
        .filter(|atom| !is_archmap_v1_atom_kind(&atom.kind))
        .map(|atom| {
            generic_validation_example(
                &atom.id,
                &atom.kind,
                "atom kind must be in the v1 constructor vocabulary",
            )
        })
        .collect::<Vec<_>>();
    check_from_examples(
        "archmap-v1-atom-kind-vocabulary",
        "atom kinds are in the v1 constructor vocabulary",
        examples,
    )
}

fn check_archmap_v1_atom_shapes(document: &ArchMapDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        examples.extend(
            v1_atom_shape_errors(atom)
                .into_iter()
                .map(|message| generic_validation_example(&atom.id, &atom.kind, &message)),
        );
    }
    check_from_examples(
        "archmap-v1-atom-required-shapes",
        "atom constructor payloads match required v1 shapes",
        examples,
    )
}

fn check_archmap_v1_atom_predicates(document: &ArchMapDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        if let Some(predicate) = atom.predicate.as_deref() {
            if !is_known_v1_predicate(predicate) {
                examples.push(generic_validation_example(
                    &atom.id,
                    predicate,
                    "predicate must resolve to the v1 predicate vocabulary",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-v1-predicate-vocabulary",
        "atom predicates resolve to the v1 predicate vocabulary",
        examples,
    )
}

fn check_archmap_v1_atom_refs(document: &ArchMapDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        for source_ref in atom_refs(atom) {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &atom.id,
                    source_ref,
                    "atom source-bearing field must resolve to sources",
                ));
            }
        }
        for source_ref in &atom.refs {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &atom.id,
                    source_ref,
                    "atom refs[] entry must resolve to sources",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-v1-atom-refs-resolve",
        "atom source refs resolve to sources",
        examples,
    )
}

fn check_archmap_v1_molecule_refs(document: &ArchMapDocumentV1) -> ValidationCheck {
    let atom_ids = document
        .atoms
        .iter()
        .map(|atom| atom.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    examples.extend(
        duplicates(
            document
                .molecules
                .iter()
                .map(|molecule| molecule.id.as_str()),
        )
        .into_iter()
        .map(|duplicate| {
            generic_validation_example("molecules[].id", &duplicate, "molecule id must be unique")
        }),
    );
    for molecule in &document.molecules {
        if molecule.id.trim().is_empty() {
            examples.push(generic_validation_example(
                "molecules[].id",
                "empty",
                "molecule id must be non-empty",
            ));
        }
        if molecule.atoms.is_empty() {
            examples.push(generic_validation_example(
                &molecule.id,
                "atoms",
                "molecule must explicitly list atom membership",
            ));
        }
        for atom_ref in &molecule.atoms {
            if !atom_ids.contains(atom_ref.as_str()) {
                examples.push(generic_validation_example(
                    &molecule.id,
                    atom_ref,
                    "molecule atom ref must resolve to atoms",
                ));
            }
        }
        for source_ref in &molecule.refs {
            if !document.sources.contains_key(source_ref) {
                examples.push(generic_validation_example(
                    &molecule.id,
                    source_ref,
                    "molecule refs[] entry must resolve to sources",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-v1-molecule-refs-resolve",
        "molecule membership and source refs resolve",
        examples,
    )
}

fn check_from_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

fn is_archmap_v1_atom_kind(kind: &str) -> bool {
    matches!(
        kind,
        "component"
            | "relation"
            | "capability"
            | "dataState"
            | "effect"
            | "authority"
            | "contract"
            | "semantic"
            | "runtime"
    )
}

fn is_known_v1_predicate(predicate: &str) -> bool {
    matches!(
        predicate,
        "placesOrder" | "checksInventoryWith" | "dependsOn" | "implements" | "calls"
    )
}

fn v1_atom_shape_errors(atom: &ArchMapAtomV1) -> Vec<String> {
    let mut errors = Vec::new();
    match atom.kind.as_str() {
        "component" => require_one(&mut errors, atom.subject.as_deref(), "subject"),
        "relation" => {
            if atom.edge.as_deref().map_or(true, str::is_empty) {
                require_one(&mut errors, atom.subject.as_deref(), "subject");
                require_one(&mut errors, atom.object.as_deref(), "object");
                require_one(&mut errors, atom.predicate.as_deref(), "predicate");
            }
        }
        "capability" => {
            require_one(&mut errors, atom.subject.as_deref(), "subject");
            require_one(&mut errors, atom.predicate.as_deref(), "predicate");
        }
        "dataState" => {
            require_one(&mut errors, atom.diagram.as_deref(), "diagram");
            require_one(&mut errors, atom.state.as_deref(), "state");
        }
        "effect" => {
            require_one(&mut errors, atom.diagram.as_deref(), "diagram");
            require_one(&mut errors, atom.effect.as_deref(), "effect");
        }
        "authority" => {
            require_one(&mut errors, atom.subject.as_deref(), "subject");
            require_one(&mut errors, atom.authority.as_deref(), "authority");
        }
        "contract" => {
            require_one(&mut errors, atom.diagram.as_deref(), "diagram");
            require_one(&mut errors, atom.contract.as_deref(), "contract");
        }
        "semantic" => {
            require_one(&mut errors, atom.diagram.as_deref(), "diagram");
            require_one(&mut errors, atom.meaning.as_deref(), "meaning");
        }
        "runtime" => {
            require_one(&mut errors, atom.edge.as_deref(), "edge");
            require_one(&mut errors, atom.interaction.as_deref(), "interaction");
        }
        _ => {}
    }
    errors
}

fn require_one(errors: &mut Vec<String>, value: Option<&str>, field: &str) {
    if value.map_or(true, |value| value.trim().is_empty()) {
        errors.push(format!("required field `{field}` is missing or empty"));
    }
}

fn atom_refs(atom: &ArchMapAtomV1) -> Vec<&str> {
    [
        atom.subject.as_deref(),
        atom.object.as_deref(),
        atom.edge.as_deref(),
        atom.diagram.as_deref(),
    ]
    .into_iter()
    .flatten()
    .collect()
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
            .operation_square_evidence
            .iter()
            .map(|evidence| evidence.operation_square_evidence_id.as_str()),
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
    for evidence in &document.operation_square_evidence {
        refs.push((
            format!(
                "operationSquareEvidence[{}].sourceRefs",
                evidence.operation_square_evidence_id
            ),
            evidence.source_refs.as_slice(),
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
        assert_eq!(
            vocabulary.doctrine_ref,
            "docs/aat/mathematical_theory/part_1_atoms_objects_laws.md"
        );
        assert_eq!(actual_kinds, expected_kinds);
        assert_eq!(
            vocabulary.required_doctrine_components,
            ["V", "Gamma", "R", "rho", "E", "N"]
        );
        assert!(vocabulary.entries.iter().all(|entry| {
            entry.doctrine_ref == "docs/aat/mathematical_theory/part_1_atoms_objects_laws.md"
                && entry.provenance_ref
                    == "docs/aat/mathematical_theory/part_1_atoms_objects_laws.md"
        }));
        assert!(
            vocabulary
                .non_conclusions
                .iter()
                .any(|text| text.contains("token membership only"))
        );
        assert!(
            vocabulary
                .non_conclusions
                .iter()
                .any(|text| text.contains("does not prove source extraction soundness"))
        );
    }
}
