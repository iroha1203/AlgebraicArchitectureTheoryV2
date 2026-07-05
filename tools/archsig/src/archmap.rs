use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AAT_ATOM_VOCABULARY_V1_SCHEMA, ARCHMAP_V2_SCHEMA, AatAtomVocabularyEntryV1,
    AatAtomVocabularyV1, ArchMapDocumentV2, ArchMapValidationReportV2, ArchMapValidationSummaryV2,
    ValidationCheck, ValidationExample, canonical_archmap_extraction_doctrine_ref_v2,
};

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
        check_archmap_v2_atom_ids(document),
        check_archmap_v2_no_diagnostic_shortcuts(document),
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
        schema_version: "archmap-validation-report/v0.5.0".to_string(),
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
        non_conclusions: vec![
            "AAT atom vocabulary is an artifact-side authoring contract; it does not prove source extraction soundness or semantic correctness.".to_string(),
            "Vocabulary lint checks token membership only and does not decide whether a new atom kind should be added to the doctrine.".to_string(),
        ],
    }
}

fn check_archmap_v2_schema(schema: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-schema050-schema",
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
        "archmap-schema050-extraction-doctrine-ref",
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
        "archmap-schema050-sources-resolve",
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
        "archmap-schema050-atom-ids",
        "atom ids are non-empty and unique",
        examples,
    )
}

fn check_archmap_v2_no_diagnostic_shortcuts(document: &ArchMapDocumentV2) -> ValidationCheck {
    let mut examples = Vec::new();
    for atom in &document.atoms {
        if let Some(token) = diagnostic_shortcut_token(&atom.id) {
            examples.push(generic_validation_example(
                &atom.id,
                &format!("id:{token}"),
                "ArchMap v2 atom ids must not pre-author diagnostic conclusions",
            ));
        }
        if let Some(predicate) = atom.predicate.as_deref() {
            if let Some(token) = diagnostic_shortcut_token(predicate) {
                examples.push(generic_validation_example(
                    &atom.id,
                    &format!("predicate:{token}"),
                    "ArchMap v2 atom predicates must stay observational; diagnostic conclusions belong to ArchSig",
                ));
            }
        }
    }
    check_from_examples(
        "archmap-schema050-no-diagnostic-shortcuts",
        "ArchMap v2 atom id / predicate fields do not pre-author diagnostic conclusions",
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
        "archmap-schema050-atom-kind-vocabulary",
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
        "archmap-schema050-atom-subject-axis-refs",
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
        "archmap-schema050-context-poset-refs",
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
        "archmap-schema050-cover-refs",
        "covers select finite source-grounded context families",
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
        assert!(vocabulary.entries.iter().all(|entry| {
            entry.doctrine_ref == "aat-theory:atom-vocabulary"
                && entry.provenance_ref == "aat-theory:atom-vocabulary"
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
