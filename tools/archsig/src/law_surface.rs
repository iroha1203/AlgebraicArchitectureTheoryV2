use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{ValidationCheck, ValidationExample};

pub const LAW_EQUATION_SURFACE_V1_SCHEMA: &str = "law-equation-surface/v0.5.1";
pub const LAW_EQUATION_SURFACE_VALIDATION_REPORT_SCHEMA: &str =
    "law-equation-surface-validation-report/v0.5.1";
pub const LAW_SURFACE_BINDING_VOCABULARY_SCHEMA: &str = "aat-atom-vocabulary-binding/v0.5.1";

const CONDITION_TYPES: [&str; 6] = [
    "closed-equational",
    "open",
    "constructible",
    "descent",
    "temporal",
    "stacky",
];

const CONCLUSION_TOKENS: [&str; 14] = [
    "boundary",
    "certificate",
    "globalcoherent",
    "h1zero",
    "lawful",
    "mismatch",
    "minimalforbiddensupports",
    "measurednonzero",
    "measuredzero",
    "nsdepth",
    "nonzero",
    "obstruction",
    "verdict",
    "violation",
];

const BINDING_AXES: [&str; 3] = ["cech", "square-free", "section-factorization"];
const BINDING_PREDICATES: [&str; 3] = ["support", "cooccurrence", "sectionValue"];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawEquationSurfaceV1 {
    pub schema: String,
    pub id: String,
    #[serde(default)]
    pub laws: Vec<LawEquationV1>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub skeleton: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub defect_sources: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quotient_sheaf_condition: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawEquationV1 {
    pub law_id: String,
    pub condition_type: String,
    #[serde(default)]
    pub witness_variables: Vec<LawWitnessVariableV1>,
    #[serde(default)]
    pub forbidden_support_generators: Vec<LawForbiddenSupportGeneratorV1>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evaluator_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawWitnessVariableV1 {
    pub variable: String,
    pub binding: LawBindingV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawBindingV1 {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub archmap_variable: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub edge: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub axis: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub predicate: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawForbiddenSupportGeneratorV1 {
    pub support: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawSurfaceBindingVocabularyV1 {
    pub schema: String,
    pub id: String,
    pub axes: Vec<String>,
    pub predicates: Vec<String>,
    pub axis_predicate_pairs: Vec<LawSurfaceBindingPairV1>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LawSurfaceBindingPairV1 {
    pub axis: String,
    pub predicates: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawSurfaceValidationReportV1 {
    #[serde(rename = "schema")]
    pub schema_version: String,
    pub input: LawSurfaceValidationInputV1,
    pub checks: Vec<ValidationCheck>,
    pub summary: LawSurfaceValidationSummaryV1,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawSurfaceValidationInputV1 {
    pub schema: String,
    pub path: String,
    pub id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawSurfaceValidationSummaryV1 {
    pub result: String,
    pub law_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

pub fn static_law_surface_binding_vocabulary_v1() -> LawSurfaceBindingVocabularyV1 {
    crate::archmap::static_aat_atom_binding_vocabulary_v1()
}

pub fn validate_law_surface_v1_report(
    surface: &LawEquationSurfaceV1,
    raw: &Value,
    input_path: &str,
) -> LawSurfaceValidationReportV1 {
    let vocabulary = static_law_surface_binding_vocabulary_v1();
    let mut checks = vec![
        check_schema(surface),
        check_identity(surface),
        check_law_ids(surface),
        check_condition_types(surface),
        check_evaluator_refs(surface),
        check_shape_rules(surface, raw),
        check_bindings(surface, &vocabulary, raw),
        check_forbidden_supports(surface),
        check_reserved_fields(raw),
        check_conclusion_tokens(surface),
    ];
    checks.push(check_vocabulary(&vocabulary));

    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    LawSurfaceValidationReportV1 {
        schema_version: LAW_EQUATION_SURFACE_VALIDATION_REPORT_SCHEMA.to_string(),
        input: LawSurfaceValidationInputV1 {
            schema: surface.schema.clone(),
            path: input_path.to_string(),
            id: surface.id.clone(),
        },
        checks,
        summary: LawSurfaceValidationSummaryV1 {
            result: result.to_string(),
            law_count: surface.laws.len(),
            failed_check_count,
            warning_check_count,
        },
    }
}

fn check_schema(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut check = validation_check(
        "law-equation-surface-v051-schema",
        "law-equation-surface uses the v0.5.1 schema discriminator",
        if surface.schema == LAW_EQUATION_SURFACE_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "expected {LAW_EQUATION_SURFACE_V1_SCHEMA}, found {}",
            surface.schema
        ));
    }
    check
}

fn check_identity(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if surface.id.trim().is_empty() {
        examples.push(generic_validation_example(
            "id",
            "empty",
            "law-equation-surface id must be non-empty",
        ));
    }
    if surface.laws.is_empty() {
        examples.push(generic_validation_example(
            "laws",
            "empty",
            "law-equation-surface must declare at least one law",
        ));
    }
    check_examples(
        "law-equation-surface-v051-identity",
        "surface identity and law declarations are present",
        examples,
    )
}

fn check_law_ids(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut seen = BTreeSet::new();
    let mut examples = Vec::new();
    for (index, law) in surface.laws.iter().enumerate() {
        if law.law_id.trim().is_empty() {
            examples.push(generic_validation_example(
                &format!("laws[{index}].lawId"),
                "empty",
                "lawId must be non-empty",
            ));
        } else if !seen.insert(law.law_id.as_str()) {
            examples.push(generic_validation_example(
                &format!("laws[{index}].lawId"),
                &law.law_id,
                "lawId must be unique within a law surface",
            ));
        }
    }
    check_examples(
        "law-equation-surface-v051-law-ids",
        "law identifiers are non-empty and unique",
        examples,
    )
}

fn check_condition_types(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, law) in surface.laws.iter().enumerate() {
        if !CONDITION_TYPES.contains(&law.condition_type.as_str()) {
            examples.push(generic_validation_example(
                &format!("laws[{index}].conditionType"),
                &law.condition_type,
                "conditionType must be one of the six AAT law condition types",
            ));
        }
    }
    check_examples(
        "law-equation-surface-v051-condition-types",
        "conditionType uses the six declared law condition types",
        examples,
    )
}

fn check_evaluator_refs(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let registry = crate::static_law_evaluator_registry_v1();
    let mut examples = Vec::new();
    for (index, law) in surface.laws.iter().enumerate() {
        if let Some(evaluator_ref) = law.evaluator_ref.as_deref()
            && !registry
                .evaluators
                .iter()
                .any(|manifest| manifest.evaluator_id == evaluator_ref)
        {
            examples.push(generic_validation_example(
                &format!("laws[{index}].evaluatorRef"),
                evaluator_ref,
                "evaluatorRef must resolve to the versioned law evaluator registry",
            ));
        }
    }
    check_examples(
        "law-equation-surface-v051-evaluator-refs",
        "non-closed evaluator references resolve through the law evaluator registry",
        examples,
    )
}

fn check_shape_rules(surface: &LawEquationSurfaceV1, raw: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, law) in surface.laws.iter().enumerate() {
        match law.condition_type.as_str() {
            "closed-equational" => {
                if law.witness_variables.is_empty() {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].witnessVariables"),
                        "empty",
                        "closed-equational law requires witnessVariables",
                    ));
                }
                if law.forbidden_support_generators.is_empty() {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].forbiddenSupportGenerators"),
                        "empty",
                        "closed-equational law requires forbiddenSupportGenerators",
                    ));
                }
                if raw_law_field_is_present(raw, index, "evaluatorRef") {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].evaluatorRef"),
                        "present",
                        "closed-equational law cannot delegate equation supply to evaluatorRef",
                    ));
                }
            }
            "open" | "constructible" | "descent" | "temporal" | "stacky" => {
                if law.evaluator_ref.as_deref().unwrap_or("").trim().is_empty() {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].evaluatorRef"),
                        "missing",
                        "non-closed law requires evaluatorRef",
                    ));
                }
                if raw_law_field_is_present(raw, index, "witnessVariables") {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].witnessVariables"),
                        "present",
                        "ideal fields are reserved for closed-equational laws",
                    ));
                }
                if raw_law_field_is_present(raw, index, "forbiddenSupportGenerators") {
                    examples.push(generic_validation_example(
                        &format!("laws[{index}].forbiddenSupportGenerators"),
                        "present",
                        "ideal fields are reserved for closed-equational laws",
                    ));
                }
            }
            _ => {}
        }
    }
    check_examples(
        "law-equation-surface-v051-shape-rules",
        "conditionType controls equation-surface fields",
        examples,
    )
}

fn check_bindings(
    surface: &LawEquationSurfaceV1,
    vocabulary: &LawSurfaceBindingVocabularyV1,
    raw: &Value,
) -> ValidationCheck {
    let mut examples = Vec::new();
    for (law_index, law) in surface.laws.iter().enumerate() {
        let mut witness_names = BTreeSet::new();
        let mut effective_archmap_variables = BTreeSet::new();
        for (variable_index, variable) in law.witness_variables.iter().enumerate() {
            let path = format!("laws[{law_index}].witnessVariables[{variable_index}].binding");
            for field in ["archmapVariable", "edge", "axis", "predicate"] {
                if raw_witness_field_is_null(raw, law_index, variable_index, field) {
                    examples.push(generic_validation_example(
                        &format!("{path}.{field}"),
                        "null",
                        "binding fields must be omitted or carry a concrete value",
                    ));
                }
            }
            if variable.variable.trim().is_empty() {
                examples.push(generic_validation_example(
                    &format!("laws[{law_index}].witnessVariables[{variable_index}].variable"),
                    "empty",
                    "witness variable names must be non-empty",
                ));
            }
            if !witness_names.insert(variable.variable.as_str()) {
                examples.push(generic_validation_example(
                    &format!("laws[{law_index}].witnessVariables[{variable_index}].variable"),
                    &variable.variable,
                    "witness variable names must be unique within a law",
                ));
            }
            if variable
                .binding
                .archmap_variable
                .as_deref()
                .is_some_and(|value| value.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    &format!("{path}.archmapVariable"),
                    "empty",
                    "archmapVariable aliases must be non-empty",
                ));
            }
            let effective_archmap_variable = variable
                .binding
                .archmap_variable
                .as_deref()
                .unwrap_or(variable.variable.as_str());
            if !effective_archmap_variables.insert(effective_archmap_variable) {
                examples.push(generic_validation_example(
                    &format!("{path}.archmapVariable"),
                    effective_archmap_variable,
                    "effective ArchMap variable aliases must be unique within a law",
                ));
            }
            let Some(axis) = variable.binding.axis.as_deref() else {
                examples.push(generic_validation_example(
                    &format!("{path}.axis"),
                    "missing",
                    "binding axis is required for vocabulary resolution",
                ));
                continue;
            };
            let Some(predicate) = variable.binding.predicate.as_deref() else {
                examples.push(generic_validation_example(
                    &format!("{path}.predicate"),
                    "missing",
                    "binding predicate is required for vocabulary resolution",
                ));
                continue;
            };
            if !vocabulary.axis_predicate_pairs.iter().any(|pair| {
                pair.axis == axis && pair.predicates.iter().any(|item| item == predicate)
            }) {
                examples.push(generic_validation_example(
                    &format!("{path}.axis/predicate"),
                    &format!("{axis}/{predicate}"),
                    "binding axis/predicate pair is not declared by the shared vocabulary manifest",
                ));
            }
            match axis {
                "cech" => {
                    if variable.binding.edge.is_none() {
                        examples.push(generic_validation_example(
                            &path,
                            "missing-edge",
                            "cech bindings require an edge declaration",
                        ));
                    }
                    if let Some(edge) = &variable.binding.edge {
                        if edge.len() != 2
                            || edge.iter().any(|value| value.trim().is_empty())
                            || edge[0] == edge[1]
                        {
                            examples.push(generic_validation_example(
                                &format!("{path}.edge"),
                                "invalid",
                                "edge binding must contain two distinct non-empty context refs",
                            ));
                        }
                    }
                    if variable.binding.archmap_variable.is_some() {
                        examples.push(generic_validation_example(
                            &format!("{path}.archmapVariable"),
                            "present",
                            "cech bindings use edge declarations rather than name aliases",
                        ));
                    }
                }
                "square-free" | "section-factorization" => {
                    if let Some(edge) = &variable.binding.edge {
                        examples.push(generic_validation_example(
                            &format!("{path}.edge"),
                            "present",
                            "square-free and section-factorization bindings use variable names",
                        ));
                        if edge.len() != 2 || edge.iter().any(|value| value.trim().is_empty()) {
                            examples.push(generic_validation_example(
                                &format!("{path}.edge"),
                                "invalid",
                                "edge binding must contain exactly two non-empty context refs",
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    check_examples(
        "law-equation-surface-v051-bindings",
        "binding declarations resolve through the shared vocabulary manifest",
        examples,
    )
}

fn check_forbidden_supports(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (law_index, law) in surface.laws.iter().enumerate() {
        let declared = law
            .witness_variables
            .iter()
            .map(|variable| variable.variable.as_str())
            .collect::<BTreeSet<_>>();
        let mut supports = BTreeSet::new();
        for (support_index, generator) in law.forbidden_support_generators.iter().enumerate() {
            if generator.support.is_empty()
                || generator
                    .support
                    .iter()
                    .any(|value| value.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    &format!(
                        "laws[{law_index}].forbiddenSupportGenerators[{support_index}].support"
                    ),
                    "empty",
                    "support generators must contain non-empty variable names",
                ));
            }
            if !generator
                .support
                .iter()
                .all(|variable| declared.contains(variable.as_str()))
            {
                examples.push(generic_validation_example(
                    &format!(
                        "laws[{law_index}].forbiddenSupportGenerators[{support_index}].support"
                    ),
                    "undeclared-variable",
                    "square-free support generators may contain only declared witness variables",
                ));
            }
            let mut canonical = generator.support.clone();
            canonical.sort();
            canonical.dedup();
            if canonical.len() != generator.support.len() {
                examples.push(generic_validation_example(
                    &format!(
                        "laws[{law_index}].forbiddenSupportGenerators[{support_index}].support"
                    ),
                    "duplicate-variable",
                    "support generators must be square-free",
                ));
            }
            if !supports.insert(canonical) {
                examples.push(generic_validation_example(
                    &format!(
                        "laws[{law_index}].forbiddenSupportGenerators[{support_index}].support"
                    ),
                    "duplicate-generator",
                    "forbidden support generators must be unique",
                ));
            }
        }
    }
    check_examples(
        "law-equation-surface-v051-support-generators",
        "forbidden support generators are square-free declarations over witness variables",
        examples,
    )
}

fn check_reserved_fields(raw: &Value) -> ValidationCheck {
    let mut examples = Vec::new();
    for field in ["skeleton", "defectSources", "quotientSheafCondition"] {
        if raw.get(field).is_some() {
            examples.push(generic_validation_example(
                field,
                "present",
                "Stage 3 reservation is declared but unsupported and must fail closed",
            ));
        }
    }
    check_examples(
        "law-equation-surface-v051-reserved-fields",
        "Stage 3 reservation fields fail closed when written",
        examples,
    )
}

fn check_conclusion_tokens(surface: &LawEquationSurfaceV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (law_index, law) in surface.laws.iter().enumerate() {
        let mut candidates = vec![("lawId".to_string(), law.law_id.as_str())];
        for (variable_index, variable) in law.witness_variables.iter().enumerate() {
            candidates.push((
                format!("laws[{law_index}].witnessVariables[{variable_index}].variable"),
                variable.variable.as_str(),
            ));
            if let Some(alias) = variable.binding.archmap_variable.as_deref() {
                candidates.push((
                    format!(
                        "laws[{law_index}].witnessVariables[{variable_index}].binding.archmapVariable"
                    ),
                    alias,
                ));
            }
        }
        for (field, value) in candidates {
            for token in CONCLUSION_TOKENS {
                if normalized_identifier_contains(value, token) {
                    examples.push(generic_validation_example(
                        &field,
                        value,
                        "witness variable names must not encode evaluator conclusions",
                    ));
                }
            }
        }
    }
    check_examples(
        "law-equation-surface-v051-no-conclusion-shortcuts",
        "law identifiers and witness variable names contain no conclusion shortcuts",
        examples,
    )
}

fn check_vocabulary(vocabulary: &LawSurfaceBindingVocabularyV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if vocabulary.schema != LAW_SURFACE_BINDING_VOCABULARY_SCHEMA {
        examples.push(generic_validation_example(
            "bindingVocabulary.schema",
            &vocabulary.schema,
            "binding vocabulary must use the v0.5.1 manifest",
        ));
    }
    if vocabulary.axes.is_empty()
        || vocabulary.predicates.is_empty()
        || vocabulary.axis_predicate_pairs.is_empty()
    {
        examples.push(generic_validation_example(
            "bindingVocabulary",
            "empty",
            "binding vocabulary must declare axes and predicates",
        ));
    }
    for axis in BINDING_AXES {
        if !vocabulary.axes.iter().any(|item| item == axis) {
            examples.push(generic_validation_example(
                "bindingVocabulary.axes",
                axis,
                "the shared AAT atom vocabulary manifest must retain every Stage 2 axis",
            ));
        }
    }
    for predicate in BINDING_PREDICATES {
        if !vocabulary.predicates.iter().any(|item| item == predicate) {
            examples.push(generic_validation_example(
                "bindingVocabulary.predicates",
                predicate,
                "the shared AAT atom vocabulary manifest must retain every Stage 2 predicate",
            ));
        }
    }
    for axis in &vocabulary.axes {
        if !BINDING_AXES.contains(&axis.as_str()) {
            examples.push(generic_validation_example(
                "bindingVocabulary.axes",
                axis,
                "binding vocabulary contains an axis outside the Stage 2 contract",
            ));
        }
    }
    for predicate in &vocabulary.predicates {
        if !BINDING_PREDICATES.contains(&predicate.as_str()) {
            examples.push(generic_validation_example(
                "bindingVocabulary.predicates",
                predicate,
                "binding vocabulary contains a predicate outside the Stage 2 contract",
            ));
        }
    }
    let mut pairs = BTreeSet::new();
    for pair in &vocabulary.axis_predicate_pairs {
        if !BINDING_AXES.contains(&pair.axis.as_str()) {
            examples.push(generic_validation_example(
                "bindingVocabulary.axisPredicatePairs[].axis",
                &pair.axis,
                "binding pair axis is outside the Stage 2 contract",
            ));
        }
        for predicate in &pair.predicates {
            if !BINDING_PREDICATES.contains(&predicate.as_str()) {
                examples.push(generic_validation_example(
                    "bindingVocabulary.axisPredicatePairs[].predicates[]",
                    predicate,
                    "binding pair predicate is outside the Stage 2 contract",
                ));
            }
            if !pairs.insert((pair.axis.as_str(), predicate.as_str())) {
                examples.push(generic_validation_example(
                    "bindingVocabulary.axisPredicatePairs",
                    &format!("{}/{}", pair.axis, predicate),
                    "binding axis/predicate pairs must be unique",
                ));
            }
        }
    }
    for (axis, predicate) in [
        ("cech", "sectionValue"),
        ("square-free", "support"),
        ("square-free", "cooccurrence"),
        ("section-factorization", "support"),
        ("section-factorization", "cooccurrence"),
    ] {
        if !pairs.contains(&(axis, predicate)) {
            examples.push(generic_validation_example(
                "bindingVocabulary.axisPredicatePairs",
                &format!("{axis}/{predicate}"),
                "the shared AAT atom vocabulary manifest must retain every required Stage 2 pair",
            ));
        }
    }
    check_examples(
        "law-equation-surface-v051-binding-vocabulary",
        "law surface and authoring use a non-empty versioned binding vocabulary",
        examples,
    )
}

fn raw_law_field_is_present(raw: &Value, index: usize, field: &str) -> bool {
    raw.get("laws")
        .and_then(Value::as_array)
        .and_then(|laws| laws.get(index))
        .and_then(Value::as_object)
        .is_some_and(|law| law.contains_key(field))
}

fn raw_witness_field_is_null(
    raw: &Value,
    law_index: usize,
    variable_index: usize,
    field: &str,
) -> bool {
    raw.get("laws")
        .and_then(Value::as_array)
        .and_then(|laws| laws.get(law_index))
        .and_then(|law| law.get("witnessVariables"))
        .and_then(Value::as_array)
        .and_then(|variables| variables.get(variable_index))
        .and_then(|variable| variable.get("binding"))
        .and_then(Value::as_object)
        .and_then(|binding| binding.get(field))
        .is_some_and(Value::is_null)
}

fn normalized_identifier_contains(value: &str, token: &str) -> bool {
    let segments = identifier_segments(value);
    let token = token.to_ascii_lowercase();
    if segments.iter().any(|segment| segment == &token) {
        return true;
    }
    for start in 0..segments.len() {
        let mut combined = String::new();
        for segment in segments.iter().skip(start) {
            combined.push_str(segment);
            if combined == token {
                return true;
            }
            if combined.len() > token.len() {
                break;
            }
        }
    }
    false
}

fn identifier_segments(value: &str) -> Vec<String> {
    let mut segments = Vec::new();
    let mut current = String::new();
    let mut previous_is_lowercase = false;
    for character in value.chars() {
        if !character.is_ascii_alphanumeric() {
            if !current.is_empty() {
                segments.push(std::mem::take(&mut current));
            }
            previous_is_lowercase = false;
            continue;
        }
        if character.is_ascii_uppercase() && previous_is_lowercase && !current.is_empty() {
            segments.push(std::mem::take(&mut current));
        }
        current.push(character.to_ascii_lowercase());
        previous_is_lowercase = character.is_ascii_lowercase();
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.reason = Some("one or more law-equation-surface contract checks failed".to_string());
        check.examples = examples;
    }
    check
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_manifest_rejects_unknown_fields() {
        let mut value = serde_json::to_value(static_law_surface_binding_vocabulary_v1())
            .expect("binding manifest serializes");
        value["unexpected"] = Value::Bool(true);
        assert!(serde_json::from_value::<LawSurfaceBindingVocabularyV1>(value).is_err());
    }
}
