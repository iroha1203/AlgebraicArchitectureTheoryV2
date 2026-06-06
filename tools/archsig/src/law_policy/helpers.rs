use std::collections::BTreeSet;

use crate::validation::{generic_validation_example, validation_check};
use crate::{ValidationCheck, ValidationExample};
pub(super) fn check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<ValidationExample>,
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
    check.count = Some(examples.len());
    check.examples = examples;
    check
}

pub(super) fn duplicate_examples(field: &str, duplicates: Vec<String>) -> Vec<ValidationExample> {
    duplicates
        .into_iter()
        .map(|id| generic_validation_example(field, &id, "duplicate id"))
        .collect()
}

pub(super) fn push_blank(examples: &mut Vec<ValidationExample>, field: &str, value: &str) {
    if value.trim().is_empty() {
        examples.push(generic_validation_example(
            field,
            value,
            "field must be non-empty",
        ));
    }
}

pub(super) fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

pub(super) fn set<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

pub(super) fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}
