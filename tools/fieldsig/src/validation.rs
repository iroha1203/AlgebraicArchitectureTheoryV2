use std::collections::BTreeMap;

use crate::{ValidationCheck, ValidationExample};

pub(crate) fn count_checks(checks: &[ValidationCheck], result: &str) -> usize {
    checks.iter().filter(|check| check.result == result).count()
}

pub(crate) fn validation_check(id: &str, title: &str, result: &str) -> ValidationCheck {
    ValidationCheck {
        id: id.to_string(),
        title: title.to_string(),
        result: result.to_string(),
        reason: None,
        count: None,
        examples: Vec::new(),
        metric: None,
        lean_boundary: None,
    }
}

pub(crate) fn generic_validation_example(
    source: &str,
    target: &str,
    evidence: &str,
) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(source.to_string()),
        target: Some(target.to_string()),
        evidence: Some(evidence.to_string()),
    }
}

pub(crate) fn duplicates<'a>(values: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
        .into_iter()
        .filter_map(|(value, count)| (count > 1).then(|| value.to_string()))
        .collect()
}
