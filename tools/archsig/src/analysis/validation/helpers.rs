fn check_from_examples(
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

fn count_check_kind(checks: &[ValidationCheck], kind: &str) -> usize {
    checks
        .iter()
        .filter(|check| check.id.contains(kind) || check.title.contains(kind))
        .count()
}

fn duplicate_examples(field: &str, duplicates: Vec<String>) -> Vec<ValidationExample> {
    duplicates
        .into_iter()
        .map(|id| generic_validation_example(field, &id, "duplicate id"))
        .collect()
}

fn push_blank(examples: &mut Vec<ValidationExample>, field: &str, value: &str) {
    if value.trim().is_empty() {
        examples.push(generic_validation_example(
            field,
            value,
            "field must be non-empty",
        ));
    }
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn set<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}
