use std::collections::BTreeSet;
use std::error::Error;
use std::fs;
use std::path::Path;

use serde_json::Value;

use crate::{
    AnalysisMetadata, EmpiricalDatasetInput, PullRequestMetrics, PullRequestRef, RepositoryRef,
};

pub fn build_pr_metadata_from_github_files(
    pull_request_path: &Path,
    files_path: &Path,
    reviews_path: Option<&Path>,
    review_threads_path: Option<&Path>,
) -> Result<EmpiricalDatasetInput, Box<dyn Error>> {
    let pull_request: Value = serde_json::from_str(&fs::read_to_string(pull_request_path)?)?;
    let files: Value = serde_json::from_str(&fs::read_to_string(files_path)?)?;
    let reviews = match reviews_path {
        Some(path) => Some(serde_json::from_str(&fs::read_to_string(path)?)?),
        None => None,
    };
    let review_threads = match review_threads_path {
        Some(path) => Some(serde_json::from_str(&fs::read_to_string(path)?)?),
        None => None,
    };

    build_pr_metadata_from_github_values(
        &pull_request,
        &files,
        reviews.as_ref(),
        review_threads.as_ref(),
    )
}

pub fn build_pr_metadata_from_github_values(
    pull_request: &Value,
    files: &Value,
    reviews: Option<&Value>,
    review_threads: Option<&Value>,
) -> Result<EmpiricalDatasetInput, Box<dyn Error>> {
    let file_items = json_items(
        files,
        &["data", "repository", "pullRequest", "files", "nodes"],
    );
    let changed_files =
        optional_usize(pull_request, &["changed_files"]).unwrap_or(file_items.len());
    let changed_lines_added = optional_usize(pull_request, &["additions"])
        .unwrap_or_else(|| sum_usize_field(&file_items, &["additions"]));
    let changed_lines_deleted = optional_usize(pull_request, &["deletions"])
        .unwrap_or_else(|| sum_usize_field(&file_items, &["deletions"]));

    let review_items = reviews
        .map(|reviews| {
            json_items(
                reviews,
                &["data", "repository", "pullRequest", "reviews", "nodes"],
            )
        })
        .unwrap_or_default();
    let thread_items = review_threads
        .map(|threads| {
            json_items(
                threads,
                &[
                    "data",
                    "repository",
                    "pullRequest",
                    "reviewThreads",
                    "nodes",
                ],
            )
        })
        .unwrap_or_default();

    let created_at = required_string(pull_request, &["created_at"])?;
    let merged_at = optional_string(pull_request, &["merged_at"]);

    Ok(EmpiricalDatasetInput {
        repository: RepositoryRef {
            owner: required_string(pull_request, &["base", "repo", "owner", "login"])?,
            name: required_string(pull_request, &["base", "repo", "name"])?,
            default_branch: required_string(pull_request, &["base", "repo", "default_branch"])?,
        },
        pull_request: PullRequestRef {
            number: required_usize(pull_request, &["number"])?,
            author: required_string(pull_request, &["user", "login"])?,
            created_at: created_at.clone(),
            merged_at: merged_at.clone(),
            base_commit: required_string(pull_request, &["base", "sha"])?,
            head_commit: required_string(pull_request, &["head", "sha"])?,
            merge_commit: optional_string(pull_request, &["merge_commit_sha"]),
            labels: pull_request_labels(pull_request),
            is_bot_generated: is_bot_generated_pull_request(pull_request),
        },
        pr_metrics: PullRequestMetrics {
            changed_files,
            changed_lines_added,
            changed_lines_deleted,
            changed_components: changed_components_from_github_files(&file_items),
            review_comment_count: optional_usize(pull_request, &["review_comments"]).unwrap_or(0),
            review_thread_count: thread_items.len(),
            review_round_count: review_items
                .iter()
                .filter(|review| review_timestamp(review).is_some())
                .count(),
            first_review_latency_hours: first_review_latency_hours(&created_at, &review_items),
            approval_latency_hours: approval_latency_hours(&created_at, &review_items),
            merge_latency_hours: merged_at
                .as_deref()
                .and_then(|merged_at| hours_between(&created_at, merged_at)),
        },
        issue_incident_links: Vec::new(),
        analysis_metadata: AnalysisMetadata::default(),
    })
}

fn json_field<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    path.iter()
        .try_fold(value, |current, key| current.get(*key))
}

fn required_string(value: &Value, path: &[&str]) -> Result<String, Box<dyn Error>> {
    optional_string(value, path)
        .ok_or_else(|| format!("missing or non-string GitHub field: {}", path.join(".")).into())
}

fn optional_string(value: &Value, path: &[&str]) -> Option<String> {
    match json_field(value, path)? {
        Value::String(text) => Some(text.clone()),
        Value::Null => None,
        _ => None,
    }
}

fn required_usize(value: &Value, path: &[&str]) -> Result<usize, Box<dyn Error>> {
    optional_usize(value, path)
        .ok_or_else(|| format!("missing or non-integer GitHub field: {}", path.join(".")).into())
}

fn optional_usize(value: &Value, path: &[&str]) -> Option<usize> {
    json_field(value, path)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())
}

fn json_items<'a>(value: &'a Value, graph_ql_nodes_path: &[&str]) -> Vec<&'a Value> {
    if let Some(items) = value.as_array() {
        return items.iter().collect();
    }
    if let Some(items) = json_field(value, &["nodes"]).and_then(Value::as_array) {
        return items.iter().collect();
    }
    if let Some(items) = json_field(value, graph_ql_nodes_path).and_then(Value::as_array) {
        return items.iter().collect();
    }
    Vec::new()
}

fn sum_usize_field(items: &[&Value], path: &[&str]) -> usize {
    items
        .iter()
        .filter_map(|item| optional_usize(item, path))
        .sum()
}

fn pull_request_labels(pull_request: &Value) -> Vec<String> {
    let mut labels: Vec<String> = json_field(pull_request, &["labels"])
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|label| optional_string(label, &["name"]))
        .collect();
    labels.sort();
    labels.dedup();
    labels
}

fn is_bot_generated_pull_request(pull_request: &Value) -> bool {
    let user = match json_field(pull_request, &["user"]) {
        Some(user) => user,
        None => return false,
    };
    let login = optional_string(user, &["login"]).unwrap_or_default();
    let user_type = optional_string(user, &["type"]).unwrap_or_default();
    user_type == "Bot" || login.ends_with("[bot]") || login.ends_with("-bot")
}

fn changed_components_from_github_files(files: &[&Value]) -> Vec<String> {
    let components: BTreeSet<String> = files
        .iter()
        .filter_map(|file| {
            optional_string(file, &["filename"])
                .or_else(|| optional_string(file, &["path"]))
                .or_else(|| optional_string(file, &["name"]))
        })
        .filter_map(|path| lean_module_id_from_path(&path))
        .collect();
    components.into_iter().collect()
}

fn lean_module_id_from_path(path: &str) -> Option<String> {
    let path = path.trim_start_matches("./");
    let module_path = path.strip_suffix(".lean")?;
    let module_id = module_path.replace(['/', '\\'], ".");
    (!module_id.is_empty()).then_some(module_id)
}

fn review_timestamp(review: &Value) -> Option<String> {
    optional_string(review, &["submitted_at"]).or_else(|| optional_string(review, &["submittedAt"]))
}

fn review_state(review: &Value) -> Option<String> {
    optional_string(review, &["state"]).map(|state| state.to_ascii_uppercase())
}

fn first_review_latency_hours(created_at: &str, reviews: &[&Value]) -> Option<f64> {
    reviews
        .iter()
        .filter_map(|review| review_timestamp(review))
        .filter_map(|submitted_at| seconds_between(created_at, &submitted_at))
        .min()
        .map(hours_from_seconds)
}

fn approval_latency_hours(created_at: &str, reviews: &[&Value]) -> Option<f64> {
    reviews
        .iter()
        .filter(|review| review_state(review).as_deref() == Some("APPROVED"))
        .filter_map(|review| review_timestamp(review))
        .filter_map(|submitted_at| seconds_between(created_at, &submitted_at))
        .min()
        .map(hours_from_seconds)
}

fn hours_between(start: &str, end: &str) -> Option<f64> {
    seconds_between(start, end).map(hours_from_seconds)
}

fn seconds_between(start: &str, end: &str) -> Option<i64> {
    let start = parse_github_timestamp(start)?;
    let end = parse_github_timestamp(end)?;
    (end >= start).then_some(end - start)
}

fn hours_from_seconds(seconds: i64) -> f64 {
    seconds as f64 / 3600.0
}

fn parse_github_timestamp(timestamp: &str) -> Option<i64> {
    let timestamp = timestamp.strip_suffix('Z')?;
    let (date, time) = timestamp.split_once('T')?;
    let mut date_parts = date.split('-');
    let year: i64 = date_parts.next()?.parse().ok()?;
    let month: i64 = date_parts.next()?.parse().ok()?;
    let day: i64 = date_parts.next()?.parse().ok()?;
    if date_parts.next().is_some() {
        return None;
    }

    let time = time.split_once('.').map_or(time, |(whole, _)| whole);
    let mut time_parts = time.split(':');
    let hour: i64 = time_parts.next()?.parse().ok()?;
    let minute: i64 = time_parts.next()?.parse().ok()?;
    let second: i64 = time_parts.next()?.parse().ok()?;
    if time_parts.next().is_some()
        || !(1..=12).contains(&month)
        || !(1..=31).contains(&day)
        || !(0..=23).contains(&hour)
        || !(0..=59).contains(&minute)
        || !(0..=60).contains(&second)
    {
        return None;
    }

    Some(days_from_civil(year, month, day) * 86_400 + hour * 3_600 + minute * 60 + second)
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = year - i64::from(month <= 2);
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month_prime = month + if month > 2 { -3 } else { 9 };
    let day_of_year = (153 * month_prime + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}
