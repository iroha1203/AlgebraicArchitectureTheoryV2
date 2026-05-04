use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    FEATURE_EXTENSION_REPORT_SCHEMA_VERSION, ORGANIZATION_POLICY_SCHEMA_VERSION,
    REPORT_ARTIFACT_RETENTION_MANIFEST_SCHEMA_VERSION,
    REPORT_ARTIFACT_RETENTION_VALIDATION_REPORT_SCHEMA_VERSION, ReportArtifactPolicyRef,
    ReportArtifactPullRequestRef, ReportArtifactRetentionManifestV0,
    ReportArtifactRetentionValidationInput, ReportArtifactRetentionValidationReportV0,
    ReportArtifactRetentionValidationSummary, ReportArtifactTraceabilityV0, RepositoryRef,
    RetainedReportArtifactRefV0, THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION, ValidationCheck,
};

const REQUIRED_ARTIFACT_KINDS: [&str; 4] = [
    "featureExtensionReport",
    "theoremCheckReport",
    "policyDecisionReport",
    "prCommentSummary",
];

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "retained report artifacts are review evidence, not Lean theorem claims",
    "missing or private artifacts are not measured-zero evidence",
    "artifact retention does not conclude architecture lawfulness",
    "PR comment summaries are reviewer-facing summaries, not proof certificates",
];

pub fn static_report_artifact_retention_manifest() -> ReportArtifactRetentionManifestV0 {
    let repository = RepositoryRef {
        owner: "iroha1203".to_string(),
        name: "AlgebraicArchitectureTheoryV2".to_string(),
        default_branch: "main".to_string(),
    };
    let pr_number = 575;
    let commit_sha = "fixture-b7-retention-commit".to_string();
    let policy_version = "2026-05-05".to_string();
    let generated_at = "2026-05-05T00:00:00Z".to_string();
    let retention_scope = "ci-pr-review-baseline-suppression".to_string();

    ReportArtifactRetentionManifestV0 {
        schema_version: REPORT_ARTIFACT_RETENTION_MANIFEST_SCHEMA_VERSION.to_string(),
        retention_id: "fixture-b7-report-artifact-retention".to_string(),
        repository: repository.clone(),
        pull_request: ReportArtifactPullRequestRef {
            number: pr_number,
            url: Some(
                "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/575".to_string(),
            ),
        },
        commit_sha: commit_sha.clone(),
        policy: ReportArtifactPolicyRef {
            policy_id: Some("aat-b7-default-organization-policy".to_string()),
            policy_version: policy_version.clone(),
            schema_version: Some(ORGANIZATION_POLICY_SCHEMA_VERSION.to_string()),
        },
        generated_at: generated_at.clone(),
        retention_scope: retention_scope.clone(),
        artifacts: vec![
            retained_artifact(
                "artifact-feature-extension-report",
                "featureExtensionReport",
                "artifacts/pr-575/feature-extension-report.json",
                &repository,
                pr_number,
                &commit_sha,
                FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
                &policy_version,
                &generated_at,
                &retention_scope,
            ),
            retained_artifact(
                "artifact-theorem-check-report",
                "theoremCheckReport",
                "artifacts/pr-575/theorem-check-report.json",
                &repository,
                pr_number,
                &commit_sha,
                THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION,
                &policy_version,
                &generated_at,
                &retention_scope,
            ),
            retained_artifact(
                "artifact-policy-decision-report",
                "policyDecisionReport",
                "artifacts/pr-575/policy-decision-report.json",
                &repository,
                pr_number,
                &commit_sha,
                "policy-decision-report-v0",
                &policy_version,
                &generated_at,
                &retention_scope,
            ),
            retained_artifact(
                "artifact-pr-comment-summary",
                "prCommentSummary",
                "artifacts/pr-575/pr-comment-summary.md",
                &repository,
                pr_number,
                &commit_sha,
                "pr-comment-summary-v0",
                &policy_version,
                &generated_at,
                &retention_scope,
            ),
        ],
        missing_or_private_artifacts: Vec::new(),
        traceability: ReportArtifactTraceabilityV0 {
            baseline_comparison_refs: vec!["baseline:pr-575".to_string()],
            suppression_workflow_refs: vec!["suppression-workflow:pr-575".to_string()],
            drift_ledger_refs: vec!["drift-ledger:pr-575".to_string()],
            reviewer_output_refs: vec!["github-pr-comment:575".to_string()],
        },
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn validate_report_artifact_retention_report(
    manifest: &ReportArtifactRetentionManifestV0,
    input_path: &str,
) -> ReportArtifactRetentionValidationReportV0 {
    let checks = vec![
        check_schema_version(manifest),
        check_identity_and_scope(manifest),
        check_artifact_kinds(manifest),
        check_artifact_metadata(manifest),
        check_missing_private_non_conclusions(manifest),
        check_traceability(manifest),
        check_non_conclusion_boundary(manifest),
    ];
    let summary = ReportArtifactRetentionValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        artifact_count: manifest.artifacts.len(),
        missing_or_private_artifact_count: manifest.missing_or_private_artifacts.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ReportArtifactRetentionValidationReportV0 {
        schema_version: REPORT_ARTIFACT_RETENTION_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ReportArtifactRetentionValidationInput {
            schema_version: manifest.schema_version.clone(),
            path: input_path.to_string(),
            retention_id: manifest.retention_id.clone(),
            repository: manifest.repository.clone(),
            pull_request_number: manifest.pull_request.number,
            commit_sha: manifest.commit_sha.clone(),
            policy_version: manifest.policy.policy_version.clone(),
        },
        manifest: manifest.clone(),
        summary,
        checks,
    }
}

#[allow(clippy::too_many_arguments)]
fn retained_artifact(
    artifact_id: &str,
    kind: &str,
    path: &str,
    repository: &RepositoryRef,
    pr_number: usize,
    commit_sha: &str,
    schema_version: &str,
    policy_version: &str,
    generated_at: &str,
    retention_scope: &str,
) -> RetainedReportArtifactRefV0 {
    RetainedReportArtifactRefV0 {
        artifact_id: artifact_id.to_string(),
        kind: kind.to_string(),
        path: path.to_string(),
        repository: repository.clone(),
        pull_request_number: pr_number,
        commit_sha: commit_sha.to_string(),
        schema_version: schema_version.to_string(),
        policy_version: policy_version.to_string(),
        generated_at: generated_at.to_string(),
        retention_scope: retention_scope.to_string(),
        visibility: "repository".to_string(),
        content_hash: None,
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn check_schema_version(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let mut check = validation_check(
        "report-artifact-retention-schema-version-supported",
        "report artifact retention manifest schema version is supported",
        if manifest.schema_version == REPORT_ARTIFACT_RETENTION_MANIFEST_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported report artifact retention schemaVersion: {}",
            manifest.schema_version
        ));
    }
    check
}

fn check_identity_and_scope(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if manifest.retention_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "retentionId",
            &manifest.commit_sha,
            "retention_id must be non-empty",
        ));
    }
    if manifest.repository.owner.trim().is_empty()
        || manifest.repository.name.trim().is_empty()
        || manifest.repository.default_branch.trim().is_empty()
    {
        invalid.push(generic_validation_example(
            &manifest.retention_id,
            "repository",
            "repository owner, name, and default branch must be recorded",
        ));
    }
    if manifest.pull_request.number == 0 {
        invalid.push(generic_validation_example(
            &manifest.retention_id,
            "pullRequest",
            "pull request number must be positive",
        ));
    }
    if manifest.commit_sha.trim().is_empty()
        || manifest.policy.policy_version.trim().is_empty()
        || manifest.generated_at.trim().is_empty()
        || manifest.retention_scope.trim().is_empty()
    {
        invalid.push(generic_validation_example(
            &manifest.retention_id,
            "retentionScope",
            "commit sha, policy version, generated_at, and retention scope must be recorded",
        ));
    }

    check_examples(
        "report-artifact-retention-identity-and-scope-recorded",
        "repository, PR, commit, policy, generated_at, and retention scope are recorded",
        invalid,
    )
}

fn check_artifact_kinds(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let supported = string_set(&REQUIRED_ARTIFACT_KINDS);
    let observed = string_set_from(
        manifest
            .artifacts
            .iter()
            .map(|artifact| artifact.kind.as_str())
            .chain(
                manifest
                    .missing_or_private_artifacts
                    .iter()
                    .map(|artifact| artifact.kind.as_str()),
            ),
    );
    let mut invalid = Vec::new();

    invalid.extend(
        duplicates(
            manifest
                .artifacts
                .iter()
                .map(|artifact| artifact.artifact_id.as_str()),
        )
        .into_iter()
        .map(|artifact_id| {
            generic_validation_example(&artifact_id, "artifactId", "duplicate artifact id")
        }),
    );
    for required_kind in REQUIRED_ARTIFACT_KINDS {
        if !observed.contains(required_kind) {
            invalid.push(generic_validation_example(
                &manifest.retention_id,
                required_kind,
                "required report artifact kind is missing",
            ));
        }
    }
    for artifact in &manifest.artifacts {
        if !supported.contains(artifact.kind.as_str()) {
            invalid.push(generic_validation_example(
                &artifact.artifact_id,
                &artifact.kind,
                "unsupported report artifact kind",
            ));
        }
    }
    for artifact in &manifest.missing_or_private_artifacts {
        if !supported.contains(artifact.kind.as_str()) {
            invalid.push(generic_validation_example(
                &artifact.kind,
                &artifact.visibility,
                "unsupported missing/private report artifact kind",
            ));
        }
    }

    check_examples(
        "report-artifact-retention-required-artifacts-present",
        "feature, theorem, policy decision, and PR comment artifacts or gaps are represented",
        invalid,
    )
}

fn check_artifact_metadata(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let mut invalid = Vec::new();

    for artifact in &manifest.artifacts {
        if artifact.artifact_id.trim().is_empty()
            || artifact.path.trim().is_empty()
            || artifact.repository.owner.trim().is_empty()
            || artifact.repository.name.trim().is_empty()
            || artifact.repository.default_branch.trim().is_empty()
            || artifact.pull_request_number == 0
            || artifact.commit_sha.trim().is_empty()
            || artifact.schema_version.trim().is_empty()
            || artifact.policy_version.trim().is_empty()
            || artifact.generated_at.trim().is_empty()
            || artifact.retention_scope.trim().is_empty()
            || artifact.visibility.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &artifact.artifact_id,
                &artifact.kind,
                "artifact ref must record path, repository, PR, commit, schema, policy, generated_at, retention scope, and visibility",
            ));
        }
        if artifact.repository != manifest.repository
            || artifact.pull_request_number != manifest.pull_request.number
            || artifact.commit_sha != manifest.commit_sha
            || artifact.policy_version != manifest.policy.policy_version
            || artifact.retention_scope != manifest.retention_scope
        {
            invalid.push(generic_validation_example(
                &artifact.artifact_id,
                &artifact.kind,
                "artifact metadata must match manifest repository, PR, commit, policy, and retention scope",
            ));
        }
        if has_blank(&artifact.non_conclusions) {
            invalid.push(generic_validation_example(
                &artifact.artifact_id,
                "nonConclusions",
                "artifact non-conclusions must not contain blanks",
            ));
        }
    }

    check_examples(
        "report-artifact-retention-artifact-metadata-recorded",
        "each artifact ref records traceable retention metadata",
        invalid,
    )
}

fn check_missing_private_non_conclusions(
    manifest: &ReportArtifactRetentionManifestV0,
) -> ValidationCheck {
    let required = string_set(&["missing or private artifacts are not measured-zero evidence"]);
    let mut invalid = Vec::new();

    for artifact in &manifest.missing_or_private_artifacts {
        let non_conclusions = string_set_from(artifact.non_conclusions.iter().map(String::as_str));
        if artifact.kind.trim().is_empty()
            || artifact.reason.trim().is_empty()
            || artifact.visibility.trim().is_empty()
            || artifact.repository.owner.trim().is_empty()
            || artifact.repository.name.trim().is_empty()
            || artifact.pull_request_number == 0
            || artifact.commit_sha.trim().is_empty()
            || artifact.schema_version.trim().is_empty()
            || artifact.policy_version.trim().is_empty()
            || artifact.generated_at.trim().is_empty()
            || artifact.retention_scope.trim().is_empty()
            || has_blank(&artifact.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &artifact.kind,
                &artifact.visibility,
                "missing/private artifact must record traceability metadata, reason, and non-conclusions",
            ));
        }
        for required_conclusion in &required {
            if !non_conclusions.contains(*required_conclusion) {
                invalid.push(generic_validation_example(
                    &artifact.kind,
                    "nonConclusions",
                    &format!("missing required non-conclusion: {required_conclusion}"),
                ));
            }
        }
    }

    check_examples(
        "report-artifact-retention-missing-private-boundary-recorded",
        "missing or private artifacts remain unmeasured evidence gaps",
        invalid,
    )
}

fn check_traceability(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let traceability = &manifest.traceability;
    let mut invalid = Vec::new();
    if traceability.baseline_comparison_refs.is_empty()
        || traceability.suppression_workflow_refs.is_empty()
        || traceability.drift_ledger_refs.is_empty()
        || traceability.reviewer_output_refs.is_empty()
        || has_blank(&traceability.baseline_comparison_refs)
        || has_blank(&traceability.suppression_workflow_refs)
        || has_blank(&traceability.drift_ledger_refs)
        || has_blank(&traceability.reviewer_output_refs)
    {
        invalid.push(generic_validation_example(
            &manifest.retention_id,
            "traceability",
            "baseline comparison, suppression workflow, drift ledger, and reviewer output refs must be recorded",
        ));
    }

    check_examples(
        "report-artifact-retention-traceability-recorded",
        "retention metadata is referenceable by baseline, suppression, ledger, and review output",
        invalid,
    )
}

fn check_non_conclusion_boundary(manifest: &ReportArtifactRetentionManifestV0) -> ValidationCheck {
    let non_conclusions = string_set_from(manifest.non_conclusions.iter().map(String::as_str));
    let invalid: Vec<_> = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !non_conclusions.contains(**required))
        .map(|required| {
            generic_validation_example(
                &manifest.retention_id,
                "nonConclusions",
                &format!("missing required non-conclusion: {required}"),
            )
        })
        .collect();

    check_examples(
        "report-artifact-retention-non-conclusion-boundary-recorded",
        "retention records theorem, lawfulness, missing/private, and PR summary non-conclusions",
        invalid,
    )
}

fn check_examples(
    id: &str,
    title: &str,
    invalid: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    let mut check = validation_check(id, title, if invalid.is_empty() { "pass" } else { "fail" });
    if !invalid.is_empty() {
        check.count = Some(invalid.len());
        check.examples = invalid;
    }
    check
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn string_set<'a>(values: &'a [&'a str]) -> BTreeSet<&'a str> {
    values.iter().copied().collect()
}

fn string_set_from<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MissingReportArtifactRefV0;

    #[test]
    fn static_manifest_validates_and_records_retention_boundary() {
        let manifest = static_report_artifact_retention_manifest();
        let report =
            validate_report_artifact_retention_report(&manifest, "static-report-artifacts");

        assert_eq!(
            report.schema_version,
            REPORT_ARTIFACT_RETENTION_VALIDATION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.artifact_count, 4);
        assert!(
            report.manifest.non_conclusions.contains(
                &"missing or private artifacts are not measured-zero evidence".to_string()
            )
        );
    }

    #[test]
    fn missing_private_artifact_without_boundary_fails_validation() {
        let mut manifest = static_report_artifact_retention_manifest();
        manifest.artifacts.pop();
        manifest
            .missing_or_private_artifacts
            .push(MissingReportArtifactRefV0 {
                kind: "prCommentSummary".to_string(),
                reason: "private PR comment storage".to_string(),
                visibility: "private".to_string(),
                repository: manifest.repository.clone(),
                pull_request_number: manifest.pull_request.number,
                commit_sha: manifest.commit_sha.clone(),
                schema_version: "pr-comment-summary-v0".to_string(),
                policy_version: manifest.policy.policy_version.clone(),
                generated_at: manifest.generated_at.clone(),
                retention_scope: manifest.retention_scope.clone(),
                non_conclusions: Vec::new(),
            });

        let report =
            validate_report_artifact_retention_report(&manifest, "invalid-report-artifacts.json");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| check.id
            == "report-artifact-retention-missing-private-boundary-recorded"
            && check.result == "fail"));
    }
}
