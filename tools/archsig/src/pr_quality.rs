use crate::validation::{count_checks, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
    PR_QUALITY_ANALYSIS_VALIDATION_REPORT_SCHEMA_VERSION, PrQualityAnalysisReportV0,
    PrQualityAnalysisValidationInput, PrQualityAnalysisValidationReportV0,
    PrQualityAnalysisValidationSummary, PrQualityArchMapArtifactRefV0, PrQualityArtifactRefV0,
    PrQualityCueV0, PrQualityMissingEvidenceV0, PrQualityReviewSummaryV0, ValidationCheck,
};

const PR_QUALITY_NON_CONCLUSIONS: [&str; 5] = [
    "PR quality analysis is review cue aggregation, not merge approval",
    "PR quality analysis does not prove implementation correctness",
    "missing evidence is retained as review context, not measured zero",
    "policy and theorem refs remain bounded by supplied reports",
    "human review and CI remain required evidence surfaces",
];

pub fn static_pr_quality_analysis_report() -> PrQualityAnalysisReportV0 {
    PrQualityAnalysisReportV0 {
        schema_version: PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-pr-quality-analysis-v0".to_string(),
        archmap_ref: PrQualityArchMapArtifactRefV0 {
            artifact_id: "artifact:archmap".to_string(),
            artifact_kind: "archmap".to_string(),
            schema_version: Some(ARCHMAP_SCHEMA_VERSION.to_string()),
            path: "archmap.json".to_string(),
            selected_map_item_ids: vec!["object-route-users".to_string()],
            non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
        },
        air_ref: Some(artifact_ref("air", "aat-air-v0", "air.json")),
        theorem_check_ref: Some(artifact_ref(
            "theorem-check",
            "theorem-precondition-check-report-v0",
            "theorem-check.json",
        )),
        feature_report_ref: Some(artifact_ref(
            "feature-report",
            "feature-extension-report-v0",
            "feature-report.json",
        )),
        policy_decision_ref: Some(artifact_ref(
            "policy-decision",
            "policy-decision-report-v0",
            "policy-decision.json",
        )),
        cues: vec![
            pr_quality_cue(
                "cue:responsibility-mixing",
                "responsibilityMixing",
                "review semantic dependency and split need before merge",
            ),
            pr_quality_cue(
                "cue:runtime-static-disagreement",
                "runtimeStaticDisagreement",
                "compare runtime evidence need with static ArchMap refs",
            ),
            pr_quality_cue(
                "cue:policy-conflict",
                "policyConflict",
                "review policy boundary and theorem precondition report",
            ),
        ],
        missing_evidence: vec![PrQualityMissingEvidenceV0 {
            boundary_id: "missing-evidence:pr-runtime".to_string(),
            boundary_kind: "missingEvidence".to_string(),
            source_refs: vec!["runtime-unmeasured-boundary".to_string()],
            reason: "runtime evidence was not supplied to selected PR analysis".to_string(),
            treatment: "retain as review cue, not merge blocker by itself".to_string(),
            non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
        }],
        review_summary: PrQualityReviewSummaryV0 {
            summary_id: "summary:pr-quality".to_string(),
            cue_count: 3,
            missing_evidence_count: 1,
            reviewer_notes: vec![
                "ArchMap is the PR-side source; planning flow is not required for PR quality analysis"
                    .to_string(),
                "report surfaces review cues and missing evidence without automatic merge decision"
                    .to_string(),
            ],
            non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
    }
}

pub fn validate_pr_quality_analysis_report(
    report: &PrQualityAnalysisReportV0,
    input_path: &str,
) -> PrQualityAnalysisValidationReportV0 {
    let checks = vec![
        simple_schema_check(
            "pr-quality-schema-version-supported",
            &report.schema_version,
            PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
        ),
        check_pr_quality_cues(report),
        check_pr_quality_boundaries(report),
    ];
    let summary = PrQualityAnalysisValidationSummary {
        result: validation_result(&checks),
        cue_count: report.cues.len(),
        missing_evidence_count: report.missing_evidence.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };
    PrQualityAnalysisValidationReportV0 {
        schema_version: PR_QUALITY_ANALYSIS_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: PrQualityAnalysisValidationInput {
            schema_version: report.schema_version.clone(),
            path: input_path.to_string(),
            report_id: report.report_id.clone(),
        },
        report: report.clone(),
        summary,
        checks,
    }
}

fn artifact_ref(kind: &str, schema_version: &str, path: &str) -> PrQualityArtifactRefV0 {
    PrQualityArtifactRefV0 {
        artifact_id: format!("artifact:{kind}"),
        artifact_kind: kind.to_string(),
        path: path.to_string(),
        schema_version: Some(schema_version.to_string()),
        non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
    }
}

fn pr_quality_cue(cue_id: &str, cue_kind: &str, review_focus: &str) -> PrQualityCueV0 {
    PrQualityCueV0 {
        cue_id: cue_id.to_string(),
        cue_kind: cue_kind.to_string(),
        source_refs: vec!["object-route-users".to_string()],
        severity: "review".to_string(),
        review_focus: review_focus.to_string(),
        evidence_boundary: "selected ArchMap/AIR/theorem-check artifacts only".to_string(),
        non_conclusions: strings(&PR_QUALITY_NON_CONCLUSIONS),
    }
}

fn simple_schema_check(id: &str, actual: &str, expected: &str) -> ValidationCheck {
    let mut check = validation_check(
        id,
        "schema version is supported",
        if actual == expected { "pass" } else { "fail" },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported schemaVersion: {actual}; expected {expected}"
        ));
    }
    check
}

fn check_pr_quality_cues(report: &PrQualityAnalysisReportV0) -> ValidationCheck {
    let invalid = report
        .cues
        .iter()
        .filter(|cue| {
            cue.cue_id.trim().is_empty()
                || cue.cue_kind.trim().is_empty()
                || cue.source_refs.is_empty()
                || cue.review_focus.trim().is_empty()
                || cue.evidence_boundary.trim().is_empty()
        })
        .map(|cue| cue.cue_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "pr-quality-analysis-review-cues-present",
        "PR quality analysis exposes review cues from ArchMap-side artifacts",
        if !report.cues.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!("invalid PR quality cues: {}", invalid.join(", ")));
    }
    check.count = Some(report.cues.len());
    check
}

fn check_pr_quality_boundaries(report: &PrQualityAnalysisReportV0) -> ValidationCheck {
    let missing = PR_QUALITY_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !report
                .non_conclusions
                .iter()
                .any(|entry| entry == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "pr-quality-analysis-non-conclusions-preserved",
        "required non-conclusions are preserved",
        if missing.is_empty() { "pass" } else { "fail" },
    );
    if !missing.is_empty() {
        check.reason = Some(format!("missing non-conclusions: {}", missing.join("; ")));
    }
    if check.result == "pass"
        && report
            .review_summary
            .reviewer_notes
            .iter()
            .any(|note| note.to_ascii_lowercase().contains("merge approval"))
    {
        check.result = "fail".to_string();
        check.reason = Some(
            "review summary must not present PR quality analysis as merge approval".to_string(),
        );
    }
    check
}

fn validation_result(checks: &[ValidationCheck]) -> String {
    if checks.iter().any(|check| check.result == "fail") {
        "fail".to_string()
    } else if checks.iter().any(|check| check.result == "warn") {
        "warn".to_string()
    } else {
        "pass".to_string()
    }
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}
