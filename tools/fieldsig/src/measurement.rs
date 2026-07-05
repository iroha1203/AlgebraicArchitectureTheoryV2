use serde::{Deserialize, Serialize};

pub const SOFTWARE_FIELD_MEASUREMENT_SCHEMA_VERSION: &str = "software-field-measurement-v0";
pub const FIELDSIG_RUN_MANIFEST_SCHEMA_VERSION: &str = "fieldsig-run-manifest-v0";
pub const SOFTWARE_FIELD_MEASUREMENT_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "software-field-measurement-validation-report-v0";
pub const FIELDSIG_RUN_MANIFEST_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "fieldsig-run-manifest-validation-report-v0";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArtifactRefV0 {
    pub ref_id: String,
    pub artifact_kind: String,
    pub schema_version: String,
    pub path: String,
    pub producer: String,
    pub boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SoftwareFieldEstimateV0 {
    pub estimate_id: String,
    pub measured_axes: Vec<String>,
    pub unmeasured_axes: Vec<String>,
    pub evidence_boundary: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SoftwareFieldMeasurementV0 {
    pub schema_version: String,
    pub measurement_id: String,
    pub observation_boundary: Vec<String>,
    pub archsig_artifact_refs: Vec<ArtifactRefV0>,
    pub workflow_evidence_refs: Vec<ArtifactRefV0>,
    pub software_field_estimate: SoftwareFieldEstimateV0,
    pub forecast_cone_refs: Vec<ArtifactRefV0>,
    pub consequence_envelope_refs: Vec<ArtifactRefV0>,
    pub governance_candidate_refs: Vec<ArtifactRefV0>,
    pub operational_feedback_refs: Vec<ArtifactRefV0>,
    pub calibration_hook_refs: Vec<ArtifactRefV0>,
    pub unknown_remainder: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FieldSigRunManifestV0 {
    pub schema_version: String,
    pub run_id: String,
    pub input_artifact_refs: Vec<ArtifactRefV0>,
    pub generated_output_refs: Vec<ArtifactRefV0>,
    pub validation_summary: FieldSigValidationSummaryV0,
    pub claim_boundary: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FieldSigValidationSummaryV0 {
    pub result: String,
    pub checked_artifact_count: usize,
    pub warning_count: usize,
    pub failed_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SoftwareFieldMeasurementValidationReportV0 {
    pub schema_version: String,
    pub input: String,
    pub measurement: SoftwareFieldMeasurementV0,
    pub summary: FieldSigValidationSummaryV0,
    pub checks: Vec<FieldSigValidationCheckV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FieldSigRunManifestValidationReportV0 {
    pub schema_version: String,
    pub input: String,
    pub manifest: FieldSigRunManifestV0,
    pub summary: FieldSigValidationSummaryV0,
    pub checks: Vec<FieldSigValidationCheckV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FieldSigValidationCheckV0 {
    pub id: String,
    pub result: String,
    pub message: String,
}

pub fn static_software_field_measurement() -> SoftwareFieldMeasurementV0 {
    SoftwareFieldMeasurementV0 {
        schema_version: SOFTWARE_FIELD_MEASUREMENT_SCHEMA_VERSION.to_string(),
        measurement_id: "measurement:coupon-field:minimal".to_string(),
        observation_boundary: vec![
            "FieldSig observes workflow evidence and artifact refs; it does not prove forecast correctness".to_string(),
            "ArchSig artifacts are consumed through JSON refs, not Rust type sharing".to_string(),
        ],
        archsig_artifact_refs: vec![artifact_ref(
            "archsig:archmap:minimal",
            "archmap",
            "archmap-v0",
            "tools/fieldsig/tests/fixtures/minimal/archmap.json",
            "archsig",
            "AAT structural evidence ref; not architecture ground truth",
        )],
        workflow_evidence_refs: vec![
            artifact_ref("workflow:prd:coupon", "prd", "markdown", "docs/example/coupon_prd.md", "human", "planning evidence"),
            artifact_ref("workflow:issue:coupon", "github-issue", "github-issue-json", "issues/field-coupon.json", "github", "issue evidence"),
            artifact_ref("workflow:ci:coupon", "ci-run", "ci-run-ref-v0", "ci/runs/field-coupon", "ci", "test evidence ref"),
        ],
        software_field_estimate: SoftwareFieldEstimateV0 {
            estimate_id: "field-estimate:coupon:minimal".to_string(),
            measured_axes: vec!["boundedIntentSupport".to_string(), "workflowEvidenceCoverage".to_string()],
            unmeasured_axes: vec!["probability".to_string(), "causalCorrectness".to_string(), "globalSafety".to_string()],
            evidence_boundary: vec!["estimate is an SFT measurement artifact, not a theorem".to_string()],
        },
        forecast_cone_refs: vec![artifact_ref("fieldsig:forecast:coupon", "forecast-cone-skeleton", "forecast-cone-skeleton-v0", "forecast-cone-skeleton.json", "fieldsig", "bounded forecast skeleton ref")],
        consequence_envelope_refs: vec![artifact_ref("fieldsig:consequence:coupon", "consequence-envelope-report", "consequence-envelope-report-v0", "consequence-envelope-report.json", "fieldsig", "review consequence envelope ref")],
        governance_candidate_refs: vec![artifact_ref("fieldsig:governance:coupon", "ai-proposal-governance", "ai-proposal-governance-v0", "ai-proposal-governance.json", "fieldsig", "governance candidate ref")],
        operational_feedback_refs: vec![artifact_ref("fieldsig:feedback:coupon", "calibration-review-record", "calibration-review-record-v0", "calibration-review-record.json", "fieldsig", "empirical feedback ref")],
        calibration_hook_refs: vec![artifact_ref("fieldsig:calibration:coupon", "forecast-calibration-hook", "forecast-calibration-hook-v0", "forecast-calibration-hook.json", "fieldsig", "calibration hook ref")],
        unknown_remainder: vec!["runtime rollout impact is unmeasured in this fixture".to_string()],
        non_conclusions: measurement_non_conclusions(),
    }
}

pub fn static_fieldsig_run_manifest() -> FieldSigRunManifestV0 {
    let measurement = static_software_field_measurement();
    FieldSigRunManifestV0 {
        schema_version: FIELDSIG_RUN_MANIFEST_SCHEMA_VERSION.to_string(),
        run_id: "fieldsig-run:minimal".to_string(),
        input_artifact_refs: measurement
            .archsig_artifact_refs
            .iter()
            .chain(measurement.workflow_evidence_refs.iter())
            .cloned()
            .collect(),
        generated_output_refs: vec![artifact_ref(
            "fieldsig:measurement:coupon",
            "software-field-measurement",
            SOFTWARE_FIELD_MEASUREMENT_SCHEMA_VERSION,
            "software-field-measurement.json",
            "fieldsig",
            "SFT measurement output",
        )],
        validation_summary: FieldSigValidationSummaryV0 {
            result: "pass".to_string(),
            checked_artifact_count: 1,
            warning_count: 0,
            failed_check_count: 0,
        },
        claim_boundary: vec![
            "run manifest records artifact refs and validation status only".to_string(),
            "validation pass is not a forecast correctness proof".to_string(),
        ],
        non_conclusions: measurement_non_conclusions(),
    }
}

pub fn validate_software_field_measurement(
    measurement: &SoftwareFieldMeasurementV0,
    input: &str,
) -> SoftwareFieldMeasurementValidationReportV0 {
    let checks = vec![
        check(
            "software-field-measurement-schema",
            measurement.schema_version == SOFTWARE_FIELD_MEASUREMENT_SCHEMA_VERSION,
            "schemaVersion must be software-field-measurement-v0",
        ),
        check(
            "software-field-measurement-archsig-ref-boundary",
            !measurement.archsig_artifact_refs.is_empty(),
            "ArchSig artifact refs must be explicit JSON refs",
        ),
        check(
            "software-field-measurement-workflow-evidence",
            !measurement.workflow_evidence_refs.is_empty(),
            "workflow evidence refs must be retained",
        ),
        check(
            "software-field-measurement-unknown-remainder",
            !measurement.unknown_remainder.is_empty(),
            "unknown remainder must be first-class",
        ),
        check(
            "software-field-measurement-non-conclusions",
            measurement
                .non_conclusions
                .iter()
                .any(|item| item.contains("does not prove forecast correctness")),
            "forecast correctness non-conclusion must be present",
        ),
    ];
    let summary = summary(&checks, 1);
    SoftwareFieldMeasurementValidationReportV0 {
        schema_version: SOFTWARE_FIELD_MEASUREMENT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: input.to_string(),
        measurement: measurement.clone(),
        summary,
        checks,
    }
}

pub fn validate_fieldsig_run_manifest(
    manifest: &FieldSigRunManifestV0,
    input: &str,
) -> FieldSigRunManifestValidationReportV0 {
    let checks = vec![
        check(
            "fieldsig-run-manifest-schema",
            manifest.schema_version == FIELDSIG_RUN_MANIFEST_SCHEMA_VERSION,
            "schemaVersion must be fieldsig-run-manifest-v0",
        ),
        check(
            "fieldsig-run-manifest-inputs",
            !manifest.input_artifact_refs.is_empty(),
            "input artifact refs must be explicit",
        ),
        check(
            "fieldsig-run-manifest-outputs",
            !manifest.generated_output_refs.is_empty(),
            "generated output refs must be explicit",
        ),
        check(
            "fieldsig-run-manifest-boundary",
            manifest
                .claim_boundary
                .iter()
                .any(|item| item.contains("not a forecast correctness proof")),
            "claim boundary must reject forecast correctness proof promotion",
        ),
    ];
    let summary = summary(&checks, manifest.input_artifact_refs.len());
    FieldSigRunManifestValidationReportV0 {
        schema_version: FIELDSIG_RUN_MANIFEST_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: input.to_string(),
        manifest: manifest.clone(),
        summary,
        checks,
    }
}

fn artifact_ref(
    ref_id: &str,
    artifact_kind: &str,
    schema_version: &str,
    path: &str,
    producer: &str,
    boundary: &str,
) -> ArtifactRefV0 {
    ArtifactRefV0 {
        ref_id: ref_id.to_string(),
        artifact_kind: artifact_kind.to_string(),
        schema_version: schema_version.to_string(),
        path: path.to_string(),
        producer: producer.to_string(),
        boundary: boundary.to_string(),
    }
}

fn measurement_non_conclusions() -> Vec<String> {
    vec![
        "FieldSig does not prove forecast correctness".to_string(),
        "FieldSig does not assign probabilities unless supplied by a calibrated external process"
            .to_string(),
        "FieldSig does not provide causal correctness or global safety guarantees".to_string(),
        "FieldSig does not replace CI, tests, or human review".to_string(),
    ]
}

fn check(id: &str, passed: bool, message: &str) -> FieldSigValidationCheckV0 {
    FieldSigValidationCheckV0 {
        id: id.to_string(),
        result: if passed { "pass" } else { "fail" }.to_string(),
        message: message.to_string(),
    }
}

fn summary(
    checks: &[FieldSigValidationCheckV0],
    checked_artifact_count: usize,
) -> FieldSigValidationSummaryV0 {
    let failed_check_count = checks.iter().filter(|check| check.result == "fail").count();
    FieldSigValidationSummaryV0 {
        result: if failed_check_count == 0 {
            "pass"
        } else {
            "fail"
        }
        .to_string(),
        checked_artifact_count,
        warning_count: 0,
        failed_check_count,
    }
}
