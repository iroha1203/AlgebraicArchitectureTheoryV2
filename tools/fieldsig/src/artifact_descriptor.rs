use std::collections::BTreeSet;

use serde_json::Value;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARTIFACT_DESCRIPTOR_SCHEMA_VERSION, ARTIFACT_DESCRIPTOR_VALIDATION_REPORT_SCHEMA_VERSION,
    ArtifactActionClassCandidateV0, ArtifactDescriptorMeasurementBoundaryV0,
    ArtifactDescriptorMissingEvidenceV0, ArtifactDescriptorScopeV0, ArtifactDescriptorSourceRefV0,
    ArtifactDescriptorV0, ArtifactDescriptorValidationInput, ArtifactDescriptorValidationReportV0,
    ArtifactDescriptorValidationSummary, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "artifact descriptor is tooling input normalization, not a Lean theorem claim",
    "artifact descriptor is not a ground truth architecture object",
    "artifact descriptor does not provide a causal forecast",
    "missing evidence and unsupported constructs are not measured zero",
    "forecast non-conclusions must be preserved by downstream SFT artifacts",
];

const REQUIRED_FORECAST_NON_CONCLUSIONS: [&str; 4] = [
    "descriptor action classes are candidates, not forecasted effects",
    "descriptor scope does not prove operation support completeness",
    "descriptor boundary does not assign probability to future outcomes",
    "descriptor evidence does not establish causal prediction",
];

const ALLOWED_ARTIFACT_KINDS: [&str; 4] = ["prd", "spec", "issue", "ai-proposal"];
const ALLOWED_MISSING_EVIDENCE_STATUSES: [&str; 4] =
    ["missing", "private", "unmeasured", "outOfScope"];

pub fn static_artifact_descriptor() -> ArtifactDescriptorV0 {
    let issue_ref = source_ref(
        "source:issue-733",
        "issue",
        "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/733",
        Some("GitHub Issue #733"),
        "primary artifact request",
        &[
            "title",
            "body",
            "completion criteria",
            "Lean status",
            "related docs",
        ],
    );
    let roadmap_ref = source_ref(
        "source:roadmap-b12",
        "doc",
        "docs/tool/roadmap.md#phase-b12-sft-forecasting-mvp",
        Some("Phase B12 / B12.1"),
        "forecasting MVP boundary",
        &["pipeline", "minimal output", "B12.1 milestone"],
    );
    let sft_ref = source_ref(
        "source:sft-computational-problems",
        "doc",
        "docs/sft/software_field_theory.md#20-sft-computational-problems",
        Some("SFT Computational Problems"),
        "theory boundary",
        &[
            "ArtifactDescriptor role",
            "ConsequenceEnvelope simulator boundary",
            "non-conclusions",
        ],
    );
    let source_refs = vec![issue_ref.clone(), roadmap_ref.clone(), sft_ref.clone()];
    let missing_evidence = vec![
        missing_evidence(
            "missing:prd-body",
            "prd",
            "fixture has no full PRD body",
            "operation support cannot be treated as complete",
            "missing",
        ),
        missing_evidence(
            "missing:runtime-impact",
            "runtime-evidence",
            "runtime traces are outside B12.1 descriptor normalization",
            "runtime propagation remains a downstream boundary item",
            "unmeasured",
        ),
    ];
    let source_ref_ids = source_refs
        .iter()
        .map(|source| source.source_ref_id.clone())
        .collect::<Vec<_>>();
    let selected_region_refs = vec![
        "tools/archsig".to_string(),
        "docs/tool/roadmap.md#phase-b12-sft-forecasting-mvp".to_string(),
        "docs/sft/software_field_theory.md#21-prd-to-consequenceenvelope-simulator".to_string(),
    ];

    ArtifactDescriptorV0 {
        schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
        descriptor_id: "fixture-artifact-descriptor/v0.5.0".to_string(),
        artifact_kind: "issue".to_string(),
        artifact_title: "B12.1 ArtifactDescriptor schema".to_string(),
        source_refs,
        action_class_candidates: vec![
            action_candidate(
                "candidate:add-schema",
                "schema-definition",
                "high",
                &["source:issue-733", "source:roadmap-b12"],
                "Issue requests a Rust schema for artifact-descriptor-schema050.",
            ),
            action_candidate(
                "candidate:add-validator",
                "tooling-validation",
                "high",
                &["source:issue-733"],
                "Issue requires a canonical fixture and validator.",
            ),
            action_candidate(
                "candidate:add-cli-entrypoint",
                "cli-entrypoint",
                "medium",
                &["source:issue-733"],
                "Issue names a fieldsig artifact-descriptor entrypoint.",
            ),
        ],
        scope: ArtifactDescriptorScopeV0 {
            scope_id: "scope:b12.1-artifact-descriptor".to_string(),
            selected_region_refs: selected_region_refs.clone(),
            excluded_region_refs: vec![
                "operation-support-estimate".to_string(),
                "forecast-cone-probability".to_string(),
                "causal-outcome-prediction".to_string(),
            ],
            target_audience: vec![
                "archsig-cli".to_string(),
                "sft-forecaster-pipeline".to_string(),
                "review-ci".to_string(),
            ],
            artifact_boundary:
                "normalizes PRD / Spec / Issue / AI proposal input before operation support"
                    .to_string(),
            assumptions: vec![
                "source refs are retained as bounded tooling evidence".to_string(),
                "action class candidates are used only as downstream estimation input".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        missing_evidence,
        measurement_boundary: ArtifactDescriptorMeasurementBoundaryV0 {
            boundary_id: "boundary:b12.1-artifact-descriptor".to_string(),
            measured_layers: vec!["artifact-normalization".to_string()],
            measured_axes: vec![
                "sourceRefs".to_string(),
                "actionClassCandidates".to_string(),
                "scope".to_string(),
                "missingEvidence".to_string(),
                "forecastNonConclusions".to_string(),
            ],
            source_ref_ids,
            selected_region_refs,
            assumptions: vec![
                "descriptor validation checks structure and boundary preservation only".to_string(),
                "descriptor validation does not run a repository extractor".to_string(),
            ],
            unsupported_constructs: vec![
                "operation support probability".to_string(),
                "ground truth architecture reconstruction".to_string(),
                "future outcome causality".to_string(),
            ],
            missing_evidence_ids: vec![
                "missing:prd-body".to_string(),
                "missing:runtime-impact".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        forecast_non_conclusions: strings(&REQUIRED_FORECAST_NON_CONCLUSIONS),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn build_artifact_descriptor_from_markdown(
    path_or_url: &str,
    contents: &str,
    artifact_kind: &str,
) -> ArtifactDescriptorV0 {
    let title = extract_markdown_title(contents).unwrap_or_else(|| fallback_title(path_or_url));
    let slug = slugify(&title);
    let source_ref_id = format!("source:markdown:{slug}");
    let source_refs = vec![source_ref(
        &source_ref_id,
        "markdown",
        path_or_url,
        Some(&title),
        "primary markdown artifact input",
        &["title", "headings", "body", "explicit scope markers"],
    )];
    let source_ref_ids = vec![source_ref_id.clone()];
    let selected_region_refs = selected_region_refs(contents, path_or_url);
    let excluded_region_refs = excluded_region_refs(contents);
    let target_audience = target_audience(contents);
    let missing_evidence = missing_evidence_from_markdown(contents);
    let missing_evidence_ids = missing_evidence
        .iter()
        .map(|evidence| evidence.evidence_id.clone())
        .collect::<Vec<_>>();

    ArtifactDescriptorV0 {
        schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
        descriptor_id: format!("descriptor:{slug}"),
        artifact_kind: artifact_kind.to_string(),
        artifact_title: title,
        source_refs,
        action_class_candidates: infer_action_candidates(contents, &source_ref_id),
        scope: ArtifactDescriptorScopeV0 {
            scope_id: format!("scope:{slug}"),
            selected_region_refs: selected_region_refs.clone(),
            excluded_region_refs,
            target_audience,
            artifact_boundary:
                "normalizes markdown artifact input before operation support estimation".to_string(),
            assumptions: vec![
                "markdown headings and retained body text are bounded tooling evidence".to_string(),
                "action class candidates are heuristic labels for downstream estimation only"
                    .to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        missing_evidence,
        measurement_boundary: ArtifactDescriptorMeasurementBoundaryV0 {
            boundary_id: format!("boundary:{slug}"),
            measured_layers: vec!["artifact-normalization".to_string()],
            measured_axes: vec![
                "sourceRefs".to_string(),
                "actionClassCandidates".to_string(),
                "scope".to_string(),
                "missingEvidence".to_string(),
                "forecastNonConclusions".to_string(),
            ],
            source_ref_ids,
            selected_region_refs,
            assumptions: vec![
                "markdown builder preserves selected source refs and boundary metadata".to_string(),
                "markdown builder does not run repository or runtime extraction".to_string(),
            ],
            unsupported_constructs: vec![
                "operation support probability".to_string(),
                "ground truth architecture reconstruction".to_string(),
                "future outcome causality".to_string(),
                "implicit requirements not written in the markdown input".to_string(),
            ],
            missing_evidence_ids,
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        forecast_non_conclusions: strings(&REQUIRED_FORECAST_NON_CONCLUSIONS),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn build_artifact_descriptor_from_github_issue_json(
    path_or_url: &str,
    value: &Value,
) -> ArtifactDescriptorV0 {
    let title = json_string(value, &["title"]).unwrap_or_else(|| fallback_title(path_or_url));
    let slug = slugify(&title);
    let source_ref_id = format!("source:github-issue-json:{slug}");
    let path = json_string(value, &["html_url", "url"]).unwrap_or_else(|| path_or_url.to_string());
    let stable_ref = json_u64(value, &["number"]).map(|number| format!("GitHub Issue #{number}"));
    let retained_fields = retained_json_fields(
        value,
        &[
            "number",
            "title",
            "body",
            "state",
            "labels",
            "assignees",
            "milestone",
            "html_url",
        ],
    );
    let body = json_string(value, &["body"]).unwrap_or_default();
    let normalized_text = format!(
        "{}\n{}\n{}",
        title,
        body,
        json_labels_text(value, "labels").unwrap_or_default()
    );
    let source_refs = vec![source_ref(
        &source_ref_id,
        "github-issue-json",
        &path,
        stable_ref.as_deref(),
        "primary GitHub Issue JSON artifact input",
        &retained_fields
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
    )];
    build_json_descriptor(
        path_or_url,
        "issue",
        title,
        slug,
        source_ref_id,
        source_refs,
        normalized_text,
        "normalizes GitHub Issue JSON before operation support estimation",
        "github issue json adapter preserves selected source refs and boundary metadata",
        vec![
            missing_evidence(
                "missing:github-api-context",
                "github-api-context",
                "GitHub Issue JSON adapter consumes a provided JSON artifact and does not fetch authenticated API context",
                "private labels, project fields, linked PRs, and hidden discussion remain unavailable unless supplied",
                "unmeasured",
            ),
            missing_evidence(
                "missing:runtime-evidence",
                "runtime-evidence",
                "GitHub Issue JSON adapter does not observe runtime traces",
                "runtime propagation remains a downstream boundary item",
                "unmeasured",
            ),
            missing_evidence(
                "missing:accepted-pr-history",
                "accepted-pr-history",
                "GitHub Issue JSON adapter does not infer accepted PR history from the issue artifact",
                "accepted support cannot be inferred from this descriptor",
                "missing",
            ),
        ],
    )
}

pub fn build_artifact_descriptor_from_ai_proposal_json(
    path_or_url: &str,
    value: &Value,
) -> ArtifactDescriptorV0 {
    let title = json_string(value, &["title", "name", "proposalTitle"])
        .unwrap_or_else(|| fallback_title(path_or_url));
    let slug = slugify(&title);
    let source_ref_id = format!("source:ai-proposal-json:{slug}");
    let retained_fields = retained_json_fields(
        value,
        &[
            "title",
            "name",
            "summary",
            "body",
            "proposal",
            "changes",
            "targets",
            "rationale",
            "constraints",
            "model",
            "promptRef",
            "promptRefs",
            "policyRef",
            "policyRefs",
        ],
    );
    let normalized_text = json_text_projection(value);
    let source_refs = vec![source_ref(
        &source_ref_id,
        "ai-proposal-json",
        path_or_url,
        json_string(value, &["id", "proposalId"]).as_deref(),
        "primary AI proposal JSON artifact input",
        &retained_fields
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
    )];
    build_json_descriptor(
        path_or_url,
        "ai-proposal",
        title,
        slug,
        source_ref_id,
        source_refs,
        normalized_text,
        "normalizes AI proposal JSON before operation support estimation",
        "ai proposal json adapter preserves selected source refs and boundary metadata",
        vec![
            missing_evidence(
                "missing:human-review",
                "human-review",
                "AI proposal JSON adapter does not establish human review or acceptance",
                "proposal support remains candidate-only until reviewed evidence is supplied",
                "missing",
            ),
            missing_evidence(
                "missing:model-evaluation",
                "model-evaluation",
                "AI proposal JSON adapter does not evaluate model quality or benchmark performance",
                "forecast quality and proposal correctness remain unavailable",
                "unmeasured",
            ),
            missing_evidence(
                "missing:runtime-evidence",
                "runtime-evidence",
                "AI proposal JSON adapter does not observe runtime traces",
                "runtime propagation remains a downstream boundary item",
                "unmeasured",
            ),
        ],
    )
}

pub fn validate_artifact_descriptor_report(
    descriptor: &ArtifactDescriptorV0,
    input_path: &str,
) -> ArtifactDescriptorValidationReportV0 {
    let checks = vec![
        check_schema_version(descriptor),
        check_identity(descriptor),
        check_source_refs(descriptor),
        check_action_candidates(descriptor),
        check_scope_and_boundary(descriptor),
        check_missing_evidence(descriptor),
        check_non_conclusions(descriptor),
    ];
    let summary = ArtifactDescriptorValidationSummary {
        result: validation_result(&checks),
        source_ref_count: descriptor.source_refs.len(),
        action_class_candidate_count: descriptor.action_class_candidates.len(),
        missing_evidence_count: descriptor.missing_evidence.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArtifactDescriptorValidationReportV0 {
        schema_version: ARTIFACT_DESCRIPTOR_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ArtifactDescriptorValidationInput {
            schema_version: descriptor.schema_version.clone(),
            path: input_path.to_string(),
            descriptor_id: descriptor.descriptor_id.clone(),
            artifact_kind: descriptor.artifact_kind.clone(),
        },
        descriptor: descriptor.clone(),
        summary,
        checks,
    }
}

fn source_ref(
    source_ref_id: &str,
    source_kind: &str,
    path_or_url: &str,
    stable_ref: Option<&str>,
    evidence_role: &str,
    retained_fields: &[&str],
) -> ArtifactDescriptorSourceRefV0 {
    ArtifactDescriptorSourceRefV0 {
        source_ref_id: source_ref_id.to_string(),
        source_kind: source_kind.to_string(),
        path_or_url: path_or_url.to_string(),
        stable_ref: stable_ref.map(str::to_string),
        evidence_role: evidence_role.to_string(),
        retained_fields: strings(retained_fields),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn action_candidate(
    candidate_id: &str,
    action_class: &str,
    confidence: &str,
    source_ref_ids: &[&str],
    rationale: &str,
) -> ArtifactActionClassCandidateV0 {
    ArtifactActionClassCandidateV0 {
        candidate_id: candidate_id.to_string(),
        action_class: action_class.to_string(),
        confidence: confidence.to_string(),
        source_ref_ids: strings(source_ref_ids),
        rationale: rationale.to_string(),
        assumptions: vec![
            "candidate was inferred from selected source refs only".to_string(),
            "candidate does not imply an operation support estimate".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_FORECAST_NON_CONCLUSIONS),
    }
}

fn missing_evidence(
    evidence_id: &str,
    evidence_kind: &str,
    reason: &str,
    effect: &str,
    status: &str,
) -> ArtifactDescriptorMissingEvidenceV0 {
    ArtifactDescriptorMissingEvidenceV0 {
        evidence_id: evidence_id.to_string(),
        evidence_kind: evidence_kind.to_string(),
        reason: reason.to_string(),
        effect: effect.to_string(),
        status: status.to_string(),
        non_conclusions: vec![
            REQUIRED_NON_CONCLUSIONS[3].to_string(),
            "missing descriptor evidence remains a downstream forecast boundary item".to_string(),
        ],
    }
}

fn check_schema_version(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let mut check = validation_check(
        "artifact-descriptor-schema-version-supported",
        "artifact descriptor schema version is supported",
        if descriptor.schema_version == ARTIFACT_DESCRIPTOR_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported artifact descriptor schema: {}",
            descriptor.schema_version
        ));
    }
    check
}

fn check_identity(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let invalid = [
        ("descriptorId", descriptor.descriptor_id.trim().is_empty()),
        ("artifactKind", descriptor.artifact_kind.trim().is_empty()),
        ("artifactTitle", descriptor.artifact_title.trim().is_empty()),
    ]
    .into_iter()
    .filter_map(|(field, missing)| missing.then_some(field))
    .collect::<Vec<_>>();
    let unsupported_kind = !ALLOWED_ARTIFACT_KINDS.contains(&descriptor.artifact_kind.as_str());
    let mut check = validation_check(
        "artifact-descriptor-identity-present",
        "descriptor identity fields and artifact kind are valid",
        if invalid.is_empty() && !unsupported_kind {
            "pass"
        } else {
            "fail"
        },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!(
            "missing required identity fields: {}",
            invalid.join(", ")
        ));
    } else if unsupported_kind {
        check.reason = Some(format!(
            "unsupported artifactKind `{}`; expected one of {}",
            descriptor.artifact_kind,
            ALLOWED_ARTIFACT_KINDS.join(", ")
        ));
    }
    check
}

fn check_source_refs(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let mut missing = Vec::new();
    let mut seen = BTreeSet::new();
    let mut duplicates = Vec::new();
    for source in &descriptor.source_refs {
        if source.source_ref_id.trim().is_empty()
            || source.source_kind.trim().is_empty()
            || source.path_or_url.trim().is_empty()
            || source.evidence_role.trim().is_empty()
            || source.retained_fields.is_empty()
        {
            missing.push(source.source_ref_id.clone());
        }
        if !seen.insert(source.source_ref_id.as_str()) {
            duplicates.push(source.source_ref_id.clone());
        }
    }
    let mut check = validation_check(
        "artifact-descriptor-source-refs-retained",
        "source refs preserve source kind, location, role, and retained fields",
        if !descriptor.source_refs.is_empty() && missing.is_empty() && duplicates.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if descriptor.source_refs.is_empty() {
        check.reason = Some("at least one source ref is required".to_string());
    } else if !missing.is_empty() {
        check.reason = Some(format!(
            "source refs with missing metadata: {}",
            missing.join(", ")
        ));
    } else if !duplicates.is_empty() {
        check.reason = Some(format!(
            "duplicate sourceRefId values: {}",
            duplicates.join(", ")
        ));
    }
    check.count = Some(descriptor.source_refs.len());
    check
}

fn check_action_candidates(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let source_ids = descriptor
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.as_str())
        .collect::<BTreeSet<_>>();
    let invalid = descriptor
        .action_class_candidates
        .iter()
        .filter(|candidate| {
            candidate.candidate_id.trim().is_empty()
                || candidate.action_class.trim().is_empty()
                || candidate.confidence.trim().is_empty()
                || candidate.source_ref_ids.is_empty()
                || candidate
                    .source_ref_ids
                    .iter()
                    .any(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
        })
        .map(|candidate| candidate.candidate_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "artifact-descriptor-action-candidates-bounded",
        "action class candidates are non-empty and point to retained source refs",
        if !descriptor.action_class_candidates.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if descriptor.action_class_candidates.is_empty() {
        check.reason = Some("at least one action class candidate is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "action candidates with missing fields or dangling source refs: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(descriptor.action_class_candidates.len());
    check
}

fn check_scope_and_boundary(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let source_ids = descriptor
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.as_str())
        .collect::<BTreeSet<_>>();
    let missing_ids = descriptor
        .missing_evidence
        .iter()
        .map(|evidence| evidence.evidence_id.as_str())
        .collect::<BTreeSet<_>>();
    let boundary = &descriptor.measurement_boundary;
    let dangling_source_refs = boundary
        .source_ref_ids
        .iter()
        .filter(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let dangling_missing_evidence = boundary
        .missing_evidence_ids
        .iter()
        .filter(|evidence_id| !missing_ids.contains(evidence_id.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let scope_invalid = descriptor.scope.scope_id.trim().is_empty()
        || descriptor.scope.selected_region_refs.is_empty()
        || descriptor.scope.artifact_boundary.trim().is_empty();
    let boundary_invalid = boundary.boundary_id.trim().is_empty()
        || boundary.measured_layers.is_empty()
        || boundary.measured_axes.is_empty()
        || boundary.source_ref_ids.is_empty()
        || boundary.assumptions.is_empty();
    let mut check = validation_check(
        "artifact-descriptor-scope-and-measurement-boundary",
        "scope and measurement boundary retain selected regions, source refs, and missing evidence refs",
        if !scope_invalid
            && !boundary_invalid
            && dangling_source_refs.is_empty()
            && dangling_missing_evidence.is_empty()
        {
            "pass"
        } else {
            "fail"
        },
    );
    if scope_invalid {
        check.reason = Some(
            "scope must include scopeId, selectedRegionRefs, and artifactBoundary".to_string(),
        );
    } else if boundary_invalid {
        check.reason = Some(
            "measurement boundary must include id, layers, axes, source refs, and assumptions"
                .to_string(),
        );
    } else if !dangling_source_refs.is_empty() {
        check.reason = Some(format!(
            "measurement boundary references unknown source refs: {}",
            dangling_source_refs.join(", ")
        ));
    } else if !dangling_missing_evidence.is_empty() {
        check.reason = Some(format!(
            "measurement boundary references unknown missing evidence ids: {}",
            dangling_missing_evidence.join(", ")
        ));
    }
    check
}

fn check_missing_evidence(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let invalid = descriptor
        .missing_evidence
        .iter()
        .filter(|evidence| {
            evidence.evidence_id.trim().is_empty()
                || evidence.evidence_kind.trim().is_empty()
                || evidence.reason.trim().is_empty()
                || evidence.effect.trim().is_empty()
                || !ALLOWED_MISSING_EVIDENCE_STATUSES.contains(&evidence.status.as_str())
        })
        .map(|evidence| evidence.evidence_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "artifact-descriptor-missing-evidence-status",
        "missing evidence keeps explicit non-zero statuses",
        if invalid.is_empty() { "pass" } else { "fail" },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!(
            "missing evidence entries with invalid metadata or status: {}",
            invalid.join(", ")
        ));
        check.examples = invalid
            .iter()
            .map(|evidence_id| {
                generic_validation_example(
                    evidence_id,
                    "missingEvidence.status",
                    "expected missing/private/unmeasured/outOfScope",
                )
            })
            .collect();
    }
    check.count = Some(descriptor.missing_evidence.len());
    check
}

fn check_non_conclusions(descriptor: &ArtifactDescriptorV0) -> ValidationCheck {
    let missing_descriptor = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !descriptor
                .non_conclusions
                .iter()
                .any(|actual| actual == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let missing_forecast = REQUIRED_FORECAST_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !descriptor
                .forecast_non_conclusions
                .iter()
                .any(|actual| actual == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "artifact-descriptor-non-conclusions-preserved",
        "descriptor and forecast non-conclusions preserve theorem, ground-truth, and causal boundaries",
        if missing_descriptor.is_empty() && missing_forecast.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !missing_descriptor.is_empty() {
        check.reason = Some(format!(
            "missing descriptor non-conclusions: {}",
            missing_descriptor.join("; ")
        ));
    } else if !missing_forecast.is_empty() {
        check.reason = Some(format!(
            "missing forecast non-conclusions: {}",
            missing_forecast.join("; ")
        ));
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

fn extract_markdown_title(contents: &str) -> Option<String> {
    contents.lines().find_map(|line| {
        let trimmed = line.trim();
        if trimmed.starts_with("# ") {
            Some(trimmed.trim_start_matches('#').trim().to_string())
        } else {
            None
        }
    })
}

fn fallback_title(path_or_url: &str) -> String {
    path_or_url
        .rsplit(['/', '\\'])
        .next()
        .filter(|segment| !segment.trim().is_empty())
        .unwrap_or("markdown artifact")
        .trim_end_matches(".md")
        .replace(['_', '-'], " ")
}

fn infer_action_candidates(
    contents: &str,
    source_ref_id: &str,
) -> Vec<ArtifactActionClassCandidateV0> {
    let lower = contents.to_ascii_lowercase();
    let mut candidates = Vec::new();
    if contains_any(&lower, &["schema", "json", "descriptor"]) {
        candidates.push(action_candidate(
            "candidate:schema-definition",
            "schema-definition",
            "medium",
            &[source_ref_id],
            "Markdown input refers to schema, JSON, or descriptor work.",
        ));
    }
    if contains_any(&lower, &["validate", "validator", "test", "fixture"]) {
        candidates.push(action_candidate(
            "candidate:tooling-validation",
            "tooling-validation",
            "medium",
            &[source_ref_id],
            "Markdown input requests validation, fixtures, or tests.",
        ));
    }
    if contains_any(&lower, &["cli", "command", "entrypoint", "entry point"]) {
        candidates.push(action_candidate(
            "candidate:cli-entrypoint",
            "cli-entrypoint",
            "medium",
            &[source_ref_id],
            "Markdown input names a command or CLI entrypoint.",
        ));
    }
    if contains_any(&lower, &["refactor", "migrate", "migration", "split"]) {
        candidates.push(action_candidate(
            "candidate:structural-change",
            "structural-change",
            "low",
            &[source_ref_id],
            "Markdown input suggests structural or migration work.",
        ));
    }
    if candidates.is_empty() {
        candidates.push(action_candidate(
            "candidate:artifact-review",
            "artifact-review",
            "low",
            &[source_ref_id],
            "Markdown input does not expose a more specific action class.",
        ));
    }
    candidates
}

fn selected_region_refs(contents: &str, path_or_url: &str) -> Vec<String> {
    let mut refs = extract_section_values(contents, &["scope", "selected region", "target"]);
    refs.extend(extract_inline_refs(contents));
    if refs.is_empty() {
        refs.push(path_or_url.to_string());
    }
    dedupe_strings(refs)
}

fn excluded_region_refs(contents: &str) -> Vec<String> {
    let refs = extract_section_values(contents, &["non-goals", "out of scope", "excluded"]);
    if refs.is_empty() {
        vec![
            "operation-support-estimate".to_string(),
            "forecast-cone-probability".to_string(),
            "causal-outcome-prediction".to_string(),
        ]
    } else {
        dedupe_strings(refs)
    }
}

fn target_audience(contents: &str) -> Vec<String> {
    let refs = extract_section_values(contents, &["audience", "reviewer", "consumer"]);
    if refs.is_empty() {
        vec![
            "archsig-cli".to_string(),
            "sft-forecaster-pipeline".to_string(),
            "review-ci".to_string(),
        ]
    } else {
        dedupe_strings(refs)
    }
}

fn missing_evidence_from_markdown(contents: &str) -> Vec<ArtifactDescriptorMissingEvidenceV0> {
    let lower = contents.to_ascii_lowercase();
    let mut evidence = vec![
        missing_evidence(
            "missing:runtime-evidence",
            "runtime-evidence",
            "markdown descriptor builder does not observe runtime traces",
            "runtime propagation remains a downstream boundary item",
            "unmeasured",
        ),
        missing_evidence(
            "missing:accepted-pr-history",
            "accepted-pr-history",
            "markdown descriptor builder does not inspect accepted PR history",
            "accepted support cannot be inferred from this descriptor",
            "missing",
        ),
    ];
    if contains_any(&lower, &["todo", "tbd", "open question", "unknown"]) {
        evidence.push(missing_evidence(
            "missing:open-questions",
            "open-questions",
            "markdown input contains unresolved questions or placeholders",
            "downstream forecast must keep unresolved requirement boundaries",
            "missing",
        ));
    }
    evidence
}

fn build_json_descriptor(
    path_or_url: &str,
    artifact_kind: &str,
    title: String,
    slug: String,
    source_ref_id: String,
    source_refs: Vec<ArtifactDescriptorSourceRefV0>,
    normalized_text: String,
    artifact_boundary: &str,
    builder_assumption: &str,
    missing_evidence: Vec<ArtifactDescriptorMissingEvidenceV0>,
) -> ArtifactDescriptorV0 {
    let source_ref_ids = vec![source_ref_id.clone()];
    let selected_region_refs = selected_region_refs(&normalized_text, path_or_url);
    let excluded_region_refs = excluded_region_refs(&normalized_text);
    let target_audience = target_audience(&normalized_text);
    let missing_evidence_ids = missing_evidence
        .iter()
        .map(|evidence| evidence.evidence_id.clone())
        .collect::<Vec<_>>();

    ArtifactDescriptorV0 {
        schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
        descriptor_id: format!("descriptor:{slug}"),
        artifact_kind: artifact_kind.to_string(),
        artifact_title: title,
        source_refs,
        action_class_candidates: infer_action_candidates(&normalized_text, &source_ref_id),
        scope: ArtifactDescriptorScopeV0 {
            scope_id: format!("scope:{slug}"),
            selected_region_refs: selected_region_refs.clone(),
            excluded_region_refs,
            target_audience,
            artifact_boundary: artifact_boundary.to_string(),
            assumptions: vec![
                "JSON fields and retained text are bounded tooling evidence".to_string(),
                "action class candidates are heuristic labels for downstream estimation only"
                    .to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        missing_evidence,
        measurement_boundary: ArtifactDescriptorMeasurementBoundaryV0 {
            boundary_id: format!("boundary:{slug}"),
            measured_layers: vec!["artifact-normalization".to_string()],
            measured_axes: vec![
                "sourceRefs".to_string(),
                "actionClassCandidates".to_string(),
                "scope".to_string(),
                "missingEvidence".to_string(),
                "forecastNonConclusions".to_string(),
            ],
            source_ref_ids,
            selected_region_refs,
            assumptions: vec![
                builder_assumption.to_string(),
                "JSON builder does not run repository, runtime, or authenticated remote extraction"
                    .to_string(),
            ],
            unsupported_constructs: vec![
                "operation support probability".to_string(),
                "ground truth architecture reconstruction".to_string(),
                "future outcome causality".to_string(),
                "implicit requirements not present in the supplied JSON artifact".to_string(),
            ],
            missing_evidence_ids,
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        forecast_non_conclusions: strings(&REQUIRED_FORECAST_NON_CONCLUSIONS),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn extract_section_values(contents: &str, section_markers: &[&str]) -> Vec<String> {
    let mut values = Vec::new();
    let mut in_section = false;
    for line in contents.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('#') {
            let heading = trimmed.trim_start_matches('#').trim().to_ascii_lowercase();
            in_section = section_markers
                .iter()
                .any(|marker| heading.contains(marker));
            continue;
        }
        if !in_section {
            continue;
        }
        if let Some(item) = trimmed
            .strip_prefix("- [ ] ")
            .or_else(|| trimmed.strip_prefix("- [x] "))
            .or_else(|| trimmed.strip_prefix("- "))
            .or_else(|| trimmed.strip_prefix("* "))
        {
            let value = item.trim();
            if !value.is_empty() {
                values.push(value.to_string());
            }
        }
    }
    values
}

fn json_string(value: &Value, keys: &[&str]) -> Option<String> {
    keys.iter().find_map(|key| {
        value
            .get(*key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
            .map(str::to_string)
    })
}

fn json_u64(value: &Value, keys: &[&str]) -> Option<u64> {
    keys.iter()
        .find_map(|key| value.get(*key).and_then(Value::as_u64))
}

fn retained_json_fields(value: &Value, candidates: &[&str]) -> Vec<String> {
    let retained = candidates
        .iter()
        .filter(|key| value.get(**key).is_some())
        .map(|key| (*key).to_string())
        .collect::<Vec<_>>();
    if retained.is_empty() {
        vec!["json".to_string()]
    } else {
        retained
    }
}

fn json_labels_text(value: &Value, key: &str) -> Option<String> {
    let labels = value.get(key)?.as_array()?;
    let names = labels
        .iter()
        .filter_map(|label| {
            label
                .get("name")
                .and_then(Value::as_str)
                .or_else(|| label.as_str())
        })
        .collect::<Vec<_>>();
    (!names.is_empty()).then(|| names.join("\n"))
}

fn json_text_projection(value: &Value) -> String {
    let mut text = Vec::new();
    collect_json_text(value, &mut text);
    text.join("\n")
}

fn collect_json_text(value: &Value, output: &mut Vec<String>) {
    match value {
        Value::String(text) => {
            let trimmed = text.trim();
            if !trimmed.is_empty() {
                output.push(trimmed.to_string());
            }
        }
        Value::Array(values) => {
            for item in values {
                collect_json_text(item, output);
            }
        }
        Value::Object(map) => {
            for item in map.values() {
                collect_json_text(item, output);
            }
        }
        _ => {}
    }
}

fn extract_inline_refs(contents: &str) -> Vec<String> {
    let mut refs = Vec::new();
    let mut parts = contents.split('`');
    while let Some(_) = parts.next() {
        let Some(value) = parts.next() else {
            break;
        };
        let value = value.trim();
        if value.contains('/') || value.ends_with(".md") || value.ends_with(".json") {
            refs.push(value.to_string());
        }
    }
    refs
}

fn slugify(value: &str) -> String {
    let mut slug = String::new();
    let mut previous_dash = false;
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            previous_dash = false;
        } else if !previous_dash && !slug.is_empty() {
            slug.push('-');
            previous_dash = true;
        }
    }
    while slug.ends_with('-') {
        slug.pop();
    }
    if slug.is_empty() {
        "markdown-artifact".to_string()
    } else {
        slug
    }
}

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| haystack.contains(needle))
}

fn dedupe_strings(values: Vec<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    values
        .into_iter()
        .filter(|value| !value.trim().is_empty())
        .filter(|value| seen.insert(value.clone()))
        .collect()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}
