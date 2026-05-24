use std::collections::BTreeSet;

use crate::validation::{count_checks, validation_check};
use crate::{
    ARCHMAP_SCHEMA_VERSION, ArchMapDocumentV0, CalibrationObservedOutcomeRefV0,
    CandidateOperationFamilyV0, ConsequenceForecastConeRefV0, ForecastUsefulnessFeedbackV0,
    INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION,
    INTENT_ARCHMAP_ALIGNMENT_VALIDATION_REPORT_SCHEMA_VERSION,
    INTENT_CALIBRATION_RECORD_SCHEMA_VERSION, INTENT_CALIBRATION_VALIDATION_REPORT_SCHEMA_VERSION,
    INTENTMAP_SCHEMA_VERSION, INTENTMAP_VALIDATION_REPORT_SCHEMA_VERSION,
    IntentAlignmentBoundaryItemV0, IntentArchMapAlignmentItemV0, IntentArchMapAlignmentV0,
    IntentArchMapAlignmentValidationInput, IntentArchMapAlignmentValidationReportV0,
    IntentArchMapAlignmentValidationSummary, IntentArchMapArtifactRefV0, IntentBoundaryItemV0,
    IntentCalibrationMatchV0, IntentCalibrationRecordV0, IntentCalibrationValidationInput,
    IntentCalibrationValidationReportV0, IntentCalibrationValidationSummary, IntentItemV0,
    IntentMapArtifactRefV0, IntentMapGeneratorV0, IntentMapV0, IntentMapValidationInput,
    IntentMapValidationReportV0, IntentMapValidationSummary, IntentSourceRefV0,
    IntentSourceUniverseV0, KnownForbiddenOperationSupportV0, MissingDecisionObservedStatusV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION, OperationSupportDescriptorRefV0,
    OperationSupportEstimateV0, OperationSupportEvidenceBoundaryV0,
    OperationSupportPolicyConstraintV0, OperationSupportUnknownRemainderV0,
    PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION,
    PR_QUALITY_ANALYSIS_VALIDATION_REPORT_SCHEMA_VERSION, PrQualityAnalysisReportV0,
    PrQualityAnalysisValidationInput, PrQualityAnalysisValidationReportV0,
    PrQualityAnalysisValidationSummary, PrQualityArtifactRefV0, PrQualityCueV0,
    PrQualityReviewSummaryV0, ValidationCheck,
};

const INTENT_NON_CONCLUSIONS: [&str; 5] = [
    "IntentMap is an LLM-authored bounded semantic extraction, not implementation ground truth",
    "IntentMap does not provide an implementation plan completeness guarantee",
    "IntentMap confidence is review priority, not probability",
    "IntentMap does not compute forecast cone results",
    "missing decisions and ambiguous intents are retained, not filled by validation",
];

const ALIGNMENT_NON_CONCLUSIONS: [&str; 5] = [
    "AlignmentMap does not prove implementation impact",
    "AlignmentMap does not guarantee future outcome or quality",
    "intentUnaligned is planning boundary, not measured zero",
    "unsupported and ambiguous alignments remain review cues",
    "validation pass does not prove semantic correctness of LLM-authored maps",
];

const FORECAST_NON_CONCLUSIONS: [&str; 13] = [
    "operation support estimate is a bounded tooling estimate, not accepted PR history",
    "operation support estimate is not actual future support",
    "unknown support is not measured zero",
    "policy constraints do not prove global policy safety",
    "operation support estimate does not prove future trajectory safety",
    "confidence is relative to retained descriptor source refs",
    "evidence boundary does not complete extractor coverage",
    "unsupported constructs remain forecast boundary items",
    "Intent-aligned operation support is not forecast correctness",
    "Intent-aligned forecast does not assign probabilities",
    "missing decisions remain planning boundaries",
    "unaligned intent is not measured zero",
    "tool projection does not prove causality or Lean theorem discharge",
];

const PR_QUALITY_NON_CONCLUSIONS: [&str; 4] = [
    "PR quality analysis is reviewer-facing evidence, not merge approval",
    "PR quality analysis does not prove architecture lawfulness",
    "missing evidence remains review boundary",
    "quality cues are not global rankings",
];

const CALIBRATION_NON_CONCLUSIONS: [&str; 4] = [
    "intent calibration record is empirical feedback, not causal proof",
    "observed implementation refs do not prove forecast correctness",
    "missing decision status is review evidence, not product decision resolution proof",
    "forecast usefulness feedback is qualitative and dataset-bound",
];

pub fn static_intent_map() -> IntentMapV0 {
    IntentMapV0 {
        schema_version: INTENTMAP_SCHEMA_VERSION.to_string(),
        intent_map_id: "fixture-intentmap-v0".to_string(),
        source_universe: IntentSourceUniverseV0 {
            universe_id: "intent-universe:coupon-prd".to_string(),
            source_refs: vec![IntentSourceRefV0 {
                source_ref_id: "source:prd:coupon".to_string(),
                source_kind: "prd".to_string(),
                path_or_url: "tools/archsig/tests/fixtures/minimal/coupon_prd.md".to_string(),
                stable_ref: Some("section:requirements".to_string()),
                evidence_role: "intent-source".to_string(),
                retained_fields: vec![
                    "operation".to_string(),
                    "workflow".to_string(),
                    "acceptance".to_string(),
                    "open-question".to_string(),
                ],
                non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
            }],
            included_kinds: vec!["prd".to_string(), "acceptance".to_string()],
            excluded_kinds: vec!["private-runtime-history".to_string()],
            boundary: "selected PRD sections only; implementation files are not inferred"
                .to_string(),
            non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
        },
        generator: IntentMapGeneratorV0 {
            authored_by: "llm".to_string(),
            prompt_ref:
                "tools/archsig/skills/intentmap-creater/references/intent-extraction-guide.md"
                    .to_string(),
            model_ref: "reviewer-supplied".to_string(),
            extraction_boundary:
                "extract semantic intent with source refs; do not invent missing decisions"
                    .to_string(),
            non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
        },
        items: vec![
            intent_item(
                "intent:coupon-apply-operation",
                "operation",
                "checkout.applyCoupon",
                &["preserve price invariant", "preserve audit trail"],
                &["exact file list", "runtime latency"],
                "measured",
                "high",
            ),
            intent_item(
                "intent:coupon-acceptance-test",
                "acceptance",
                "test oracle for valid and expired coupons",
                &["observable acceptance criterion"],
                &["implementation framework choice"],
                "assumed",
                "medium",
            ),
            intent_item(
                "intent:coupon-stackable-decision",
                "ambiguity",
                "whether coupons may stack",
                &["open product decision"],
                &["resolved behavior"],
                "decision-needed",
                "high",
            ),
        ],
        missing_decisions: vec![intent_boundary(
            "missing-decision:coupon-stacking",
            "missingDecision",
            &["intent:coupon-stackable-decision"],
            "PRD does not decide whether coupons may stack",
            "retain as planning boundary and do not choose a behavior",
        )],
        ambiguous_intents: vec![intent_boundary(
            "ambiguous-intent:discount-composition",
            "ambiguousIntent",
            &["intent:coupon-stackable-decision"],
            "discount composition policy can change forecast branch",
            "route through alignment and forecast unknown remainder",
        )],
        missing_evidence: vec![intent_boundary(
            "missing-evidence:runtime-coupon-traffic",
            "missingEvidence",
            &["intent:coupon-apply-operation"],
            "runtime coupon usage is not supplied by PRD",
            "retain as evidence need, not as zero load",
        )],
        non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
    }
}

pub fn validate_intent_map(
    intent_map: &IntentMapV0,
    input_path: &str,
) -> IntentMapValidationReportV0 {
    let checks = vec![
        check_intent_schema(intent_map),
        check_intent_source_refs(intent_map),
        check_intent_items(intent_map),
        check_intent_boundaries(intent_map),
        check_intent_non_conclusions(intent_map),
    ];
    let summary = IntentMapValidationSummary {
        result: validation_result(&checks),
        intent_item_count: intent_map.items.len(),
        missing_decision_count: intent_map.missing_decisions.len(),
        ambiguous_intent_count: intent_map.ambiguous_intents.len(),
        missing_evidence_count: intent_map.missing_evidence.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };
    IntentMapValidationReportV0 {
        schema_version: INTENTMAP_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: IntentMapValidationInput {
            schema_version: intent_map.schema_version.clone(),
            path: input_path.to_string(),
            intent_map_id: intent_map.intent_map_id.clone(),
        },
        intent_map: intent_map.clone(),
        summary,
        checks,
    }
}

pub fn static_intent_archmap_alignment() -> IntentArchMapAlignmentV0 {
    let intent_map = static_intent_map();
    IntentArchMapAlignmentV0 {
        schema_version: INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION.to_string(),
        alignment_map_id: "fixture-intent-archmap-alignment-v0".to_string(),
        intent_map_ref: IntentMapArtifactRefV0 {
            schema_version: INTENTMAP_SCHEMA_VERSION.to_string(),
            intent_map_id: intent_map.intent_map_id.clone(),
            path: "tools/archsig/tests/fixtures/minimal/intentmap.json".to_string(),
            intent_item_ids: intent_map
                .items
                .iter()
                .map(|item| item.intent_item_id.clone())
                .collect(),
            non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
        },
        archmap_ref: IntentArchMapArtifactRefV0 {
            schema_version: ARCHMAP_SCHEMA_VERSION.to_string(),
            map_id: "fixture-archmap-v0".to_string(),
            path: "tools/archsig/tests/fixtures/minimal/archmap.json".to_string(),
            map_item_ids: vec![
                "object-route-users".to_string(),
                "policy-layered-route-service".to_string(),
                "runtime-unmeasured-boundary".to_string(),
            ],
            non_conclusions: strings(&ALIGNMENT_NON_CONCLUSIONS),
        },
        alignments: vec![
            alignment_item(
                "alignment:coupon-operation-route",
                "intentToObject",
                "intent:coupon-apply-operation",
                &["object-route-users"],
                &["operation target"],
                &["exact implementation diff"],
                "medium",
            ),
            alignment_item(
                "alignment:coupon-test-oracle",
                "intentToTestOracle",
                "intent:coupon-acceptance-test",
                &["policy-layered-route-service"],
                &["test oracle candidate"],
                &["test framework selection"],
                "medium",
            ),
        ],
        unaligned_intents: vec![alignment_boundary(
            "unaligned:coupon-stacking",
            "intentUnaligned",
            &["intent:coupon-stackable-decision"],
            &[],
            "current ArchMap has no resolved stacking policy target",
            "retain as planning risk and unknown forecast remainder",
        )],
        unsupported_intents: vec![alignment_boundary(
            "unsupported:runtime-traffic",
            "unsupportedIntent",
            &["intent:coupon-apply-operation"],
            &["runtime-unmeasured-boundary"],
            "runtime traffic evidence is outside selected ArchMap",
            "retain as runtime evidence need",
        )],
        ambiguous_alignments: vec![alignment_boundary(
            "ambiguous:discount-policy",
            "ambiguousAlignment",
            &["intent:coupon-stackable-decision"],
            &["policy-layered-route-service"],
            "policy boundary is related but not a resolved stacking decision",
            "review before forecast interpretation",
        )],
        missing_evidence: vec![alignment_boundary(
            "missing-evidence:coupon-runtime",
            "missingEvidence",
            &["intent:coupon-apply-operation"],
            &["runtime-unmeasured-boundary"],
            "runtime evidence is absent",
            "keep as missing evidence, not measured zero",
        )],
        non_conclusions: strings(&ALIGNMENT_NON_CONCLUSIONS),
    }
}

pub fn validate_intent_archmap_alignment(
    alignment: &IntentArchMapAlignmentV0,
    intent_map: Option<&IntentMapV0>,
    archmap: Option<&ArchMapDocumentV0>,
    input_path: &str,
) -> IntentArchMapAlignmentValidationReportV0 {
    let checks = vec![
        check_alignment_schema(alignment),
        check_alignment_refs(alignment, intent_map, archmap),
        check_alignment_items(alignment),
        check_alignment_boundaries(alignment),
        check_alignment_non_conclusions(alignment),
    ];
    let summary = IntentArchMapAlignmentValidationSummary {
        result: validation_result(&checks),
        alignment_count: alignment.alignments.len(),
        unaligned_intent_count: alignment.unaligned_intents.len(),
        unsupported_intent_count: alignment.unsupported_intents.len(),
        ambiguous_alignment_count: alignment.ambiguous_alignments.len(),
        missing_evidence_count: alignment.missing_evidence.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };
    IntentArchMapAlignmentValidationReportV0 {
        schema_version: INTENT_ARCHMAP_ALIGNMENT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: IntentArchMapAlignmentValidationInput {
            schema_version: alignment.schema_version.clone(),
            path: input_path.to_string(),
            alignment_map_id: alignment.alignment_map_id.clone(),
            intent_map_id: alignment.intent_map_ref.intent_map_id.clone(),
            archmap_id: alignment.archmap_ref.map_id.clone(),
        },
        alignment_map: alignment.clone(),
        summary,
        checks,
    }
}

pub fn build_operation_support_estimate_from_intent_alignment(
    intent_map: &IntentMapV0,
    archmap: &ArchMapDocumentV0,
    alignment: &IntentArchMapAlignmentV0,
) -> OperationSupportEstimateV0 {
    let source_ref_ids = intent_source_ids(intent_map);
    let candidate_operation_families = alignment
        .alignments
        .iter()
        .map(|item| {
            let intent_kind = intent_map
                .items
                .iter()
                .find(|intent| intent.intent_item_id == item.intent_item_ref)
                .map(|intent| intent.intent_kind.as_str())
                .unwrap_or("intent");
            CandidateOperationFamilyV0 {
                family_id: format!("family:intent:{}", stable_id(&item.intent_item_ref)),
                operation_family: format!("intent-{intent_kind}-{}", item.alignment_kind),
                support_kind: "supported-by-intent-archmap-alignment".to_string(),
                action_class_candidate_ids: vec![item.intent_item_ref.clone()],
                source_ref_ids: source_ref_ids.clone(),
                confidence: item.confidence.clone(),
                rationale: format!(
                    "Derived from {} aligned to ArchMap refs {}.",
                    item.intent_item_ref,
                    item.archmap_item_refs.join(", ")
                ),
                assumptions: vec![
                    "operation family is derived from retained IntentMap and AlignmentMap refs"
                        .to_string(),
                    "alignment confidence is review priority, not probability".to_string(),
                ],
                non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
            }
        })
        .collect::<Vec<_>>();
    let family_ids = candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: format!(
            "estimate:intent-alignment:{}",
            stable_id(&alignment.alignment_map_id)
        ),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION.to_string(),
            descriptor_id: alignment.alignment_map_id.clone(),
            artifact_kind: "intent-archmap-alignment".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids: intent_map
                .items
                .iter()
                .map(|item| item.intent_item_id.clone())
                .collect(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        candidate_operation_families,
        policy_constraints: vec![OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:intent-alignment:no-overclaim".to_string(),
            constraint_kind: "forecast-boundary".to_string(),
            applies_to_family_ids: family_ids.clone(),
            source_ref_ids: source_ref_ids.clone(),
            rule: "Do not treat IntentMap x ArchMap alignment as forecast correctness.".to_string(),
            safety_claim_boundary:
                "projection preserves alignment evidence and planning boundaries only".to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:intent-alignment:probability".to_string(),
            operation_family: "future-outcome-probability".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            constraint_refs: vec!["constraint:intent-alignment:no-overclaim".to_string()],
            reason: "IntentMap and AlignmentMap retain semantic links, not future outcome probabilities"
                .to_string(),
            boundary: "probability, causality, and quality ranking remain non-conclusions"
                .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        unknown_remainder: vec![OperationSupportUnknownRemainderV0 {
            remainder_id: "unknown:intent-alignment-boundary".to_string(),
            affected_family_ids: family_ids,
            source_ref_ids: source_ref_ids.clone(),
            unknown_axes: planning_unknown_axes(intent_map, alignment),
            reason:
                "missing decisions, ambiguous alignments, unsupported intents, and runtime evidence needs remain unresolved"
                    .to_string(),
            treatment:
                "retain as unknown planning remainder for ForecastCone and ConsequenceEnvelope"
                    .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: format!(
                "boundary:intent-alignment:{}",
                stable_id(&alignment.alignment_map_id)
            ),
            source_ref_ids,
            measurement_boundary_refs: vec![
                intent_map.intent_map_id.clone(),
                archmap.map_id.clone(),
                alignment.alignment_map_id.clone(),
            ],
            confidence_boundary:
                "IntentMap and AlignmentMap confidence is qualitative review priority".to_string(),
            evidence_kinds: vec![
                "intent-map".to_string(),
                "archmap".to_string(),
                "alignment-map".to_string(),
            ],
            unsupported_constructs: alignment
                .unsupported_intents
                .iter()
                .map(|item| item.reason.clone())
                .collect(),
            assumptions: vec![
                "LLM-authored maps were reviewed through validation reports".to_string(),
                "current ArchMap is the selected architecture universe".to_string(),
            ],
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }
}

pub fn static_pr_quality_analysis_report() -> PrQualityAnalysisReportV0 {
    PrQualityAnalysisReportV0 {
        schema_version: PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-pr-quality-analysis-v0".to_string(),
        archmap_ref: static_intent_archmap_alignment().archmap_ref,
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
        missing_evidence: vec![alignment_boundary(
            "missing-evidence:pr-runtime",
            "missingEvidence",
            &[],
            &["runtime-unmeasured-boundary"],
            "runtime evidence was not supplied to selected PR analysis",
            "retain as review cue, not merge blocker by itself",
        )],
        review_summary: PrQualityReviewSummaryV0 {
            summary_id: "summary:pr-quality".to_string(),
            cue_count: 3,
            missing_evidence_count: 1,
            reviewer_notes: vec![
                "ArchMap is the PR-side source; IntentMap planning flow is not required for PR quality analysis"
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

pub fn static_intent_calibration_record() -> IntentCalibrationRecordV0 {
    let intent_map = static_intent_map();
    IntentCalibrationRecordV0 {
        schema_version: INTENT_CALIBRATION_RECORD_SCHEMA_VERSION.to_string(),
        calibration_id: "fixture-intent-calibration-record-v0".to_string(),
        intent_map_ref: IntentMapArtifactRefV0 {
            schema_version: INTENTMAP_SCHEMA_VERSION.to_string(),
            intent_map_id: intent_map.intent_map_id.clone(),
            path: "tools/archsig/tests/fixtures/minimal/intentmap.json".to_string(),
            intent_item_ids: intent_map
                .items
                .iter()
                .map(|item| item.intent_item_id.clone())
                .collect(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        },
        forecast_cone_ref: ConsequenceForecastConeRefV0 {
            forecast_cone_schema_version: "forecast-cone-skeleton-v0".to_string(),
            cone_id: "cone:intent-alignment".to_string(),
            operation_support_estimate_id: "estimate:intent-alignment".to_string(),
            source_ref_ids: vec!["source:prd:coupon".to_string()],
            forecast_boundary_refs: vec!["boundary:intent-alignment".to_string()],
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        },
        observed_artifact_refs: vec![CalibrationObservedOutcomeRefV0 {
            observed_ref_id: "observed:pr:coupon-tests".to_string(),
            observed_kind: "implementation-pr".to_string(),
            path_or_url: "https://example.invalid/pr/1".to_string(),
            status: "observed".to_string(),
            b10_refs: vec!["B10:implementation-pr".to_string()],
            b11_refs: vec!["B11:runtime-observation-needed".to_string()],
            evidence_boundary: "selected PR metadata only".to_string(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        }],
        intent_matches: vec![IntentCalibrationMatchV0 {
            match_id: "match:coupon-operation".to_string(),
            intent_item_id: "intent:coupon-apply-operation".to_string(),
            forecast_item_id: "path:family-intent-coupon-apply-operation".to_string(),
            observed_ref_id: Some("observed:pr:coupon-tests".to_string()),
            status: "observed-partial".to_string(),
            rationale: "PR evidence addresses the operation intent but not runtime traffic"
                .to_string(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        }],
        missing_decision_statuses: vec![MissingDecisionObservedStatusV0 {
            decision_id: "missing-decision:coupon-stacking".to_string(),
            intent_item_refs: vec!["intent:coupon-stackable-decision".to_string()],
            status: "unresolved".to_string(),
            observed_ref_ids: Vec::new(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        }],
        forecast_usefulness_feedback: vec![ForecastUsefulnessFeedbackV0 {
            feedback_id: "feedback:coupon-planning".to_string(),
            intent_item_refs: vec!["intent:coupon-apply-operation".to_string()],
            forecast_item_refs: vec!["path:family-intent-coupon-apply-operation".to_string()],
            feedback_kind: "review-focus-useful".to_string(),
            reviewer_note:
                "forecast cue identified runtime evidence need before implementation review"
                    .to_string(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        }],
        non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
    }
}

pub fn validate_intent_calibration_record(
    record: &IntentCalibrationRecordV0,
    input_path: &str,
) -> IntentCalibrationValidationReportV0 {
    let checks = vec![
        simple_schema_check(
            "intent-calibration-schema-version-supported",
            &record.schema_version,
            INTENT_CALIBRATION_RECORD_SCHEMA_VERSION,
        ),
        check_intent_calibration_refs(record),
        check_intent_calibration_boundaries(record),
    ];
    let summary = IntentCalibrationValidationSummary {
        result: validation_result(&checks),
        intent_match_count: record.intent_matches.len(),
        observed_artifact_count: record.observed_artifact_refs.len(),
        missing_decision_status_count: record.missing_decision_statuses.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };
    IntentCalibrationValidationReportV0 {
        schema_version: INTENT_CALIBRATION_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: IntentCalibrationValidationInput {
            schema_version: record.schema_version.clone(),
            path: input_path.to_string(),
            calibration_id: record.calibration_id.clone(),
            intent_map_id: record.intent_map_ref.intent_map_id.clone(),
        },
        record: record.clone(),
        summary,
        checks,
    }
}

fn check_intent_schema(intent_map: &IntentMapV0) -> ValidationCheck {
    simple_schema_check(
        "intentmap-schema-version-supported",
        &intent_map.schema_version,
        INTENTMAP_SCHEMA_VERSION,
    )
}

fn check_intent_source_refs(intent_map: &IntentMapV0) -> ValidationCheck {
    let invalid = intent_map.intent_map_id.trim().is_empty()
        || intent_map.source_universe.source_refs.is_empty()
        || intent_map.source_universe.boundary.trim().is_empty()
        || intent_map.generator.prompt_ref.trim().is_empty()
        || intent_map.source_universe.source_refs.iter().any(|source| {
            source.source_ref_id.trim().is_empty() || source.retained_fields.is_empty()
        });
    let mut check = validation_check(
        "intentmap-source-universe-retained",
        "IntentMap retains source refs, prompt boundary, and selected universe",
        if invalid { "fail" } else { "pass" },
    );
    check.count = Some(intent_map.source_universe.source_refs.len());
    check
}

fn check_intent_items(intent_map: &IntentMapV0) -> ValidationCheck {
    let source_ids = intent_source_id_set(intent_map);
    let invalid = intent_map
        .items
        .iter()
        .filter(|item| {
            item.intent_item_id.trim().is_empty()
                || item.intent_kind.trim().is_empty()
                || item.source_refs.is_empty()
                || item
                    .source_refs
                    .iter()
                    .any(|source_ref| !source_ids.contains(source_ref.as_str()))
                || item.target_intent_ref.trim().is_empty()
                || item.claim_classification.trim().is_empty()
                || item.confidence.trim().is_empty()
                || invalid_claim_classification(&item.claim_classification)
                || item.confidence.to_ascii_lowercase().contains("probability")
        })
        .map(|item| item.intent_item_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "intentmap-items-source-bound",
        "intent items retain required fields, source refs, claim classification, and confidence boundary",
        if !intent_map.items.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if intent_map.items.is_empty() {
        check.reason = Some("at least one intent item is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!("invalid intent items: {}", invalid.join(", ")));
    }
    check.count = Some(intent_map.items.len());
    check
}

fn check_intent_boundaries(intent_map: &IntentMapV0) -> ValidationCheck {
    let intent_ids = intent_id_set(intent_map);
    let source_ids = intent_source_id_set(intent_map);
    let mut invalid =
        invalid_intent_boundaries(&intent_map.missing_decisions, &intent_ids, &source_ids);
    invalid.extend(invalid_intent_boundaries(
        &intent_map.ambiguous_intents,
        &intent_ids,
        &source_ids,
    ));
    invalid.extend(invalid_intent_boundaries(
        &intent_map.missing_evidence,
        &intent_ids,
        &source_ids,
    ));
    let boundary_count = intent_map.missing_decisions.len()
        + intent_map.ambiguous_intents.len()
        + intent_map.missing_evidence.len();
    let mut check = validation_check(
        "intentmap-boundaries-first-class",
        "missing decisions, ambiguous intents, and missing evidence are explicit boundaries",
        if boundary_count > 0 && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if boundary_count == 0 {
        check.reason = Some("at least one planning or evidence boundary is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "invalid intent boundary refs: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(boundary_count);
    check
}

fn check_intent_non_conclusions(intent_map: &IntentMapV0) -> ValidationCheck {
    required_non_conclusions_check(
        "intentmap-non-conclusions-preserved",
        &intent_map.non_conclusions,
        &INTENT_NON_CONCLUSIONS,
    )
}

fn check_alignment_schema(alignment: &IntentArchMapAlignmentV0) -> ValidationCheck {
    simple_schema_check(
        "intent-archmap-alignment-schema-version-supported",
        &alignment.schema_version,
        INTENT_ARCHMAP_ALIGNMENT_SCHEMA_VERSION,
    )
}

fn check_alignment_refs(
    alignment: &IntentArchMapAlignmentV0,
    intent_map: Option<&IntentMapV0>,
    archmap: Option<&ArchMapDocumentV0>,
) -> ValidationCheck {
    let mut invalid = Vec::new();
    if let Some(intent_map) = intent_map {
        let ids = intent_id_set(intent_map);
        invalid.extend(
            alignment
                .intent_map_ref
                .intent_item_ids
                .iter()
                .filter(|id| !ids.contains(id.as_str()))
                .cloned(),
        );
    }
    if let Some(archmap) = archmap {
        let ids = archmap_id_set(archmap);
        invalid.extend(
            alignment
                .archmap_ref
                .map_item_ids
                .iter()
                .filter(|id| !ids.contains(id.as_str()))
                .cloned(),
        );
    }
    let missing = alignment.intent_map_ref.intent_item_ids.is_empty()
        || alignment.archmap_ref.map_item_ids.is_empty()
        || alignment.intent_map_ref.schema_version != INTENTMAP_SCHEMA_VERSION
        || alignment.archmap_ref.schema_version != ARCHMAP_SCHEMA_VERSION;
    let mut check = validation_check(
        "intent-archmap-alignment-artifact-refs-retained",
        "AlignmentMap retains IntentMap and ArchMap refs and validates supplied dangling refs",
        if !missing && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if missing {
        check.reason = Some(
            "IntentMap and ArchMap refs with schema versions and ids are required".to_string(),
        );
    } else if !invalid.is_empty() {
        check.reason = Some(format!("dangling artifact refs: {}", invalid.join(", ")));
    }
    check
}

fn check_alignment_items(alignment: &IntentArchMapAlignmentV0) -> ValidationCheck {
    let intent_ids = alignment
        .intent_map_ref
        .intent_item_ids
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let archmap_ids = alignment
        .archmap_ref
        .map_item_ids
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let invalid = alignment
        .alignments
        .iter()
        .filter(|item| {
            item.alignment_id.trim().is_empty()
                || invalid_alignment_kind(&item.alignment_kind)
                || !intent_ids.contains(item.intent_item_ref.as_str())
                || (item.alignment_kind != "intentUnaligned" && item.archmap_item_refs.is_empty())
                || item
                    .archmap_item_refs
                    .iter()
                    .any(|id| !archmap_ids.contains(id.as_str()))
                || item.confidence.to_ascii_lowercase().contains("probability")
        })
        .map(|item| item.alignment_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "intent-archmap-alignment-items-linked",
        "alignment items link intent refs and ArchMap refs without treating unsupported intent as zero",
        if !alignment.alignments.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if alignment.alignments.is_empty() {
        check.reason = Some("at least one alignment item is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!("invalid alignment items: {}", invalid.join(", ")));
    }
    check.count = Some(alignment.alignments.len());
    check
}

fn check_alignment_boundaries(alignment: &IntentArchMapAlignmentV0) -> ValidationCheck {
    let boundary_count = alignment.unaligned_intents.len()
        + alignment.unsupported_intents.len()
        + alignment.ambiguous_alignments.len()
        + alignment.missing_evidence.len();
    let invalid = alignment
        .unaligned_intents
        .iter()
        .chain(alignment.unsupported_intents.iter())
        .chain(alignment.ambiguous_alignments.iter())
        .chain(alignment.missing_evidence.iter())
        .filter(|item| {
            item.boundary_id.trim().is_empty()
                || item.intent_item_refs.is_empty()
                || item.reason.trim().is_empty()
                || treats_unknown_as_zero(&item.treatment)
        })
        .map(|item| item.boundary_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "intent-archmap-alignment-boundaries-not-measured-zero",
        "unaligned, unsupported, ambiguous, and missing-evidence boundaries remain explicit",
        if boundary_count > 0 && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if boundary_count == 0 {
        check.reason = Some("at least one alignment boundary is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "invalid measured-zero boundary treatment: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(boundary_count);
    check
}

fn check_alignment_non_conclusions(alignment: &IntentArchMapAlignmentV0) -> ValidationCheck {
    required_non_conclusions_check(
        "intent-archmap-alignment-non-conclusions-preserved",
        &alignment.non_conclusions,
        &ALIGNMENT_NON_CONCLUSIONS,
    )
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
    let mut check = required_non_conclusions_check(
        "pr-quality-analysis-non-conclusions-preserved",
        &report.non_conclusions,
        &PR_QUALITY_NON_CONCLUSIONS,
    );
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

fn check_intent_calibration_refs(record: &IntentCalibrationRecordV0) -> ValidationCheck {
    let intent_ids = record
        .intent_map_ref
        .intent_item_ids
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let observed_ids = record
        .observed_artifact_refs
        .iter()
        .map(|item| item.observed_ref_id.as_str())
        .collect::<BTreeSet<_>>();
    let invalid = record
        .intent_matches
        .iter()
        .filter(|item| {
            !intent_ids.contains(item.intent_item_id.as_str())
                || item.forecast_item_id.trim().is_empty()
                || item
                    .observed_ref_id
                    .as_ref()
                    .is_some_and(|id| !observed_ids.contains(id.as_str()))
        })
        .map(|item| item.match_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "intent-calibration-intent-forecast-observed-linked",
        "calibration links IntentMap items, forecast items, and observed implementation refs",
        if !record.intent_matches.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!(
            "invalid calibration matches: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(record.intent_matches.len());
    check
}

fn check_intent_calibration_boundaries(record: &IntentCalibrationRecordV0) -> ValidationCheck {
    let statuses_ok = record.missing_decision_statuses.iter().all(|status| {
        matches!(
            status.status.as_str(),
            "resolved" | "unresolved" | "partially-resolved"
        )
    });
    let mut check = required_non_conclusions_check(
        "intent-calibration-causality-boundary-preserved",
        &record.non_conclusions,
        &CALIBRATION_NON_CONCLUSIONS,
    );
    if check.result == "pass" && !statuses_ok {
        check.result = "fail".to_string();
        check.reason = Some(
            "missing decision status must be resolved, partially-resolved, or unresolved"
                .to_string(),
        );
    }
    check
}

fn intent_item(
    intent_item_id: &str,
    intent_kind: &str,
    target_intent_ref: &str,
    preserves: &[&str],
    forgets: &[&str],
    claim_classification: &str,
    confidence: &str,
) -> IntentItemV0 {
    IntentItemV0 {
        intent_item_id: intent_item_id.to_string(),
        intent_kind: intent_kind.to_string(),
        source_refs: vec!["source:prd:coupon".to_string()],
        target_intent_ref: target_intent_ref.to_string(),
        preserves: strings(preserves),
        forgets: strings(forgets),
        claim_classification: claim_classification.to_string(),
        confidence: confidence.to_string(),
        required_assumptions: vec!["selected PRD text is the intent source universe".to_string()],
        missing_decisions: Vec::new(),
        missing_evidence: Vec::new(),
        non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
    }
}

fn intent_boundary(
    boundary_id: &str,
    boundary_kind: &str,
    intent_item_refs: &[&str],
    reason: &str,
    treatment: &str,
) -> IntentBoundaryItemV0 {
    IntentBoundaryItemV0 {
        boundary_id: boundary_id.to_string(),
        boundary_kind: boundary_kind.to_string(),
        intent_item_refs: strings(intent_item_refs),
        source_ref_ids: vec!["source:prd:coupon".to_string()],
        reason: reason.to_string(),
        treatment: treatment.to_string(),
        non_conclusions: strings(&INTENT_NON_CONCLUSIONS),
    }
}

fn alignment_item(
    alignment_id: &str,
    alignment_kind: &str,
    intent_item_ref: &str,
    archmap_item_refs: &[&str],
    preserves: &[&str],
    forgets: &[&str],
    confidence: &str,
) -> IntentArchMapAlignmentItemV0 {
    IntentArchMapAlignmentItemV0 {
        alignment_id: alignment_id.to_string(),
        alignment_kind: alignment_kind.to_string(),
        intent_item_ref: intent_item_ref.to_string(),
        archmap_item_refs: strings(archmap_item_refs),
        preserves: strings(preserves),
        forgets: strings(forgets),
        confidence: confidence.to_string(),
        missing_decisions: Vec::new(),
        missing_evidence: Vec::new(),
        non_conclusions: strings(&ALIGNMENT_NON_CONCLUSIONS),
    }
}

fn alignment_boundary(
    boundary_id: &str,
    boundary_kind: &str,
    intent_item_refs: &[&str],
    archmap_item_refs: &[&str],
    reason: &str,
    treatment: &str,
) -> IntentAlignmentBoundaryItemV0 {
    IntentAlignmentBoundaryItemV0 {
        boundary_id: boundary_id.to_string(),
        boundary_kind: boundary_kind.to_string(),
        intent_item_refs: strings(intent_item_refs),
        archmap_item_refs: strings(archmap_item_refs),
        reason: reason.to_string(),
        treatment: treatment.to_string(),
        non_conclusions: strings(&ALIGNMENT_NON_CONCLUSIONS),
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

fn required_non_conclusions_check(
    id: &str,
    actual: &[String],
    required: &[&str],
) -> ValidationCheck {
    let missing = required
        .iter()
        .filter(|required| !actual.iter().any(|entry| entry == *required))
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        id,
        "required non-conclusions are preserved",
        if missing.is_empty() { "pass" } else { "fail" },
    );
    if !missing.is_empty() {
        check.reason = Some(format!("missing non-conclusions: {}", missing.join("; ")));
    }
    check
}

fn invalid_intent_boundaries(
    boundaries: &[IntentBoundaryItemV0],
    intent_ids: &BTreeSet<&str>,
    source_ids: &BTreeSet<&str>,
) -> Vec<String> {
    boundaries
        .iter()
        .filter(|item| {
            item.boundary_id.trim().is_empty()
                || item.boundary_kind.trim().is_empty()
                || item.intent_item_refs.is_empty()
                || item.source_ref_ids.is_empty()
                || item.reason.trim().is_empty()
                || item.treatment.trim().is_empty()
                || treats_unknown_as_zero(&item.treatment)
                || item
                    .intent_item_refs
                    .iter()
                    .any(|id| !intent_ids.contains(id.as_str()))
                || item
                    .source_ref_ids
                    .iter()
                    .any(|id| !source_ids.contains(id.as_str()))
        })
        .map(|item| item.boundary_id.clone())
        .collect()
}

fn planning_unknown_axes(
    intent_map: &IntentMapV0,
    alignment: &IntentArchMapAlignmentV0,
) -> Vec<String> {
    let mut axes = intent_map
        .missing_decisions
        .iter()
        .chain(intent_map.ambiguous_intents.iter())
        .chain(intent_map.missing_evidence.iter())
        .map(|item| format!("{}: {}", item.boundary_kind, item.reason))
        .chain(
            alignment
                .unaligned_intents
                .iter()
                .map(|item| item.reason.clone()),
        )
        .chain(
            alignment
                .unsupported_intents
                .iter()
                .map(|item| item.reason.clone()),
        )
        .chain(
            alignment
                .ambiguous_alignments
                .iter()
                .map(|item| item.reason.clone()),
        )
        .chain(
            alignment
                .missing_evidence
                .iter()
                .map(|item| item.reason.clone()),
        )
        .collect::<Vec<_>>();
    axes.sort();
    axes.dedup();
    axes
}

fn invalid_claim_classification(value: &str) -> bool {
    !matches!(
        value,
        "measured" | "assumed" | "unmeasured" | "ambiguous" | "decision-needed"
    )
}

fn invalid_alignment_kind(value: &str) -> bool {
    !matches!(
        value,
        "intentToObject"
            | "intentToRelation"
            | "intentToWorkflow"
            | "intentToStateTransition"
            | "intentToPolicyBoundary"
            | "intentToTestOracle"
            | "intentToRuntimeObservation"
            | "intentUnaligned"
    )
}

fn intent_source_ids(intent_map: &IntentMapV0) -> Vec<String> {
    intent_map
        .source_universe
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.clone())
        .collect()
}

fn intent_source_id_set(intent_map: &IntentMapV0) -> BTreeSet<&str> {
    intent_map
        .source_universe
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.as_str())
        .collect()
}

fn intent_id_set(intent_map: &IntentMapV0) -> BTreeSet<&str> {
    intent_map
        .items
        .iter()
        .map(|item| item.intent_item_id.as_str())
        .collect()
}

fn archmap_id_set(archmap: &ArchMapDocumentV0) -> BTreeSet<&str> {
    archmap
        .map_items
        .iter()
        .map(|item| item.map_item_id.as_str())
        .collect()
}

fn treats_unknown_as_zero(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    (value.contains("measured zero") && !value.contains("not measured zero"))
        || value.contains("safe to ignore")
        || value.contains("no impact")
}

fn validation_result(checks: &[ValidationCheck]) -> String {
    if count_checks(checks, "fail") > 0 {
        "fail".to_string()
    } else if count_checks(checks, "warn") > 0 {
        "warn".to_string()
    } else {
        "pass".to_string()
    }
}

fn stable_id(value: &str) -> String {
    let mut slug = String::new();
    let mut last_dash = false;
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_dash = false;
        } else if !last_dash {
            slug.push('-');
            last_dash = true;
        }
    }
    slug.trim_matches('-').to_string()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}
