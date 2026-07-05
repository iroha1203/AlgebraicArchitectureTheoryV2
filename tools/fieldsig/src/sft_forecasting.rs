use std::collections::BTreeSet;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    AffectedArchitectureRegionV0, CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION,
    CONSEQUENCE_ENVELOPE_REPORT_VALIDATION_REPORT_SCHEMA_VERSION, CalibrationEnvelopeRefV0,
    CalibrationForecastItemRefV0, CalibrationMatchV0, CalibrationObservedOutcomeRefV0,
    CalibrationReferenceBoundariesV0, ComparableSignatureAxisV0,
    ConsequenceEnvelopeRecommendationsV0, ConsequenceEnvelopeReportV0,
    ConsequenceEnvelopeSummaryProjectionV0, ConsequenceEnvelopeValidationInput,
    ConsequenceEnvelopeValidationReportV0, ConsequenceEnvelopeValidationSummary,
    ConsequenceForecastConeRefV0, ConsequenceMissingBoundaryItemV0, ConsequenceReviewerActionV0,
    ConsequenceTheoremBoundaryItemV0, ConsequenceTypedBoundaryFailureV0,
    ConsequenceUnknownRemainderV0, ExpectedAxisDeltaRangeV0,
    FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION,
    FORECAST_CALIBRATION_HOOK_VALIDATION_REPORT_SCHEMA_VERSION,
    FORECAST_CONE_SKELETON_SCHEMA_VERSION, FORECAST_CONE_SKELETON_VALIDATION_REPORT_SCHEMA_VERSION,
    ForecastBoundaryV0, ForecastBoundedHorizonV0, ForecastCalibrationHookV0,
    ForecastCalibrationHookValidationInput, ForecastCalibrationHookValidationReportV0,
    ForecastCalibrationHookValidationSummary, ForecastConeSkeletonV0,
    ForecastConeSkeletonValidationInput, ForecastConeSkeletonValidationReportV0,
    ForecastConeSkeletonValidationSummary, ForecastFiniteSupportRefV0, ForecastGluingEvidenceV0,
    ForecastGovernanceInterventionEvidenceV0, ForecastOperationSupportRefV0,
    ForecastPathClassCandidateV0, ForecastTypedBoundaryFailureV0, ForecastUnknownRemainderV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION, OperationSupportEstimateV0,
    OperationSupportUnknownRemainderV0, SFT_REVIEW_SUMMARY_SCHEMA_VERSION,
    SFT_REVIEW_SUMMARY_VALIDATION_REPORT_SCHEMA_VERSION, SelectedObstructionWitnessCandidateV0,
    SftReviewBoundaryFailureV0, SftReviewFutureV0, SftReviewLlmJudgementContractV0,
    SftReviewNextActionV0, SftReviewSummaryEnvelopeRefV0, SftReviewSummaryV0,
    SftReviewSummaryValidationInput, SftReviewSummaryValidationReportV0,
    SftReviewSummaryValidationSummary, ValidationCheck,
};

const FORECAST_NON_CONCLUSIONS: [&str; 5] = [
    "forecast cone skeleton is bounded by selected finite support and horizon",
    "forecast cone skeleton does not assign probabilities",
    "forecast cone skeleton does not prove global risk reduction",
    "forecast cone skeleton does not prove trajectory-level safety",
    "forecast cone skeleton is not an empirical prediction theorem",
];

const ENVELOPE_NON_CONCLUSIONS: [&str; 5] = [
    "consequence envelope is a report projection, not a Lean theorem proof",
    "consequence envelope does not identify a unique causal artifact action",
    "consequence envelope does not prove global safety",
    "unknown remainder is not measured zero",
    "summary projection is for review and CI consumption only",
];

const REVIEW_SUMMARY_NON_CONCLUSIONS: [&str; 5] = [
    "SFT review summary is deterministic projection, not final LLM judgement",
    "review status is judgement-ready triage, not merge approval",
    "opened and closed futures are bounded review items, not predictions",
    "boundary failures require human or LLM judgement with evidence refs",
    "summary does not promote ArchSig evidence to Lean theorem proof",
];

const REVIEW_STATUSES: [&str; 5] = [
    "governed",
    "risky",
    "blocked",
    "boundary_failure",
    "needs_human_judgement",
];

const CALIBRATION_NON_CONCLUSIONS: [&str; 5] = [
    "calibration hook does not prove forecast correctness",
    "calibration hook does not provide a causal proof",
    "calibration hook is not a Lean theorem claim",
    "calibration hook does not establish field completeness",
    "unmatched, unavailable, private, and notComparable outcomes are not measured zero",
];

const CALIBRATION_STATUSES: [&str; 5] = [
    "matched",
    "unmatched",
    "unavailable",
    "private",
    "notComparable",
];

pub fn static_forecast_cone_skeleton() -> ForecastConeSkeletonV0 {
    let source_ref_ids = vec![
        "source:issue-735".to_string(),
        "source:operation-support-estimate-fixture".to_string(),
        "source:roadmap-b12".to_string(),
        "source:sft-consequence-envelope".to_string(),
    ];
    let family_ids = vec![
        "family:schema-validation-artifact".to_string(),
        "family:cli-fixture-validation".to_string(),
    ];
    let support_ref_ids = vec![
        "support:schema-validation-artifact".to_string(),
        "support:cli-fixture-validation".to_string(),
    ];

    ForecastConeSkeletonV0 {
        schema_version: FORECAST_CONE_SKELETON_SCHEMA_VERSION.to_string(),
        cone_id: "fixture-forecast-cone-skeleton/v0.5.0".to_string(),
        operation_support_ref: ForecastOperationSupportRefV0 {
            estimate_schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
            estimate_id: "fixture-operation-support-estimate/v0.5.0".to_string(),
            descriptor_id: "fixture-artifact-descriptor/v0.5.0".to_string(),
            candidate_operation_family_ids: family_ids.clone(),
            source_ref_ids: source_ref_ids.clone(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        finite_support_refs: vec![
            finite_support_ref(
                "support:schema-validation-artifact",
                "finite-operation-family",
                &["family:schema-validation-artifact"],
                &[
                    "source:issue-735",
                    "source:operation-support-estimate-fixture",
                ],
                "schema and validator support is finite under the selected B12 fixture",
            ),
            finite_support_ref(
                "support:cli-fixture-validation",
                "finite-cli-support",
                &["family:cli-fixture-validation"],
                &["source:issue-735", "source:roadmap-b12"],
                "CLI fixture validation support is finite and source-bound",
            ),
        ],
        bounded_horizon: ForecastBoundedHorizonV0 {
            horizon_id: "horizon:b12-mvp-skeleton".to_string(),
            horizon_kind: "bounded-step".to_string(),
            max_steps: 3,
            time_window: "Phase B12 MVP issue chain".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            boundary: "bounded to B12.3 skeleton construction before probability or causal claims"
                .to_string(),
            assumptions: vec![
                "horizon counts artifact pipeline steps, not calendar predictions".to_string(),
                "downstream report and calibration artifacts remain separate".to_string(),
            ],
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        path_class_candidates: vec![
            path_class_candidate(
                "path:schema-to-envelope",
                "descriptor-estimate-cone-envelope",
                &[
                    "support:schema-validation-artifact",
                    "support:cli-fixture-validation",
                ],
                &[
                    "family:schema-validation-artifact",
                    "family:cli-fixture-validation",
                ],
                &[
                    "source:issue-735",
                    "source:operation-support-estimate-fixture",
                    "source:roadmap-b12",
                    "source:sft-consequence-envelope",
                ],
                &["schemaCompleteness", "boundaryRetention"],
                "The selected artifact path can feed a report skeleton without assigning probability.",
            ),
            path_class_candidate(
                "path:cli-validation-feedback",
                "fixture-validation-feedback",
                &["support:cli-fixture-validation"],
                &["family:cli-fixture-validation"],
                &["source:issue-735", "source:roadmap-b12"],
                &["validatorCoverage", "unknownRemainder"],
                "CLI validation can expose missing boundaries while retaining unknown support.",
            ),
        ],
        gluing_evidence: vec![ForecastGluingEvidenceV0 {
            gluing_id: "gluing:schema-envelope-local-futures".to_string(),
            local_future_refs: vec![
                "path:schema-to-envelope".to_string(),
                "path:cli-validation-feedback".to_string(),
            ],
            status: "missing_evidence".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            boundary: "local forecast futures are listed for review; gluing is not proved"
                .to_string(),
            reviewer_action:
                "check whether schema and CLI validation futures can be reviewed together"
                    .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        governance_interventions: vec![ForecastGovernanceInterventionEvidenceV0 {
            intervention_id: "governance:retain-boundary-and-open-issue".to_string(),
            intervention_kind: "review-gate".to_string(),
            target_path_class_ids: vec!["path:cli-validation-feedback".to_string()],
            policy_refs: vec!["policy:sft-review-boundary".to_string()],
            cut_action: "open downstream issue before treating runtime unknowns as closed"
                .to_string(),
            preservation_boundary:
                "governance cut is a reviewer action candidate, not correctness proof".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            reviewer_action: "ask reviewer to confirm whether boundary issue is required"
                .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        typed_boundary_failures: vec![ForecastTypedBoundaryFailureV0 {
            failure_id: "failure:runtime-invariant-missing".to_string(),
            failure_kind: "missing-invariant".to_string(),
            affected_path_class_ids: vec!["path:cli-validation-feedback".to_string()],
            evidence_refs: source_ref_ids.clone(),
            reason: "runtime propagation invariant is absent from the selected support".to_string(),
            reviewer_action: "request invariant evidence or keep runtime future open".to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        forecast_boundary: ForecastBoundaryV0 {
            boundary_id: "boundary:b12.3-forecast-cone-skeleton".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            measurement_boundary_refs: vec![
                "boundary:b12.2-operation-support-estimate".to_string(),
                "docs/tool/roadmap.md#b123-forecastcone-skeleton".to_string(),
            ],
            support_ref_ids,
            horizon_ref_ids: vec!["horizon:b12-mvp-skeleton".to_string()],
            unsupported_constructs: vec![
                "probability assignment".to_string(),
                "global risk reduction proof".to_string(),
                "trajectory-level safety proof".to_string(),
                "empirical prediction theorem".to_string(),
            ],
            assumptions: vec![
                "path classes are candidates under selected finite support".to_string(),
                "unmeasured axes remain explicit unknown remainder".to_string(),
            ],
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        unknown_remainder: vec![ForecastUnknownRemainderV0 {
            remainder_id: "unknown:unmeasured-runtime-and-policy-axes".to_string(),
            affected_path_class_ids: vec![
                "path:schema-to-envelope".to_string(),
                "path:cli-validation-feedback".to_string(),
            ],
            source_ref_ids,
            unknown_axes: vec![
                "runtime propagation".to_string(),
                "private PRD constraints".to_string(),
                "future reviewer behavior".to_string(),
            ],
            reason:
                "selected B12.3 inputs do not measure runtime, private, or future feedback axes"
                    .to_string(),
            treatment: "retain as unknown forecast remainder under the selected horizon"
                .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }],
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }
}

pub fn validate_forecast_cone_skeleton(
    cone: &ForecastConeSkeletonV0,
    input_path: &str,
) -> ForecastConeSkeletonValidationReportV0 {
    let checks = vec![
        check_forecast_schema(cone),
        check_forecast_support_refs(cone),
        check_forecast_horizon(cone),
        check_forecast_path_classes(cone),
        check_forecast_grand_theorem_evidence(cone),
        check_forecast_boundary(cone),
        check_forecast_unknown_remainder(cone),
        check_required_non_conclusions(
            "forecast-cone-skeleton-non-conclusions-preserved",
            &cone.non_conclusions,
            &FORECAST_NON_CONCLUSIONS,
        ),
    ];
    let summary = ForecastConeSkeletonValidationSummary {
        result: validation_result(&checks),
        finite_support_ref_count: cone.finite_support_refs.len(),
        path_class_candidate_count: cone.path_class_candidates.len(),
        unknown_remainder_count: cone.unknown_remainder.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ForecastConeSkeletonValidationReportV0 {
        schema_version: FORECAST_CONE_SKELETON_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ForecastConeSkeletonValidationInput {
            schema_version: cone.schema_version.clone(),
            path: input_path.to_string(),
            cone_id: cone.cone_id.clone(),
            estimate_id: cone.operation_support_ref.estimate_id.clone(),
        },
        cone: cone.clone(),
        summary,
        checks,
    }
}

pub fn build_forecast_cone_skeleton_from_operation_support(
    estimate: &OperationSupportEstimateV0,
    max_steps: u32,
    time_window: &str,
) -> ForecastConeSkeletonV0 {
    let source_ref_ids = forecast_source_refs_from_estimate(estimate);
    let family_ids = estimate
        .candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    let horizon_id = format!("horizon:{}:bounded", id_suffix(&estimate.estimate_id));
    let finite_support_refs = estimate
        .candidate_operation_families
        .iter()
        .map(|family| {
            let family_source_refs = retained_source_refs(&family.source_ref_ids, &source_ref_ids);
            ForecastFiniteSupportRefV0 {
                support_ref_id: support_ref_id_for_family(&family.family_id),
                support_kind: format!("finite-{}", id_suffix(&family.operation_family)),
                operation_family_ids: vec![family.family_id.clone()],
                source_ref_ids: family_source_refs,
                boundary: format!(
                    "finite support is scoped to operation family {} under selected operation support refs",
                    family.family_id
                ),
                assumptions: vec![
                    "support is finite under selected operation support estimate refs".to_string(),
                    "support refs do not imply operation support completeness".to_string(),
                ],
                non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
            }
        })
        .collect::<Vec<_>>();
    let support_ref_ids = finite_support_refs
        .iter()
        .map(|support| support.support_ref_id.clone())
        .collect::<Vec<_>>();
    let path_class_candidates = estimate
        .candidate_operation_families
        .iter()
        .map(|family| {
            let family_source_refs = retained_source_refs(&family.source_ref_ids, &source_ref_ids);
            ForecastPathClassCandidateV0 {
                path_class_id: path_class_id_for_family(&family.family_id),
                path_class: format!("{}-bounded-path", id_suffix(&family.operation_family)),
                support_ref_ids: vec![support_ref_id_for_family(&family.family_id)],
                operation_family_ids: vec![family.family_id.clone()],
                horizon_ref_id: horizon_id.clone(),
                source_ref_ids: family_source_refs,
                affected_axes: affected_axes_for_family(&family.operation_family),
                rationale: format!(
                    "Derived from operation support family {} without assigning probability.",
                    family.family_id
                ),
                probability_boundary: "no probability is assigned by the forecast cone skeleton"
                    .to_string(),
                non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
            }
        })
        .collect::<Vec<_>>();
    let path_ids = path_class_candidates
        .iter()
        .map(|path| path.path_class_id.clone())
        .collect::<Vec<_>>();
    let unknown_remainder = forecast_unknown_remainder_from_estimate(
        &estimate.unknown_remainder,
        &source_ref_ids,
        &path_ids,
    );
    let typed_boundary_failures =
        forecast_typed_boundary_failures(estimate, &source_ref_ids, &path_ids);
    let gluing_evidence = forecast_gluing_evidence(&path_ids, &source_ref_ids);
    let governance_interventions =
        forecast_governance_interventions(estimate, &source_ref_ids, &path_ids);

    ForecastConeSkeletonV0 {
        schema_version: FORECAST_CONE_SKELETON_SCHEMA_VERSION.to_string(),
        cone_id: format!("cone:{}", estimate.estimate_id),
        operation_support_ref: ForecastOperationSupportRefV0 {
            estimate_schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
            estimate_id: estimate.estimate_id.clone(),
            descriptor_id: estimate.descriptor_ref.descriptor_id.clone(),
            candidate_operation_family_ids: family_ids,
            source_ref_ids: source_ref_ids.clone(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        finite_support_refs,
        bounded_horizon: ForecastBoundedHorizonV0 {
            horizon_id: horizon_id.clone(),
            horizon_kind: "bounded-step".to_string(),
            max_steps,
            time_window: time_window.to_string(),
            source_ref_ids: source_ref_ids.clone(),
            boundary:
                "horizon bounds path class generation and does not make a calendar prediction"
                    .to_string(),
            assumptions: vec![
                "horizon counts forecast construction steps, not causal event probability"
                    .to_string(),
                "downstream consequence envelope and calibration remain separate artifacts"
                    .to_string(),
            ],
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        path_class_candidates,
        gluing_evidence,
        governance_interventions,
        typed_boundary_failures,
        forecast_boundary: ForecastBoundaryV0 {
            boundary_id: format!("boundary:{}:forecast-cone-skeleton", estimate.estimate_id),
            source_ref_ids: source_ref_ids.clone(),
            measurement_boundary_refs: unique_strings(
                std::iter::once(estimate.evidence_boundary.boundary_id.clone())
                    .chain(estimate.evidence_boundary.measurement_boundary_refs.clone())
                    .collect(),
            ),
            support_ref_ids,
            horizon_ref_ids: vec![horizon_id],
            unsupported_constructs: forecast_unsupported_constructs(estimate),
            assumptions: vec![
                "path classes are candidates under selected finite operation support".to_string(),
                "unmeasured axes remain explicit unknown remainder".to_string(),
            ],
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        },
        unknown_remainder,
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }
}

pub fn static_consequence_envelope_report() -> ConsequenceEnvelopeReportV0 {
    let source_ref_ids = vec![
        "source:issue-736".to_string(),
        "source:forecast-cone-fixture".to_string(),
        "source:roadmap-b12".to_string(),
    ];

    ConsequenceEnvelopeReportV0 {
        schema_version: CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
        envelope_id: "fixture-consequence-envelope-report/v0.5.0".to_string(),
        forecast_cone_ref: ConsequenceForecastConeRefV0 {
            forecast_cone_schema_version: FORECAST_CONE_SKELETON_SCHEMA_VERSION.to_string(),
            cone_id: "fixture-forecast-cone-skeleton/v0.5.0".to_string(),
            operation_support_estimate_id: "fixture-operation-support-estimate/v0.5.0".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            forecast_boundary_refs: vec!["boundary:b12.3-forecast-cone-skeleton".to_string()],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        affected_architecture_regions: vec![
            AffectedArchitectureRegionV0 {
                region_id: "region:tools-archsig-sft".to_string(),
                region_ref: "tools/archsig".to_string(),
                effect_kind: "tooling-artifact-surface".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                boundary: "region is selected by B12 tooling scope, not inferred as global architecture impact"
                    .to_string(),
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
            AffectedArchitectureRegionV0 {
                region_id: "region:docs-sft-boundary".to_string(),
                region_ref: "docs/sft".to_string(),
                effect_kind: "claim-boundary-documentation".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                boundary: "documentation boundary tracks non-conclusions only".to_string(),
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
        ],
        comparable_signature_axes: vec![
            ComparableSignatureAxisV0 {
                axis_id: "axis:boundary-retention".to_string(),
                axis_name: "boundaryRetention".to_string(),
                measurement_boundary_refs: vec![
                    "boundary:b12.3-forecast-cone-skeleton".to_string(),
                    "boundary:b12.4-consequence-envelope".to_string(),
                ],
                comparability: "comparable only across retained source refs and forecast boundary items"
                    .to_string(),
                missing_invariant_refs: vec!["missing:runtime-propagation-invariant".to_string()],
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
            ComparableSignatureAxisV0 {
                axis_id: "axis:unknown-remainder".to_string(),
                axis_name: "unknownRemainder".to_string(),
                measurement_boundary_refs: vec!["boundary:b12.4-consequence-envelope".to_string()],
                comparability: "compares explicit unknown items, not absent or safe axes".to_string(),
                missing_invariant_refs: vec!["missing:private-feedback-boundary".to_string()],
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
        ],
        expected_axis_delta_ranges: vec![
            ExpectedAxisDeltaRangeV0 {
                delta_id: "delta:boundary-retention-nonnegative".to_string(),
                axis_id: "axis:boundary-retention".to_string(),
                range_kind: "qualitative-nonnegative".to_string(),
                lower_bound: Some("retained".to_string()),
                upper_bound: Some("retained-plus-report-summary".to_string()),
                source_ref_ids: source_ref_ids.clone(),
                boundary: "expected range is qualitative and fixture-bound".to_string(),
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
            ExpectedAxisDeltaRangeV0 {
                delta_id: "delta:unknown-remainder-explicit".to_string(),
                axis_id: "axis:unknown-remainder".to_string(),
                range_kind: "qualitative-explicit".to_string(),
                lower_bound: Some("unknown retained".to_string()),
                upper_bound: None,
                source_ref_ids: source_ref_ids.clone(),
                boundary: "unknown remainder is reported, not resolved".to_string(),
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            },
        ],
        obstruction_witness_candidates: vec![SelectedObstructionWitnessCandidateV0 {
            candidate_id: "obstruction:runtime-boundary-missing".to_string(),
            obstruction_kind: "missing-runtime-boundary".to_string(),
            region_ids: vec!["region:tools-archsig-sft".to_string()],
            axis_ids: vec!["axis:unknown-remainder".to_string()],
            evidence_refs: source_ref_ids.clone(),
            selection_boundary:
                "selected as a review candidate, not as a proved obstruction witness".to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        missing_boundary_items: vec![ConsequenceMissingBoundaryItemV0 {
            item_id: "missing:runtime-propagation-invariant".to_string(),
            item_kind: "missing-invariant".to_string(),
            affected_axis_ids: vec!["axis:unknown-remainder".to_string()],
            reason: "runtime propagation is outside B12.4 report evidence".to_string(),
            treatment: "report as missing boundary item for review and issue decomposition"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        typed_boundary_failures: vec![ConsequenceTypedBoundaryFailureV0 {
            failure_id: "failure:runtime-invariant-missing".to_string(),
            failure_kind: "missing-invariant".to_string(),
            affected_region_ids: vec!["region:tools-archsig-sft".to_string()],
            affected_axis_ids: vec!["axis:unknown-remainder".to_string()],
            evidence_refs: source_ref_ids.clone(),
            reason: "runtime propagation invariant is absent from the selected report evidence"
                .to_string(),
            next_action: "request runtime invariant evidence or keep the future open".to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        reviewer_actions: vec![ConsequenceReviewerActionV0 {
            action_id: "action:review-runtime-boundary".to_string(),
            action_kind: "request-evidence".to_string(),
            status: "needs_human_judgement".to_string(),
            source_item_refs: vec!["missing:runtime-propagation-invariant".to_string()],
            evidence_refs: source_ref_ids.clone(),
            message: "Review runtime propagation evidence before closing the forecast boundary"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        theorem_boundary_items: vec![ConsequenceTheoremBoundaryItemV0 {
            item_id: "theorem-boundary:no-lean-promotion".to_string(),
            theorem_or_claim_ref: "AAT theorem boundary".to_string(),
            boundary: "report does not upgrade forecast artifacts to Lean theorem claims".to_string(),
            required_evidence: vec![
                "formal theorem statement".to_string(),
                "Lean proof".to_string(),
                "separate empirical validation".to_string(),
            ],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        recommendations: ConsequenceEnvelopeRecommendationsV0 {
            review: vec![
                "review retained source refs before treating any region as affected".to_string(),
                "check missing boundary items before accepting axis deltas".to_string(),
            ],
            ci: vec!["run consequence-envelope validator on report artifacts".to_string()],
            issue_decomposition: vec![
                "split runtime propagation boundary into a downstream empirical issue".to_string(),
            ],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        summary_projection: ConsequenceEnvelopeSummaryProjectionV0 {
            summary_id: "summary:b12.4-review-projection".to_string(),
            headline: "B12 forecast report keeps boundary and unknown remainder explicit".to_string(),
            affected_region_count: 2,
            comparable_axis_count: 2,
            missing_boundary_count: 1,
            reviewer_notes: vec![
                "No probability or causal safety claim is emitted.".to_string(),
                "Unknown runtime and private feedback remain report items.".to_string(),
            ],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        unknown_remainder: vec![ConsequenceUnknownRemainderV0 {
            remainder_id: "unknown:private-and-runtime-outcomes".to_string(),
            affected_region_ids: vec!["region:tools-archsig-sft".to_string()],
            affected_axis_ids: vec!["axis:unknown-remainder".to_string()],
            unknown_axes: vec![
                "private PRD decisions".to_string(),
                "runtime outcome evidence".to_string(),
                "future CI and review behavior".to_string(),
            ],
            treatment: "retain as unresolved report remainder under the selected boundary"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
    }
}

pub fn build_consequence_envelope_from_forecast_cone(
    cone: &ForecastConeSkeletonV0,
) -> ConsequenceEnvelopeReportV0 {
    let source_ref_ids = forecast_source_refs_from_cone(cone);
    let forecast_boundary_refs = unique_strings(
        std::iter::once(cone.forecast_boundary.boundary_id.clone())
            .chain(cone.forecast_boundary.measurement_boundary_refs.clone())
            .collect(),
    );
    let measurement_boundary_refs = if forecast_boundary_refs.is_empty() {
        vec![format!(
            "boundary:{}:consequence-envelope",
            id_suffix(&cone.cone_id)
        )]
    } else {
        forecast_boundary_refs.clone()
    };

    let affected_architecture_regions = consequence_regions_from_cone(cone, &source_ref_ids);
    let region_ids = affected_architecture_regions
        .iter()
        .map(|region| region.region_id.clone())
        .collect::<Vec<_>>();
    let comparable_signature_axes = consequence_axes_from_cone(cone, &measurement_boundary_refs);
    let axis_ids = comparable_signature_axes
        .iter()
        .map(|axis| axis.axis_id.clone())
        .collect::<Vec<_>>();
    let expected_axis_delta_ranges = consequence_delta_ranges(&axis_ids, &source_ref_ids);
    let missing_boundary_items =
        consequence_missing_boundaries(cone, &axis_ids, &measurement_boundary_refs);
    let missing_boundary_count = missing_boundary_items.len();
    let typed_boundary_failures =
        consequence_typed_boundary_failures(cone, &region_ids, &axis_ids, &source_ref_ids);
    let reviewer_actions = consequence_reviewer_actions(
        &missing_boundary_items,
        &typed_boundary_failures,
        cone,
        &source_ref_ids,
    );
    let obstruction_witness_candidates =
        consequence_obstruction_candidates(cone, &region_ids, &axis_ids, &source_ref_ids);
    let unknown_remainder = consequence_unknown_remainder(cone, &region_ids, &axis_ids);

    ConsequenceEnvelopeReportV0 {
        schema_version: CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
        envelope_id: format!("envelope:{}", cone.cone_id),
        forecast_cone_ref: ConsequenceForecastConeRefV0 {
            forecast_cone_schema_version: FORECAST_CONE_SKELETON_SCHEMA_VERSION.to_string(),
            cone_id: cone.cone_id.clone(),
            operation_support_estimate_id: cone.operation_support_ref.estimate_id.clone(),
            source_ref_ids: source_ref_ids.clone(),
            forecast_boundary_refs,
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        affected_architecture_regions,
        comparable_signature_axes,
        expected_axis_delta_ranges,
        obstruction_witness_candidates,
        missing_boundary_items,
        typed_boundary_failures,
        reviewer_actions,
        theorem_boundary_items: vec![ConsequenceTheoremBoundaryItemV0 {
            item_id: format!("theorem-boundary:{}:no-lean-promotion", id_suffix(&cone.cone_id)),
            theorem_or_claim_ref: "AAT theorem boundary".to_string(),
            boundary: "generated consequence envelope does not upgrade forecast artifacts to Lean theorem claims"
                .to_string(),
            required_evidence: vec![
                "formal theorem statement".to_string(),
                "Lean proof".to_string(),
                "separate empirical validation".to_string(),
            ],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }],
        recommendations: ConsequenceEnvelopeRecommendationsV0 {
            review: vec![
                "review retained source refs before treating regions as affected".to_string(),
                "check missing boundary items before accepting axis deltas".to_string(),
            ],
            ci: vec![
                "run consequence-envelope validator on generated report artifacts".to_string(),
                "retain forecast cone skeleton validation as an upstream check".to_string(),
            ],
            issue_decomposition: consequence_issue_recommendations(cone),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        summary_projection: ConsequenceEnvelopeSummaryProjectionV0 {
            summary_id: format!("summary:{}:review-projection", id_suffix(&cone.cone_id)),
            headline: "Forecast cone projection keeps affected regions, axes, and unknown remainder explicit"
                .to_string(),
            affected_region_count: region_ids.len(),
            comparable_axis_count: axis_ids.len(),
            missing_boundary_count,
            reviewer_notes: vec![
                "No probability or causal safety claim is emitted.".to_string(),
                "Unknown forecast remainder remains a report item.".to_string(),
            ],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        },
        unknown_remainder,
        non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
    }
}

pub fn validate_consequence_envelope_report(
    envelope: &ConsequenceEnvelopeReportV0,
    input_path: &str,
) -> ConsequenceEnvelopeValidationReportV0 {
    let checks = vec![
        check_envelope_schema(envelope),
        check_envelope_source_refs(envelope),
        check_envelope_regions_and_axes(envelope),
        check_envelope_boundaries(envelope),
        check_envelope_reviewer_actions(envelope),
        check_envelope_unknown_remainder(envelope),
        check_required_non_conclusions(
            "consequence-envelope-non-conclusions-preserved",
            &envelope.non_conclusions,
            &ENVELOPE_NON_CONCLUSIONS,
        ),
    ];
    let summary = ConsequenceEnvelopeValidationSummary {
        result: validation_result(&checks),
        affected_region_count: envelope.affected_architecture_regions.len(),
        comparable_axis_count: envelope.comparable_signature_axes.len(),
        obstruction_candidate_count: envelope.obstruction_witness_candidates.len(),
        missing_boundary_count: envelope.missing_boundary_items.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ConsequenceEnvelopeValidationReportV0 {
        schema_version: CONSEQUENCE_ENVELOPE_REPORT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ConsequenceEnvelopeValidationInput {
            schema_version: envelope.schema_version.clone(),
            path: input_path.to_string(),
            envelope_id: envelope.envelope_id.clone(),
            cone_id: envelope.forecast_cone_ref.cone_id.clone(),
        },
        envelope: envelope.clone(),
        summary,
        checks,
    }
}

pub fn static_sft_review_summary() -> SftReviewSummaryV0 {
    build_sft_review_summary_from_consequence_envelope(&static_consequence_envelope_report())
}

pub fn build_sft_review_summary_from_consequence_envelope(
    envelope: &ConsequenceEnvelopeReportV0,
) -> SftReviewSummaryV0 {
    let evidence_refs = envelope_source_ids(envelope)
        .into_iter()
        .map(str::to_string)
        .collect::<Vec<_>>();
    let boundary_refs = envelope_boundary_refs(envelope);
    let boundary_failures =
        envelope
            .typed_boundary_failures
            .iter()
            .map(|failure| SftReviewBoundaryFailureV0 {
                failure_id: format!("summary:{}", failure.failure_id),
                failure_kind: failure.failure_kind.clone(),
                evidence_refs: retained_source_refs(&failure.evidence_refs, &evidence_refs),
                boundary_refs: boundary_refs.clone(),
                reviewer_action: failure.next_action.clone(),
            })
            .chain(envelope.missing_boundary_items.iter().map(|missing| {
                SftReviewBoundaryFailureV0 {
                    failure_id: format!("summary:{}", missing.item_id),
                    failure_kind: missing.item_kind.clone(),
                    evidence_refs: evidence_refs.clone(),
                    boundary_refs: boundary_refs.clone(),
                    reviewer_action: missing.treatment.clone(),
                }
            }))
            .collect::<Vec<_>>();
    let next_actions = envelope
        .reviewer_actions
        .iter()
        .map(|action| SftReviewNextActionV0 {
            action_id: format!("summary:{}", action.action_id),
            action_kind: action.action_kind.clone(),
            source_item_refs: action.source_item_refs.clone(),
            evidence_refs: retained_source_refs(&action.evidence_refs, &evidence_refs),
            message: action.message.clone(),
        })
        .chain(
            envelope
                .recommendations
                .review
                .iter()
                .enumerate()
                .map(|(idx, item)| SftReviewNextActionV0 {
                    action_id: format!("summary:review-recommendation-{idx}"),
                    action_kind: "review-recommendation".to_string(),
                    source_item_refs: Vec::new(),
                    evidence_refs: evidence_refs.clone(),
                    message: item.clone(),
                }),
        )
        .collect::<Vec<_>>();
    let opened_futures = envelope
        .affected_architecture_regions
        .iter()
        .map(|region| SftReviewFutureV0 {
            future_id: format!("opened:{}", id_suffix(&region.region_id)),
            future_kind: region.effect_kind.clone(),
            region_refs: vec![region.region_id.clone()],
            axis_refs: envelope
                .comparable_signature_axes
                .iter()
                .map(|axis| axis.axis_id.clone())
                .collect(),
            evidence_refs: retained_source_refs(&region.source_ref_ids, &evidence_refs),
            boundary: region.boundary.clone(),
        })
        .collect::<Vec<_>>();
    let closed_futures = envelope
        .missing_boundary_items
        .iter()
        .map(|item| SftReviewFutureV0 {
            future_id: format!("closed:{}", id_suffix(&item.item_id)),
            future_kind: item.item_kind.clone(),
            region_refs: Vec::new(),
            axis_refs: item.affected_axis_ids.clone(),
            evidence_refs: evidence_refs.clone(),
            boundary: item.reason.clone(),
        })
        .collect::<Vec<_>>();
    let status = review_status(&boundary_failures, &next_actions);

    SftReviewSummaryV0 {
        schema_version: SFT_REVIEW_SUMMARY_SCHEMA_VERSION.to_string(),
        summary_id: format!("summary:{}", envelope.envelope_id),
        envelope_ref: SftReviewSummaryEnvelopeRefV0 {
            envelope_schema_version: CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
            envelope_id: envelope.envelope_id.clone(),
            cone_id: envelope.forecast_cone_ref.cone_id.clone(),
            source_ref_ids: evidence_refs.clone(),
        },
        status,
        opened_futures,
        closed_futures,
        boundary_failures,
        next_actions,
        llm_judgement_contract: SftReviewLlmJudgementContractV0 {
            input_fields: strings(&[
                "observationBoundary",
                "operationSupport",
                "pathClasses",
                "affectedRegions",
                "missingInvariantRefs",
                "unknownRemainder",
                "policyConstraints",
                "sourceRefs",
            ]),
            output_fields: strings(&[
                "status",
                "openedFutures",
                "closedFutures",
                "evidence",
                "reviewerMessage",
                "nextActions",
                "confidenceBoundary",
            ]),
            required_evidence_policy:
                "every judgement item must cite evidenceRefs and boundaryRefs".to_string(),
            forbidden_readings: strings(&[
                "probability claim",
                "causal proof",
                "Lean theorem promotion",
                "unknown remainder as measured zero",
                "merge approval",
            ]),
            confidence_boundary:
                "confidence is bounded review judgement over retained evidence refs".to_string(),
        },
        reviewer_message:
            "Review opened futures, closed futures, boundary failures, and next actions before judgement"
                .to_string(),
        evidence_refs,
        boundary_refs,
        non_conclusions: strings(&REVIEW_SUMMARY_NON_CONCLUSIONS),
    }
}

pub fn validate_sft_review_summary(
    summary: &SftReviewSummaryV0,
    input_path: &str,
) -> SftReviewSummaryValidationReportV0 {
    let checks = vec![
        check_review_summary_schema(summary),
        check_review_summary_status(summary),
        check_review_summary_refs(summary),
        check_review_summary_contract(summary),
        check_required_non_conclusions(
            "sft-review-summary-non-conclusions-preserved",
            &summary.non_conclusions,
            &REVIEW_SUMMARY_NON_CONCLUSIONS,
        ),
    ];
    let validation_summary = SftReviewSummaryValidationSummary {
        result: validation_result(&checks),
        opened_future_count: summary.opened_futures.len(),
        closed_future_count: summary.closed_futures.len(),
        boundary_failure_count: summary.boundary_failures.len(),
        next_action_count: summary.next_actions.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    SftReviewSummaryValidationReportV0 {
        schema_version: SFT_REVIEW_SUMMARY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: SftReviewSummaryValidationInput {
            schema_version: summary.schema_version.clone(),
            path: input_path.to_string(),
            summary_id: summary.summary_id.clone(),
            envelope_id: summary.envelope_ref.envelope_id.clone(),
        },
        summary: summary.clone(),
        validation_summary,
        checks,
    }
}

pub fn static_forecast_calibration_hook() -> ForecastCalibrationHookV0 {
    let source_ref_ids = vec![
        "source:issue-737".to_string(),
        "source:consequence-envelope-fixture".to_string(),
        "source:b10-report-outcome-daily-ledger".to_string(),
        "source:b11-signature-trajectory-report".to_string(),
    ];

    ForecastCalibrationHookV0 {
        schema_version: FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION.to_string(),
        hook_id: "fixture-forecast-calibration-hook/v0.5.0".to_string(),
        envelope_ref: CalibrationEnvelopeRefV0 {
            envelope_schema_version: CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
            envelope_id: "fixture-consequence-envelope-report/v0.5.0".to_string(),
            cone_id: "fixture-forecast-cone-skeleton/v0.5.0".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        },
        forecast_item_refs: vec![
            CalibrationForecastItemRefV0 {
                forecast_item_id: "forecast-item:boundary-retention-delta".to_string(),
                item_kind: "axis-delta-range".to_string(),
                envelope_item_ref: "delta:boundary-retention-nonnegative".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                comparison_boundary: "compare only retained report item ids and observed refs"
                    .to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
            CalibrationForecastItemRefV0 {
                forecast_item_id: "forecast-item:runtime-boundary-missing".to_string(),
                item_kind: "missing-boundary".to_string(),
                envelope_item_ref: "missing:runtime-propagation-invariant".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                comparison_boundary: "missing boundary can remain unavailable or private".to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
        ],
        observed_outcome_refs: vec![
            CalibrationObservedOutcomeRefV0 {
                observed_ref_id: "observed:b10-daily-ledger".to_string(),
                observed_kind: "report-outcome-daily-ledger".to_string(),
                path_or_url: "tools/fieldsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
                    .to_string(),
                status: "matched".to_string(),
                b10_refs: vec!["b10:report-outcome-daily-ledger".to_string()],
                b11_refs: Vec::new(),
                evidence_boundary: "B10 ledger is fixture evidence, not correctness proof"
                    .to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
            CalibrationObservedOutcomeRefV0 {
                observed_ref_id: "observed:b11-trajectory-private".to_string(),
                observed_kind: "signature-trajectory-report".to_string(),
                path_or_url: "private-or-unavailable".to_string(),
                status: "private".to_string(),
                b10_refs: Vec::new(),
                b11_refs: vec!["b11:signature-trajectory-report".to_string()],
                evidence_boundary: "private trajectory evidence is retained as private, not zero"
                    .to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
        ],
        matches: vec![
            CalibrationMatchV0 {
                match_id: "match:boundary-retention-ledger".to_string(),
                forecast_item_id: "forecast-item:boundary-retention-delta".to_string(),
                observed_ref_id: Some("observed:b10-daily-ledger".to_string()),
                status: "matched".to_string(),
                rationale: "forecast item can be linked to a retained B10 ledger fixture".to_string(),
                update_boundary: "link can seed calibration review but does not prove correctness"
                    .to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
            CalibrationMatchV0 {
                match_id: "match:runtime-boundary-private".to_string(),
                forecast_item_id: "forecast-item:runtime-boundary-missing".to_string(),
                observed_ref_id: Some("observed:b11-trajectory-private".to_string()),
                status: "private".to_string(),
                rationale: "runtime trajectory evidence is outside the public fixture boundary"
                    .to_string(),
                update_boundary: "private evidence remains unavailable to calibration scoring"
                    .to_string(),
                non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
            },
        ],
        reference_boundaries: CalibrationReferenceBoundariesV0 {
            b10_refs: vec![
                "outcome-linkage-dataset/v0.5.0".to_string(),
                "report-outcome-daily-ledger/v0.5.0".to_string(),
            ],
            b11_refs: vec![
                "signature-trajectory-report/v0.5.0".to_string(),
                "architecture-dynamics-metrics-report/v0.5.0".to_string(),
            ],
            unavailable_refs: vec!["observed:future-review-outcome".to_string()],
            private_refs: vec!["observed:b11-trajectory-private".to_string()],
            measurement_boundary:
                "calibration compares retained forecast and observed refs without treating gaps as zero"
                    .to_string(),
            non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&CALIBRATION_NON_CONCLUSIONS),
    }
}

pub fn validate_forecast_calibration_hook(
    hook: &ForecastCalibrationHookV0,
    input_path: &str,
) -> ForecastCalibrationHookValidationReportV0 {
    let checks = vec![
        check_calibration_schema(hook),
        check_calibration_refs(hook),
        check_calibration_statuses(hook),
        check_calibration_boundaries(hook),
        check_required_non_conclusions(
            "forecast-calibration-hook-non-conclusions-preserved",
            &hook.non_conclusions,
            &CALIBRATION_NON_CONCLUSIONS,
        ),
    ];
    let summary = ForecastCalibrationHookValidationSummary {
        result: validation_result(&checks),
        forecast_item_count: hook.forecast_item_refs.len(),
        observed_outcome_count: hook.observed_outcome_refs.len(),
        match_count: hook.matches.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ForecastCalibrationHookValidationReportV0 {
        schema_version: FORECAST_CALIBRATION_HOOK_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ForecastCalibrationHookValidationInput {
            schema_version: hook.schema_version.clone(),
            path: input_path.to_string(),
            hook_id: hook.hook_id.clone(),
            envelope_id: hook.envelope_ref.envelope_id.clone(),
        },
        hook: hook.clone(),
        summary,
        checks,
    }
}

fn forecast_source_refs_from_estimate(estimate: &OperationSupportEstimateV0) -> Vec<String> {
    let mut refs = Vec::new();
    refs.extend(estimate.descriptor_ref.source_ref_ids.clone());
    refs.extend(estimate.evidence_boundary.source_ref_ids.clone());
    for family in &estimate.candidate_operation_families {
        refs.extend(family.source_ref_ids.clone());
    }
    for constraint in &estimate.policy_constraints {
        refs.extend(constraint.source_ref_ids.clone());
    }
    for forbidden in &estimate.known_forbidden_support {
        refs.extend(forbidden.source_ref_ids.clone());
    }
    for remainder in &estimate.unknown_remainder {
        refs.extend(remainder.source_ref_ids.clone());
    }
    unique_strings(refs)
}

fn retained_source_refs(candidate_refs: &[String], all_source_refs: &[String]) -> Vec<String> {
    let all = all_source_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let retained = candidate_refs
        .iter()
        .filter(|source| all.contains(source.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if retained.is_empty() {
        all_source_refs.to_vec()
    } else {
        unique_strings(retained)
    }
}

fn support_ref_id_for_family(family_id: &str) -> String {
    format!("support:{}", id_suffix(family_id))
}

fn path_class_id_for_family(family_id: &str) -> String {
    format!("path:{}", id_suffix(family_id))
}

fn affected_axes_for_family(operation_family: &str) -> Vec<String> {
    let family = operation_family.to_ascii_lowercase();
    if family.contains("schema") || family.contains("validator") {
        strings(&["schemaCompleteness", "boundaryRetention"])
    } else if family.contains("cli") || family.contains("fixture") {
        strings(&["validatorCoverage", "unknownRemainder"])
    } else if family.contains("policy") || family.contains("constraint") {
        strings(&["policyBoundary", "boundaryRetention"])
    } else {
        strings(&["boundaryRetention", "unknownRemainder"])
    }
}

fn forecast_unknown_remainder_from_estimate(
    remainders: &[OperationSupportUnknownRemainderV0],
    source_ref_ids: &[String],
    path_ids: &[String],
) -> Vec<ForecastUnknownRemainderV0> {
    remainders
        .iter()
        .map(|remainder| {
            let affected_path_class_ids =
                path_ids_for_unknown_remainder(&remainder.affected_family_ids, path_ids);
            ForecastUnknownRemainderV0 {
                remainder_id: format!("forecast:{}", remainder.remainder_id),
                affected_path_class_ids,
                source_ref_ids: retained_source_refs(&remainder.source_ref_ids, source_ref_ids),
                unknown_axes: remainder.unknown_axes.clone(),
                reason: format!(
                    "{}; propagated from operation support unknown remainder",
                    remainder.reason
                ),
                treatment:
                    "retain as unknown forecast remainder under the selected bounded horizon"
                        .to_string(),
                non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn forecast_gluing_evidence(
    path_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<ForecastGluingEvidenceV0> {
    let status = if path_ids.len() > 1 {
        "requires_review"
    } else {
        "single_local_future"
    };
    vec![ForecastGluingEvidenceV0 {
        gluing_id: "gluing:local-futures".to_string(),
        local_future_refs: path_ids.to_vec(),
        status: status.to_string(),
        source_ref_ids: source_ref_ids.to_vec(),
        boundary: "local futures are listed for bounded review; gluing is not a theorem conclusion"
            .to_string(),
        reviewer_action: "confirm whether selected local futures can be reviewed together"
            .to_string(),
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }]
}

fn forecast_governance_interventions(
    estimate: &OperationSupportEstimateV0,
    source_ref_ids: &[String],
    path_ids: &[String],
) -> Vec<ForecastGovernanceInterventionEvidenceV0> {
    let from_policy = estimate
        .policy_constraints
        .iter()
        .map(|constraint| ForecastGovernanceInterventionEvidenceV0 {
            intervention_id: format!("governance:{}", id_suffix(&constraint.constraint_id)),
            intervention_kind: constraint_kind_to_intervention(&constraint.constraint_kind),
            target_path_class_ids: path_ids_for_unknown_remainder(
                &constraint.applies_to_family_ids,
                path_ids,
            ),
            policy_refs: if constraint.policy_refs.is_empty() {
                vec![constraint.constraint_id.clone()]
            } else {
                constraint.policy_refs.clone()
            },
            cut_action: if constraint.governance_action_refs.is_empty() {
                "review policy constraint before closing this future".to_string()
            } else {
                format!(
                    "apply governance actions {}",
                    constraint.governance_action_refs.join(", ")
                )
            },
            preservation_boundary: constraint.safety_claim_boundary.clone(),
            source_ref_ids: retained_source_refs(&constraint.source_ref_ids, source_ref_ids),
            reviewer_action:
                "decide whether the policy constraint cuts, allows, or leaves the future unknown"
                    .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    if from_policy.is_empty() {
        vec![ForecastGovernanceInterventionEvidenceV0 {
            intervention_id: "governance:policy-undefined".to_string(),
            intervention_kind: "missing-policy".to_string(),
            target_path_class_ids: path_ids.to_vec(),
            policy_refs: Vec::new(),
            cut_action: "do not treat missing policy as a safe path".to_string(),
            preservation_boundary: "policy undefined remains review boundary".to_string(),
            source_ref_ids: source_ref_ids.to_vec(),
            reviewer_action: "define policy or keep affected futures open".to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }]
    } else {
        from_policy
    }
}

fn forecast_typed_boundary_failures(
    estimate: &OperationSupportEstimateV0,
    source_ref_ids: &[String],
    path_ids: &[String],
) -> Vec<ForecastTypedBoundaryFailureV0> {
    let mut failures = estimate
        .known_forbidden_support
        .iter()
        .map(|forbidden| ForecastTypedBoundaryFailureV0 {
            failure_id: format!("failure:{}", id_suffix(&forbidden.forbidden_id)),
            failure_kind: "forbidden-future-path-class".to_string(),
            affected_path_class_ids: path_ids.to_vec(),
            evidence_refs: retained_source_refs(&forbidden.source_ref_ids, source_ref_ids),
            reason: forbidden.reason.clone(),
            reviewer_action:
                "treat forbidden support as a closed or blocked future unless policy changes"
                    .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    failures.extend(estimate.unknown_remainder.iter().map(|remainder| {
        ForecastTypedBoundaryFailureV0 {
            failure_id: format!("failure:{}", id_suffix(&remainder.remainder_id)),
            failure_kind: boundary_failure_kind(&remainder.unknown_axes),
            affected_path_class_ids: path_ids_for_unknown_remainder(
                &remainder.affected_family_ids,
                path_ids,
            ),
            evidence_refs: retained_source_refs(&remainder.source_ref_ids, source_ref_ids),
            reason: remainder.reason.clone(),
            reviewer_action: "request missing evidence or keep the future as unknown remainder"
                .to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        }
    }));
    if failures.is_empty() {
        failures.push(ForecastTypedBoundaryFailureV0 {
            failure_id: "failure:undefined-operation-support".to_string(),
            failure_kind: "undefined-operation-support".to_string(),
            affected_path_class_ids: path_ids.to_vec(),
            evidence_refs: source_ref_ids.to_vec(),
            reason: "no explicit forbidden or unknown support item was generated".to_string(),
            reviewer_action: "review operation support boundary before judgement".to_string(),
            non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
        });
    }
    failures
}

fn constraint_kind_to_intervention(kind: &str) -> String {
    let kind = kind.to_ascii_lowercase();
    if kind.contains("forbidden") {
        "future-cut".to_string()
    } else if kind.contains("conditional") {
        "conditional-allowance".to_string()
    } else {
        "review-gate".to_string()
    }
}

fn boundary_failure_kind(axes: &[String]) -> String {
    let joined = axes.join(" ").to_ascii_lowercase();
    if joined.contains("invariant") {
        "missing-invariant".to_string()
    } else if joined.contains("operation") || joined.contains("support") {
        "undefined-operation-support".to_string()
    } else if joined.contains("gluing") {
        "unglued-local-futures".to_string()
    } else {
        "missing-observation-boundary".to_string()
    }
}

fn path_ids_for_unknown_remainder(
    affected_family_ids: &[String],
    path_ids: &[String],
) -> Vec<String> {
    let affected = affected_family_ids
        .iter()
        .map(|family_id| path_class_id_for_family(family_id))
        .filter(|path_id| path_ids.iter().any(|known| known == path_id))
        .collect::<Vec<_>>();
    if affected.is_empty() {
        path_ids.to_vec()
    } else {
        unique_strings(affected)
    }
}

fn forecast_unsupported_constructs(estimate: &OperationSupportEstimateV0) -> Vec<String> {
    let mut constructs = vec![
        "probability assignment".to_string(),
        "global risk reduction proof".to_string(),
        "trajectory-level safety proof".to_string(),
        "empirical prediction theorem".to_string(),
    ];
    constructs.extend(estimate.evidence_boundary.unsupported_constructs.clone());
    constructs.extend(
        estimate
            .known_forbidden_support
            .iter()
            .map(|forbidden| forbidden.operation_family.clone()),
    );
    unique_strings(constructs)
}

fn forecast_source_refs_from_cone(cone: &ForecastConeSkeletonV0) -> Vec<String> {
    let mut refs = Vec::new();
    refs.extend(cone.operation_support_ref.source_ref_ids.clone());
    refs.extend(cone.bounded_horizon.source_ref_ids.clone());
    refs.extend(cone.forecast_boundary.source_ref_ids.clone());
    for support in &cone.finite_support_refs {
        refs.extend(support.source_ref_ids.clone());
    }
    for path in &cone.path_class_candidates {
        refs.extend(path.source_ref_ids.clone());
    }
    for remainder in &cone.unknown_remainder {
        refs.extend(remainder.source_ref_ids.clone());
    }
    let refs = unique_strings(refs);
    if refs.is_empty() {
        vec![format!("source:{}", id_suffix(&cone.cone_id))]
    } else {
        refs
    }
}

fn consequence_regions_from_cone(
    cone: &ForecastConeSkeletonV0,
    source_ref_ids: &[String],
) -> Vec<AffectedArchitectureRegionV0> {
    let regions = cone
        .path_class_candidates
        .iter()
        .map(|path| AffectedArchitectureRegionV0 {
            region_id: region_id_for_path(&path.path_class_id),
            region_ref: path.path_class.clone(),
            effect_kind: "forecast-path-class".to_string(),
            source_ref_ids: retained_source_refs(&path.source_ref_ids, source_ref_ids),
            boundary: format!(
                "region is selected from forecast path class {} under the bounded cone, not inferred as global architecture impact",
                path.path_class_id
            ),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    if regions.is_empty() {
        vec![AffectedArchitectureRegionV0 {
            region_id: format!("region:{}:forecast-boundary", id_suffix(&cone.cone_id)),
            region_ref: "forecast-boundary".to_string(),
            effect_kind: "forecast-boundary-review".to_string(),
            source_ref_ids: source_ref_ids.to_vec(),
            boundary:
                "fallback region records the forecast boundary without inferring global impact"
                    .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }]
    } else {
        regions
    }
}

fn consequence_axes_from_cone(
    cone: &ForecastConeSkeletonV0,
    measurement_boundary_refs: &[String],
) -> Vec<ComparableSignatureAxisV0> {
    let mut axis_names = cone
        .path_class_candidates
        .iter()
        .flat_map(|path| path.affected_axes.clone())
        .collect::<Vec<_>>();
    if axis_names.is_empty() {
        axis_names.push("unknownRemainder".to_string());
    }
    unique_strings(axis_names)
        .into_iter()
        .map(|axis_name| ComparableSignatureAxisV0 {
            axis_id: axis_id_for_name(&axis_name),
            axis_name,
            measurement_boundary_refs: measurement_boundary_refs.to_vec(),
            comparability:
                "comparable only across retained forecast source refs and boundary items"
                    .to_string(),
            missing_invariant_refs: vec![format!(
                "missing:{}:invariant",
                id_suffix(&measurement_boundary_refs.join("-"))
            )],
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect()
}

fn consequence_delta_ranges(
    axis_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<ExpectedAxisDeltaRangeV0> {
    axis_ids
        .iter()
        .map(|axis_id| ExpectedAxisDeltaRangeV0 {
            delta_id: format!("delta:{}:forecast-range", id_suffix(axis_id)),
            axis_id: axis_id.clone(),
            range_kind: "qualitative-bounded".to_string(),
            lower_bound: Some("retained".to_string()),
            upper_bound: Some("bounded-forecast-projection".to_string()),
            source_ref_ids: source_ref_ids.to_vec(),
            boundary: "expected range is qualitative and bounded by forecast cone evidence"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect()
}

fn consequence_missing_boundaries(
    cone: &ForecastConeSkeletonV0,
    axis_ids: &[String],
    measurement_boundary_refs: &[String],
) -> Vec<ConsequenceMissingBoundaryItemV0> {
    let mut items = cone
        .forecast_boundary
        .unsupported_constructs
        .iter()
        .map(|construct| ConsequenceMissingBoundaryItemV0 {
            item_id: format!("missing:{}:boundary", id_suffix(construct)),
            item_kind: "unsupported-construct-boundary".to_string(),
            affected_axis_ids: axis_ids.to_vec(),
            reason: format!(
                "{} is outside the selected forecast cone boundary",
                construct
            ),
            treatment: "retain as missing boundary item for reviewer and issue decomposition"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    if items.is_empty() {
        items.push(ConsequenceMissingBoundaryItemV0 {
            item_id: format!(
                "missing:{}:measurement-boundary",
                id_suffix(&measurement_boundary_refs.join("-"))
            ),
            item_kind: "measurement-boundary".to_string(),
            affected_axis_ids: axis_ids.to_vec(),
            reason: "forecast cone did not provide unsupported constructs".to_string(),
            treatment: "retain as missing boundary item for reviewer and issue decomposition"
                .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        });
    }
    items
}

fn consequence_obstruction_candidates(
    cone: &ForecastConeSkeletonV0,
    region_ids: &[String],
    axis_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<SelectedObstructionWitnessCandidateV0> {
    let candidates = cone
        .unknown_remainder
        .iter()
        .map(|remainder| SelectedObstructionWitnessCandidateV0 {
            candidate_id: format!("obstruction:{}", id_suffix(&remainder.remainder_id)),
            obstruction_kind: "unknown-forecast-boundary".to_string(),
            region_ids: region_ids_for_paths(&remainder.affected_path_class_ids, region_ids),
            axis_ids: axis_ids_for_paths(cone, &remainder.affected_path_class_ids, axis_ids),
            evidence_refs: retained_source_refs(&remainder.source_ref_ids, source_ref_ids),
            selection_boundary:
                "selected as a review candidate, not as a proved obstruction witness".to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        vec![SelectedObstructionWitnessCandidateV0 {
            candidate_id: format!("obstruction:{}:forecast-boundary", id_suffix(&cone.cone_id)),
            obstruction_kind: "forecast-boundary-review".to_string(),
            region_ids: region_ids.to_vec(),
            axis_ids: axis_ids.to_vec(),
            evidence_refs: source_ref_ids.to_vec(),
            selection_boundary:
                "selected as a review candidate, not as a proved obstruction witness".to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }]
    } else {
        candidates
    }
}

fn consequence_unknown_remainder(
    cone: &ForecastConeSkeletonV0,
    region_ids: &[String],
    axis_ids: &[String],
) -> Vec<ConsequenceUnknownRemainderV0> {
    let remainders = cone
        .unknown_remainder
        .iter()
        .map(|remainder| ConsequenceUnknownRemainderV0 {
            remainder_id: format!("envelope:{}", remainder.remainder_id),
            affected_region_ids: region_ids_for_paths(
                &remainder.affected_path_class_ids,
                region_ids,
            ),
            affected_axis_ids: axis_ids_for_paths(
                cone,
                &remainder.affected_path_class_ids,
                axis_ids,
            ),
            unknown_axes: remainder.unknown_axes.clone(),
            treatment:
                "retain as unresolved consequence envelope remainder under the selected boundary"
                    .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    if remainders.is_empty() {
        vec![ConsequenceUnknownRemainderV0 {
            remainder_id: format!("unknown:{}:forecast-boundary", id_suffix(&cone.cone_id)),
            affected_region_ids: region_ids.to_vec(),
            affected_axis_ids: axis_ids.to_vec(),
            unknown_axes: vec!["unreported forecast remainder".to_string()],
            treatment:
                "retain as unresolved consequence envelope remainder under the selected boundary"
                    .to_string(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }]
    } else {
        remainders
    }
}

fn consequence_typed_boundary_failures(
    cone: &ForecastConeSkeletonV0,
    region_ids: &[String],
    axis_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<ConsequenceTypedBoundaryFailureV0> {
    cone.typed_boundary_failures
        .iter()
        .map(|failure| ConsequenceTypedBoundaryFailureV0 {
            failure_id: format!("envelope:{}", failure.failure_id),
            failure_kind: failure.failure_kind.clone(),
            affected_region_ids: region_ids_for_paths(&failure.affected_path_class_ids, region_ids),
            affected_axis_ids: axis_ids_for_paths(cone, &failure.affected_path_class_ids, axis_ids),
            evidence_refs: retained_source_refs(&failure.evidence_refs, source_ref_ids),
            reason: failure.reason.clone(),
            next_action: failure.reviewer_action.clone(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect()
}

fn consequence_reviewer_actions(
    missing_boundary_items: &[ConsequenceMissingBoundaryItemV0],
    typed_boundary_failures: &[ConsequenceTypedBoundaryFailureV0],
    cone: &ForecastConeSkeletonV0,
    source_ref_ids: &[String],
) -> Vec<ConsequenceReviewerActionV0> {
    let mut actions = missing_boundary_items
        .iter()
        .map(|item| ConsequenceReviewerActionV0 {
            action_id: format!("action:{}", id_suffix(&item.item_id)),
            action_kind: "resolve-boundary".to_string(),
            status: "needs_human_judgement".to_string(),
            source_item_refs: vec![item.item_id.clone()],
            evidence_refs: source_ref_ids.to_vec(),
            message: item.treatment.clone(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        })
        .collect::<Vec<_>>();
    actions.extend(
        typed_boundary_failures
            .iter()
            .map(|failure| ConsequenceReviewerActionV0 {
                action_id: format!("action:{}", id_suffix(&failure.failure_id)),
                action_kind: "typed-boundary-failure".to_string(),
                status: if failure.failure_kind.contains("forbidden") {
                    "blocked".to_string()
                } else {
                    "boundary_failure".to_string()
                },
                source_item_refs: vec![failure.failure_id.clone()],
                evidence_refs: retained_source_refs(&failure.evidence_refs, source_ref_ids),
                message: failure.next_action.clone(),
                non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
            }),
    );
    actions.extend(cone.governance_interventions.iter().map(|intervention| {
        ConsequenceReviewerActionV0 {
            action_id: format!("action:{}", id_suffix(&intervention.intervention_id)),
            action_kind: intervention.intervention_kind.clone(),
            status: "needs_human_judgement".to_string(),
            source_item_refs: vec![intervention.intervention_id.clone()],
            evidence_refs: retained_source_refs(&intervention.source_ref_ids, source_ref_ids),
            message: intervention.reviewer_action.clone(),
            non_conclusions: strings(&ENVELOPE_NON_CONCLUSIONS),
        }
    }));
    actions
}

fn consequence_issue_recommendations(cone: &ForecastConeSkeletonV0) -> Vec<String> {
    let mut recommendations = cone
        .unknown_remainder
        .iter()
        .map(|remainder| {
            format!(
                "decompose unknown forecast remainder {} into a downstream empirical or review issue",
                remainder.remainder_id
            )
        })
        .collect::<Vec<_>>();
    if recommendations.is_empty() {
        recommendations.push(
            "decompose forecast boundary review into a downstream empirical or review issue"
                .to_string(),
        );
    }
    recommendations
}

fn region_ids_for_paths(path_ids: &[String], all_region_ids: &[String]) -> Vec<String> {
    let selected = path_ids
        .iter()
        .map(|path_id| region_id_for_path(path_id))
        .filter(|region_id| all_region_ids.iter().any(|known| known == region_id))
        .collect::<Vec<_>>();
    if selected.is_empty() {
        all_region_ids.to_vec()
    } else {
        unique_strings(selected)
    }
}

fn axis_ids_for_paths(
    cone: &ForecastConeSkeletonV0,
    path_ids: &[String],
    all_axis_ids: &[String],
) -> Vec<String> {
    let selected_path_ids = path_ids.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let selected = cone
        .path_class_candidates
        .iter()
        .filter(|path| selected_path_ids.contains(path.path_class_id.as_str()))
        .flat_map(|path| path.affected_axes.iter().map(|axis| axis_id_for_name(axis)))
        .filter(|axis_id| all_axis_ids.iter().any(|known| known == axis_id))
        .collect::<Vec<_>>();
    if selected.is_empty() {
        all_axis_ids.to_vec()
    } else {
        unique_strings(selected)
    }
}

fn region_id_for_path(path_id: &str) -> String {
    format!("region:{}", id_suffix(path_id))
}

fn axis_id_for_name(axis_name: &str) -> String {
    format!("axis:{}", id_suffix(axis_name))
}

fn finite_support_ref(
    support_ref_id: &str,
    support_kind: &str,
    operation_family_ids: &[&str],
    source_ref_ids: &[&str],
    boundary: &str,
) -> ForecastFiniteSupportRefV0 {
    ForecastFiniteSupportRefV0 {
        support_ref_id: support_ref_id.to_string(),
        support_kind: support_kind.to_string(),
        operation_family_ids: strings(operation_family_ids),
        source_ref_ids: strings(source_ref_ids),
        boundary: boundary.to_string(),
        assumptions: vec![
            "support is finite under selected fixture refs".to_string(),
            "support does not imply operation support completeness".to_string(),
        ],
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }
}

fn path_class_candidate(
    path_class_id: &str,
    path_class: &str,
    support_ref_ids: &[&str],
    operation_family_ids: &[&str],
    source_ref_ids: &[&str],
    affected_axes: &[&str],
    rationale: &str,
) -> ForecastPathClassCandidateV0 {
    ForecastPathClassCandidateV0 {
        path_class_id: path_class_id.to_string(),
        path_class: path_class.to_string(),
        support_ref_ids: strings(support_ref_ids),
        operation_family_ids: strings(operation_family_ids),
        horizon_ref_id: "horizon:b12-mvp-skeleton".to_string(),
        source_ref_ids: strings(source_ref_ids),
        affected_axes: strings(affected_axes),
        rationale: rationale.to_string(),
        probability_boundary: "no probability is assigned by the skeleton".to_string(),
        non_conclusions: strings(&FORECAST_NON_CONCLUSIONS),
    }
}

fn check_forecast_schema(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let invalid = cone.schema_version != FORECAST_CONE_SKELETON_SCHEMA_VERSION
        || cone.cone_id.trim().is_empty()
        || cone.operation_support_ref.estimate_schema_version
            != OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION
        || cone.operation_support_ref.estimate_id.trim().is_empty()
        || cone.operation_support_ref.source_ref_ids.is_empty();
    let mut check = validation_check(
        "forecast-cone-skeleton-schema-supported",
        "forecast cone schema and operation support ref are supported",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "schema, coneId, operation support estimate schema, estimate id, and source refs are required"
                .to_string(),
        );
    }
    check
}

fn check_forecast_support_refs(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let families = forecast_family_ids(cone);
    let invalid = cone
        .finite_support_refs
        .iter()
        .filter(|support| {
            support.support_ref_id.trim().is_empty()
                || support.operation_family_ids.is_empty()
                || support.source_ref_ids.is_empty()
                || support.boundary.trim().is_empty()
                || support
                    .operation_family_ids
                    .iter()
                    .any(|family| !families.contains(family.as_str()))
                || support
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|support| support.support_ref_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "forecast-cone-finite-support-refs-retained",
        "finite support refs are present and linked to operation support families",
        if !cone.finite_support_refs.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if cone.finite_support_refs.is_empty() {
        check.reason = Some("at least one finite support ref is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "finite support refs with missing or dangling refs: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(cone.finite_support_refs.len());
    check
}

fn check_forecast_horizon(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let horizon = &cone.bounded_horizon;
    let invalid = horizon.horizon_id.trim().is_empty()
        || horizon.max_steps == 0
        || horizon.source_ref_ids.is_empty()
        || horizon.boundary.trim().is_empty()
        || horizon
            .source_ref_ids
            .iter()
            .any(|source| !sources.contains(source.as_str()));
    let mut check = validation_check(
        "forecast-cone-bounded-horizon-present",
        "bounded horizon is explicit and source-bound",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "horizon id, positive maxSteps, source refs, and a boundary are required".to_string(),
        );
    }
    check
}

fn check_forecast_path_classes(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let supports = support_ids(cone);
    let families = forecast_family_ids(cone);
    let invalid = cone
        .path_class_candidates
        .iter()
        .filter(|path| {
            path.path_class_id.trim().is_empty()
                || path.support_ref_ids.is_empty()
                || path.operation_family_ids.is_empty()
                || path.horizon_ref_id != cone.bounded_horizon.horizon_id
                || path.probability_boundary.trim().is_empty()
                || overpromotes_probability(&path.probability_boundary)
                || path
                    .support_ref_ids
                    .iter()
                    .any(|support| !supports.contains(support.as_str()))
                || path
                    .operation_family_ids
                    .iter()
                    .any(|family| !families.contains(family.as_str()))
                || path
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|path| path.path_class_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "forecast-cone-path-classes-bounded",
        "path class candidates are finite, source-bound, and non-probabilistic",
        if !cone.path_class_candidates.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if cone.path_class_candidates.is_empty() {
        check.reason = Some("at least one path class candidate is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "path classes with missing refs or probability over-promotion: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(cone.path_class_candidates.len());
    check
}

fn check_forecast_grand_theorem_evidence(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let paths = path_ids(cone);
    let invalid_gluing = cone
        .gluing_evidence
        .iter()
        .filter(|item| {
            item.gluing_id.trim().is_empty()
                || item.local_future_refs.is_empty()
                || item.status.trim().is_empty()
                || item.boundary.trim().is_empty()
                || item.reviewer_action.trim().is_empty()
                || item
                    .local_future_refs
                    .iter()
                    .any(|path| !paths.contains(path.as_str()))
                || item
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|item| item.gluing_id.clone())
        .collect::<Vec<_>>();
    let invalid_governance = cone
        .governance_interventions
        .iter()
        .filter(|item| {
            item.intervention_id.trim().is_empty()
                || item.target_path_class_ids.is_empty()
                || item.cut_action.trim().is_empty()
                || item.preservation_boundary.trim().is_empty()
                || item.reviewer_action.trim().is_empty()
                || item
                    .target_path_class_ids
                    .iter()
                    .any(|path| !paths.contains(path.as_str()))
                || item
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|item| item.intervention_id.clone())
        .collect::<Vec<_>>();
    let invalid_failures = cone
        .typed_boundary_failures
        .iter()
        .filter(|item| {
            item.failure_id.trim().is_empty()
                || item.failure_kind.trim().is_empty()
                || item.affected_path_class_ids.is_empty()
                || item.reason.trim().is_empty()
                || item.reviewer_action.trim().is_empty()
                || item
                    .affected_path_class_ids
                    .iter()
                    .any(|path| !paths.contains(path.as_str()))
                || item
                    .evidence_refs
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|item| item.failure_id.clone())
        .collect::<Vec<_>>();
    let valid = !cone.gluing_evidence.is_empty()
        && !cone.governance_interventions.is_empty()
        && !cone.typed_boundary_failures.is_empty()
        && invalid_gluing.is_empty()
        && invalid_governance.is_empty()
        && invalid_failures.is_empty();
    let mut check = validation_check(
        "forecast-cone-grand-theorem-review-evidence-retained",
        "gluing, governance, and typed boundary failure evidence are retained",
        if valid { "pass" } else { "fail" },
    );
    if !valid {
        check.reason = Some(format!(
            "invalid gluing [{}], governance [{}], or typed failures [{}]",
            invalid_gluing.join(", "),
            invalid_governance.join(", "),
            invalid_failures.join(", ")
        ));
    }
    check
}

fn check_forecast_boundary(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let supports = support_ids(cone);
    let boundary = &cone.forecast_boundary;
    let invalid = boundary.boundary_id.trim().is_empty()
        || boundary.source_ref_ids.is_empty()
        || boundary.measurement_boundary_refs.is_empty()
        || boundary.support_ref_ids.is_empty()
        || boundary.horizon_ref_ids.is_empty()
        || boundary
            .source_ref_ids
            .iter()
            .any(|source| !sources.contains(source.as_str()))
        || boundary
            .support_ref_ids
            .iter()
            .any(|support| !supports.contains(support.as_str()))
        || !boundary
            .horizon_ref_ids
            .iter()
            .any(|horizon| horizon == &cone.bounded_horizon.horizon_id);
    let mut check = validation_check(
        "forecast-cone-boundary-retained",
        "forecast boundary retains support, horizon, measurement, and source refs",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "forecast boundary requires source refs, measurement refs, support refs, and horizon refs"
                .to_string(),
        );
    }
    check
}

fn check_forecast_unknown_remainder(cone: &ForecastConeSkeletonV0) -> ValidationCheck {
    let sources = forecast_source_ids(cone);
    let paths = path_ids(cone);
    let invalid = cone
        .unknown_remainder
        .iter()
        .filter(|remainder| {
            remainder.remainder_id.trim().is_empty()
                || remainder.affected_path_class_ids.is_empty()
                || remainder.unknown_axes.is_empty()
                || treats_unknown_as_zero(&remainder.treatment)
                || remainder
                    .affected_path_class_ids
                    .iter()
                    .any(|path| !paths.contains(path.as_str()))
                || remainder
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|remainder| remainder.remainder_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "forecast-cone-unknown-remainder-not-measured-zero",
        "unknown forecast axes remain explicit and are not treated as measured zero",
        if !cone.unknown_remainder.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if cone.unknown_remainder.is_empty() {
        check.reason = Some("at least one unknown remainder item is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "unknown remainder entries with missing refs or measured-zero treatment: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(cone.unknown_remainder.len());
    check
}

fn check_envelope_schema(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let invalid = envelope.schema_version != CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION
        || envelope.envelope_id.trim().is_empty()
        || envelope.forecast_cone_ref.forecast_cone_schema_version
            != FORECAST_CONE_SKELETON_SCHEMA_VERSION
        || envelope.forecast_cone_ref.cone_id.trim().is_empty()
        || envelope.forecast_cone_ref.source_ref_ids.is_empty();
    let mut check = validation_check(
        "consequence-envelope-schema-supported",
        "consequence envelope schema and forecast cone ref are supported",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "schema, envelopeId, forecast cone schema, cone id, and source refs are required"
                .to_string(),
        );
    }
    check
}

fn check_envelope_source_refs(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let sources = envelope_source_ids(envelope);
    let dangling_regions = envelope
        .affected_architecture_regions
        .iter()
        .filter(|region| {
            region.source_ref_ids.is_empty()
                || region
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|region| region.region_id.clone())
        .collect::<Vec<_>>();
    let dangling_deltas = envelope
        .expected_axis_delta_ranges
        .iter()
        .filter(|delta| {
            delta.source_ref_ids.is_empty()
                || delta
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|delta| delta.delta_id.clone())
        .collect::<Vec<_>>();
    let invalid = !dangling_regions.is_empty() || !dangling_deltas.is_empty();
    let mut check = validation_check(
        "consequence-envelope-source-refs-retained",
        "regions and delta ranges retain source refs",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(format!(
            "dangling source refs in regions [{}] or deltas [{}]",
            dangling_regions.join(", "),
            dangling_deltas.join(", ")
        ));
    }
    check
}

fn check_envelope_regions_and_axes(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let region_ids = region_ids(envelope);
    let axis_ids = axis_ids(envelope);
    let invalid_regions = envelope
        .affected_architecture_regions
        .iter()
        .filter(|region| {
            region.region_id.trim().is_empty()
                || region.region_ref.trim().is_empty()
                || region.boundary.trim().is_empty()
        })
        .map(|region| region.region_id.clone())
        .collect::<Vec<_>>();
    let invalid_axes = envelope
        .comparable_signature_axes
        .iter()
        .filter(|axis| {
            axis.axis_id.trim().is_empty()
                || axis.axis_name.trim().is_empty()
                || axis.measurement_boundary_refs.is_empty()
                || axis.comparability.trim().is_empty()
        })
        .map(|axis| axis.axis_id.clone())
        .collect::<Vec<_>>();
    let invalid_obstructions = envelope
        .obstruction_witness_candidates
        .iter()
        .filter(|candidate| {
            candidate.candidate_id.trim().is_empty()
                || candidate
                    .region_ids
                    .iter()
                    .any(|id| !region_ids.contains(id.as_str()))
                || candidate
                    .axis_ids
                    .iter()
                    .any(|id| !axis_ids.contains(id.as_str()))
                || candidate.selection_boundary.trim().is_empty()
        })
        .map(|candidate| candidate.candidate_id.clone())
        .collect::<Vec<_>>();
    let invalid = !invalid_regions.is_empty()
        || !invalid_axes.is_empty()
        || !invalid_obstructions.is_empty()
        || envelope.affected_architecture_regions.is_empty()
        || envelope.comparable_signature_axes.is_empty();
    let mut check = validation_check(
        "consequence-envelope-regions-axes-and-obstructions-linked",
        "affected regions, comparable axes, and obstruction candidates are linked",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(format!(
            "invalid regions [{}], axes [{}], or obstruction candidates [{}]",
            invalid_regions.join(", "),
            invalid_axes.join(", "),
            invalid_obstructions.join(", ")
        ));
    }
    check
}

fn check_envelope_boundaries(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let axis_ids = axis_ids(envelope);
    let invalid_missing = envelope
        .missing_boundary_items
        .iter()
        .filter(|item| {
            item.item_id.trim().is_empty()
                || item.affected_axis_ids.is_empty()
                || item
                    .affected_axis_ids
                    .iter()
                    .any(|axis| !axis_ids.contains(axis.as_str()))
                || treats_unknown_as_zero(&item.treatment)
        })
        .map(|item| item.item_id.clone())
        .collect::<Vec<_>>();
    let invalid_theorem = envelope
        .theorem_boundary_items
        .iter()
        .filter(|item| item.item_id.trim().is_empty() || item.required_evidence.is_empty())
        .map(|item| item.item_id.clone())
        .collect::<Vec<_>>();
    let has_summary = !envelope.summary_projection.summary_id.trim().is_empty()
        && envelope.summary_projection.affected_region_count
            == envelope.affected_architecture_regions.len()
        && envelope.summary_projection.comparable_axis_count
            == envelope.comparable_signature_axes.len()
        && envelope.summary_projection.missing_boundary_count
            == envelope.missing_boundary_items.len();
    let invalid = invalid_missing.is_empty() && invalid_theorem.is_empty() && has_summary;
    let mut check = validation_check(
        "consequence-envelope-boundaries-and-summary-retained",
        "missing boundaries, theorem boundaries, and summary projection are retained",
        if invalid { "pass" } else { "fail" },
    );
    if !invalid {
        check.reason = Some(format!(
            "invalid missing boundary items [{}], theorem boundary items [{}], or summary counts",
            invalid_missing.join(", "),
            invalid_theorem.join(", ")
        ));
    }
    check
}

fn check_envelope_reviewer_actions(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let regions = region_ids(envelope);
    let axes = axis_ids(envelope);
    let sources = envelope_source_ids(envelope);
    let invalid_failures = envelope
        .typed_boundary_failures
        .iter()
        .filter(|failure| {
            failure.failure_id.trim().is_empty()
                || failure.failure_kind.trim().is_empty()
                || failure.next_action.trim().is_empty()
                || failure
                    .affected_region_ids
                    .iter()
                    .any(|region| !regions.contains(region.as_str()))
                || failure
                    .affected_axis_ids
                    .iter()
                    .any(|axis| !axes.contains(axis.as_str()))
                || failure
                    .evidence_refs
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|failure| failure.failure_id.clone())
        .collect::<Vec<_>>();
    let invalid_actions = envelope
        .reviewer_actions
        .iter()
        .filter(|action| {
            action.action_id.trim().is_empty()
                || action.action_kind.trim().is_empty()
                || action.status.trim().is_empty()
                || action.evidence_refs.is_empty()
                || action.message.trim().is_empty()
                || action
                    .evidence_refs
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|action| action.action_id.clone())
        .collect::<Vec<_>>();
    let valid = !envelope.reviewer_actions.is_empty()
        && invalid_failures.is_empty()
        && invalid_actions.is_empty();
    let mut check = validation_check(
        "consequence-envelope-reviewer-actions-retained",
        "typed boundary failures and reviewer next actions retain evidence refs",
        if valid { "pass" } else { "fail" },
    );
    if !valid {
        check.reason = Some(format!(
            "invalid typed failures [{}] or reviewer actions [{}]",
            invalid_failures.join(", "),
            invalid_actions.join(", ")
        ));
    }
    check
}

fn check_review_summary_schema(summary: &SftReviewSummaryV0) -> ValidationCheck {
    let invalid = summary.schema_version != SFT_REVIEW_SUMMARY_SCHEMA_VERSION
        || summary.summary_id.trim().is_empty()
        || summary.envelope_ref.envelope_schema_version
            != CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION
        || summary.envelope_ref.envelope_id.trim().is_empty()
        || summary.envelope_ref.source_ref_ids.is_empty();
    let mut check = validation_check(
        "sft-review-summary-schema-supported",
        "review summary schema and consequence envelope ref are supported",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "schema, summaryId, envelope schema, envelope id, and source refs are required"
                .to_string(),
        );
    }
    check
}

fn check_review_summary_status(summary: &SftReviewSummaryV0) -> ValidationCheck {
    let allowed = REVIEW_STATUSES.iter().copied().collect::<BTreeSet<_>>();
    let invalid = !allowed.contains(summary.status.as_str());
    let mut check = validation_check(
        "sft-review-summary-status-bounded",
        "review status is one of the judgement-ready bounded statuses",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(format!(
            "unsupported review summary status: {}",
            summary.status
        ));
    }
    check
}

fn check_review_summary_refs(summary: &SftReviewSummaryV0) -> ValidationCheck {
    let evidence = summary
        .evidence_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let boundaries = summary
        .boundary_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let invalid_futures = summary
        .opened_futures
        .iter()
        .chain(summary.closed_futures.iter())
        .filter(|future| {
            future.future_id.trim().is_empty()
                || future.boundary.trim().is_empty()
                || future.evidence_refs.is_empty()
                || future
                    .evidence_refs
                    .iter()
                    .any(|source| !evidence.contains(source.as_str()))
        })
        .map(|future| future.future_id.clone())
        .collect::<Vec<_>>();
    let invalid_failures = summary
        .boundary_failures
        .iter()
        .filter(|failure| {
            failure.failure_id.trim().is_empty()
                || failure.evidence_refs.is_empty()
                || failure.boundary_refs.is_empty()
                || failure
                    .evidence_refs
                    .iter()
                    .any(|source| !evidence.contains(source.as_str()))
                || failure
                    .boundary_refs
                    .iter()
                    .any(|boundary| !boundaries.contains(boundary.as_str()))
        })
        .map(|failure| failure.failure_id.clone())
        .collect::<Vec<_>>();
    let invalid_actions = summary
        .next_actions
        .iter()
        .filter(|action| {
            action.action_id.trim().is_empty()
                || action.message.trim().is_empty()
                || action.evidence_refs.is_empty()
                || action
                    .evidence_refs
                    .iter()
                    .any(|source| !evidence.contains(source.as_str()))
        })
        .map(|action| action.action_id.clone())
        .collect::<Vec<_>>();
    let valid = !summary.opened_futures.is_empty()
        && !summary.next_actions.is_empty()
        && invalid_futures.is_empty()
        && invalid_failures.is_empty()
        && invalid_actions.is_empty();
    let mut check = validation_check(
        "sft-review-summary-evidence-and-boundary-refs-required",
        "futures, boundary failures, and next actions cite evidence and boundary refs",
        if valid { "pass" } else { "fail" },
    );
    if !valid {
        check.reason = Some(format!(
            "invalid futures [{}], failures [{}], or actions [{}]",
            invalid_futures.join(", "),
            invalid_failures.join(", "),
            invalid_actions.join(", ")
        ));
    }
    check
}

fn check_review_summary_contract(summary: &SftReviewSummaryV0) -> ValidationCheck {
    let contract = &summary.llm_judgement_contract;
    let forbidden = contract.forbidden_readings.join(" ").to_ascii_lowercase();
    let valid = contract
        .input_fields
        .iter()
        .any(|field| field == "unknownRemainder")
        && contract
            .output_fields
            .iter()
            .any(|field| field == "nextActions")
        && contract.required_evidence_policy.contains("evidenceRefs")
        && forbidden.contains("probability")
        && forbidden.contains("lean theorem")
        && forbidden.contains("measured zero")
        && !contract.confidence_boundary.trim().is_empty();
    let mut check = validation_check(
        "sft-review-summary-llm-judgement-contract-bounded",
        "LLM judgement contract requires evidence refs and forbidden readings",
        if valid { "pass" } else { "fail" },
    );
    if !valid {
        check.reason = Some(
            "contract must include unknown remainder, next actions, evidence refs, and forbidden readings"
                .to_string(),
        );
    }
    check
}

fn check_envelope_unknown_remainder(envelope: &ConsequenceEnvelopeReportV0) -> ValidationCheck {
    let regions = region_ids(envelope);
    let axes = axis_ids(envelope);
    let invalid = envelope
        .unknown_remainder
        .iter()
        .filter(|remainder| {
            remainder.remainder_id.trim().is_empty()
                || remainder.unknown_axes.is_empty()
                || treats_unknown_as_zero(&remainder.treatment)
                || remainder
                    .affected_region_ids
                    .iter()
                    .any(|region| !regions.contains(region.as_str()))
                || remainder
                    .affected_axis_ids
                    .iter()
                    .any(|axis| !axes.contains(axis.as_str()))
        })
        .map(|remainder| remainder.remainder_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "consequence-envelope-unknown-remainder-not-measured-zero",
        "unknown report remainder remains explicit and is not treated as measured zero",
        if !envelope.unknown_remainder.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if envelope.unknown_remainder.is_empty() {
        check.reason = Some("at least one unknown remainder item is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "unknown remainder entries with missing refs or measured-zero treatment: {}",
            invalid.join(", ")
        ));
    }
    check
}

fn check_calibration_schema(hook: &ForecastCalibrationHookV0) -> ValidationCheck {
    let invalid = hook.schema_version != FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION
        || hook.hook_id.trim().is_empty()
        || hook.envelope_ref.envelope_schema_version != CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION
        || hook.envelope_ref.envelope_id.trim().is_empty()
        || hook.envelope_ref.source_ref_ids.is_empty();
    let mut check = validation_check(
        "forecast-calibration-hook-schema-supported",
        "calibration hook schema and envelope ref are supported",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "schema, hookId, envelope schema, envelope id, and source refs are required"
                .to_string(),
        );
    }
    check
}

fn check_calibration_refs(hook: &ForecastCalibrationHookV0) -> ValidationCheck {
    let sources = calibration_source_ids(hook);
    let forecast_ids = forecast_item_ids(hook);
    let observed_ids = observed_ref_ids(hook);
    let invalid_forecast = hook
        .forecast_item_refs
        .iter()
        .filter(|item| {
            item.forecast_item_id.trim().is_empty()
                || item.envelope_item_ref.trim().is_empty()
                || item.source_ref_ids.is_empty()
                || item
                    .source_ref_ids
                    .iter()
                    .any(|source| !sources.contains(source.as_str()))
        })
        .map(|item| item.forecast_item_id.clone())
        .collect::<Vec<_>>();
    let invalid_matches = hook
        .matches
        .iter()
        .filter(|item| {
            item.match_id.trim().is_empty()
                || !forecast_ids.contains(item.forecast_item_id.as_str())
                || item
                    .observed_ref_id
                    .as_ref()
                    .is_some_and(|observed| !observed_ids.contains(observed.as_str()))
        })
        .map(|item| item.match_id.clone())
        .collect::<Vec<_>>();
    let invalid = !hook.forecast_item_refs.is_empty()
        && !hook.matches.is_empty()
        && invalid_forecast.is_empty()
        && invalid_matches.is_empty();
    let mut check = validation_check(
        "forecast-calibration-hook-forecast-and-observed-refs-linked",
        "forecast items, observed refs, and matches are linked",
        if invalid { "pass" } else { "fail" },
    );
    if !invalid {
        check.reason = Some(format!(
            "invalid forecast item refs [{}] or match refs [{}]",
            invalid_forecast.join(", "),
            invalid_matches.join(", ")
        ));
    }
    check
}

fn check_calibration_statuses(hook: &ForecastCalibrationHookV0) -> ValidationCheck {
    let allowed = CALIBRATION_STATUSES
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let invalid_observed = hook
        .observed_outcome_refs
        .iter()
        .filter(|observed| {
            !allowed.contains(observed.status.as_str())
                || treats_unknown_as_zero(&observed.evidence_boundary)
        })
        .map(|observed| observed.observed_ref_id.clone())
        .collect::<Vec<_>>();
    let invalid_matches = hook
        .matches
        .iter()
        .filter(|item| {
            !allowed.contains(item.status.as_str()) || treats_unknown_as_zero(&item.update_boundary)
        })
        .map(|item| item.match_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "forecast-calibration-hook-statuses-not-measured-zero",
        "matched, unmatched, unavailable, private, and notComparable statuses are not measured zero",
        if invalid_observed.is_empty() && invalid_matches.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !invalid_observed.is_empty() || !invalid_matches.is_empty() {
        check.reason = Some(format!(
            "invalid observed statuses [{}] or match statuses [{}]",
            invalid_observed.join(", "),
            invalid_matches.join(", ")
        ));
        check.examples = invalid_observed
            .iter()
            .chain(invalid_matches.iter())
            .map(|id| {
                generic_validation_example(
                    id,
                    "status/updateBoundary",
                    "allowed statuses must not be collapsed into measured zero",
                )
            })
            .collect();
    }
    check
}

fn check_calibration_boundaries(hook: &ForecastCalibrationHookV0) -> ValidationCheck {
    let invalid = hook.reference_boundaries.b10_refs.is_empty()
        || hook.reference_boundaries.b11_refs.is_empty()
        || hook
            .reference_boundaries
            .measurement_boundary
            .trim()
            .is_empty()
        || treats_unknown_as_zero(&hook.reference_boundaries.measurement_boundary);
    let mut check = validation_check(
        "forecast-calibration-hook-b10-b11-boundaries-retained",
        "B10 and B11 reference boundaries are retained",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason =
            Some("B10 refs, B11 refs, and non-zero measurement boundary are required".to_string());
    }
    check
}

fn check_required_non_conclusions(
    id: &str,
    actual: &[String],
    required: &[&str],
) -> ValidationCheck {
    let missing = required
        .iter()
        .filter(|required| !actual.iter().any(|actual| actual == *required))
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        id,
        "required non-conclusions are preserved",
        if missing.is_empty() { "pass" } else { "fail" },
    );
    if !missing.is_empty() {
        check.reason = Some(format!(
            "missing required non-conclusions: {}",
            missing.join(", ")
        ));
    }
    check.count = Some(actual.len());
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

fn forecast_source_ids(cone: &ForecastConeSkeletonV0) -> BTreeSet<&str> {
    cone.operation_support_ref
        .source_ref_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn forecast_family_ids(cone: &ForecastConeSkeletonV0) -> BTreeSet<&str> {
    cone.operation_support_ref
        .candidate_operation_family_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn support_ids(cone: &ForecastConeSkeletonV0) -> BTreeSet<&str> {
    cone.finite_support_refs
        .iter()
        .map(|support| support.support_ref_id.as_str())
        .collect()
}

fn path_ids(cone: &ForecastConeSkeletonV0) -> BTreeSet<&str> {
    cone.path_class_candidates
        .iter()
        .map(|path| path.path_class_id.as_str())
        .collect()
}

fn envelope_source_ids(envelope: &ConsequenceEnvelopeReportV0) -> BTreeSet<&str> {
    envelope
        .forecast_cone_ref
        .source_ref_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn envelope_boundary_refs(envelope: &ConsequenceEnvelopeReportV0) -> Vec<String> {
    unique_strings(
        envelope
            .forecast_cone_ref
            .forecast_boundary_refs
            .iter()
            .cloned()
            .chain(
                envelope
                    .comparable_signature_axes
                    .iter()
                    .flat_map(|axis| axis.measurement_boundary_refs.clone()),
            )
            .chain(
                envelope
                    .theorem_boundary_items
                    .iter()
                    .map(|item| item.item_id.clone()),
            )
            .collect(),
    )
}

fn region_ids(envelope: &ConsequenceEnvelopeReportV0) -> BTreeSet<&str> {
    envelope
        .affected_architecture_regions
        .iter()
        .map(|region| region.region_id.as_str())
        .collect()
}

fn axis_ids(envelope: &ConsequenceEnvelopeReportV0) -> BTreeSet<&str> {
    envelope
        .comparable_signature_axes
        .iter()
        .map(|axis| axis.axis_id.as_str())
        .collect()
}

fn calibration_source_ids(hook: &ForecastCalibrationHookV0) -> BTreeSet<&str> {
    hook.envelope_ref
        .source_ref_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn forecast_item_ids(hook: &ForecastCalibrationHookV0) -> BTreeSet<&str> {
    hook.forecast_item_refs
        .iter()
        .map(|item| item.forecast_item_id.as_str())
        .collect()
}

fn observed_ref_ids(hook: &ForecastCalibrationHookV0) -> BTreeSet<&str> {
    hook.observed_outcome_refs
        .iter()
        .map(|item| item.observed_ref_id.as_str())
        .collect()
}

fn overpromotes_probability(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    (value.contains("probability") || value.contains("probabilistic"))
        && !(value.contains("no probability") || value.contains("does not assign"))
}

fn treats_unknown_as_zero(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    value.contains("measured zero")
        || value.contains("treated as zero")
        || value.contains("safe")
        || value.contains("absent")
}

fn review_status(
    boundary_failures: &[SftReviewBoundaryFailureV0],
    next_actions: &[SftReviewNextActionV0],
) -> String {
    if boundary_failures
        .iter()
        .any(|failure| failure.failure_kind.contains("forbidden"))
    {
        "blocked".to_string()
    } else if !boundary_failures.is_empty() {
        "boundary_failure".to_string()
    } else if !next_actions.is_empty() {
        "needs_human_judgement".to_string()
    } else {
        "governed".to_string()
    }
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}

fn unique_strings(values: Vec<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut unique = Vec::new();
    for value in values {
        if seen.insert(value.clone()) {
            unique.push(value);
        }
    }
    unique
}

fn id_suffix(value: &str) -> String {
    let suffix = value
        .rsplit_once(':')
        .map(|(_, suffix)| suffix)
        .unwrap_or(value);
    let mut slug = String::new();
    let mut last_was_dash = false;
    for ch in suffix.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_was_dash = false;
        } else if !last_was_dash {
            slug.push('-');
            last_was_dash = true;
        }
    }
    let slug = slug.trim_matches('-').to_string();
    if slug.is_empty() {
        "unknown".to_string()
    } else {
        slug
    }
}
