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
    ConsequenceForecastConeRefV0, ConsequenceMissingBoundaryItemV0,
    ConsequenceTheoremBoundaryItemV0, ConsequenceUnknownRemainderV0, ExpectedAxisDeltaRangeV0,
    FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION,
    FORECAST_CALIBRATION_HOOK_VALIDATION_REPORT_SCHEMA_VERSION,
    FORECAST_CONE_SKELETON_SCHEMA_VERSION, FORECAST_CONE_SKELETON_VALIDATION_REPORT_SCHEMA_VERSION,
    ForecastBoundaryV0, ForecastBoundedHorizonV0, ForecastCalibrationHookV0,
    ForecastCalibrationHookValidationInput, ForecastCalibrationHookValidationReportV0,
    ForecastCalibrationHookValidationSummary, ForecastConeSkeletonV0,
    ForecastConeSkeletonValidationInput, ForecastConeSkeletonValidationReportV0,
    ForecastConeSkeletonValidationSummary, ForecastFiniteSupportRefV0,
    ForecastOperationSupportRefV0, ForecastPathClassCandidateV0, ForecastUnknownRemainderV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION, OperationSupportEstimateV0,
    OperationSupportUnknownRemainderV0, SelectedObstructionWitnessCandidateV0, ValidationCheck,
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
        cone_id: "fixture-forecast-cone-skeleton-v0".to_string(),
        operation_support_ref: ForecastOperationSupportRefV0 {
            estimate_schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
            estimate_id: "fixture-operation-support-estimate-v0".to_string(),
            descriptor_id: "fixture-artifact-descriptor-v0".to_string(),
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
        envelope_id: "fixture-consequence-envelope-report-v0".to_string(),
        forecast_cone_ref: ConsequenceForecastConeRefV0 {
            forecast_cone_schema_version: FORECAST_CONE_SKELETON_SCHEMA_VERSION.to_string(),
            cone_id: "fixture-forecast-cone-skeleton-v0".to_string(),
            operation_support_estimate_id: "fixture-operation-support-estimate-v0".to_string(),
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

pub fn validate_consequence_envelope_report(
    envelope: &ConsequenceEnvelopeReportV0,
    input_path: &str,
) -> ConsequenceEnvelopeValidationReportV0 {
    let checks = vec![
        check_envelope_schema(envelope),
        check_envelope_source_refs(envelope),
        check_envelope_regions_and_axes(envelope),
        check_envelope_boundaries(envelope),
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

pub fn static_forecast_calibration_hook() -> ForecastCalibrationHookV0 {
    let source_ref_ids = vec![
        "source:issue-737".to_string(),
        "source:consequence-envelope-fixture".to_string(),
        "source:b10-report-outcome-daily-ledger".to_string(),
        "source:b11-signature-trajectory-report".to_string(),
    ];

    ForecastCalibrationHookV0 {
        schema_version: FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION.to_string(),
        hook_id: "fixture-forecast-calibration-hook-v0".to_string(),
        envelope_ref: CalibrationEnvelopeRefV0 {
            envelope_schema_version: CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
            envelope_id: "fixture-consequence-envelope-report-v0".to_string(),
            cone_id: "fixture-forecast-cone-skeleton-v0".to_string(),
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
                path_or_url: "tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
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
                "outcome-linkage-dataset-v0".to_string(),
                "report-outcome-daily-ledger-v0".to_string(),
            ],
            b11_refs: vec![
                "signature-trajectory-report-v0".to_string(),
                "architecture-dynamics-metrics-report-v0".to_string(),
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
            "schemaVersion, coneId, operation support estimate schema, estimate id, and source refs are required"
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
            "schemaVersion, envelopeId, forecast cone schema, cone id, and source refs are required"
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
            "schemaVersion, hookId, envelope schema, envelope id, and source refs are required"
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
