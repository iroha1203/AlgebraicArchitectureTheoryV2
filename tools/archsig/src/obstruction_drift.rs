use std::collections::BTreeSet;

use serde_json::json;

use crate::{
    ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION, ArchitectureDriftLedgerEntryV0,
    ArchitectureDriftLedgerV0, DriftLedgerAggregationWindowV0, DriftLedgerSourceV0,
    DriftLedgerSuppressionV0, FeatureReportEdgeRef, FeatureReportEvidenceRef,
    FeatureReportObstructionWitness, OBSTRUCTION_WITNESS_SCHEMA_VERSION,
    ObstructionWitnessArtifactV0, ObstructionWitnessVersioningV0, SchemaArtifactCompatibilityV0,
    SchemaCoverageExactnessBoundaryV0, SchemaFieldMappingV0, SchemaRequiredAssumptionV0,
};

const COMPATIBILITY_POLICY_REF: &str = "b9-compatibility-policy-v0";

pub fn static_obstruction_witness_artifact() -> ObstructionWitnessArtifactV0 {
    let witness = FeatureReportObstructionWitness {
        witness_id: "witness-hidden-cache-access".to_string(),
        layer: "static".to_string(),
        kind: "hidden_interaction".to_string(),
        extension_role: vec![
            "hidden_interaction".to_string(),
            "invariant_not_preserved".to_string(),
        ],
        extension_classification: vec!["interaction".to_string()],
        components: vec!["CouponService".to_string(), "PaymentAdapter".to_string()],
        edges: vec![FeatureReportEdgeRef {
            relation_id: "relation-coupon-payment-cache".to_string(),
            from: Some("CouponService".to_string()),
            to: Some("PaymentAdapter".to_string()),
            kind: "call".to_string(),
        }],
        paths: vec!["path-coupon-payment-cache".to_string()],
        diagrams: Vec::new(),
        nonfillability_witness_ref: None,
        operation: Some("feature_addition".to_string()),
        evidence: vec![
            FeatureReportEvidenceRef {
                evidence_ref: "evidence-source-coupon-cache".to_string(),
                kind: Some("source_location".to_string()),
                artifact_ref: Some("artifact-current-feature-report".to_string()),
                path: Some("src/coupon/CouponService.ts".to_string()),
                symbol: Some("CouponService.calculate".to_string()),
                rule_id: Some("typescript-static-call-fixture-v0".to_string()),
            },
            FeatureReportEvidenceRef {
                evidence_ref: "evidence-private-runtime-log".to_string(),
                kind: Some("private_runtime_log".to_string()),
                artifact_ref: None,
                path: None,
                symbol: None,
                rule_id: Some("retention-manifest-private-evidence-v0".to_string()),
            },
        ],
        theorem_reference: vec!["StaticSplitFeatureExtension".to_string()],
        claim_level: "tooling".to_string(),
        claim_classification: "MEASURED".to_string(),
        measurement_boundary: "measuredNonzero".to_string(),
        non_conclusions: vec![
            "private runtime log evidence is not measured-zero evidence".to_string(),
            "witness compatibility does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
        repair_candidates: vec!["repair-coupon-boundary".to_string()],
    };

    ObstructionWitnessArtifactV0 {
        schema_version: OBSTRUCTION_WITNESS_SCHEMA_VERSION.to_string(),
        schema_compatibility: Some(obstruction_witness_schema_compatibility_metadata(&witness)),
        witness,
        versioning: ObstructionWitnessVersioningV0 {
            target_fields: vec![
                "witnessId".to_string(),
                "layer".to_string(),
                "kind".to_string(),
                "extensionRole".to_string(),
                "extensionClassification".to_string(),
                "evidence".to_string(),
                "theoremReference".to_string(),
                "claimLevel".to_string(),
                "claimClassification".to_string(),
                "measurementBoundary".to_string(),
                "nonConclusions".to_string(),
                "repairCandidates".to_string(),
            ],
            compatibility_boundaries: vec![
                "witness evidence refs remain evidence refs, not formal proof claims".to_string(),
                "private / missing / unmeasured evidence is never rounded to measuredZero"
                    .to_string(),
                "measurementBoundary and claimClassification are versioned independently"
                    .to_string(),
            ],
            evidence_state_policy: vec![
                "private evidence remains unmeasured unless an explicit public artifact ref is present"
                    .to_string(),
                "missing evidence is reported as missing, not zero".to_string(),
                "unmeasured evidence does not discharge theorem preconditions".to_string(),
            ],
        },
        non_conclusions: vec![
            "obstruction witness schema compatibility is not semantic preservation".to_string(),
            "obstruction witness schema compatibility does not imply extractor completeness"
                .to_string(),
            "obstruction witness schema compatibility does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

pub fn static_architecture_drift_ledger() -> ArchitectureDriftLedgerV0 {
    let entries = vec![
        ArchitectureDriftLedgerEntryV0 {
            ledger_entry_id: "ledger-entry-hidden-cache-active".to_string(),
            observed_at: "2026-05-05T00:00:00Z".to_string(),
            architecture_id: "checkout-service".to_string(),
            revision_ref: Some("main@fixture-b9-drift-current".to_string()),
            subject_ref: "component:CouponService->PaymentAdapter".to_string(),
            witness_fingerprint: Some(
                "hidden-cache-access:CouponService:PaymentAdapter".to_string(),
            ),
            policy_ref: Some("boundary-policy-v0".to_string()),
            aggregation_window: DriftLedgerAggregationWindowV0 {
                window_start: Some("2026-05-04T00:00:00Z".to_string()),
                window_end: Some("2026-05-05T00:00:00Z".to_string()),
                window_kind: "daily".to_string(),
            },
            source: DriftLedgerSourceV0 {
                kind: "daily_batch".to_string(),
                reference: Some("batch:archsig-daily:2026-05-05".to_string()),
            },
            metric_id: "same_boundary_violation_reopened_count".to_string(),
            layer: "static".to_string(),
            measured_value: Some(json!(1)),
            measurement_boundary: "measuredNonzero".to_string(),
            evidence_refs: vec![
                "feature-report:pr-575".to_string(),
                "retention:fixture-b7-report-artifact-retention".to_string(),
            ],
            confidence: "high".to_string(),
            introduced_by_pr: Some("575".to_string()),
            first_seen_at: Some("2026-05-04T10:00:00Z".to_string()),
            last_seen_at: Some("2026-05-05T00:00:00Z".to_string()),
            owner: Some("checkout-platform".to_string()),
            status: "suppressed".to_string(),
            suppression: Some(DriftLedgerSuppressionV0 {
                reason: Some("temporary review suppression for migration window".to_string()),
                approved_by: Some("architecture-reviewer".to_string()),
                approved_at: Some("2026-05-04T11:00:00Z".to_string()),
                expires_at: Some("2026-05-11T00:00:00Z".to_string()),
                scope: Some("pr-575 hidden interaction witness".to_string()),
                policy_ref: Some("boundary-policy-v0".to_string()),
                witness_ref: Some("witness-hidden-cache-access".to_string()),
            }),
            repair_candidates: vec!["repair-coupon-boundary".to_string()],
            linked_witness_refs: vec!["witness-hidden-cache-access".to_string()],
            linked_claim_refs: vec!["claim-static-boundary".to_string()],
            non_conclusions: vec![
                "suppression metadata is not repair success".to_string(),
                "ledger status is operational state, not formal proof state".to_string(),
            ],
        },
        ArchitectureDriftLedgerEntryV0 {
            ledger_entry_id: "ledger-entry-private-runtime-unmeasured".to_string(),
            observed_at: "2026-05-05T00:00:00Z".to_string(),
            architecture_id: "checkout-service".to_string(),
            revision_ref: Some("main@fixture-b9-drift-current".to_string()),
            subject_ref: "runtime:PaymentAdapter".to_string(),
            witness_fingerprint: Some("private-runtime-log:PaymentAdapter".to_string()),
            policy_ref: Some("runtime-evidence-policy-v0".to_string()),
            aggregation_window: DriftLedgerAggregationWindowV0 {
                window_start: Some("2026-05-04T00:00:00Z".to_string()),
                window_end: Some("2026-05-05T00:00:00Z".to_string()),
                window_kind: "daily".to_string(),
            },
            source: DriftLedgerSourceV0 {
                kind: "scheduled_scan".to_string(),
                reference: Some("scan:runtime-private-fixture".to_string()),
            },
            metric_id: "private_runtime_evidence_count".to_string(),
            layer: "runtime".to_string(),
            measured_value: None,
            measurement_boundary: "unmeasured".to_string(),
            evidence_refs: vec!["missing-private-artifact:runtime-log".to_string()],
            confidence: "medium".to_string(),
            introduced_by_pr: None,
            first_seen_at: Some("2026-05-05T00:00:00Z".to_string()),
            last_seen_at: Some("2026-05-05T00:00:00Z".to_string()),
            owner: None,
            status: "unmeasured".to_string(),
            suppression: None,
            repair_candidates: Vec::new(),
            linked_witness_refs: vec!["witness-hidden-cache-access".to_string()],
            linked_claim_refs: Vec::new(),
            non_conclusions: vec![
                "private / missing runtime evidence is not measured-zero evidence".to_string(),
                "unmeasured runtime evidence does not conclude runtime risk zero".to_string(),
            ],
        },
    ];

    ArchitectureDriftLedgerV0 {
        schema_version: ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION.to_string(),
        schema_compatibility: Some(architecture_drift_ledger_schema_compatibility_metadata(
            &entries,
        )),
        ledger_id: "fixture-b9-architecture-drift-ledger".to_string(),
        generated_at: "2026-05-05T00:00:00Z".to_string(),
        baseline_ref: Some("baseline:pr-575".to_string()),
        retention_manifest_ref: Some(
            "report-artifacts:fixture-b7-report-artifact-retention".to_string(),
        ),
        suppression_workflow_refs: vec!["suppression-workflow:pr-575".to_string()],
        entries,
        non_conclusions: vec![
            "architecture drift ledger is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "ledger compatibility does not prove semantic preservation".to_string(),
            "ledger compatibility does not imply extractor completeness".to_string(),
        ],
    }
}

pub fn obstruction_witness_schema_compatibility_metadata(
    witness: &FeatureReportObstructionWitness,
) -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "obstruction-witness".to_string(),
        schema_version_name: OBSTRUCTION_WITNESS_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "witnessId",
                "witnessId",
                "stable",
                "preserve stable witness identity",
            ),
            field_mapping("layer", "layer", "stable", "preserve architecture layer"),
            field_mapping("kind", "kind", "stable", "preserve witness kind"),
            field_mapping(
                "evidence",
                "evidence",
                "stable",
                "preserve evidence refs and state",
            ),
            field_mapping(
                "claimClassification",
                "claimClassification",
                "stable",
                "do not promote tooling claims",
            ),
            field_mapping(
                "measurementBoundary",
                "measurementBoundary",
                "stable",
                "preserve measuredZero / measuredNonzero / unmeasured / outOfScope distinction",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve witness guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: required_assumptions(
            BTreeSet::from([
                "witness evidence refs are traceable".to_string(),
                "private and missing witness evidence remains unmeasured".to_string(),
                "claim classification is reviewed separately from schema migration".to_string(),
            ]),
            "obstruction-witness",
        ),
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: format!("witness.{}.evidence", witness.layer),
                measurement_boundary: witness.measurement_boundary.clone(),
                coverage_assumptions: witness
                    .evidence
                    .iter()
                    .map(|evidence| evidence.evidence_ref.clone())
                    .collect(),
                exactness_assumptions: vec![
                    "evidence refs are reviewed as tooling evidence".to_string(),
                    "theorem refs do not discharge missing preconditions by migration".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "witness.evidence.private-or-missing".to_string(),
                measurement_boundary: "unmeasured".to_string(),
                coverage_assumptions: vec![
                    "private evidence ref remains private".to_string(),
                    "missing artifact ref remains missing".to_string(),
                ],
                exactness_assumptions: vec![
                    "private / missing / unmeasured evidence is not rounded to measuredZero"
                        .to_string(),
                ],
            },
        ],
        non_conclusions: common_non_conclusions("obstruction witness"),
    }
}

pub fn architecture_drift_ledger_schema_compatibility_metadata(
    entries: &[ArchitectureDriftLedgerEntryV0],
) -> SchemaArtifactCompatibilityV0 {
    let mut boundaries = vec![
        SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: "ledger.retention.baseline.suppression".to_string(),
            measurement_boundary: "operationalMetadata".to_string(),
            coverage_assumptions: vec![
                "retentionManifestRef is present when retained reports are referenced".to_string(),
                "baselineRef is present when baseline deltas are reported".to_string(),
                "suppressionWorkflowRefs are present when suppressed status is reported"
                    .to_string(),
            ],
            exactness_assumptions: vec![
                "retention / baseline / suppression metadata is versioned with the ledger schema"
                    .to_string(),
            ],
        },
        SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: "ledger.private-or-missing-evidence".to_string(),
            measurement_boundary: "unmeasured".to_string(),
            coverage_assumptions: vec![
                "private retained artifact remains private".to_string(),
                "missing evidence ref remains missing".to_string(),
            ],
            exactness_assumptions: vec![
                "private / missing / unmeasured evidence is not rounded to measuredZero"
                    .to_string(),
            ],
        },
    ];

    boundaries.extend(
        entries
            .iter()
            .map(|entry| SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: format!("ledger.metric.{}", entry.metric_id),
                measurement_boundary: entry.measurement_boundary.clone(),
                coverage_assumptions: entry.evidence_refs.clone(),
                exactness_assumptions: vec![
                    "ledger metric status is operational state, not formal proof state".to_string(),
                ],
            }),
    );

    SchemaArtifactCompatibilityV0 {
        artifact_id: "architecture-drift-ledger".to_string(),
        schema_version_name: ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "entries[].subjectRef",
                "entries[].subjectRef",
                "stable",
                "preserve stable grouping key",
            ),
            field_mapping(
                "entries[].witnessFingerprint",
                "entries[].witnessFingerprint",
                "stable",
                "preserve repeated violation grouping key",
            ),
            field_mapping(
                "entries[].aggregationWindow",
                "entries[].aggregationWindow",
                "stable",
                "preserve metric aggregation boundary",
            ),
            field_mapping(
                "entries[].measurementBoundary",
                "entries[].measurementBoundary",
                "stable",
                "preserve measured / unmeasured / out-of-scope state",
            ),
            field_mapping(
                "entries[].suppression",
                "entries[].suppression",
                "stable",
                "preserve suppression audit metadata",
            ),
            field_mapping(
                "retentionManifestRef",
                "retentionManifestRef",
                "stable",
                "preserve retained artifact traceability",
            ),
            field_mapping(
                "baselineRef",
                "baselineRef",
                "stable",
                "preserve baseline comparison link",
            ),
            field_mapping(
                "suppressionWorkflowRefs",
                "suppressionWorkflowRefs",
                "stable",
                "preserve suppression workflow links",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve ledger guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: required_assumptions(
            BTreeSet::from([
                "stable grouping keys are preserved".to_string(),
                "retention metadata is present for retained artifact refs".to_string(),
                "suppression metadata is preserved for suppressed or accepted-risk entries"
                    .to_string(),
                "private and missing ledger evidence remains unmeasured".to_string(),
            ]),
            "architecture-drift-ledger",
        ),
        coverage_exactness_boundaries: boundaries,
        non_conclusions: common_non_conclusions("architecture drift ledger"),
    }
}

fn required_assumptions(
    assumptions: BTreeSet<String>,
    applies_to: &str,
) -> Vec<SchemaRequiredAssumptionV0> {
    assumptions
        .into_iter()
        .map(|assumption| SchemaRequiredAssumptionV0 {
            assumption_id: stable_id_fragment(&assumption),
            applies_to: applies_to.to_string(),
            required_for: "schema compatibility review".to_string(),
            fallback_when_missing: "report as missing or undischarged; do not infer a formal claim"
                .to_string(),
        })
        .collect()
}

fn field_mapping(
    source_field: &str,
    target_field: &str,
    mapping_kind: &str,
    required_review: &str,
) -> SchemaFieldMappingV0 {
    SchemaFieldMappingV0 {
        source_field: source_field.to_string(),
        target_field: target_field.to_string(),
        mapping_kind: mapping_kind.to_string(),
        required_review: required_review.to_string(),
    }
}

fn common_non_conclusions(artifact: &str) -> Vec<String> {
    vec![
        format!("{artifact} schema compatibility metadata does not prove semantic preservation"),
        format!("{artifact} schema compatibility metadata does not imply extractor completeness"),
        "compatibility pass does not promote tooling evidence to a Lean theorem claim".to_string(),
        "private / missing / unmeasured evidence is not measured-zero evidence".to_string(),
    ]
}

fn stable_id_fragment(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() {
                ch.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect::<String>()
        .split('-')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("-")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_obstruction_witness_fixture_matches_builder() {
        let fixture: ObstructionWitnessArtifactV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/obstruction_witness.json"
        ))
        .expect("obstruction witness fixture parses");
        assert_eq!(fixture, static_obstruction_witness_artifact());
    }

    #[test]
    fn static_drift_ledger_fixture_matches_builder() {
        let fixture: ArchitectureDriftLedgerV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/architecture_drift_ledger.json"
        ))
        .expect("architecture drift ledger fixture parses");
        assert_eq!(fixture, static_architecture_drift_ledger());
    }
}
