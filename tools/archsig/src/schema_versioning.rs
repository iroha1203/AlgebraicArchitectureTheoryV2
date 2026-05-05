use std::collections::BTreeSet;

use crate::{
    AIR_SCHEMA_VERSION, AirClaim, AirCoverage, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    FeatureReportCoverageGap, FeatureReportRuntimeSummary, FeatureReportSemanticPathSummary,
    SchemaArtifactCompatibilityV0, SchemaCoverageExactnessBoundaryV0, SchemaFieldMappingV0,
    SchemaRequiredAssumptionV0,
};

const COMPATIBILITY_POLICY_REF: &str = "b9-compatibility-policy-v0";

pub(crate) fn air_schema_compatibility_metadata(
    coverage: &AirCoverage,
    claims: &[AirClaim],
) -> SchemaArtifactCompatibilityV0 {
    let required_assumptions: BTreeSet<String> = claims
        .iter()
        .flat_map(|claim| {
            claim
                .required_assumptions
                .iter()
                .chain(claim.coverage_assumptions.iter())
                .chain(claim.exactness_assumptions.iter())
                .chain(claim.missing_preconditions.iter())
        })
        .cloned()
        .collect();
    let non_conclusions = claims
        .iter()
        .flat_map(|claim| claim.non_conclusions.iter().cloned())
        .chain(common_schema_non_conclusions())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    SchemaArtifactCompatibilityV0 {
        artifact_id: "air".to_string(),
        schema_version_name: AIR_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "coverage.layers[].extractionScope",
                "coverage.layers[].extractionScope",
                "stable",
                "preserve coverage source boundaries",
            ),
            field_mapping(
                "coverage.layers[].exactnessAssumptions",
                "coverage.layers[].exactnessAssumptions",
                "stable",
                "preserve exactness assumptions",
            ),
            field_mapping(
                "coverage.layers[].unsupportedConstructs",
                "coverage.layers[].unsupportedConstructs",
                "stable",
                "do not treat unsupported constructs as measured zero",
            ),
            field_mapping(
                "claims[].missingPreconditions",
                "claims[].missingPreconditions",
                "stable",
                "preserve theorem bridge preconditions",
            ),
            field_mapping(
                "claims[].nonConclusions",
                "claims[].nonConclusions",
                "stable",
                "preserve non-conclusion guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: required_schema_assumptions(required_assumptions, "air"),
        coverage_exactness_boundaries: coverage
            .layers
            .iter()
            .map(|layer| SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: layer.layer.clone(),
                measurement_boundary: layer.measurement_boundary.clone(),
                coverage_assumptions: layer
                    .extraction_scope
                    .iter()
                    .chain(layer.unsupported_constructs.iter())
                    .cloned()
                    .collect(),
                exactness_assumptions: layer.exactness_assumptions.clone(),
            })
            .collect(),
        non_conclusions,
    }
}

pub(crate) fn feature_report_schema_compatibility_metadata(
    coverage_gaps: &[FeatureReportCoverageGap],
    undischarged_assumptions: &[String],
    runtime_summary: &FeatureReportRuntimeSummary,
    semantic_path_summary: &FeatureReportSemanticPathSummary,
    report_non_conclusions: &[String],
) -> SchemaArtifactCompatibilityV0 {
    let required_assumptions = undischarged_assumptions.iter().cloned().collect();
    let non_conclusions = report_non_conclusions
        .iter()
        .cloned()
        .chain(runtime_summary.non_conclusions.iter().cloned())
        .chain(semantic_path_summary.non_conclusions.iter().cloned())
        .chain(common_schema_non_conclusions())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    let mut boundaries: Vec<SchemaCoverageExactnessBoundaryV0> = coverage_gaps
        .iter()
        .map(|gap| SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: gap.layer.clone(),
            measurement_boundary: gap.measurement_boundary.clone(),
            coverage_assumptions: gap
                .unmeasured_axes
                .iter()
                .chain(gap.unsupported_constructs.iter())
                .cloned()
                .collect(),
            exactness_assumptions: gap.non_conclusions.clone(),
        })
        .collect();
    boundaries.push(SchemaCoverageExactnessBoundaryV0 {
        axis_or_layer: "runtime".to_string(),
        measurement_boundary: runtime_summary.measurement_boundary.clone(),
        coverage_assumptions: runtime_summary.coverage_gaps.clone(),
        exactness_assumptions: runtime_summary.exactness_assumptions.clone(),
    });
    boundaries.push(SchemaCoverageExactnessBoundaryV0 {
        axis_or_layer: "semantic".to_string(),
        measurement_boundary: semantic_path_summary.measurement_boundary.clone(),
        coverage_assumptions: semantic_path_summary.coverage_gaps.clone(),
        exactness_assumptions: semantic_path_summary.exactness_assumptions.clone(),
    });

    SchemaArtifactCompatibilityV0 {
        artifact_id: "feature-extension-report".to_string(),
        schema_version_name: FEATURE_EXTENSION_REPORT_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "coverageGaps[].nonConclusions",
                "coverageGaps[].nonConclusions",
                "stable",
                "preserve coverage gap guardrails",
            ),
            field_mapping(
                "theoremPreconditionChecks[].missingPreconditions",
                "theoremPreconditionChecks[].missingPreconditions",
                "stable",
                "preserve theorem bridge preconditions",
            ),
            field_mapping(
                "unsupportedConstructs",
                "unsupportedConstructs",
                "stable",
                "do not treat unsupported constructs as discharged assumptions",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve report non-conclusions",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: required_schema_assumptions(
            required_assumptions,
            "feature-extension-report",
        ),
        coverage_exactness_boundaries: boundaries,
        non_conclusions,
    }
}

fn required_schema_assumptions(
    assumptions: BTreeSet<String>,
    applies_to: &str,
) -> Vec<SchemaRequiredAssumptionV0> {
    let assumptions = if assumptions.is_empty() {
        BTreeSet::from(["schema compatibility metadata remains explicit".to_string()])
    } else {
        assumptions
    };
    assumptions
        .into_iter()
        .map(|assumption| SchemaRequiredAssumptionV0 {
            assumption_id: stable_id_fragment(&assumption),
            applies_to: applies_to.to_string(),
            required_for: "schema compatibility review".to_string(),
            fallback_when_missing: "report as undischarged; do not infer a formal claim"
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

fn common_schema_non_conclusions() -> impl Iterator<Item = String> {
    [
        "schema compatibility metadata does not prove semantic preservation",
        "schema compatibility metadata does not imply extractor completeness",
        "compatibility pass does not promote tooling evidence to a Lean theorem claim",
        "coverage gaps and unsupported constructs are not measured-zero evidence",
    ]
    .into_iter()
    .map(str::to_string)
}

fn stable_id_fragment(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect()
}
