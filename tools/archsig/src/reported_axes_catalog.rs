use crate::{
    BenchmarkSuiteFixtureV0, BenchmarkSuiteUpdateRuleV0,
    DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION, DetectableValuesReportedAxesCatalogV0,
    ReportedAxisCatalogEntryV0, SchemaArtifactCompatibilityV0, SchemaCoverageExactnessBoundaryV0,
    SchemaFieldMappingV0, SchemaRequiredAssumptionV0,
};

const COMPATIBILITY_POLICY_REF: &str = "b9-compatibility-policy-v0";

pub fn static_detectable_values_reported_axes_catalog() -> DetectableValuesReportedAxesCatalogV0 {
    let catalog_version = "archsig-reported-axes-catalog-v0";
    let benchmark_suite_version = "archsig-benchmark-suite-v0";
    let axes = vec![
        axis(
            "hasCycle",
            "static",
            "usize",
            vec!["Signature artifact", "AIR", "Feature Extension Report"],
            "measuredZero",
            vec!["static import graph edges are extracted inside the selected measurement unit"],
            vec!["StrictLayered.noCycle"],
            vec!["0 is measuredZero only when metricStatus.hasCycle is measured"],
        ),
        axis(
            "sccMaxSize",
            "static",
            "usize",
            vec!["Signature artifact", "AIR", "Feature Extension Report"],
            "measuredZero",
            vec!["static component graph is measured"],
            vec![],
            vec!["missing SCC evidence remains unmeasured rather than 0"],
        ),
        axis(
            "boundaryViolationCount",
            "policy",
            "usize",
            vec!["Signature artifact", "AIR", "Feature Extension Report"],
            "measuredZero",
            vec!["boundary policy file or policy selector is present"],
            vec![],
            vec!["absence of policy evidence is unmeasured, not policy compliance"],
        ),
        axis(
            "runtimePropagation",
            "runtime",
            "Option Nat",
            vec!["AIR", "Feature Extension Report"],
            "unmeasured",
            vec!["runtime edge evidence is supplied with runtime-edge-projection-v0"],
            vec![
                "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction",
            ],
            vec![
                "None is unmeasured, not measuredZero",
                "some 0 requires coverage, projection, exactness, and theorem preconditions before a formal claim",
            ],
        ),
        axis(
            "semanticDiagramFillability",
            "semantic",
            "observed | obstructed | unmeasured",
            vec!["AIR", "Feature Extension Report"],
            "unmeasured",
            vec!["selected diagram observation evidence and contract/test evidence are present"],
            vec![],
            vec!["unmeasured semantic evidence is not treated as commuting"],
        ),
    ];

    DetectableValuesReportedAxesCatalogV0 {
        schema_version: DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION.to_string(),
        catalog_id: "archsig-detectable-values-reported-axes-catalog".to_string(),
        catalog_version: catalog_version.to_string(),
        benchmark_suite_version: benchmark_suite_version.to_string(),
        frozen_fixtures: frozen_fixtures(),
        update_rules: update_rules(),
        schema_compatibility: Some(schema_compatibility_metadata(&axes)),
        axes,
        non_conclusions: vec![
            "reported axis catalog membership does not imply extractor completeness".to_string(),
            "benchmark fixture pass does not prove architecture lawfulness".to_string(),
            "measuredZero is distinct from unmeasured and outOfScope".to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

fn frozen_fixtures() -> Vec<BenchmarkSuiteFixtureV0> {
    vec![
        fixture(
            "air-static-split-success",
            "tools/archsig/tests/fixtures/air/good_extension.json",
            "AIR",
            vec!["static split classification", "runtime unmeasured boundary"],
            vec!["hasCycle:measuredZero", "runtimePropagation:unmeasured"],
        ),
        fixture(
            "air-runtime-measured-zero",
            "tools/archsig/tests/fixtures/air/runtime_measured_zero.json",
            "AIR",
            vec!["runtime measured zero boundary"],
            vec!["runtimePropagation:measuredZero"],
        ),
        fixture(
            "air-runtime-measured-nonzero",
            "tools/archsig/tests/fixtures/air/runtime_measured_nonzero.json",
            "AIR",
            vec!["runtime measured nonzero boundary"],
            vec!["runtimePropagation:measuredNonzero"],
        ),
        fixture(
            "air-runtime-unmeasured",
            "tools/archsig/tests/fixtures/air/runtime_unmeasured.json",
            "AIR",
            vec!["runtime unmeasured boundary"],
            vec!["runtimePropagation:unmeasured"],
        ),
        fixture(
            "air-semantic-unmeasured",
            "tools/archsig/tests/fixtures/air/semantic_unmeasured.json",
            "AIR",
            vec!["semantic unmeasured boundary"],
            vec!["semanticDiagramFillability:unmeasured"],
        ),
        fixture(
            "air-ai-metadata-missing-unmeasured",
            "tools/archsig/tests/fixtures/air/ai_metadata_missing_unmeasured.json",
            "AIR",
            vec!["generated-change metadata gap"],
            vec![
                "aiSessionTraceability:unmeasured",
                "boundaryViolationCount:unmeasured",
            ],
        ),
    ]
}

fn update_rules() -> Vec<BenchmarkSuiteUpdateRuleV0> {
    vec![
        update_rule(
            "axis-addition-requires-version-review",
            "axes[] addition",
            "add schemaCompatibility.requiredAssumptions and coverageExactnessBoundaries for the new axis",
            "archsig schema-compatibility must report requiresMigration for the added axis until reviewed",
            "new axis support does not imply extractor completeness",
        ),
        update_rule(
            "axis-rename-requires-explicit-field-mapping",
            "axes[].axisId rename",
            "declare the source and target axis id in schemaCompatibility.fieldMappings",
            "archsig schema-compatibility must surface renamed axis ids as requiresMigration",
            "renamed axes do not preserve semantics by name alone",
        ),
        update_rule(
            "axis-removal-requires-migration-note",
            "axes[] removal",
            "record the removed axis as deprecated or require a migration note",
            "archsig schema-compatibility must report requiresMigration when a boundary disappears",
            "removed axes are not silently outOfScope",
        ),
        update_rule(
            "measurement-boundary-change-requires-review",
            "axes[].allowedMeasurementBoundaries or defaultMeasurementBoundary change",
            "preserve measuredZero / measuredNonzero / unmeasured / outOfScope distinction",
            "archsig schema-compatibility must report requiresMigration for boundary changes",
            "unmeasured is never rounded to measuredZero by migration",
        ),
    ]
}

fn fixture(
    fixture_id: &str,
    path: &str,
    artifact_kind: &str,
    frozen_for: Vec<&str>,
    expected_boundaries: Vec<&str>,
) -> BenchmarkSuiteFixtureV0 {
    BenchmarkSuiteFixtureV0 {
        fixture_id: fixture_id.to_string(),
        path: path.to_string(),
        artifact_kind: artifact_kind.to_string(),
        frozen_for: frozen_for.into_iter().map(str::to_string).collect(),
        expected_boundaries: expected_boundaries
            .into_iter()
            .map(str::to_string)
            .collect(),
        update_rule_refs: vec![
            "axis-addition-requires-version-review".to_string(),
            "axis-rename-requires-explicit-field-mapping".to_string(),
            "axis-removal-requires-migration-note".to_string(),
            "measurement-boundary-change-requires-review".to_string(),
        ],
    }
}

fn update_rule(
    rule_id: &str,
    applies_to: &str,
    required_review: &str,
    compatibility_check: &str,
    non_conclusion: &str,
) -> BenchmarkSuiteUpdateRuleV0 {
    BenchmarkSuiteUpdateRuleV0 {
        rule_id: rule_id.to_string(),
        applies_to: applies_to.to_string(),
        required_review: required_review.to_string(),
        compatibility_check: compatibility_check.to_string(),
        non_conclusion: non_conclusion.to_string(),
    }
}

fn axis(
    axis_id: &str,
    layer: &str,
    value_type: &str,
    reported_in: Vec<&str>,
    default_measurement_boundary: &str,
    evidence_requirements: Vec<&str>,
    theorem_refs: Vec<&str>,
    compatibility_notes: Vec<&str>,
) -> ReportedAxisCatalogEntryV0 {
    ReportedAxisCatalogEntryV0 {
        axis_id: axis_id.to_string(),
        layer: layer.to_string(),
        value_type: value_type.to_string(),
        reported_in: reported_in.into_iter().map(str::to_string).collect(),
        allowed_measurement_boundaries: vec![
            "measuredZero".to_string(),
            "measuredNonzero".to_string(),
            "unmeasured".to_string(),
            "outOfScope".to_string(),
        ],
        default_measurement_boundary: default_measurement_boundary.to_string(),
        evidence_requirements: evidence_requirements
            .into_iter()
            .map(str::to_string)
            .collect(),
        theorem_refs: theorem_refs.into_iter().map(str::to_string).collect(),
        compatibility_notes: compatibility_notes
            .into_iter()
            .map(str::to_string)
            .collect(),
        non_conclusions: vec![
            "axis value compatibility does not prove semantic preservation".to_string(),
            "unmeasured axis evidence is not measured-zero evidence".to_string(),
            "reported axis evidence does not promote a Lean theorem claim".to_string(),
        ],
    }
}

fn schema_compatibility_metadata(
    axes: &[ReportedAxisCatalogEntryV0],
) -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "detectable-values-reported-axes-catalog".to_string(),
        schema_version_name: DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping("axes[].axisId", "axes[].axisId", "stable", "axis identity"),
            field_mapping(
                "axes[].allowedMeasurementBoundaries",
                "axes[].allowedMeasurementBoundaries",
                "stable",
                "preserve measuredZero / measuredNonzero / unmeasured / outOfScope distinction",
            ),
            field_mapping(
                "axes[].defaultMeasurementBoundary",
                "axes[].defaultMeasurementBoundary",
                "stable",
                "default boundary changes require migration review",
            ),
            field_mapping(
                "frozenFixtures[].expectedBoundaries",
                "frozenFixtures[].expectedBoundaries",
                "stable",
                "benchmark expected boundaries are part of compatibility review",
            ),
        ],
        deprecated_fields: vec![],
        required_assumptions: vec![
            required_assumption(
                "axis-addition-reviewed",
                "axes[]",
                "schema compatibility review",
                "report added axis as missing migration review; do not infer extractor completeness or a formal claim",
            ),
            required_assumption(
                "axis-rename-explicit-field-mapping",
                "axes[].axisId",
                "schema compatibility review",
                "report rename as missing migration review unless fieldMappings declare source and target; do not infer a formal claim",
            ),
            required_assumption(
                "measurement-boundary-distinction-preserved",
                "axes[].allowedMeasurementBoundaries",
                "schema compatibility review",
                "report changed boundary as missing migration review; do not infer a formal claim",
            ),
        ],
        coverage_exactness_boundaries: axes
            .iter()
            .map(|axis| SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: axis.axis_id.clone(),
                measurement_boundary: axis.default_measurement_boundary.clone(),
                coverage_assumptions: axis.evidence_requirements.clone(),
                exactness_assumptions: axis.compatibility_notes.clone(),
            })
            .collect(),
        non_conclusions: vec![
            "reported axes catalog compatibility metadata does not prove semantic preservation"
                .to_string(),
            "reported axes catalog compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "unmeasured axis evidence is not measured-zero evidence".to_string(),
        ],
    }
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

fn required_assumption(
    assumption_id: &str,
    applies_to: &str,
    required_for: &str,
    fallback_when_missing: &str,
) -> SchemaRequiredAssumptionV0 {
    SchemaRequiredAssumptionV0 {
        assumption_id: assumption_id.to_string(),
        applies_to: applies_to.to_string(),
        required_for: required_for.to_string(),
        fallback_when_missing: fallback_when_missing.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_reported_axes_catalog_freezes_benchmark_boundaries() {
        let catalog = static_detectable_values_reported_axes_catalog();
        assert_eq!(
            catalog.schema_version,
            DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION
        );
        assert!(catalog.frozen_fixtures.iter().any(|fixture| {
            fixture
                .expected_boundaries
                .contains(&"runtimePropagation:unmeasured".to_string())
        }));
        assert!(catalog.axes.iter().any(|axis| {
            axis.axis_id == "runtimePropagation"
                && axis.default_measurement_boundary == "unmeasured"
                && axis
                    .allowed_measurement_boundaries
                    .contains(&"measuredZero".to_string())
                && axis
                    .allowed_measurement_boundaries
                    .contains(&"unmeasured".to_string())
        }));
        assert!(
            catalog
                .schema_compatibility
                .as_ref()
                .expect("schema compatibility metadata exists")
                .coverage_exactness_boundaries
                .iter()
                .any(|boundary| boundary.axis_or_layer == "runtimePropagation"
                    && boundary.measurement_boundary == "unmeasured")
        );
    }

    #[test]
    fn canonical_fixture_matches_static_reported_axes_catalog() {
        let fixture: DetectableValuesReportedAxesCatalogV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/detectable_values_reported_axes_catalog.json"
        ))
        .expect("detectable values / reported axes catalog fixture parses");
        assert_eq!(fixture, static_detectable_values_reported_axes_catalog());
    }
}
