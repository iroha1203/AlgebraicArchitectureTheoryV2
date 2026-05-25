use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    MEASUREMENT_UNIT_REGISTRY_SCHEMA_VERSION,
    MEASUREMENT_UNIT_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION,
    MeasurementEvidenceAdapterBoundaryV0, MeasurementEvidenceSourceV0, MeasurementUnitRegistryV0,
    MeasurementUnitRegistryValidationInput, MeasurementUnitRegistryValidationReportV0,
    MeasurementUnitRegistryValidationSummary, MeasurementUnitV0, PYTHON_COMPONENT_KIND,
    ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "measurement unit registry is tooling validation, not a Lean theorem",
    "selected measurement units do not conclude global architecture completeness",
    "selected measurement units do not conclude Lean ComponentUniverse completeness",
    "runtime or semantic adapter coverage gaps are not measured-zero evidence",
    "private or missing evidence sources remain unmeasured unless explicitly supplied",
];

const SUPPORTED_UNIT_KINDS: [&str; 3] = ["repository-root", "service-root", "deployment-unit"];
const SUPPORTED_SOURCE_KINDS: [&str; 6] = [
    "runtime-trace",
    "service-mesh",
    "log",
    "semantic-workflow",
    "contract-test",
    "manual-diagram",
];
const SUPPORTED_ADAPTER_KINDS: [&str; 2] =
    ["runtime-evidence-adapter", "semantic-evidence-adapter"];
const SUPPORTED_LAYERS: [&str; 2] = ["runtime", "semantic"];
const SUPPORTED_EVIDENCE_KINDS: [&str; 5] = [
    "runtime_trace",
    "observation_result",
    "semantic_diagram",
    "test",
    "manual_annotation",
];

pub fn static_measurement_unit_registry() -> MeasurementUnitRegistryV0 {
    MeasurementUnitRegistryV0 {
        schema_version: MEASUREMENT_UNIT_REGISTRY_SCHEMA_VERSION.to_string(),
        registry_id: "aat-b8-measurement-unit-registry".to_string(),
        scope: "B8 monorepo and multi-service measurement unit boundaries".to_string(),
        units: vec![
            measurement_unit(
                "repo-root-aat-fixture",
                "repository-root",
                ".",
                None,
                None,
                &["Formal", "tools.archsig"],
                vec![evidence_source(
                    "repo-runtime-trace-sample",
                    "runtime-trace",
                    "repo-root-aat-fixture",
                    "artifacts/runtime/repo-runtime-trace.json",
                    "sampled internal telemetry",
                    &[
                        "trace covers only the selected repository revision",
                        "missing services are retained as unmeasured runtime evidence",
                    ],
                    &["private-telemetry", "unsampled-background-jobs"],
                )],
                vec![evidence_source(
                    "repo-semantic-workflow-sample",
                    "semantic-workflow",
                    "repo-root-aat-fixture",
                    "docs/workflows/order-flow.md",
                    "manual workflow annotation",
                    &[
                        "workflow evidence covers only the documented fixture path",
                        "undocumented workflows are unsupported semantic coverage",
                    ],
                    &["implicit-human-process", "undocumented-workflow-branch"],
                )],
                &[
                    "repository root is the checkout and artifact path base",
                    "service roots and deployment units are selected separately",
                ],
                &["implicit-service-boundary", "private-runtime-telemetry"],
                &["aat-air-v0", "feature-extension-report-v0"],
            ),
            measurement_unit(
                "billing-service-fixture",
                "service-root",
                ".",
                Some("services/billing"),
                None,
                &["billing.api", "billing.worker"],
                vec![evidence_source(
                    "billing-service-mesh-trace",
                    "service-mesh",
                    "billing-service-fixture",
                    "artifacts/runtime/billing-service-mesh.json",
                    "service mesh sample",
                    &[
                        "service mesh edges cover only the billing namespace",
                        "cross-namespace traffic is retained as unsupported unless selected",
                    ],
                    &["mesh-sampling-window", "private-cross-namespace-traffic"],
                )],
                Vec::new(),
                &[
                    "service root identifies source ownership, not deployment topology",
                    "selected components are bounded by the service fixture",
                ],
                &["shared-library-runtime-calls", "external-managed-service"],
                &["aat-air-v0", "feature-extension-report-v0"],
            ),
            measurement_unit(
                "billing-worker-deployment-fixture",
                "deployment-unit",
                ".",
                Some("services/billing"),
                Some("deployments/billing-worker"),
                &["billing.worker"],
                vec![evidence_source(
                    "billing-worker-log-sample",
                    "log",
                    "billing-worker-deployment-fixture",
                    "artifacts/runtime/billing-worker.log.json",
                    "redacted production log",
                    &[
                        "log evidence covers the selected deployment unit and retention window",
                        "redacted fields remain unmeasured",
                    ],
                    &["redacted-log-field", "missing-retention-window"],
                )],
                Vec::new(),
                &[
                    "deployment unit identifies runtime packaging, not full service behavior",
                    "runtime evidence is bounded by the selected deployment unit",
                ],
                &["sidecar-runtime-edge", "ephemeral-job"],
                &["aat-air-v0", "feature-extension-report-v0"],
            ),
        ],
        evidence_adapters: vec![
            evidence_adapter(
                "runtime-edge-measurement-unit-adapter-v0",
                "runtime-evidence-adapter",
                &[
                    "repo-root-aat-fixture",
                    "billing-service-fixture",
                    "billing-worker-deployment-fixture",
                ],
                &["runtime"],
                &["runtime_trace", "observation_result"],
                "runtime-edge-projection-v0",
                &[
                    "runtime evidence sources are attached to explicit measurementUnitRefs",
                    "repository root, service root, and deployment unit are not collapsed",
                ],
                &[
                    "runtime edge source and target ids resolve inside the selected AIR component universe",
                    "runtime traces preserve observed directed dependency edges only",
                ],
                &["private-telemetry", "sampling-gap", "unresolved-service-identity"],
            ),
            evidence_adapter(
                "semantic-workflow-measurement-unit-adapter-v0",
                "semantic-evidence-adapter",
                &["repo-root-aat-fixture"],
                &["semantic"],
                &["semantic_diagram", "test", "manual_annotation"],
                "semantic-workflow-projection-v0",
                &[
                    "semantic workflow sources are selected explicitly per measurement unit",
                    "manual workflow evidence is bounded by referenced paths",
                ],
                &[
                    "workflow nodes are projected only when they resolve to selected component refs",
                    "diagram evidence preserves documented path order but not global semantic completeness",
                ],
                &["unmapped-workflow-node", "implicit-business-rule", "private-contract-test"],
            ),
        ],
        explicit_assumptions: vec![
            "measurement units are selected before runtime or semantic evidence is interpreted"
                .to_string(),
            "repository root, service root, and deployment unit boundaries are recorded separately"
                .to_string(),
            "runtime and semantic evidence adapters trace coverage gaps to AIR and Feature Extension Report metadata"
                .to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_measurement_unit_registry_report(
    registry: &MeasurementUnitRegistryV0,
    input_path: &str,
) -> MeasurementUnitRegistryValidationReportV0 {
    let checks = vec![
        check_schema_version(registry),
        check_registry_identity(registry),
        check_unit_ids(registry),
        check_unit_boundaries(registry),
        check_evidence_sources(registry),
        check_adapter_boundaries(registry),
        check_non_conclusion_boundary(registry),
    ];
    let summary = MeasurementUnitRegistryValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        unit_count: registry.units.len(),
        evidence_adapter_count: registry.evidence_adapters.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    MeasurementUnitRegistryValidationReportV0 {
        schema_version: MEASUREMENT_UNIT_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: MeasurementUnitRegistryValidationInput {
            schema_version: registry.schema_version.clone(),
            path: input_path.to_string(),
            registry_id: registry.registry_id.clone(),
            scope: registry.scope.clone(),
        },
        registry: registry.clone(),
        summary,
        checks,
    }
}

#[allow(clippy::too_many_arguments)]
fn measurement_unit(
    unit_id: &str,
    unit_kind: &str,
    repository_root: &str,
    service_root: Option<&str>,
    deployment_unit: Option<&str>,
    selected_component_refs: &[&str],
    runtime_evidence_sources: Vec<MeasurementEvidenceSourceV0>,
    semantic_workflow_sources: Vec<MeasurementEvidenceSourceV0>,
    coverage_assumptions: &[&str],
    unsupported_constructs: &[&str],
    output_artifacts: &[&str],
) -> MeasurementUnitV0 {
    MeasurementUnitV0 {
        unit_id: unit_id.to_string(),
        unit_kind: unit_kind.to_string(),
        repository_root: repository_root.to_string(),
        service_root: service_root.map(str::to_string),
        deployment_unit: deployment_unit.map(str::to_string),
        component_id_kind: PYTHON_COMPONENT_KIND.to_string(),
        selected_component_refs: strings(selected_component_refs),
        runtime_evidence_sources,
        semantic_workflow_sources,
        coverage_assumptions: strings(coverage_assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        output_artifacts: strings(output_artifacts),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn evidence_source(
    source_id: &str,
    source_kind: &str,
    owner_unit_ref: &str,
    path: &str,
    privacy_boundary: &str,
    coverage_assumptions: &[&str],
    unsupported_constructs: &[&str],
) -> MeasurementEvidenceSourceV0 {
    MeasurementEvidenceSourceV0 {
        source_id: source_id.to_string(),
        source_kind: source_kind.to_string(),
        owner_unit_ref: owner_unit_ref.to_string(),
        path: path.to_string(),
        privacy_boundary: privacy_boundary.to_string(),
        coverage_assumptions: strings(coverage_assumptions),
        unsupported_constructs: strings(unsupported_constructs),
    }
}

#[allow(clippy::too_many_arguments)]
fn evidence_adapter(
    adapter_id: &str,
    adapter_kind: &str,
    measurement_unit_refs: &[&str],
    measured_layers: &[&str],
    evidence_kinds: &[&str],
    projection_rule: &str,
    coverage_assumptions: &[&str],
    exactness_assumptions: &[&str],
    unsupported_constructs: &[&str],
) -> MeasurementEvidenceAdapterBoundaryV0 {
    MeasurementEvidenceAdapterBoundaryV0 {
        adapter_id: adapter_id.to_string(),
        adapter_kind: adapter_kind.to_string(),
        measurement_unit_refs: strings(measurement_unit_refs),
        measured_layers: strings(measured_layers),
        evidence_kinds: strings(evidence_kinds),
        projection_rule: projection_rule.to_string(),
        coverage_assumptions: strings(coverage_assumptions),
        exactness_assumptions: strings(exactness_assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        output_artifacts: vec![
            "aat-air-v0".to_string(),
            "feature-extension-report-v0".to_string(),
        ],
        theorem_bridge_preconditions: vec![
            "explicit Lean ComponentUniverse bridge precondition".to_string(),
            "AIR coverage layer matches the selected measurement unit refs".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn check_schema_version(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let mut check = validation_check(
        "measurement-unit-registry-schema-version-supported",
        "measurement unit registry schema version is supported",
        if registry.schema_version == MEASUREMENT_UNIT_REGISTRY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported measurement unit registry schemaVersion: {}",
            registry.schema_version
        ));
    }
    check
}

fn check_registry_identity(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if registry.registry_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "registryId",
            &registry.scope,
            "registry_id must be non-empty",
        ));
    }
    if registry.scope.trim().is_empty() {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "scope",
            "scope must be non-empty",
        ));
    }
    if registry.explicit_assumptions.is_empty() || has_blank(&registry.explicit_assumptions) {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "explicitAssumptions",
            "registry must record explicit assumptions",
        ));
    }
    check_examples(
        "measurement-unit-registry-identity-recorded",
        "registry id, scope, and explicit assumptions are recorded",
        invalid,
    )
}

fn check_unit_ids(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let duplicate_unit_ids = duplicates(registry.units.iter().map(|unit| unit.unit_id.as_str()));
    let mut invalid: Vec<_> = registry
        .units
        .iter()
        .filter(|unit| unit.unit_id.trim().is_empty())
        .map(|unit| {
            generic_validation_example(&unit.unit_id, &unit.unit_kind, "unit_id must be non-empty")
        })
        .chain(
            duplicate_unit_ids
                .into_iter()
                .map(|id| generic_validation_example(&id, &id, "duplicate unit_id")),
        )
        .collect();
    if registry.units.is_empty() {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "units",
            "registry must contain at least one measurement unit",
        ));
    }
    check_examples(
        "measurement-unit-ids-valid",
        "measurement unit ids are non-empty and unique",
        invalid,
    )
}

fn check_unit_boundaries(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let unit_kinds = string_set(SUPPORTED_UNIT_KINDS);
    let mut invalid = Vec::new();
    for unit in &registry.units {
        if !unit_kinds.contains(unit.unit_kind.as_str()) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                &unit.unit_kind,
                "unsupported unit_kind",
            ));
        }
        if unit.repository_root.trim().is_empty() {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "repositoryRoot",
                "repository root must be explicit",
            ));
        }
        if unit.unit_kind == "service-root" && is_blank_option(&unit.service_root) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "serviceRoot",
                "service-root measurement unit must record serviceRoot",
            ));
        }
        if unit.unit_kind == "deployment-unit"
            && (is_blank_option(&unit.service_root) || is_blank_option(&unit.deployment_unit))
        {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "deploymentUnit",
                "deployment-unit measurement unit must record serviceRoot and deploymentUnit",
            ));
        }
        if unit.component_id_kind.trim().is_empty() {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "componentIdKind",
                "component id kind must be explicit",
            ));
        }
        if unit.selected_component_refs.is_empty() || has_blank(&unit.selected_component_refs) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "selectedComponentRefs",
                "selected component refs must be explicit",
            ));
        }
        if unit.coverage_assumptions.is_empty() || has_blank(&unit.coverage_assumptions) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "coverageAssumptions",
                "coverage assumptions must be explicit",
            ));
        }
        if unit.unsupported_constructs.is_empty() || has_blank(&unit.unsupported_constructs) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "unsupportedConstructs",
                "unsupported constructs must be traceable",
            ));
        }
        if unit.output_artifacts.is_empty() || has_blank(&unit.output_artifacts) {
            invalid.push(generic_validation_example(
                &unit.unit_id,
                "outputArtifacts",
                "output artifacts must be explicit",
            ));
        }
    }
    check_examples(
        "measurement-unit-boundaries-recorded",
        "repository root, service root, deployment unit, coverage, and unsupported boundaries are recorded",
        invalid,
    )
}

fn check_evidence_sources(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let unit_ids: BTreeSet<&str> = registry
        .units
        .iter()
        .map(|unit| unit.unit_id.as_str())
        .collect();
    let source_kinds = string_set(SUPPORTED_SOURCE_KINDS);
    let mut source_ids = Vec::new();
    let mut invalid = Vec::new();

    for unit in &registry.units {
        for source in unit
            .runtime_evidence_sources
            .iter()
            .chain(unit.semantic_workflow_sources.iter())
        {
            source_ids.push(source.source_id.as_str());
            validate_evidence_source(source, &unit_ids, &source_kinds, &mut invalid);
        }
    }

    for id in duplicates(source_ids.into_iter()) {
        invalid.push(generic_validation_example(&id, &id, "duplicate source_id"));
    }
    check_examples(
        "measurement-unit-evidence-sources-recorded",
        "runtime evidence sources and semantic workflow sources are explicit and owned by selected units",
        invalid,
    )
}

fn validate_evidence_source(
    source: &MeasurementEvidenceSourceV0,
    unit_ids: &BTreeSet<&str>,
    source_kinds: &BTreeSet<&str>,
    invalid: &mut Vec<crate::ValidationExample>,
) {
    if source.source_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "sourceId",
            &source.owner_unit_ref,
            "source_id must be non-empty",
        ));
    }
    if !source_kinds.contains(source.source_kind.as_str()) {
        invalid.push(generic_validation_example(
            &source.source_id,
            &source.source_kind,
            "unsupported source_kind",
        ));
    }
    if !unit_ids.contains(source.owner_unit_ref.as_str()) {
        invalid.push(generic_validation_example(
            &source.source_id,
            &source.owner_unit_ref,
            "owner_unit_ref must resolve to a measurement unit",
        ));
    }
    if source.path.trim().is_empty() {
        invalid.push(generic_validation_example(
            &source.source_id,
            "path",
            "source path must be explicit",
        ));
    }
    if source.privacy_boundary.trim().is_empty() {
        invalid.push(generic_validation_example(
            &source.source_id,
            "privacyBoundary",
            "privacy boundary must be explicit",
        ));
    }
    if source.coverage_assumptions.is_empty() || has_blank(&source.coverage_assumptions) {
        invalid.push(generic_validation_example(
            &source.source_id,
            "coverageAssumptions",
            "source coverage assumptions must be explicit",
        ));
    }
    if source.unsupported_constructs.is_empty() || has_blank(&source.unsupported_constructs) {
        invalid.push(generic_validation_example(
            &source.source_id,
            "unsupportedConstructs",
            "source unsupported constructs must be traceable",
        ));
    }
}

fn check_adapter_boundaries(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let unit_ids: BTreeSet<&str> = registry
        .units
        .iter()
        .map(|unit| unit.unit_id.as_str())
        .collect();
    let duplicate_adapter_ids = duplicates(
        registry
            .evidence_adapters
            .iter()
            .map(|adapter| adapter.adapter_id.as_str()),
    );
    let adapter_kinds = string_set(SUPPORTED_ADAPTER_KINDS);
    let layers = string_set(SUPPORTED_LAYERS);
    let evidence_kinds = string_set(SUPPORTED_EVIDENCE_KINDS);
    let mut invalid: Vec<_> = duplicate_adapter_ids
        .into_iter()
        .map(|id| generic_validation_example(&id, &id, "duplicate adapter_id"))
        .collect();

    if registry.evidence_adapters.is_empty() {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "evidenceAdapters",
            "registry must contain runtime or semantic evidence adapter boundaries",
        ));
    }

    for adapter in &registry.evidence_adapters {
        validate_adapter_boundary(
            adapter,
            &unit_ids,
            &adapter_kinds,
            &layers,
            &evidence_kinds,
            &mut invalid,
        );
    }

    check_examples(
        "measurement-unit-evidence-adapter-boundaries-recorded",
        "runtime and semantic evidence adapters resolve measurement units and record coverage, exactness, unsupported, and output boundaries",
        invalid,
    )
}

fn validate_adapter_boundary(
    adapter: &MeasurementEvidenceAdapterBoundaryV0,
    unit_ids: &BTreeSet<&str>,
    adapter_kinds: &BTreeSet<&str>,
    layers: &BTreeSet<&str>,
    evidence_kinds: &BTreeSet<&str>,
    invalid: &mut Vec<crate::ValidationExample>,
) {
    if adapter.adapter_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "adapterId",
            &adapter.adapter_kind,
            "adapter_id must be non-empty",
        ));
    }
    if !adapter_kinds.contains(adapter.adapter_kind.as_str()) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            &adapter.adapter_kind,
            "unsupported adapter_kind",
        ));
    }
    if adapter.measurement_unit_refs.is_empty() || has_blank(&adapter.measurement_unit_refs) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "measurementUnitRefs",
            "adapter must reference selected measurement units",
        ));
    }
    for unit_ref in &adapter.measurement_unit_refs {
        if !unit_ids.contains(unit_ref.as_str()) {
            invalid.push(generic_validation_example(
                &adapter.adapter_id,
                unit_ref,
                "measurement_unit_ref must resolve",
            ));
        }
    }
    if adapter.measured_layers.is_empty() || has_blank(&adapter.measured_layers) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "measuredLayers",
            "adapter measured layers must be explicit",
        ));
    }
    for layer in &adapter.measured_layers {
        if !layers.contains(layer.as_str()) {
            invalid.push(generic_validation_example(
                &adapter.adapter_id,
                layer,
                "unsupported measured_layer",
            ));
        }
    }
    for evidence_kind in &adapter.evidence_kinds {
        if !evidence_kinds.contains(evidence_kind.as_str()) {
            invalid.push(generic_validation_example(
                &adapter.adapter_id,
                evidence_kind,
                "unsupported evidence_kind",
            ));
        }
    }
    if adapter.evidence_kinds.is_empty() || has_blank(&adapter.evidence_kinds) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "evidenceKinds",
            "adapter evidence kinds must be explicit",
        ));
    }
    if adapter.projection_rule.trim().is_empty() {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "projectionRule",
            "projection rule must be explicit",
        ));
    }
    if adapter.coverage_assumptions.is_empty() || has_blank(&adapter.coverage_assumptions) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "coverageAssumptions",
            "adapter coverage assumptions must be explicit",
        ));
    }
    if adapter.exactness_assumptions.is_empty() || has_blank(&adapter.exactness_assumptions) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "exactnessAssumptions",
            "adapter exactness assumptions must be explicit",
        ));
    }
    if adapter.unsupported_constructs.is_empty() || has_blank(&adapter.unsupported_constructs) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "unsupportedConstructs",
            "adapter unsupported constructs must be traceable",
        ));
    }
    if adapter.output_artifacts.is_empty() || has_blank(&adapter.output_artifacts) {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "outputArtifacts",
            "adapter output artifacts must be explicit",
        ));
    }
    if adapter.theorem_bridge_preconditions.is_empty()
        || has_blank(&adapter.theorem_bridge_preconditions)
    {
        invalid.push(generic_validation_example(
            &adapter.adapter_id,
            "theoremBridgePreconditions",
            "theorem bridge preconditions must be explicit",
        ));
    }
}

fn check_non_conclusion_boundary(registry: &MeasurementUnitRegistryV0) -> ValidationCheck {
    let mut invalid = missing_required_non_conclusions(
        &registry.registry_id,
        &registry.non_conclusions,
        "registry non_conclusions must preserve measurement unit boundaries",
    );
    for unit in &registry.units {
        invalid.extend(missing_required_non_conclusions(
            &unit.unit_id,
            &unit.non_conclusions,
            "unit non_conclusions must preserve measurement unit boundaries",
        ));
    }
    for adapter in &registry.evidence_adapters {
        invalid.extend(missing_required_non_conclusions(
            &adapter.adapter_id,
            &adapter.non_conclusions,
            "adapter non_conclusions must preserve runtime and semantic evidence boundaries",
        ));
    }
    check_examples(
        "measurement-unit-non-conclusion-boundary-recorded",
        "measurement units are separated from global completeness, Lean ComponentUniverse, and measured-zero claims",
        invalid,
    )
}

fn missing_required_non_conclusions(
    source: &str,
    non_conclusions: &[String],
    evidence: &str,
) -> Vec<crate::ValidationExample> {
    REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !non_conclusions.iter().any(|value| value == **required))
        .map(|required| generic_validation_example(source, required, evidence))
        .collect()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn is_blank_option(value: &Option<String>) -> bool {
    value
        .as_ref()
        .map(|value| value.trim().is_empty())
        .unwrap_or(true)
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}

fn check_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    check.count = Some(examples.len());
    check.examples = examples;
    check
}
