use std::collections::BTreeSet;

use crate::{
    AirClaim, AirCoverageLayer, AirDocumentV0, AirSemanticDiagram,
    THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION, TheoremPackageMetadataV0,
    TheoremPackageRegistryV0, TheoremPreconditionCheck, TheoremPreconditionCheckInput,
    TheoremPreconditionCheckReportV0, TheoremPreconditionCheckSummary,
};

const RUNTIME_PROPAGATION_SUBJECT_REF: &str = "signature.runtimePropagation";
const SEMANTIC_DIAGRAM_SUBJECT_PREFIX: &str = "semantic.diagram.";
const NO_SOLUTION_CERTIFICATE_SUBJECT_PREFIX: &str = "synthesis.noSolutionCertificate.";
const AI_HUMAN_REVIEW_REQUIRED_PRECONDITION: &str =
    "AI session human review is required before promoting formal claim";

pub fn static_theorem_package_registry() -> TheoremPackageRegistryV0 {
    TheoremPackageRegistryV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        scope: "static, runtime, semantic, and synthesis theorem package registry v0".to_string(),
        packages: vec![
            static_split_theorem_package(),
            runtime_zero_bridge_package(),
            semantic_diagram_filler_package(),
            semantic_nonfillability_package(),
            semantic_numerical_curvature_zero_package(),
            no_solution_certificate_package(),
        ],
    }
}

fn static_split_theorem_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "static-theorem-package-v0".to_string(),
        lean_entrypoint: "SelectedStaticSplitExtension".to_string(),
        theorem_refs: vec![
            "SelectedStaticSplitExtension".to_string(),
            "CoreEdgesPreserved".to_string(),
            "DeclaredInterfaceFactorization".to_string(),
            "NoNewForbiddenStaticEdge".to_string(),
            "EmbeddingPolicyPreserved".to_string(),
        ],
        supported_subject_refs: vec![
            "extension.embedding".to_string(),
            "extension.feature".to_string(),
            "extension.split".to_string(),
            "signature.hasCycle".to_string(),
            "signature.projectionSoundnessViolation".to_string(),
            "signature.lspViolationCount".to_string(),
            "signature.boundaryViolationCount".to_string(),
            "signature.abstractionViolationCount".to_string(),
        ],
        supported_axes: vec![
            "hasCycle".to_string(),
            "projectionSoundnessViolation".to_string(),
            "lspViolationCount".to_string(),
            "boundaryViolationCount".to_string(),
            "abstractionViolationCount".to_string(),
        ],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "measuredZero".to_string(),
        required_assumptions: vec![
            "core edges are preserved".to_string(),
            "feature/core interactions factor through a declared interface".to_string(),
            "no new forbidden static edge is introduced".to_string(),
            "embedding policy is preserved".to_string(),
        ],
        coverage_assumptions: vec![
            "static dependency graph is inside the measured universe".to_string(),
            "policy selector covers the checked static edges".to_string(),
        ],
        exactness_assumptions: vec![
            "AIR component and relation identifiers match the Lean package parameters".to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "static theorem package does not conclude runtime flatness".to_string(),
            "static theorem package does not conclude semantic flatness".to_string(),
            "static theorem package does not prove extractor completeness".to_string(),
        ],
    }
}

fn runtime_zero_bridge_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "runtime-zero-bridge-package-v0".to_string(),
        lean_entrypoint:
            "ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff"
                .to_string(),
        theorem_refs: vec![
            "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction"
                .to_string(),
            "ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff"
                .to_string(),
            "runtimePropagationOfFinite_eq_zero_iff_noSemanticRuntimeExposureObstruction_under_universe"
                .to_string(),
            "v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff_noSemanticRuntimeExposureObstruction_under_universe"
                .to_string(),
        ],
        supported_subject_refs: vec![RUNTIME_PROPAGATION_SUBJECT_REF.to_string()],
        supported_axes: vec!["runtimePropagation".to_string()],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "measuredZero".to_string(),
        required_assumptions: vec![
            "runtimePropagation is computed over a measured 0/1 RuntimeDependencyGraph"
                .to_string(),
            "runtimePropagation is read as runtime exposure radius, not blast radius".to_string(),
            "the measured runtime graph is finite over the AIR component universe".to_string(),
        ],
        coverage_assumptions: vec![
            "runtime edge evidence covers the runtime component pairs in scope".to_string(),
            "runtime coverage records runtimePropagation as a measured axis".to_string(),
        ],
        exactness_assumptions: vec![
            "runtime-edge-projection-v0 maps each observed component pair to one runtime edge"
                .to_string(),
            "runtime evidence component ids resolve inside the AIR component universe".to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "runtime zero bridge does not prove runtime telemetry completeness".to_string(),
            "runtime zero bridge does not prove extractor completeness".to_string(),
            "runtime zero bridge does not conclude runtime blast radius".to_string(),
            "runtime zero bridge does not conclude policy-aware runtime propagation".to_string(),
        ],
    }
}

fn semantic_diagram_filler_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "semantic-diagram-filler-package-v0".to_string(),
        lean_entrypoint: "Chapter9DiagramFilling".to_string(),
        theorem_refs: vec![
            "ArchitecturePath.PathHomotopy".to_string(),
            "DiagramFiller".to_string(),
            "diagramFiller_observation_eq".to_string(),
        ],
        supported_subject_refs: vec!["semantic.diagram".to_string()],
        supported_axes: vec![
            "semanticDiagramCommutation".to_string(),
            "projectionSoundnessViolation".to_string(),
        ],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "measuredZero".to_string(),
        required_assumptions: vec![
            "selected semantic diagram has explicit lhs and rhs architecture paths".to_string(),
            "selected homotopy generators preserve the observed contract".to_string(),
            "diagram filler contract is discharged for the selected finite path calculus"
                .to_string(),
        ],
        coverage_assumptions: vec![
            "semantic coverage records the selected diagram universe".to_string(),
            "contract and test evidence cover the selected diagram observations".to_string(),
        ],
        exactness_assumptions: vec![
            "AIR path refs, diagram refs, and observation refs match the Lean package parameters"
                .to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "semantic diagram filler package does not prove global semantic flatness".to_string(),
            "semantic diagram filler package does not prove extractor completeness".to_string(),
            "unmeasured semantic diagrams are not treated as commuting".to_string(),
        ],
    }
}

fn semantic_nonfillability_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "semantic-nonfillability-package-v0".to_string(),
        lean_entrypoint: "Chapter9DiagramFilling".to_string(),
        theorem_refs: vec![
            "NonFillabilityWitness".to_string(),
            "NonFillabilityWitnessFor".to_string(),
            "observationDifference_refutesDiagramFiller".to_string(),
            "observationDifference_nonFillabilityWitnessFor".to_string(),
            "obstructionAsNonFillability_sound".to_string(),
            "obstructionAsNonFillability_complete_bounded".to_string(),
        ],
        supported_subject_refs: vec!["semantic.diagram".to_string()],
        supported_axes: vec![
            "semanticDiagramCommutation".to_string(),
            "projectionSoundnessViolation".to_string(),
        ],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "measuredNonzero".to_string(),
        required_assumptions: vec![
            "selected observations are comparable".to_string(),
            "selected witness value refutes the diagram filler".to_string(),
            "non-fillability is scoped to the selected semantic diagram".to_string(),
        ],
        coverage_assumptions: vec![
            "semantic coverage records the selected non-fillability witness".to_string(),
            "contract and test evidence cover the observed lhs and rhs paths".to_string(),
        ],
        exactness_assumptions: vec![
            "observation-result evidence matches the selected AIR diagram observations".to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "non-fillability witness does not prove global semantic completeness".to_string(),
            "non-fillability witness does not refute arbitrary split predicates".to_string(),
            "absence of a selected non-fillability witness is not evidence of commutation"
                .to_string(),
        ],
    }
}

fn semantic_numerical_curvature_zero_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "semantic-numerical-curvature-zero-package-v0".to_string(),
        lean_entrypoint: "Formal.Arch.Signature.Curvature".to_string(),
        theorem_refs: vec![
            "numericalCurvature_eq_zero_iff_DiagramCommutes".to_string(),
            "numericalCurvature_eq_zero_of_DiagramCommutes".to_string(),
            "DiagramCommutes_of_numericalCurvature_eq_zero".to_string(),
            "numericalCurvatureObstruction_iff_DiagramBad".to_string(),
            "not_numericalCurvatureObstruction_iff_DiagramCommutes".to_string(),
            "diagramLawful_iff_noNumericalCurvatureObstruction".to_string(),
            "totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero".to_string(),
            "totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes".to_string(),
            "totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction".to_string(),
            "totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero"
                .to_string(),
            "totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes".to_string(),
            "totalWeightedCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction"
                .to_string(),
        ],
        supported_subject_refs: vec![
            "semantic.diagram".to_string(),
            "signature.semanticCurvature".to_string(),
        ],
        supported_axes: vec![
            "semanticCurvature".to_string(),
            "semanticDiagramCommutation".to_string(),
        ],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "measuredZero".to_string(),
        required_assumptions: vec![
            "selected observation distance is zero-separating".to_string(),
            "selected measured diagram universe is finite".to_string(),
            "weighted curvature claims record positive weights for every measured diagram"
                .to_string(),
        ],
        coverage_assumptions: vec![
            "semantic coverage records the measured diagram universe".to_string(),
            "required diagram coverage is bounded to the selected universe".to_string(),
        ],
        exactness_assumptions: vec![
            "curvature values are computed from the same observations referenced by AIR"
                .to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "numerical curvature zero bridge does not prove global semantic flatness".to_string(),
            "numerical curvature zero bridge does not prove business semantics completeness"
                .to_string(),
            "weighted curvature does not conclude empirical cost correlation".to_string(),
        ],
    }
}

fn no_solution_certificate_package() -> TheoremPackageMetadataV0 {
    TheoremPackageMetadataV0 {
        package_id: "no-solution-certificate-package-v0".to_string(),
        lean_entrypoint: "NoSolutionCertificate.sound_of_valid".to_string(),
        theorem_refs: vec![
            "NoSolutionCertificate".to_string(),
            "ValidNoSolutionCertificate".to_string(),
            "NoSolutionCertificate.sound_of_valid".to_string(),
            "ArchitectureCalculusLaw.noSolutionCertificateSoundnessLaw_conclusion".to_string(),
        ],
        supported_subject_refs: vec![NO_SOLUTION_CERTIFICATE_SUBJECT_PREFIX.to_string()],
        supported_axes: vec!["synthesisNoSolution".to_string()],
        claim_level: "formal".to_string(),
        claim_classification: "proved".to_string(),
        measurement_boundary: "certificateBacked".to_string(),
        required_assumptions: vec![
            "candidate universe is finite and explicitly enumerated".to_string(),
            "valid no-solution certificate is supplied".to_string(),
            "certificate cases cover the selected constraints".to_string(),
        ],
        coverage_assumptions: vec![
            "constraint refs and obstruction witness refs resolve in the bounded synthesis universe"
                .to_string(),
            "unsupported constructs are reported rather than discharged".to_string(),
        ],
        exactness_assumptions: vec![
            "certificate case refs match the Lean no-solution package parameters".to_string(),
        ],
        missing_preconditions: Vec::new(),
        non_conclusions: vec![
            "no-solution certificate package does not prove solver completeness".to_string(),
            "no-solution certificate package does not prove extractor completeness".to_string(),
            "solver no-candidate result alone is not a no-solution certificate".to_string(),
        ],
    }
}

pub fn build_theorem_precondition_check_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> TheoremPreconditionCheckReportV0 {
    let registry = static_theorem_package_registry();
    let checks = theorem_precondition_checks(document, &registry);
    let summary = theorem_precondition_check_summary(&checks, document.claims.len());

    TheoremPreconditionCheckReportV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        input: TheoremPreconditionCheckInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        registry,
        summary,
        checks,
    }
}

fn theorem_precondition_checks(
    document: &AirDocumentV0,
    registry: &TheoremPackageRegistryV0,
) -> Vec<TheoremPreconditionCheck> {
    document
        .claims
        .iter()
        .map(|claim| theorem_precondition_check(document, claim, registry))
        .collect()
}

fn theorem_precondition_check(
    document: &AirDocumentV0,
    claim: &AirClaim,
    registry: &TheoremPackageRegistryV0,
) -> TheoremPreconditionCheck {
    let applicable_packages: Vec<&TheoremPackageMetadataV0> = registry
        .packages
        .iter()
        .filter(|package| theorem_package_applies_to_claim(package, claim))
        .collect();
    let known_refs: BTreeSet<String> = registry
        .packages
        .iter()
        .flat_map(|package| package.theorem_refs.iter().cloned())
        .collect();
    let unknown_theorem_refs: Vec<String> = claim
        .theorem_refs
        .iter()
        .filter(|theorem_ref| !known_refs.contains(theorem_ref.as_str()))
        .cloned()
        .collect();
    let applicable_package_refs = applicable_packages
        .iter()
        .map(|package| package.package_id.clone())
        .collect();
    let projection_rule = theorem_precondition_projection_rule(document, claim);
    let mut missing_preconditions = claim.missing_preconditions.clone();
    add_runtime_inferred_missing_preconditions(
        document,
        claim,
        &applicable_packages,
        projection_rule.as_ref(),
        &mut missing_preconditions,
    );
    add_semantic_inferred_missing_preconditions(
        document,
        claim,
        &applicable_packages,
        &mut missing_preconditions,
    );
    let ai_human_review_required = add_ai_session_human_review_missing_precondition(
        document,
        claim,
        &mut missing_preconditions,
    );

    let (resolved_claim_classification, result, reason) = if ai_human_review_required {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "AI session human review boundary blocks formal claim promotion".to_string(),
        )
    } else if !unknown_theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim cites theorem refs outside the theorem package registry".to_string(),
        )
    } else if claim.claim_classification == "measured" {
        (
            "MEASURED_WITNESS".to_string(),
            "pass".to_string(),
            "tooling measurement remains a measured witness, not a formal proved claim".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !missing_preconditions.is_empty()
    {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "missing preconditions block formal proved classification".to_string(),
        )
    } else if claim.claim_level == "formal" && !missing_preconditions.is_empty() {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "missing preconditions block formal claim promotion".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.theorem_refs.is_empty()
        && theorem_refs_discharge_applicable_package(&applicable_packages, claim)
    {
        (
            "FORMAL_PROVED".to_string(),
            "pass".to_string(),
            "theorem refs are registered and missing preconditions are empty".to_string(),
        )
    } else if claim.claim_level == "formal" && claim.claim_classification == "proved" {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "formal proved claim needs registered theorem refs".to_string(),
        )
    } else if claim.claim_classification == "unmeasured" || !claim.missing_preconditions.is_empty()
    {
        (
            "UNMEASURED".to_string(),
            "warn".to_string(),
            "claim remains outside the measured theorem boundary".to_string(),
        )
    } else if !claim.theorem_refs.is_empty()
        && !theorem_refs_discharge_applicable_package(&applicable_packages, claim)
    {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim has theorem refs but no applicable theorem package discharges them".to_string(),
        )
    } else {
        (
            "TOOLING_CLAIM".to_string(),
            "pass".to_string(),
            "claim is reported at tooling level".to_string(),
        )
    };

    TheoremPreconditionCheck {
        claim_id: claim.claim_id.clone(),
        subject_ref: claim.subject_ref.clone(),
        applicable_package_refs,
        theorem_refs: claim.theorem_refs.clone(),
        unknown_theorem_refs,
        claim_level: claim.claim_level.clone(),
        input_claim_classification: claim.claim_classification.clone(),
        resolved_claim_classification,
        measurement_boundary: claim.measurement_boundary.clone(),
        projection_rule,
        required_assumptions: claim.required_assumptions.clone(),
        coverage_assumptions: claim.coverage_assumptions.clone(),
        exactness_assumptions: claim.exactness_assumptions.clone(),
        missing_preconditions,
        non_conclusions: claim.non_conclusions.clone(),
        result,
        reason,
    }
}

fn theorem_precondition_check_summary(
    checks: &[TheoremPreconditionCheck],
    checked_claim_count: usize,
) -> TheoremPreconditionCheckSummary {
    let blocked_claim_count = checks
        .iter()
        .filter(|check| check.resolved_claim_classification == "BLOCKED_FORMAL_CLAIM")
        .count();
    let unknown_theorem_ref_count = checks
        .iter()
        .map(|check| check.unknown_theorem_refs.len())
        .sum();
    let result = if checks.iter().any(|check| check.result == "warn") {
        "warn"
    } else {
        "pass"
    };

    TheoremPreconditionCheckSummary {
        result: result.to_string(),
        checked_claim_count,
        applicable_claim_count: checks
            .iter()
            .filter(|check| !check.applicable_package_refs.is_empty())
            .count(),
        formal_proved_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "FORMAL_PROVED")
            .count(),
        measured_witness_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "MEASURED_WITNESS")
            .count(),
        blocked_claim_count,
        unmeasured_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "UNMEASURED")
            .count(),
        unknown_theorem_ref_count,
    }
}

fn theorem_package_applies_to_claim(package: &TheoremPackageMetadataV0, claim: &AirClaim) -> bool {
    let theorem_ref_matches = claim
        .theorem_refs
        .iter()
        .any(|theorem_ref| package.theorem_refs.contains(theorem_ref));
    if !claim.theorem_refs.is_empty()
        && claim
            .subject_ref
            .starts_with(SEMANTIC_DIAGRAM_SUBJECT_PREFIX)
        && package.package_id.starts_with("semantic-")
    {
        return theorem_ref_matches;
    }

    let subject_matches = package.supported_subject_refs.iter().any(|subject_ref| {
        subject_ref == &claim.subject_ref
            || (subject_ref == "semantic.diagram"
                && claim
                    .subject_ref
                    .starts_with(SEMANTIC_DIAGRAM_SUBJECT_PREFIX))
            || (subject_ref == NO_SOLUTION_CERTIFICATE_SUBJECT_PREFIX
                && claim
                    .subject_ref
                    .starts_with(NO_SOLUTION_CERTIFICATE_SUBJECT_PREFIX))
    });

    theorem_ref_matches || subject_matches
}

fn theorem_refs_discharge_applicable_package(
    applicable_packages: &[&TheoremPackageMetadataV0],
    claim: &AirClaim,
) -> bool {
    applicable_packages.iter().any(|package| {
        claim
            .theorem_refs
            .iter()
            .any(|theorem_ref| package.theorem_refs.contains(theorem_ref))
    })
}

fn theorem_precondition_projection_rule(
    document: &AirDocumentV0,
    claim: &AirClaim,
) -> Option<String> {
    if claim.subject_ref != RUNTIME_PROPAGATION_SUBJECT_REF {
        return None;
    }

    runtime_coverage_layer(document).and_then(|layer| layer.projection_rule.clone())
}

fn runtime_coverage_layer(document: &AirDocumentV0) -> Option<&AirCoverageLayer> {
    document
        .coverage
        .layers
        .iter()
        .find(|layer| layer.layer == "runtime")
}

fn semantic_coverage_layer(document: &AirDocumentV0) -> Option<&AirCoverageLayer> {
    document
        .coverage
        .layers
        .iter()
        .find(|layer| layer.layer == "semantic")
}

fn add_runtime_inferred_missing_preconditions(
    document: &AirDocumentV0,
    claim: &AirClaim,
    applicable_packages: &[&TheoremPackageMetadataV0],
    projection_rule: Option<&String>,
    missing_preconditions: &mut Vec<String>,
) {
    if claim.subject_ref != RUNTIME_PROPAGATION_SUBJECT_REF
        || claim.claim_level != "formal"
        || claim.claim_classification != "proved"
        || !applicable_packages
            .iter()
            .any(|package| package.package_id == "runtime-zero-bridge-package-v0")
    {
        return;
    }

    if !runtime_axis_is_measured_zero(document) {
        push_missing_once(
            missing_preconditions,
            "runtimePropagation axis is not recorded as measured zero",
        );
    }
    if !runtime_coverage_measures_runtime_propagation(document) {
        push_missing_once(
            missing_preconditions,
            "runtime coverage layer does not record runtimePropagation as measured",
        );
    }
    if projection_rule.is_none() {
        push_missing_once(
            missing_preconditions,
            "runtime projection rule is not recorded for the runtime coverage layer",
        );
    }
    if claim.required_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "runtime zero bridge required assumptions are not recorded",
        );
    }
    if claim.coverage_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "runtime coverage assumptions are not recorded",
        );
    }
    if claim.exactness_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "runtime projection exactness assumptions are not recorded",
        );
    }
}

fn add_semantic_inferred_missing_preconditions(
    document: &AirDocumentV0,
    claim: &AirClaim,
    applicable_packages: &[&TheoremPackageMetadataV0],
    missing_preconditions: &mut Vec<String>,
) {
    if claim.claim_level != "formal"
        || !applicable_packages
            .iter()
            .any(|package| package.package_id.starts_with("semantic-"))
    {
        return;
    }

    let semantic_layer = semantic_coverage_layer(document);
    if semantic_layer.is_none() {
        push_missing_once(
            missing_preconditions,
            "semantic coverage layer is not recorded",
        );
    }
    if semantic_layer.is_some_and(|layer| layer.universe_refs.is_empty()) {
        push_missing_once(
            missing_preconditions,
            "semantic coverage universe refs are not recorded",
        );
    }
    if semantic_layer.is_some_and(|layer| layer.extraction_scope.is_empty()) {
        push_missing_once(
            missing_preconditions,
            "semantic coverage extraction scope is not recorded",
        );
    }
    if semantic_layer.is_some_and(|layer| layer.exactness_assumptions.is_empty()) {
        push_missing_once(
            missing_preconditions,
            "semantic coverage exactness assumptions are not recorded",
        );
    }
    if semantic_layer.is_some_and(|layer| layer.measured_axes.is_empty()) {
        push_missing_once(
            missing_preconditions,
            "semantic coverage measured axes are not recorded",
        );
    }

    let diagrams = semantic_diagrams_for_claim(document, claim);
    if diagrams.is_empty() {
        push_missing_once(
            missing_preconditions,
            "semantic formal claim does not reference a selected semantic diagram",
        );
    }
    if diagrams.iter().any(|diagram| {
        !architecture_path_exists(document, &diagram.lhs_path_ref)
            || !architecture_path_exists(document, &diagram.rhs_path_ref)
    }) {
        push_missing_once(
            missing_preconditions,
            "semantic diagram lhs/rhs path refs do not resolve to AIR architecture paths",
        );
    }

    let evidence_kinds = claim_evidence_kinds(document, claim);
    if !evidence_kinds
        .iter()
        .any(|kind| kind == "observation_result")
    {
        push_missing_once(
            missing_preconditions,
            "semantic formal claim lacks observation-result evidence",
        );
    }
    if !evidence_kinds.iter().any(|kind| kind == "test") {
        push_missing_once(
            missing_preconditions,
            "semantic formal claim lacks test evidence",
        );
    }
    if !evidence_kinds
        .iter()
        .any(|kind| kind == "manual_annotation" || kind == "semantic_diagram")
    {
        push_missing_once(
            missing_preconditions,
            "semantic formal claim lacks contract or diagram evidence",
        );
    }
    if claim.required_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "semantic theorem required assumptions are not recorded",
        );
    }
    if claim.coverage_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "semantic coverage assumptions are not recorded",
        );
    }
    if claim.exactness_assumptions.is_empty() {
        push_missing_once(
            missing_preconditions,
            "semantic exactness assumptions are not recorded",
        );
    }

    for package in applicable_packages
        .iter()
        .filter(|package| package.package_id.starts_with("semantic-"))
    {
        if package.measurement_boundary != claim.measurement_boundary {
            push_missing_once(
                missing_preconditions,
                &format!(
                    "{} expects measurement boundary {}",
                    package.package_id, package.measurement_boundary
                ),
            );
        }
        if semantic_layer
            .is_some_and(|layer| layer.measurement_boundary != package.measurement_boundary)
        {
            push_missing_once(
                missing_preconditions,
                &format!(
                    "{} expects semantic coverage boundary {}",
                    package.package_id, package.measurement_boundary
                ),
            );
        }
    }
}

fn add_ai_session_human_review_missing_precondition(
    document: &AirDocumentV0,
    claim: &AirClaim,
    missing_preconditions: &mut Vec<String>,
) -> bool {
    if document.feature.source != "ai_session" || claim.claim_level != "formal" {
        return false;
    }
    if document
        .feature
        .ai_session
        .as_ref()
        .and_then(|ai_session| ai_session.human_reviewed)
        == Some(true)
    {
        return false;
    }

    push_missing_once(missing_preconditions, AI_HUMAN_REVIEW_REQUIRED_PRECONDITION);
    true
}

fn semantic_diagrams_for_claim<'a>(
    document: &'a AirDocumentV0,
    claim: &AirClaim,
) -> Vec<&'a AirSemanticDiagram> {
    document
        .semantic_diagrams
        .iter()
        .filter(|diagram| {
            diagram.filler_claim_ref.as_ref() == Some(&claim.claim_id)
                || document.nonfillability_witnesses.iter().any(|witness| {
                    witness.claim_ref == claim.claim_id && witness.diagram_ref == diagram.id
                })
                || claim.subject_ref == format!("{SEMANTIC_DIAGRAM_SUBJECT_PREFIX}{}", diagram.id)
        })
        .collect()
}

fn architecture_path_exists(document: &AirDocumentV0, path_ref: &str) -> bool {
    document
        .architecture_paths
        .iter()
        .any(|path| path.path_id == path_ref)
}

fn claim_evidence_kinds(document: &AirDocumentV0, claim: &AirClaim) -> BTreeSet<String> {
    document
        .evidence
        .iter()
        .filter(|evidence| claim.evidence_refs.contains(&evidence.evidence_id))
        .map(|evidence| evidence.kind.clone())
        .collect()
}

fn runtime_axis_is_measured_zero(document: &AirDocumentV0) -> bool {
    document.signature.axes.iter().any(|axis| {
        axis.axis == "runtimePropagation"
            && axis.measured
            && axis.measurement_boundary == "measuredZero"
            && axis.value == Some(0)
    })
}

fn runtime_coverage_measures_runtime_propagation(document: &AirDocumentV0) -> bool {
    runtime_coverage_layer(document).is_some_and(|layer| {
        layer.measurement_boundary == "measuredZero"
            && layer
                .measured_axes
                .iter()
                .any(|axis| axis == "runtimePropagation")
    })
}

fn push_missing_once(missing_preconditions: &mut Vec<String>, precondition: &str) {
    if !missing_preconditions
        .iter()
        .any(|existing| existing == precondition)
    {
        missing_preconditions.push(precondition.to_string());
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::air_fixture_document;
    use crate::{AirClaim, THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION};

    use super::build_theorem_precondition_check_report;

    fn runtime_zero_bridge_theorem_refs() -> Vec<String> {
        vec![
            "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction"
                .to_string(),
            "ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff"
                .to_string(),
            "runtimePropagationOfFinite_eq_zero_iff_noSemanticRuntimeExposureObstruction_under_universe"
                .to_string(),
        ]
    }

    fn runtime_zero_bridge_claim(
        claim_id: &str,
        required_assumptions: Vec<String>,
        coverage_assumptions: Vec<String>,
        exactness_assumptions: Vec<String>,
        missing_preconditions: Vec<String>,
    ) -> AirClaim {
        AirClaim {
            claim_id: claim_id.to_string(),
            subject_ref: "signature.runtimePropagation".to_string(),
            predicate:
                "runtimePropagation = some 0 discharges bounded runtime exposure obstruction"
                    .to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: runtime_zero_bridge_theorem_refs(),
            evidence_refs: Vec::new(),
            required_assumptions,
            coverage_assumptions,
            exactness_assumptions,
            missing_preconditions,
            non_conclusions: vec![
                "runtime blast radius is not concluded".to_string(),
                "runtime telemetry completeness is not concluded".to_string(),
            ],
        }
    }

    fn mark_runtime_projection_measured(document: &mut crate::AirDocumentV0) {
        let runtime_axis = document
            .signature
            .axes
            .iter_mut()
            .find(|axis| axis.axis == "runtimePropagation")
            .expect("runtimePropagation axis exists");
        runtime_axis.value = Some(0);
        runtime_axis.measured = true;
        runtime_axis.measurement_boundary = "measuredZero".to_string();
        runtime_axis.source = Some("runtime-edge-projection-v0".to_string());
        runtime_axis.reason = None;

        let runtime_layer = document
            .coverage
            .layers
            .iter_mut()
            .find(|layer| layer.layer == "runtime")
            .expect("runtime coverage layer exists");
        runtime_layer.measurement_boundary = "measuredZero".to_string();
        runtime_layer.measured_axes = vec!["runtimePropagation".to_string()];
        runtime_layer.unmeasured_axes = Vec::new();
        runtime_layer.projection_rule = Some("runtime-edge-projection-v0".to_string());
        runtime_layer.exactness_assumptions = vec![
            "runtime-edge-projection-v0 maps each observed component pair to one runtime edge"
                .to_string(),
        ];
    }

    #[test]
    fn theorem_check_keeps_measured_witness_out_of_formal_proved_claims() {
        let document = air_fixture_document("good_extension.json");
        let report = build_theorem_precondition_check_report(&document, "good_extension.json");

        assert_eq!(
            report.schema_version,
            THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION
        );
        assert_eq!(
            report.registry.scope,
            "static, runtime, semantic, and synthesis theorem package registry v0"
        );
        assert!(report.registry.packages.iter().any(|package| {
            package.theorem_refs
                == vec![
                    "SelectedStaticSplitExtension".to_string(),
                    "CoreEdgesPreserved".to_string(),
                    "DeclaredInterfaceFactorization".to_string(),
                    "NoNewForbiddenStaticEdge".to_string(),
                    "EmbeddingPolicyPreserved".to_string(),
                ]
        }));
        assert!(report.registry.packages.iter().any(|package| {
            package.package_id == "runtime-zero-bridge-package-v0"
                && package
                    .theorem_refs
                    .contains(&"ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction".to_string())
        }));
        assert!(report.registry.packages.iter().any(|package| {
            package.package_id == "semantic-nonfillability-package-v0"
                && package
                    .theorem_refs
                    .contains(&"observationDifference_refutesDiagramFiller".to_string())
        }));

        let boundary_check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-boundary-zero")
            .expect("boundary claim is checked");
        assert_eq!(
            boundary_check.resolved_claim_classification,
            "MEASURED_WITNESS"
        );
        assert_eq!(report.summary.formal_proved_claim_count, 0);
        assert!(report.summary.measured_witness_count > 0);
    }

    #[test]
    fn theorem_check_blocks_formal_claims_with_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-blocked".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec!["SelectedStaticSplitExtension".to_string()],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: vec![
                "declared interface factorization not discharged".to_string(),
            ],
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-blocked")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "BLOCKED_FORMAL_CLAIM");
        assert_eq!(check.result, "warn");
        assert_eq!(report.summary.blocked_claim_count, 1);
        assert_eq!(report.summary.formal_proved_claim_count, 0);
    }

    #[test]
    fn theorem_check_accepts_registered_formal_claim_without_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-proved".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: Vec::new(),
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-proved")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(check.result, "pass");
        assert_eq!(report.summary.formal_proved_claim_count, 1);
    }

    #[test]
    fn theorem_check_accepts_runtime_zero_bridge_only_when_boundary_is_recorded() {
        let mut document = air_fixture_document("good_extension.json");
        mark_runtime_projection_measured(&mut document);
        document.claims.push(runtime_zero_bridge_claim(
            "claim-runtime-zero-bridge-proved",
            vec![
                "runtimePropagation is computed over a measured 0/1 RuntimeDependencyGraph"
                    .to_string(),
            ],
            vec!["runtime edge evidence coverage".to_string()],
            vec!["runtime-edge-projection-v0 exactness".to_string()],
            Vec::new(),
        ));
        document.claims.push(runtime_zero_bridge_claim(
            "claim-runtime-zero-bridge-blocked",
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        ));

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let proved = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-runtime-zero-bridge-proved")
            .expect("runtime proved claim is checked");
        let blocked = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-runtime-zero-bridge-blocked")
            .expect("runtime blocked claim is checked");

        assert_eq!(proved.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(
            proved.projection_rule.as_deref(),
            Some("runtime-edge-projection-v0")
        );
        assert_eq!(
            blocked.resolved_claim_classification,
            "BLOCKED_FORMAL_CLAIM"
        );
        assert!(blocked.missing_preconditions.iter().any(
            |precondition| precondition == "runtime coverage assumptions are not recorded"
        ));
        assert!(
            blocked
                .missing_preconditions
                .iter()
                .any(|precondition| precondition
                    == "runtime projection exactness assumptions are not recorded")
        );
        assert_eq!(report.summary.formal_proved_claim_count, 1);
        assert_eq!(report.summary.blocked_claim_count, 1);
    }

    #[test]
    fn theorem_check_distinguishes_semantic_measured_witness_and_formal_claim() {
        let mut document = air_fixture_document("semantic_nonfillability.json");
        document.claims.push(AirClaim {
            claim_id: "claim-rounding-order-nonfillability-proved".to_string(),
            subject_ref: "semantic.diagram.diagram-coupon-discount-order".to_string(),
            predicate: "selected observation difference refutes the selected diagram filler"
                .to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredNonzero".to_string(),
            theorem_refs: vec![
                "observationDifference_refutesDiagramFiller".to_string(),
                "obstructionAsNonFillability_sound".to_string(),
            ],
            evidence_refs: vec![
                "evidence-rounding-order".to_string(),
                "evidence-coupon-flow-test".to_string(),
                "evidence-coupon-contract".to_string(),
                "evidence-coupon-diagram".to_string(),
            ],
            required_assumptions: vec![
                "selected observations are comparable".to_string(),
                "selected witness value refutes the diagram filler".to_string(),
            ],
            coverage_assumptions: vec![
                "selected business-flow test covers coupon / discount ordering".to_string(),
            ],
            exactness_assumptions: vec![
                "fixture records both selected workflow observations".to_string(),
            ],
            missing_preconditions: Vec::new(),
            non_conclusions: vec![
                "global semantic flatness is not concluded".to_string(),
                "business semantics completeness is not concluded".to_string(),
            ],
        });

        let report =
            build_theorem_precondition_check_report(&document, "semantic_nonfillability.json");
        let measured = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-rounding-order-nonfillability")
            .expect("semantic measured witness is checked");
        let blocked = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-coupon-discount-filler-blocked")
            .expect("semantic blocked filler claim is checked");
        let proved = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-rounding-order-nonfillability-proved")
            .expect("semantic formal non-fillability claim is checked");

        assert_eq!(measured.resolved_claim_classification, "MEASURED_WITNESS");
        assert_eq!(
            blocked.resolved_claim_classification,
            "BLOCKED_FORMAL_CLAIM"
        );
        assert_eq!(proved.resolved_claim_classification, "FORMAL_PROVED");
        assert!(
            proved
                .applicable_package_refs
                .contains(&"semantic-nonfillability-package-v0".to_string())
        );
        assert_eq!(proved.missing_preconditions, Vec::<String>::new());
    }
}
