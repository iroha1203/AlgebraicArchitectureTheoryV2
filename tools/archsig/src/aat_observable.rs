use std::collections::BTreeSet;

use crate::validation::{count_checks, validation_check};
use crate::{
    AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION, AAT_OBSERVABLE_BUNDLE_VALIDATION_REPORT_SCHEMA_VERSION,
    AIR_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION, AatAnalyticAxisV0, AatConceptMappingV0,
    AatCoverageBoundaryV0, AatFeatureExtensionEvidenceV0, AatLlmReviewSurfaceV0,
    AatObservableBundleV0, AatObservableBundleValidationInputV0,
    AatObservableBundleValidationReportV0, AatObservableBundleValidationSummaryV0,
    AatObservableSourceRefV0, AatObservedAxisV0, AatOperationCandidateV0,
    AatProjectionObservationEvidenceV0, AatRepairSynthesisEvidenceV0, AatResponsibilityBoundaryV0,
    AatReviewActionV0, AatSelectedUniverseV0, AatSemanticDiagramEvidenceV0,
    AatStateEffectLawEvidenceV0, AatTheoremBoundaryV0, AatWitnessCatalogEntryV0,
    FEATURE_EXTENSION_REPORT_SCHEMA_VERSION, ValidationCheck,
};

const AAT_OBSERVABLE_NON_CONCLUSIONS: [&str; 9] = [
    "AAT observable bundle is tooling evidence, not a Lean theorem proof",
    "validation pass does not prove extractor completeness",
    "unmeasured is not measured zero",
    "private, unavailable, unsupported, and dynamic blind spots are retained as boundaries",
    "absence of witness refs does not prove global lawfulness",
    "operation candidates are review cues, not theorem discharge",
    "analytic value zero does not imply structural flatness without zero-reflecting assumptions",
    "LLM review output is judgment support, not automatic merge approval",
    "human review remains responsible for accepting risk and product decisions",
];

pub fn static_aat_observable_bundle() -> AatObservableBundleV0 {
    let non_conclusions = strings(&AAT_OBSERVABLE_NON_CONCLUSIONS);
    AatObservableBundleV0 {
        schema_version: AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION.to_string(),
        bundle_id: "fixture-aat-observable-bundle-v0".to_string(),
        architecture_id: "coupon-service".to_string(),
        source_refs: vec![
            source_ref(
                "source:air:coupon",
                "air",
                AIR_SCHEMA_VERSION,
                "tools/archsig/tests/fixtures/air/good_extension.json",
                &["components", "relations", "claims", "coverage", "semanticDiagrams"],
            ),
            source_ref(
                "source:archmap:coupon",
                "archmap",
                ARCHMAP_SCHEMA_VERSION,
                "tools/archsig/tests/fixtures/minimal/archmap.json",
                &["sourceUniverse", "mapItems", "coverage", "conflicts"],
            ),
            source_ref(
                "source:feature-report:coupon",
                "feature-extension-report",
                FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
                "tools/archsig/tests/fixtures/minimal/feature_extension_report.json",
                &[
                    "introducedObstructionWitnesses",
                    "semanticPathSummary",
                    "repairSuggestions",
                ],
            ),
        ],
        selected_universe: AatSelectedUniverseV0 {
            universe_id: "universe:coupon-selected".to_string(),
            included_refs: vec!["component:checkout".to_string(), "component:coupon".to_string()],
            excluded_refs: vec!["component:billing-private".to_string()],
            private_refs: vec!["repo:private-observability".to_string()],
            unavailable_refs: vec!["runtime:production-traces".to_string()],
            unsupported_refs: vec!["framework:dynamic-plugin-loader".to_string()],
            dynamic_boundary_refs: vec!["boundary:runtime-dispatch".to_string()],
            exactness_assumptions: vec![
                "static import graph is selected as structural evidence".to_string(),
                "runtime traces are unavailable unless supplied as runtime-edge-evidence".to_string(),
            ],
            measurement_status: "partiallyMeasured".to_string(),
            non_conclusions: vec![
                "selected universe is not the complete deployed system".to_string(),
                "excluded refs are not measured zero".to_string(),
            ],
        },
        concept_mappings: concept_mappings(),
        observed_axes: observed_axes(),
        coverage_boundaries: coverage_boundaries(),
        witness_catalog: witness_catalog(),
        operation_candidates: operation_candidates(),
        projection_observation_evidence: projection_observation_evidence(),
        feature_extension_evidence: feature_extension_evidence(),
        semantic_diagram_evidence: semantic_diagram_evidence(),
        state_effect_law_evidence: state_effect_law_evidence(),
        repair_synthesis_evidence: repair_synthesis_evidence(),
        analytic_axes: analytic_axes(),
        theorem_boundaries: theorem_boundaries(),
        review_actions: review_actions(),
        llm_review_surface: AatLlmReviewSurfaceV0 {
            skill_ref: "tools/archsig/skills/aat-reviewer/SKILL.md".to_string(),
            input_artifact_refs: vec![
                "source:air:coupon".to_string(),
                "source:feature-report:coupon".to_string(),
                "bundle:fixture-aat-observable-bundle-v0".to_string(),
            ],
            review_questions: vec![
                "Which invariant is preserved, broken, unmeasured, or out of scope?".to_string(),
                "Which obstruction witnesses are typed as obstruction circuits, and which circuit families remain unmeasured?".to_string(),
                "Which operation family is plausible, and what must stay a human judgment?".to_string(),
                "Which theorem boundary blocks a formal claim?".to_string(),
                "What next evidence would change the review decision?".to_string(),
            ],
            output_categories: vec![
                "violation".to_string(),
                "risk".to_string(),
                "acceptable".to_string(),
                "unmeasured".to_string(),
                "nextEvidence".to_string(),
            ],
            deterministic_inputs: vec![
                "schema validation results".to_string(),
                "dangling ref checks".to_string(),
                "measurement status and source refs".to_string(),
            ],
            llm_judgment_boundaries: vec![
                "semantic operation classification".to_string(),
                "review severity and next evidence prioritization".to_string(),
            ],
            human_review_boundaries: vec![
                "risk acceptance".to_string(),
                "product decision resolution".to_string(),
                "merge approval".to_string(),
            ],
            non_conclusions: vec![
                "LLM review does not prove semantic correctness".to_string(),
                "LLM review does not approve merge automatically".to_string(),
            ],
        },
        responsibility_boundary: AatResponsibilityBoundaryV0 {
            deterministic_tool: vec![
                "validate schema version and refs".to_string(),
                "preserve measurement status and nonConclusions".to_string(),
                "surface measured witnesses and dangling refs".to_string(),
            ],
            llm_review: vec![
                "interpret operation candidates against AAT questions".to_string(),
                "translate nonConclusions into next evidence and guardrails".to_string(),
            ],
            human_review: vec![
                "decide acceptable residual risk".to_string(),
                "accept or reject design tradeoffs".to_string(),
            ],
            formal_proof: vec![
                "Lean theorem packages remain separate from ArchSig validation".to_string(),
            ],
            non_conclusions: vec![
                "responsibility split does not make tooling output a proof".to_string(),
            ],
        },
        non_conclusions,
    }
}

pub fn validate_aat_observable_bundle(
    bundle: &AatObservableBundleV0,
    input_path: &str,
) -> AatObservableBundleValidationReportV0 {
    let checks = vec![
        check_schema(bundle),
        check_source_refs(bundle),
        check_concept_coverage(bundle),
        check_measurement_statuses(bundle),
        check_witness_review_actions(bundle),
        check_operation_evidence_refs(bundle),
        check_theorem_boundary_actions(bundle),
        check_responsibility_boundary(bundle),
        check_non_conclusions(bundle),
    ];
    let summary = AatObservableBundleValidationSummaryV0 {
        result: validation_result(&checks),
        concept_count: bundle.concept_mappings.len(),
        witness_count: bundle.witness_catalog.len(),
        operation_candidate_count: bundle.operation_candidates.len(),
        review_action_count: bundle.review_actions.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };
    AatObservableBundleValidationReportV0 {
        schema_version: AAT_OBSERVABLE_BUNDLE_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: AatObservableBundleValidationInputV0 {
            schema_version: bundle.schema_version.clone(),
            path: input_path.to_string(),
            bundle_id: bundle.bundle_id.clone(),
        },
        bundle: bundle.clone(),
        summary,
        checks,
    }
}

fn concept_mappings() -> Vec<AatConceptMappingV0> {
    vec![
        concept(
            "concept:architecture-object",
            "ArchitectureObject / ComponentUniverse",
            &["source:archmap:coupon", "source:air:coupon"],
            &["coverage-boundary:dynamic-dispatch"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+human",
            &["component universe coverage is not complete extraction"],
        ),
        concept(
            "concept:obstruction-witness",
            "ObstructionWitness",
            &["source:feature-report:coupon"],
            &["witness:projection-mismatch", "witness:nonfillability"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "measuredNonzero",
            "deterministic+LLM+human",
            &["witness absence does not prove lawfulness"],
        ),
        concept(
            "concept:theorem-boundary",
            "TheoremBoundary / NonConclusion",
            &["theorem-check-report-v0"],
            &["boundary:formal-precondition-missing"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "unmeasured",
            "deterministic+human",
            &["blocked formal claim is not a measured violation"],
        ),
        concept(
            "concept:operation",
            "ArchitectureOperation",
            &["pr-quality-analysis-report-v0", "fieldsig-sft-artifact-ref"],
            &["operation:coupon-feature-extension"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+LLM",
            &["operation candidate is not theorem discharge"],
        ),
        concept(
            "concept:projection-observation",
            "Projection / Observation / LSP / DIP",
            &["source:air:coupon"],
            &["evidence:projection-abstraction"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+LLM",
            &["local contract evidence is not global layering proof"],
        ),
        concept(
            "concept:feature-extension",
            "FeatureExtension / ExtensionObstruction",
            &["source:feature-report:coupon"],
            &["feature-evidence:coupon-extension"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+LLM+human",
            &["extension obstruction classes are not disjointness proof"],
        ),
        concept(
            "concept:semantic-diagram",
            "Path / Homotopy / DiagramFiller / NonFillability",
            &["source:air:coupon"],
            &["semantic:evidence:coupon-noncommutation"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "measuredNonzero",
            "deterministic+LLM",
            &["semantic evidence is not static edge evidence"],
        ),
        concept(
            "concept:state-effect",
            "StateTransition / EffectBoundary",
            &["source:air:coupon"],
            &["state-effect:evidence:coupon-replay"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+LLM+human",
            &["state law evidence is not event log completeness"],
        ),
        concept(
            "concept:repair-synthesis",
            "Repair / Synthesis / ComplexityTransfer",
            &["source:feature-report:coupon"],
            &["repair:evidence:coupon-boundary"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+LLM+human",
            &["repair suggestion is not whole-system improvement"],
        ),
        concept(
            "concept:analytic-representation",
            "AnalyticRepresentation / ObstructionValuation",
            &["signature-axis:projectionSoundnessViolation"],
            &["analytic-axis:projection-soundness"],
            &["tools/archsig/skills/aat-reviewer/SKILL.md"],
            "representable",
            "retained",
            "reviewable",
            "partiallyMeasured",
            "deterministic+human",
            &["metric zero is not structural flatness without reflection assumptions"],
        ),
        concept(
            "concept:global-higher-completeness",
            "Global higher-categorical completeness",
            &[],
            &["coverage-boundary:out-of-scope-hott"],
            &[],
            "outOfScope",
            "notRetained",
            "humanOnly",
            "outOfScope",
            "human",
            &["HoTT or higher category completeness is out of scope for ArchSig v0"],
        ),
    ]
}

fn observed_axes() -> Vec<AatObservedAxisV0> {
    vec![
        AatObservedAxisV0 {
            axis_id: "axis:projectionSoundnessViolation".to_string(),
            concept_refs: vec!["concept:projection-observation".to_string()],
            artifact_refs: vec!["source:air:coupon".to_string()],
            measurement_status: "measuredNonzero".to_string(),
            value: Some(1),
            boundary: "selected AIR claim and witness universe".to_string(),
            non_conclusions: vec![
                "nonzero selected axis is not global architecture ranking".to_string(),
            ],
        },
        AatObservedAxisV0 {
            axis_id: "axis:runtimePropagation".to_string(),
            concept_refs: vec!["concept:state-effect".to_string()],
            artifact_refs: vec!["runtime-edge-evidence-v0".to_string()],
            measurement_status: "unmeasured".to_string(),
            value: None,
            boundary: "runtime traces unavailable".to_string(),
            non_conclusions: vec!["unmeasured runtime propagation is not zero".to_string()],
        },
    ]
}

fn coverage_boundaries() -> Vec<AatCoverageBoundaryV0> {
    vec![
        AatCoverageBoundaryV0 {
            boundary_id: "coverage-boundary:dynamic-dispatch".to_string(),
            boundary_kind: "dynamicBlindSpot".to_string(),
            affected_refs: vec!["component:plugin-runtime".to_string()],
            measurement_status: "unmeasured".to_string(),
            review_action_ref: Some("review:request-runtime-evidence".to_string()),
            non_conclusions: vec![
                "dynamic dispatch blind spot is not measured absence".to_string(),
            ],
        },
        AatCoverageBoundaryV0 {
            boundary_id: "coverage-boundary:out-of-scope-hott".to_string(),
            boundary_kind: "outOfScope".to_string(),
            affected_refs: vec!["concept:global-higher-completeness".to_string()],
            measurement_status: "outOfScope".to_string(),
            review_action_ref: None,
            non_conclusions: vec![
                "out-of-scope concept is not silently unsupported evidence".to_string(),
            ],
        },
    ]
}

fn witness_catalog() -> Vec<AatWitnessCatalogEntryV0> {
    vec![
        witness(
            "witness:projection-mismatch",
            "projectionFailure",
            &["law:lsp-observation-preservation"],
            &["source:air:coupon"],
            "measuredNonzero",
            "high",
            "review:inspect-projection-mismatch",
            &["projection mismatch does not prove global undecomposability"],
        ),
        witness(
            "witness:nonfillability",
            "nonFillabilityWitness",
            &["law:semantic-commutation"],
            &["source:air:coupon"],
            "measuredNonzero",
            "medium",
            "review:inspect-semantic-diagram",
            &["nonfillability witness is selected-diagram evidence only"],
        ),
        witness(
            "witness:effect-leakage",
            "effectLeakage",
            &["law:effect-boundary"],
            &["source:air:coupon"],
            "partiallyMeasured",
            "medium",
            "review:request-effect-evidence",
            &["effect leakage cue is not operational cost theorem"],
        ),
        witness(
            "witness:complexity-transfer",
            "complexityTransfer",
            &["law:repair-selected-axis"],
            &["source:feature-report:coupon"],
            "reviewNeeded",
            "medium",
            "review:inspect-repair-transfer",
            &["selected repair improvement is not whole-system improvement"],
        ),
    ]
}

fn operation_candidates() -> Vec<AatOperationCandidateV0> {
    vec![AatOperationCandidateV0 {
        operation_ref: "operation:coupon-feature-extension".to_string(),
        operation_kind: "featureExtension".to_string(),
        role: "introduce coupon workflow while preserving checkout price invariant".to_string(),
        confidence: "medium".to_string(),
        deterministic_cues: vec![
            "added coupon component".to_string(),
            "added checkout-to-coupon relation".to_string(),
        ],
        llm_judgment_needed: vec![
            "whether coupon logic is extension or policy migration".to_string(),
            "whether transferred obstruction is acceptable".to_string(),
        ],
        evidence_refs: vec!["feature-evidence:coupon-extension".to_string()],
        preserved_invariant_refs: vec!["invariant:price-total-nonnegative".to_string()],
        possible_transferred_obstruction_refs: vec!["witness:complexity-transfer".to_string()],
        non_conclusions: vec!["operation candidate is not a semantic theorem".to_string()],
    }]
}

fn projection_observation_evidence() -> Vec<AatProjectionObservationEvidenceV0> {
    vec![AatProjectionObservationEvidenceV0 {
        evidence_ref: "evidence:projection-abstraction".to_string(),
        evidence_kind: "projectionMismatch".to_string(),
        source_ref: "component:coupon-adapter".to_string(),
        target_ref: "interface:discount-policy".to_string(),
        local_contract_boundary: "LSP cue over selected interface methods".to_string(),
        global_layering_boundary: "does not conclude global Clean Architecture compliance"
            .to_string(),
        witness_refs: vec!["witness:projection-mismatch".to_string()],
        non_conclusions: vec!["DIP-compatible cue is not decomposability proof".to_string()],
    }]
}

fn feature_extension_evidence() -> Vec<AatFeatureExtensionEvidenceV0> {
    vec![AatFeatureExtensionEvidenceV0 {
        evidence_ref: "feature-evidence:coupon-extension".to_string(),
        feature_ref: "feature:coupon".to_string(),
        operation_ref: "operation:coupon-feature-extension".to_string(),
        obstruction_classifications: vec![
            "inheritedCoreObstruction".to_string(),
            "interactionObstruction".to_string(),
            "residualCoverageGap".to_string(),
        ],
        source_refs: vec!["source:feature-report:coupon".to_string()],
        witness_refs: vec!["witness:projection-mismatch".to_string()],
        missing_evidence_refs: vec!["runtime:production-traces".to_string()],
        static_boundary: "static component/relation delta is retained".to_string(),
        runtime_boundary: "runtime law cases are unavailable unless supplied".to_string(),
        semantic_boundary: "semantic diagrams are selected examples".to_string(),
        coverage_boundary: "coverage gap remains residual evidence need".to_string(),
        non_conclusions: vec!["feature extension is not just component delta".to_string()],
    }]
}

fn semantic_diagram_evidence() -> Vec<AatSemanticDiagramEvidenceV0> {
    vec![AatSemanticDiagramEvidenceV0 {
        evidence_ref: "semantic:evidence:coupon-noncommutation".to_string(),
        path_refs: vec![
            "path:apply-then-audit".to_string(),
            "path:audit-then-apply".to_string(),
        ],
        homotopy_refs: vec!["homotopy:coupon-audit-order".to_string()],
        diagram_refs: vec!["diagram:coupon-audit".to_string()],
        filler_status: "nonCommuting".to_string(),
        nonfillability_witness_refs: vec!["witness:nonfillability".to_string()],
        observation_refs: vec!["observation:coupon-audit-log".to_string()],
        measurement_status: "measuredNonzero".to_string(),
        non_conclusions: vec![
            "selected non-commutation is not arbitrary split failure".to_string(),
        ],
    }]
}

fn state_effect_law_evidence() -> Vec<AatStateEffectLawEvidenceV0> {
    vec![AatStateEffectLawEvidenceV0 {
        evidence_ref: "state-effect:evidence:coupon-replay".to_string(),
        law_kind: "replayRoundtripCompensationProjection".to_string(),
        law_case_refs: vec!["case:coupon-expired-replay".to_string()],
        measurement_status: "partiallyMeasured".to_string(),
        witness_refs: vec!["witness:effect-leakage".to_string()],
        unmeasured_law_families: vec![
            "sagaCompensationCompleteness".to_string(),
            "migrationNaturality".to_string(),
        ],
        non_conclusions: vec!["state/effect law case is not event log completeness".to_string()],
    }]
}

fn repair_synthesis_evidence() -> Vec<AatRepairSynthesisEvidenceV0> {
    vec![AatRepairSynthesisEvidenceV0 {
        evidence_ref: "repair:evidence:coupon-boundary".to_string(),
        repair_step_refs: vec!["repair:move-coupon-policy-behind-interface".to_string()],
        synthesis_candidate_refs: vec!["synthesis:discount-policy-adapter".to_string()],
        no_solution_certificate_refs: vec!["no-solution:legacy-plugin-boundary".to_string()],
        selected_obstruction_decrease_refs: vec!["witness:projection-mismatch".to_string()],
        transferred_risk_refs: vec!["witness:complexity-transfer".to_string()],
        solver_status: "noCandidateDistinguishedFromNoSolutionCertificate".to_string(),
        non_conclusions: vec![
            "repair suggestion is not automatic patch or all-obstruction removal".to_string(),
        ],
    }]
}

fn analytic_axes() -> Vec<AatAnalyticAxisV0> {
    vec![AatAnalyticAxisV0 {
        axis_id: "analytic-axis:projection-soundness".to_string(),
        metric_ref: "axis:projectionSoundnessViolation".to_string(),
        representation_strength: vec![
            "zeroPreserving".to_string(),
            "obstructionPreserving".to_string(),
            "notZeroReflecting".to_string(),
            "notObstructionReflecting".to_string(),
        ],
        selected_witness_universe: vec!["witness:projection-mismatch".to_string()],
        aggregate_zero_reflection:
            "requires complete selected witness universe and explicit zero-reflecting claim"
                .to_string(),
        coverage_assumptions: vec![
            "selected AIR witnesses are complete for this axis only if declared".to_string(),
        ],
        non_conclusions: vec!["aggregate value 0 alone does not imply flatness".to_string()],
    }]
}

fn theorem_boundaries() -> Vec<AatTheoremBoundaryV0> {
    vec![AatTheoremBoundaryV0 {
        boundary_ref: "boundary:formal-precondition-missing".to_string(),
        claim_ref: "claim:coupon-extension-lawful".to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: "blockedFormalClaim".to_string(),
        missing_preconditions: vec![
            "complete selected runtime evidence".to_string(),
            "projection exactness".to_string(),
        ],
        measured_violation_refs: vec!["witness:projection-mismatch".to_string()],
        review_action_ref: "review:block-formal-promotion".to_string(),
        non_conclusions: vec![
            "missing precondition is not measured violation by itself".to_string(),
        ],
    }]
}

fn review_actions() -> Vec<AatReviewActionV0> {
    vec![
        review_action(
            "review:inspect-projection-mismatch",
            "measuredViolation",
            &["witness:projection-mismatch"],
            "inspect abstraction mapping and decide whether boundary repair is required",
            &["interface contract evidence", "adapter test evidence"],
            "human-review",
            &["measured violation is selected-universe evidence"],
        ),
        review_action(
            "review:request-runtime-evidence",
            "nextEvidence",
            &["coverage-boundary:dynamic-dispatch"],
            "request runtime traces or mark runtime law family unmeasured",
            &["runtime-edge-evidence-v0"],
            "human-review",
            &["missing runtime evidence is not zero runtime risk"],
        ),
        review_action(
            "review:inspect-semantic-diagram",
            "reviewGuardrail",
            &["witness:nonfillability"],
            "keep semantic non-commutation separate from static dependency violation",
            &["semantic diagram fixture", "observation refs"],
            "llm-review",
            &["semantic witness does not prove global semantic completeness"],
        ),
        review_action(
            "review:block-formal-promotion",
            "blockedFormalClaim",
            &["boundary:formal-precondition-missing"],
            "do not promote tooling evidence to Lean theorem claim",
            &["theorem-precondition-check-report-v0"],
            "deterministic-tool",
            &["blocked formal claim is not tool failure"],
        ),
        review_action(
            "review:inspect-repair-transfer",
            "evidenceGap",
            &["witness:complexity-transfer"],
            "verify selected repair does not transfer unacceptable complexity",
            &["post-repair feature report", "policy decision report"],
            "human-review",
            &["selected-axis improvement is not total quality improvement"],
        ),
        review_action(
            "review:request-effect-evidence",
            "nextEvidence",
            &["witness:effect-leakage"],
            "request replay, roundtrip, compensation, or projection law case evidence",
            &["state-effect law fixture", "runtime edge evidence"],
            "human-review",
            &["effect law cue is not operational completeness"],
        ),
    ]
}

fn check_schema(bundle: &AatObservableBundleV0) -> ValidationCheck {
    if bundle.schema_version == AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION {
        validation_check(
            "aat-observable-schema-version",
            "schema version is supported",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-schema-version",
            "schema version is supported",
            "fail",
        )
    }
}

fn check_source_refs(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let missing = bundle
        .source_refs
        .iter()
        .filter(|source| {
            source.source_ref_id.is_empty()
                || source.path.is_empty()
                || source.retained_fields.is_empty()
                || source.non_conclusions.is_empty()
        })
        .count();
    if missing == 0 && !bundle.source_refs.is_empty() {
        validation_check(
            "aat-observable-source-refs",
            "source refs retain fields and boundaries",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-source-refs",
            "source refs retain fields and boundaries",
            "fail",
        )
    }
}

fn check_concept_coverage(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let concepts: BTreeSet<&str> = bundle
        .concept_mappings
        .iter()
        .map(|mapping| mapping.aat_concept.as_str())
        .collect();
    let required = [
        "ArchitectureObject / ComponentUniverse",
        "ObstructionWitness",
        "TheoremBoundary / NonConclusion",
        "ArchitectureOperation",
        "Projection / Observation / LSP / DIP",
        "FeatureExtension / ExtensionObstruction",
        "Path / Homotopy / DiagramFiller / NonFillability",
        "StateTransition / EffectBoundary",
        "Repair / Synthesis / ComplexityTransfer",
        "AnalyticRepresentation / ObstructionValuation",
    ];
    if required.iter().all(|concept| concepts.contains(concept)) {
        validation_check(
            "aat-observable-concept-coverage",
            "major AAT concepts are mapped",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-concept-coverage",
            "major AAT concepts are mapped",
            "fail",
        )
    }
}

fn check_measurement_statuses(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let has_measured_zero_boundary = bundle
        .concept_mappings
        .iter()
        .any(|item| item.measurement_status == "measuredZero")
        || bundle
            .observed_axes
            .iter()
            .any(|axis| axis.measurement_status == "measuredZero");
    let statuses: BTreeSet<&str> = bundle
        .concept_mappings
        .iter()
        .map(|mapping| mapping.measurement_status.as_str())
        .chain(
            bundle
                .coverage_boundaries
                .iter()
                .map(|boundary| boundary.measurement_status.as_str()),
        )
        .collect();
    if statuses.contains("unmeasured")
        && statuses.contains("outOfScope")
        && statuses.contains("partiallyMeasured")
        && !has_measured_zero_boundary
    {
        validation_check(
            "aat-observable-measurement-statuses",
            "unmeasured/out-of-scope/partial statuses are explicit and not collapsed to measured zero",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-measurement-statuses",
            "unmeasured/out-of-scope/partial statuses are explicit and not collapsed to measured zero",
            "fail",
        )
    }
}

fn check_witness_review_actions(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let action_ids: BTreeSet<&str> = bundle
        .review_actions
        .iter()
        .map(|action| action.review_action_id.as_str())
        .collect();
    if !bundle.witness_catalog.is_empty()
        && bundle
            .witness_catalog
            .iter()
            .all(|witness| action_ids.contains(witness.review_action_ref.as_str()))
    {
        validation_check(
            "aat-observable-witness-review-actions",
            "witnesses point to review actions",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-witness-review-actions",
            "witnesses point to review actions",
            "fail",
        )
    }
}

fn check_operation_evidence_refs(bundle: &AatObservableBundleV0) -> ValidationCheck {
    if !bundle.operation_candidates.is_empty()
        && bundle.operation_candidates.iter().all(|operation| {
            !operation.evidence_refs.is_empty()
                && !operation.non_conclusions.is_empty()
                && !operation.llm_judgment_needed.is_empty()
        })
    {
        validation_check(
            "aat-observable-operation-boundary",
            "operation candidates keep evidence and LLM boundary",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-operation-boundary",
            "operation candidates keep evidence and LLM boundary",
            "fail",
        )
    }
}

fn check_theorem_boundary_actions(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let action_ids: BTreeSet<&str> = bundle
        .review_actions
        .iter()
        .map(|action| action.review_action_id.as_str())
        .collect();
    if !bundle.theorem_boundaries.is_empty()
        && bundle.theorem_boundaries.iter().all(|boundary| {
            action_ids.contains(boundary.review_action_ref.as_str())
                && boundary.claim_level != "formal-proof"
                && !boundary.non_conclusions.is_empty()
        })
    {
        validation_check(
            "aat-observable-theorem-boundary-actions",
            "theorem boundaries block formal promotion",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-theorem-boundary-actions",
            "theorem boundaries block formal promotion",
            "fail",
        )
    }
}

fn check_responsibility_boundary(bundle: &AatObservableBundleV0) -> ValidationCheck {
    if !bundle.responsibility_boundary.deterministic_tool.is_empty()
        && !bundle.responsibility_boundary.llm_review.is_empty()
        && !bundle.responsibility_boundary.human_review.is_empty()
        && !bundle.responsibility_boundary.formal_proof.is_empty()
        && !bundle.llm_review_surface.review_questions.is_empty()
    {
        validation_check(
            "aat-observable-responsibility-boundary",
            "deterministic/LLM/human/formal responsibilities are separated",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-responsibility-boundary",
            "deterministic/LLM/human/formal responsibilities are separated",
            "fail",
        )
    }
}

fn check_non_conclusions(bundle: &AatObservableBundleV0) -> ValidationCheck {
    let required = [
        "tooling evidence",
        "extractor completeness",
        "unmeasured is not measured zero",
        "automatic merge approval",
    ];
    if required.iter().all(|needle| {
        bundle
            .non_conclusions
            .iter()
            .any(|entry| entry.contains(needle))
    }) {
        validation_check(
            "aat-observable-non-conclusions",
            "bundle retains AAT claim boundaries",
            "pass",
        )
    } else {
        validation_check(
            "aat-observable-non-conclusions",
            "bundle retains AAT claim boundaries",
            "fail",
        )
    }
}

fn source_ref(
    id: &str,
    kind: &str,
    schema_version: &str,
    path: &str,
    retained_fields: &[&str],
) -> AatObservableSourceRefV0 {
    AatObservableSourceRefV0 {
        source_ref_id: id.to_string(),
        artifact_kind: kind.to_string(),
        schema_version: schema_version.to_string(),
        path: path.to_string(),
        retained_fields: strings(retained_fields),
        non_conclusions: vec!["source ref does not prove artifact completeness".to_string()],
    }
}

fn concept(
    id: &str,
    concept: &str,
    artifact_refs: &[&str],
    report_refs: &[&str],
    skill_refs: &[&str],
    expressibility: &str,
    retention_status: &str,
    review_status: &str,
    measurement_status: &str,
    responsibility: &str,
    non_conclusions: &[&str],
) -> AatConceptMappingV0 {
    AatConceptMappingV0 {
        concept_id: id.to_string(),
        aat_concept: concept.to_string(),
        artifact_refs: strings(artifact_refs),
        report_refs: strings(report_refs),
        skill_refs: strings(skill_refs),
        expressibility: expressibility.to_string(),
        retention_status: retention_status.to_string(),
        review_status: review_status.to_string(),
        measurement_status: measurement_status.to_string(),
        responsibility: responsibility.to_string(),
        non_conclusions: strings(non_conclusions),
    }
}

fn witness(
    witness_ref: &str,
    kind: &str,
    law_refs: &[&str],
    source_refs: &[&str],
    measurement_status: &str,
    severity: &str,
    review_action_ref: &str,
    non_conclusions: &[&str],
) -> AatWitnessCatalogEntryV0 {
    AatWitnessCatalogEntryV0 {
        witness_ref: witness_ref.to_string(),
        witness_kind: kind.to_string(),
        law_refs: strings(law_refs),
        source_refs: strings(source_refs),
        measurement_status: measurement_status.to_string(),
        severity: severity.to_string(),
        review_action_ref: review_action_ref.to_string(),
        non_conclusions: strings(non_conclusions),
    }
}

fn review_action(
    id: &str,
    category: &str,
    source_refs: &[&str],
    action: &str,
    next_evidence: &[&str],
    owner: &str,
    non_conclusions: &[&str],
) -> AatReviewActionV0 {
    AatReviewActionV0 {
        review_action_id: id.to_string(),
        category: category.to_string(),
        source_refs: strings(source_refs),
        action: action.to_string(),
        next_evidence: strings(next_evidence),
        owner: owner.to_string(),
        non_conclusions: strings(non_conclusions),
    }
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

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}
