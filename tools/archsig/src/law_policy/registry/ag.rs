use crate::LawEvaluatorManifestV1;

pub fn ag_evaluator_manifests() -> Vec<LawEvaluatorManifestV1> {
    vec![
        ag_manifest("ag.cech-obstruction", "ag.cech-obstruction"),
        ag_coherence_manifest(),
        ag_restriction_manifest(),
        ag_section_manifest(),
        ag_boundary_residue_manifest(),
        ag_manifest("ag.square-free-repair", "ag.square-free-repair"),
        ag_manifest("ag.law-conflict-tor", "ag.law-conflict-tor"),
        ag_manifest("ag.sheaf-laplacian", "ag.sheaf-laplacian"),
        ag_manifest("ag.period-stokes", "ag.period-stokes"),
        ag_period_stokes_audit_manifest(),
        ag_manifest("ag.support-transfer", "ag.support-transfer"),
        ag_saga_descent_manifest(),
        ag_saga_grounded_manifest(),
    ]
}

pub fn binding_axes_for(evaluator_id: &str) -> &'static [&'static str] {
    match evaluator_id {
        "ag.cech-obstruction" => &["cech"],
        "ag.coherence-obstruction"
        | "ag.restriction-compatibility"
        | "ag.boundary-residue"
        | "ag.square-free-repair"
        | "ag.law-conflict-tor"
        | "ag.saga-descent" => &["square-free"],
        "ag.section-factorization" => &["section-factorization"],
        "ag.sheaf-laplacian" => &["laplacian"],
        "ag.period-stokes" | "ag.period-stokes-audit" => &["period"],
        "ag.support-transfer" => &["transfer"],
        _ => &[],
    }
}

fn ag_saga_descent_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.saga-descent".to_string(),
        law_id: "ag.saga-descent".to_string(),
        condition_types: vec!["descent".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: Vec::new(),
        required_molecule_condition:
            "archmap/v0.5.2 selected finite cover plus a checked archsig-repair-plan/v0.5.2 artifact"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover from MeasurementProfile and supplied RepairPlan complex"
                .to_string(),
        missing_blocker_rule:
            "missing RepairPlan is not_computed with silence_by_design; invalid RepairPlan fails validation before measurement"
                .to_string(),
        pass_criteria:
            "supplied residual is a B1 boundary and complete-support faithfulness is satisfied inside the selected RepairPlan complex"
                .to_string(),
        violation_criteria:
            "supplied residual is not a B1 boundary, or complete-support semantic projection exposes an alias witness"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution:
            "SAGA descent emits selected-complex-relative boundary-membership and global-coherence verdicts without consuming conclusion tokens from input"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
            "/boundaryStatements".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_saga_grounded_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.saga-grounded".to_string(),
        law_id: "ag.saga-grounded".to_string(),
        condition_types: vec!["descent".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: Vec::new(),
        required_molecule_condition:
            "law-equation-surface/v0.5.2 Stage 3 fields plus a checked saga-grounding RepairPlan slot"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover, chart-local defect observables, and the selected policy-row profile"
                .to_string(),
        missing_blocker_rule:
            "missing grounding, Stage 3 defect source, witnessVariables/forbiddenSupportGenerators, Layer D supplied data, aligned skeleton, selected quotient condition, or finite witness bound is not_computed with silence_by_design"
                .to_string(),
        pass_criteria:
            "grounded witnessVariables and forbiddenSupportGenerators generate the finite F2 Boolean quotient; holdsCriterion raw-value checks derive the displayed law premise, interpretation class, and law-dependent packet"
                .to_string(),
        violation_criteria:
            "a non-empty chart-local defect observable emits MEASURED_LAW_DEFECT_AT_CHART and not_established law-dependent conclusions"
                .to_string(),
        typed_result_schema: "archsig-saga-conclusions/v0.5.2".to_string(),
        distance_contribution:
            "grounded 10-conclusion packet keeps law-dependent and law-independent structures separate and records generated quotient provenance"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_coherence_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.coherence-obstruction".to_string(),
        law_id: "ag.coherence-obstruction".to_string(),
        condition_types: vec!["descent".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: vec!["cech.sectionValue".to_string()],
        required_molecule_condition:
            "archmap/v0.5.2 contexts and selected cover triple-overlap 2-skeleton".to_string(),
        scope_filtering_rule:
            "selected finite poset site and cover from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing section value witness atoms are unmeasured; incomplete 2-skeleton is not_computed"
                .to_string(),
        pass_criteria:
            "selected-cover banded abelian F2 H2 coherence cocycle is a coboundary"
                .to_string(),
        violation_criteria:
            "selected-cover banded abelian F2 H2 coherence cocycle has a representative outside im d1"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution: "structural H2 coherence verdict remains cover-relative and F2-banded"
            .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_coherence_obstruction_negative.json".to_string()],
    }
}

fn ag_boundary_residue_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.boundary-residue".to_string(),
        law_id: "ag.boundary-residue".to_string(),
        condition_types: vec!["descent".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "boundary-residue.patchRole".to_string(),
            "boundary-residue.restrictionColumn".to_string(),
            "boundary-residue.sectionValue".to_string(),
        ],
        required_molecule_condition:
            "archmap/v0.5.2 selected cover with core, feature, and boundary patch roles plus finite F2 restriction columns"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover and witness variables from the supplied law surface".to_string(),
        missing_blocker_rule:
            "missing patch classification, boundary section value, or restriction matrix is not_computed"
                .to_string(),
        pass_criteria:
            "selected boundary mismatch section lies in the F2 image of Mayer-Vietoris d0"
                .to_string(),
        violation_criteria:
            "selected boundary mismatch section is outside the F2 image of Mayer-Vietoris d0"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution:
            "structural boundary residue verdict remains selected-cover and F2-relative"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_period_stokes_audit_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.period-stokes-audit".to_string(),
        law_id: "ag.period-stokes-audit".to_string(),
        condition_types: vec!["temporal".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "period.dOmegaIntegral".to_string(),
            "period.boundaryPeriod".to_string(),
        ],
        required_molecule_condition:
            "archmap/v0.5.2 selected cover with supplied dOmegaIntegral and boundaryPeriod audit values"
                .to_string(),
        scope_filtering_rule:
            "selected finite cover and fixed coefficient MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing audit pairs or unresolved strict coefficient data yields unknown/not_computed, not a crash"
                .to_string(),
        pass_criteria:
            "all supplied fixed-coefficient Stokes audit residuals are zero".to_string(),
        violation_criteria:
            "at least one supplied fixed-coefficient Stokes audit residual is nonzero".to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution:
            "structural verdict is scoped to supplied independent Stokes accounting values only"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/computedInvariants".to_string(),
            "/analyticReadings".to_string(),
            "/assumptions".to_string(),
        ],
        negative_fixtures: Vec::new(),
    }
}

fn ag_section_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.section-factorization".to_string(),
        law_id: "ag.section-factorization".to_string(),
        condition_types: vec![
            "open".to_string(),
            "descent".to_string(),
            "closed-equational".to_string(),
        ],
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "section-factorization.support".to_string(),
            "section-factorization.witnessAssignment".to_string(),
        ],
        required_molecule_condition:
            "archmap/v0.5.2 selected cover, finite forbidden supports, and one selected Boolean section"
                .to_string(),
        scope_filtering_rule:
            "selected finite poset site and witness family from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing witnessAssignment or raw support atoms are not_computed; partial undecidable assignment is unknown"
                .to_string(),
        pass_criteria:
            "selected total section avoids every minimal forbidden support, so s^* I_Ob^U=0"
                .to_string(),
        violation_criteria: "selected section active support contains a minimal forbidden support"
            .to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution:
            "structural section factorization verdict remains selected-section relative".to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_section_factorization_negative.json".to_string()],
    }
}

fn ag_restriction_manifest() -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: "ag.restriction-compatibility".to_string(),
        law_id: "ag.restriction-compatibility".to_string(),
        condition_types: vec!["descent".to_string(), "closed-equational".to_string()],
        required_atom_constructors: Vec::new(),
        required_predicates: vec![
            "restriction-compatibility.restrictionIdealGenerator".to_string(),
        ],
        required_molecule_condition:
            "archmap/v0.5.2 contexts, selected cover restriction edges, and finite ideal generator supports"
                .to_string(),
        scope_filtering_rule:
            "selected finite poset site and cover from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing restriction edges or endpoint generator contracts are not_computed".to_string(),
        pass_criteria:
            "every selected restriction edge carries source ideal generators into the target ideal"
                .to_string(),
        violation_criteria:
            "some selected restriction edge has a source generator with no target generator dividing its support"
                .to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution:
            "structural restriction compatibility verdict remains selected-cover and presentation-relative"
                .to_string(),
        summary_output_refs: vec!["/structuralVerdict".to_string()],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec!["ag_restriction_compatibility_negative.json".to_string()],
    }
}

fn ag_manifest(evaluator_id: &str, law_id: &str) -> LawEvaluatorManifestV1 {
    LawEvaluatorManifestV1 {
        evaluator_id: evaluator_id.to_string(),
        law_id: law_id.to_string(),
        condition_types: condition_types_for(evaluator_id),
        required_atom_constructors: Vec::new(),
        required_predicates: Vec::new(),
        required_molecule_condition:
            "archmap/v0.5.2 contexts and covers replace molecule primary input".to_string(),
        scope_filtering_rule: "selected finite poset site from MeasurementProfile".to_string(),
        missing_blocker_rule:
            "missing MeasurementProfile fails validation before evaluator execution".to_string(),
        pass_criteria: "schema foundation only; concrete AG evaluator verdicts are follow-up work"
            .to_string(),
        violation_criteria:
            "schema foundation only; concrete AG evaluator verdicts are follow-up work".to_string(),
        typed_result_schema: "archsig-measurement-packet/v0.5.2".to_string(),
        distance_contribution: "structural verdict and analytic readings remain separated"
            .to_string(),
        summary_output_refs: vec![
            "/structuralVerdict".to_string(),
            "/analyticReadings".to_string(),
        ],
        detail_output_refs: vec![
            "/assumptions".to_string(),
            "/computedInvariants".to_string(),
        ],
        negative_fixtures: vec![
            "tests/fixtures/ag_measurement/law_policy_missing_profile.json".to_string(),
        ],
    }
}

fn condition_types_for(evaluator_id: &str) -> Vec<String> {
    let condition_types = match evaluator_id {
        "ag.cech-obstruction" => ["descent", "closed-equational"].as_slice(),
        "ag.square-free-repair" | "ag.law-conflict-tor" => ["closed-equational"].as_slice(),
        "ag.sheaf-laplacian" => ["constructible", "closed-equational"].as_slice(),
        "ag.period-stokes" => ["temporal", "closed-equational"].as_slice(),
        "ag.support-transfer" => ["constructible", "closed-equational"].as_slice(),
        "ag.section-factorization" => ["open", "descent", "closed-equational"].as_slice(),
        _ => &[],
    };
    condition_types
        .iter()
        .map(|value| (*value).to_string())
        .collect()
}
