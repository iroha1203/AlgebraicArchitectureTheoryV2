use std::collections::BTreeSet;

use super::constants::{
    MAX_PART4_DISTANCE_PROFILE_WEIGHT, MAX_PART4_OPERATION_COST,
    REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS, REQUIRED_PART4_DISTANCE_PROFILE_NON_CONCLUSIONS,
    REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS,
};
use super::helpers::{check_from_examples, has_blank, push_blank, set};
use crate::validation::{generic_validation_example, validation_check};
use crate::{LawPolicyDocumentV0, LawPolicyReadingBoundaryV0, ValidationCheck, ValidationExample};

pub(super) fn check_measurement_policy(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let required_store_kinds = BTreeSet::from([
        "archmap-delta",
        "archmap-commit",
        "archmap-snapshot",
        "archmap-index",
    ]);
    let present_store_kinds = policy
        .measurement_policy
        .arch_map_store_ref_kinds
        .iter()
        .map(|kind| kind.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "measurementPolicy.policyId",
        &policy.measurement_policy.policy_id,
    );
    if policy.measurement_policy.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &policy.measurement_policy.policy_id,
            "selectedAxisRefs",
            "measurement policy must select axes for monodromy and boundary holonomy readings",
        ));
    }
    for axis_ref in &policy.measurement_policy.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &policy.measurement_policy.policy_id,
                axis_ref,
                "measurement policy selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    for required_kind in required_store_kinds {
        if !present_store_kinds.contains(required_kind) {
            examples.push(generic_validation_example(
                &policy.measurement_policy.policy_id,
                required_kind,
                "measurement policy must declare every ArchMapStore ref kind",
            ));
        }
    }
    push_blank(
        &mut examples,
        "measurementPolicy.distanceKind",
        &policy.measurement_policy.distance_kind,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.weightPolicy",
        &policy.measurement_policy.weight_policy,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.coveragePolicy",
        &policy.measurement_policy.coverage_policy,
    );
    push_blank(
        &mut examples,
        "measurementPolicy.measurementBoundary",
        &policy.measurement_policy.measurement_boundary,
    );
    if policy.measurement_policy.non_conclusions.is_empty()
        || has_blank(&policy.measurement_policy.non_conclusions)
    {
        examples.push(generic_validation_example(
            &policy.measurement_policy.policy_id,
            "nonConclusions",
            "measurement policy must keep non-conclusions explicit",
        ));
    }

    check_from_examples(
        "law-policy-monodromy-measurement-policy",
        "LawPolicy declares selected axes, distance, weight, coverage, and ArchMapStore ref kinds for monodromy readings",
        examples,
        "fail",
    )
}

pub(super) fn check_part4_distance_profile(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let Some(profile) = &policy.part4_distance_profile else {
        return validation_check(
            "law-policy-part4-distance-profile",
            "part4DistanceProfile is absent; legacy LawPolicy remains parseable but cannot drive complete Part IV distance measurement",
            "warn",
        );
    };

    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let coverage_ids = set(policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.as_str()));
    let required_atom_axes = BTreeSet::from([
        "atom.fiber",
        "atom.carrier",
        "atom.valence",
        "atom.semanticAnchor",
    ]);
    let present_atom_axes = profile
        .atom_weights
        .iter()
        .map(|weight| weight.axis_ref.as_str())
        .collect::<BTreeSet<_>>();
    let present_signature_axes = profile
        .signature_weights
        .iter()
        .map(|weight| weight.axis_ref.as_str())
        .collect::<BTreeSet<_>>();
    let present_non_conclusions = profile
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "part4DistanceProfile.profileId",
        &profile.profile_id,
    );
    for required_axis in required_atom_axes {
        if !present_atom_axes.contains(required_axis) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required_axis,
                "part4DistanceProfile.atomWeights must include every Part IV Atom geometry component",
            ));
        }
    }
    for weight in &profile.atom_weights {
        if ![
            "atom.fiber",
            "atom.carrier",
            "atom.valence",
            "atom.semanticAnchor",
        ]
        .contains(&weight.axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &weight.axis_ref,
                "part4DistanceProfile.atomWeights must not include unused Atom geometry components",
            ));
        }
    }
    if profile.signature_weights.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "signatureWeights",
            "part4DistanceProfile must declare signature-axis weights from LawPolicy",
        ));
    }
    for signature_axis_id in &signature_axis_ids {
        if !present_signature_axes.contains(signature_axis_id) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                signature_axis_id,
                "part4DistanceProfile.signatureWeights must include every selected signature axis",
            ));
        }
    }
    for weight in profile
        .atom_weights
        .iter()
        .chain(profile.signature_weights.iter())
    {
        push_blank(
            &mut examples,
            "part4DistanceProfile.weight.axisRef",
            &weight.axis_ref,
        );
        push_blank(
            &mut examples,
            &format!("part4DistanceProfile.weight[{}].sourceRef", weight.axis_ref),
            &weight.source_ref,
        );
        if weight.weight <= 0 {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &weight.axis_ref,
                "part4DistanceProfile weights must be positive selected distances",
            ));
        }
        if weight.weight > MAX_PART4_DISTANCE_PROFILE_WEIGHT {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &weight.axis_ref,
                "part4DistanceProfile weights must stay within the bounded ArchSig distance range",
            ));
        }
    }
    for weight in &profile.signature_weights {
        if !signature_axis_ids.contains(weight.axis_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &weight.axis_ref,
                "part4DistanceProfile.signatureWeights[].axisRef must reference a known signature axis",
            ));
        }
    }
    if profile.operation_costs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "operationCosts",
            "part4DistanceProfile must declare operation costs instead of relying on evaluator fallbacks",
        ));
    }
    for cost in &profile.operation_costs {
        push_blank(
            &mut examples,
            "part4DistanceProfile.operationCosts[].operationKind",
            &cost.operation_kind,
        );
        push_blank(
            &mut examples,
            &format!(
                "part4DistanceProfile.operationCosts[{}].sourceRef",
                cost.operation_kind
            ),
            &cost.source_ref,
        );
        if cost.cost <= 0 {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &cost.operation_kind,
                "part4DistanceProfile operation costs must be positive selected distances",
            ));
        }
        if cost.cost > MAX_PART4_OPERATION_COST {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &cost.operation_kind,
                "part4DistanceProfile operation costs must stay within the bounded ArchSig distance range",
            ));
        }
    }
    push_blank(
        &mut examples,
        "part4DistanceProfile.aggregationPolicy",
        &profile.aggregation_policy,
    );
    push_blank(
        &mut examples,
        "part4DistanceProfile.unmeasuredPolicy",
        &profile.unmeasured_policy,
    );
    if !profile.unmeasured_policy.contains("not zero") {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "unmeasuredPolicy",
            "part4DistanceProfile.unmeasuredPolicy must explicitly state that unmeasured is not zero",
        ));
    }
    push_blank(
        &mut examples,
        "part4DistanceProfile.lawOverlayPolicy",
        &profile.law_overlay_policy,
    );
    if profile.coverage_requirement_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "coverageRequirementRefs",
            "part4DistanceProfile must reference LawPolicy coverage requirements",
        ));
    }
    for coverage_ref in &profile.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                coverage_ref,
                "part4DistanceProfile.coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    push_blank(
        &mut examples,
        "part4DistanceProfile.evidenceBoundary",
        &profile.evidence_boundary,
    );
    if profile.non_conclusions.is_empty() || has_blank(&profile.non_conclusions) {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "nonConclusions",
            "part4DistanceProfile must keep profile-local non-conclusions explicit",
        ));
    }
    for required in REQUIRED_PART4_DISTANCE_PROFILE_NON_CONCLUSIONS {
        if !present_non_conclusions.contains(required) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required,
                "missing required Part IV distance profile non-conclusion",
            ));
        }
    }

    check_from_examples(
        "law-policy-part4-distance-profile",
        "LawPolicy declares the selected Part IV DistanceProfile used by ArchSig distance measurement",
        examples,
        "fail",
    )
}

pub(super) fn check_spectrum_measurement_profile(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let Some(profile) = &policy.spectrum_measurement_profile else {
        return validation_check(
            "law-policy-spectrum-measurement-profile",
            "optional spectrum measurement profile is absent; LawPolicy remains valid without ACTS readings",
            "pass",
        );
    };

    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let coverage_ids = set(policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.as_str()));
    let present_non_conclusions = profile
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.profileId",
        &profile.profile_id,
    );
    if profile.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "selectedAxisRefs",
            "spectrum profile must select axes for curvature support readings",
        ));
    }
    for axis_ref in &profile.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                axis_ref,
                "spectrum profile selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    if profile.measured_witness_rule_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "measuredWitnessRuleRefs",
            "spectrum profile must declare measured witness rule refs",
        ));
    }
    for witness_ref in &profile.measured_witness_rule_refs {
        if !witness_ids.contains(witness_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                witness_ref,
                "spectrum profile measuredWitnessRuleRefs must reference known witness rules",
            ));
        }
    }
    if profile.distance_kinds.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "distanceKinds",
            "spectrum profile must declare at least one axis distance kind",
        ));
    }
    for distance in &profile.distance_kinds {
        if !axis_ids.contains(distance.axis_ref.as_str())
            && !signature_axis_ids.contains(distance.axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &distance.axis_ref,
                "spectrum distanceKinds[].axisRef must reference known axes or signature axes",
            ));
        }
        push_blank(
            &mut examples,
            &format!("spectrum distance kind for {}", distance.axis_ref),
            &distance.distance_kind,
        );
    }
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.weightPolicy",
        &profile.weight_policy,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.supportProjectionRule",
        &profile.support_projection_rule,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.transferEdgeRule",
        &profile.transfer_edge_rule,
    );
    if profile.coverage_requirement_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "coverageRequirementRefs",
            "spectrum profile must reference coverage requirements",
        ));
    }
    for coverage_ref in &profile.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                coverage_ref,
                "spectrum profile coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    validate_reading_boundary(
        &mut examples,
        &profile.profile_id,
        "spectrumMeasurementProfile.readingBoundary",
        &profile.reading_boundary,
        &coverage_ids,
    );
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.coverageBoundary",
        &profile.coverage_boundary,
    );
    if profile.exactness_assumption_refs.is_empty() || has_blank(&profile.exactness_assumption_refs)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "exactnessAssumptionRefs",
            "spectrum profile must record exactness assumption refs",
        ));
    }
    push_blank(
        &mut examples,
        "spectrumMeasurementProfile.measurementBoundary",
        &profile.measurement_boundary,
    );
    if profile.non_conclusions.is_empty() || has_blank(&profile.non_conclusions) {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "nonConclusions",
            "spectrum profile must keep non-conclusions explicit",
        ));
    }
    for required in REQUIRED_SPECTRUM_PROFILE_NON_CONCLUSIONS {
        if !present_non_conclusions.contains(required) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required,
                "missing required spectrum profile non-conclusion",
            ));
        }
    }

    check_from_examples(
        "law-policy-spectrum-measurement-profile",
        "LawPolicy keeps spectrum measurement recipes separate from the selected law universe",
        examples,
        "fail",
    )
}

pub(super) fn check_homotopy_measurement_profile(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let Some(profile) = &policy.homotopy_measurement_profile else {
        return validation_check(
            "law-policy-homotopy-measurement-profile",
            "optional homotopy measurement profile is absent; LawPolicy remains valid without homotopy readings",
            "pass",
        );
    };

    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let signature_axis_ids = set(policy
        .signature_axis_definitions
        .iter()
        .map(|axis| axis.signature_axis_id.as_str()));
    let coverage_ids = set(policy
        .coverage_requirements
        .iter()
        .map(|requirement| requirement.coverage_requirement_id.as_str()));
    let present_non_conclusions = profile
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.profileId",
        &profile.profile_id,
    );
    if profile.selected_axis_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "selectedAxisRefs",
            "homotopy profile must select axes for continuation and holonomy readings",
        ));
    }
    for axis_ref in &profile.selected_axis_refs {
        if !axis_ids.contains(axis_ref.as_str()) && !signature_axis_ids.contains(axis_ref.as_str())
        {
            examples.push(generic_validation_example(
                &profile.profile_id,
                axis_ref,
                "homotopy profile selectedAxisRefs must reference known axes or signature axes",
            ));
        }
    }
    if profile.path_discovery_rules.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "pathDiscoveryRules",
            "homotopy profile must declare path discovery rules",
        ));
    }
    for rule in &profile.path_discovery_rules {
        push_blank(&mut examples, "pathDiscoveryRules[].ruleId", &rule.rule_id);
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].pathSourceKind", rule.rule_id),
            &rule.path_source_kind,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].endpointPolicy", rule.rule_id),
            &rule.endpoint_policy,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].candidateSource", rule.rule_id),
            &rule.candidate_source,
        );
        push_blank(
            &mut examples,
            &format!("pathDiscoveryRules[{}].evidenceBoundary", rule.rule_id),
            &rule.evidence_boundary,
        );
        if rule.non_conclusions.is_empty() || has_blank(&rule.non_conclusions) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy path discovery rules must keep non-conclusions explicit",
            ));
        }
    }
    if profile.filler_rules.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "fillerRules",
            "homotopy profile must declare filler rules",
        ));
    }
    for rule in &profile.filler_rules {
        push_blank(&mut examples, "fillerRules[].ruleId", &rule.rule_id);
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].fillerKind", rule.rule_id),
            &rule.filler_kind,
        );
        if rule.required_source_ref_kinds.is_empty() || has_blank(&rule.required_source_ref_kinds) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy filler rules must declare required source ref kinds",
            ));
        }
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].missingFillerBehavior", rule.rule_id),
            &rule.missing_filler_behavior,
        );
        push_blank(
            &mut examples,
            &format!("fillerRules[{}].evidenceBoundary", rule.rule_id),
            &rule.evidence_boundary,
        );
        if rule.non_conclusions.is_empty() || has_blank(&rule.non_conclusions) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                &rule.rule_id,
                "homotopy filler rules must keep non-conclusions explicit",
            ));
        }
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.loopMeasurementPolicy.policyId",
        &profile.loop_measurement_policy.policy_id,
    );
    if profile
        .loop_measurement_policy
        .loop_candidate_sources
        .is_empty()
        || has_blank(&profile.loop_measurement_policy.loop_candidate_sources)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "loopMeasurementPolicy.loopCandidateSources",
            "homotopy loop measurement policy must declare candidate sources",
        ));
    }
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.filledLoopReading",
        &profile.loop_measurement_policy.filled_loop_reading,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.unfilledLoopReading",
        &profile.loop_measurement_policy.unfilled_loop_reading,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.holonomyDistanceKind",
        &profile.loop_measurement_policy.holonomy_distance_kind,
    );
    push_blank(
        &mut examples,
        "loopMeasurementPolicy.localCurvatureReadingBoundary",
        &profile
            .loop_measurement_policy
            .local_curvature_reading_boundary,
    );
    if profile.loop_measurement_policy.non_conclusions.is_empty()
        || has_blank(&profile.loop_measurement_policy.non_conclusions)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "loopMeasurementPolicy.nonConclusions",
            "homotopy loop measurement policy must keep non-conclusions explicit",
        ));
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.continuationPolicy",
        &profile.continuation_policy,
    );
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.distancePolicy",
        &profile.distance_policy,
    );
    if profile.coverage_requirement_refs.is_empty() {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "coverageRequirementRefs",
            "homotopy profile must reference coverage requirements",
        ));
    }
    for coverage_ref in &profile.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                coverage_ref,
                "homotopy profile coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    validate_reading_boundary(
        &mut examples,
        &profile.profile_id,
        "homotopyMeasurementProfile.readingBoundary",
        &profile.reading_boundary,
        &coverage_ids,
    );
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.coverageBoundary",
        &profile.coverage_boundary,
    );
    if profile.exactness_assumption_refs.is_empty() || has_blank(&profile.exactness_assumption_refs)
    {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "exactnessAssumptionRefs",
            "homotopy profile must record exactness assumption refs",
        ));
    }
    push_blank(
        &mut examples,
        "homotopyMeasurementProfile.measurementBoundary",
        &profile.measurement_boundary,
    );
    if profile.non_conclusions.is_empty() || has_blank(&profile.non_conclusions) {
        examples.push(generic_validation_example(
            &profile.profile_id,
            "nonConclusions",
            "homotopy profile must keep non-conclusions explicit",
        ));
    }
    for required in REQUIRED_HOMOTOPY_PROFILE_NON_CONCLUSIONS {
        if !present_non_conclusions.contains(required) {
            examples.push(generic_validation_example(
                &profile.profile_id,
                required,
                "missing required homotopy profile non-conclusion",
            ));
        }
    }

    check_from_examples(
        "law-policy-homotopy-measurement-profile",
        "LawPolicy keeps homotopy path, filler, loop, coverage, and non-conclusion recipes separate from the selected law universe",
        examples,
        "fail",
    )
}
pub(super) fn validate_reading_boundary(
    examples: &mut Vec<ValidationExample>,
    subject: &str,
    field: &str,
    boundary: &LawPolicyReadingBoundaryV0,
    coverage_ids: &BTreeSet<&str>,
) {
    push_blank(
        examples,
        &format!("{field}.readingStrength"),
        &boundary.reading_strength,
    );
    if boundary.zero_reflection_assumptions.is_empty()
        || has_blank(&boundary.zero_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.zeroReflectionAssumptions"),
            "reading boundary must declare zero-reflection assumptions",
        ));
    }
    if boundary.obstruction_reflection_assumptions.is_empty()
        || has_blank(&boundary.obstruction_reflection_assumptions)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.obstructionReflectionAssumptions"),
            "reading boundary must declare obstruction-reflection assumptions",
        ));
    }
    if boundary.coverage_requirement_refs.is_empty()
        || has_blank(&boundary.coverage_requirement_refs)
    {
        examples.push(generic_validation_example(
            subject,
            &format!("{field}.coverageRequirementRefs"),
            "reading boundary must reference coverage requirements",
        ));
    }
    for coverage_ref in &boundary.coverage_requirement_refs {
        if !coverage_ids.contains(coverage_ref.as_str()) {
            examples.push(generic_validation_example(
                subject,
                coverage_ref,
                "reading boundary coverageRequirementRefs must reference known coverage requirements",
            ));
        }
    }
    push_blank(
        examples,
        &format!("{field}.witnessCompletenessBoundary"),
        &boundary.witness_completeness_boundary,
    );
}
