use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    AIR_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION, ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION,
    ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION, ARTIFACT_DESCRIPTOR_SCHEMA_VERSION,
    AirArchitecturePath, AirArtifact, AirClaim, AirComponent, AirCoverage, AirCoverageLayer,
    AirDocumentV0, AirEvidence, AirExtension, AirFeature, AirIdPolicies, AirNonfillabilityWitness,
    AirOperationTrace, AirPolicies, AirRelation, AirRevision, AirSemanticDiagram, AirSignature,
    ArchMapAtomicObservationSummary, ArchMapConflict, ArchMapDocumentV0,
    ArchMapLeanPreservationChecklistEntry, ArchMapLeanPreservationVocabularyEntry, ArchMapMapItem,
    ArchMapSourceInventoryV0, ArchMapSourceRef, ArchMapValidationReportV0,
    ArchMapValidationSummary, CandidateOperationFamilyV0, KnownForbiddenOperationSupportV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION, OperationSupportDescriptorRefV0,
    OperationSupportEstimateV0, OperationSupportEvidenceBoundaryV0,
    OperationSupportPolicyConstraintV0, OperationSupportUnknownRemainderV0, Sig0Document,
    ValidationCheck,
};

const OPERATION_SUPPORT_REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "operation support estimate is a bounded tooling estimate, not accepted PR history",
    "operation support estimate is not actual future support",
    "unknown support is not measured zero",
    "policy constraints do not prove global policy safety",
    "operation support estimate does not prove future trajectory safety",
];

const OPERATION_SUPPORT_EVIDENCE_BOUNDARY_NON_CONCLUSIONS: [&str; 3] = [
    "confidence is relative to retained descriptor source refs",
    "evidence boundary does not complete extractor coverage",
    "unsupported constructs remain forecast boundary items",
];

const ARCHSIG_COMPUTED_INVARIANT_KINDS: [&str; 17] = [
    "measurement-invariant",
    "cech-h1-rank",
    "minimal-forbidden-supports",
    "tor1-class-support",
    "boundary-residue-rank",
    "residual-boundary-membership",
    "selected-cover-edge-support",
    "coherence-obstruction-count",
    "restriction-compatibility-rank",
    "section-factorization-rank",
    "sheaf-laplacian-spectrum",
    "period-stokes-pairing",
    "period-stokes-audit",
    "support-transfer-rank",
    "topological-debt-capacity",
    "saga-grounded-conclusions",
    "h1-comparison-transfer",
];

const ARCHSIG_SUPPLIED_DATA_KINDS: [&str; 6] = [
    "archmap",
    "law-policy",
    "measurement-profile",
    "law-equation-surface",
    "repair-plan",
    "residual-packet",
];

pub struct ArchMapSourceInventoryInput<'a> {
    pub path: &'a str,
    pub document: Option<&'a ArchMapSourceInventoryV0>,
    pub read_error: Option<String>,
}

pub fn validate_archmap_report(
    document: &ArchMapDocumentV0,
    input_path: &str,
    sig0: Option<&Sig0Document>,
    source_inventory: Option<ArchMapSourceInventoryInput<'_>>,
) -> ArchMapValidationReportV0 {
    let source_inventory_checks = vec![
        check_archmap_schema_version(&document.schema_version),
        check_source_inventory_boundary(document),
        check_source_inventory_artifact(document, source_inventory.as_ref()),
    ];
    let mut source_ref_checks = vec![check_archmap_unique_map_item_ids(document)];
    source_ref_checks.push(check_source_refs(document));
    let claim_boundary_checks = vec![
        check_measured_claim_evidence(document),
        check_missing_evidence_not_measured_zero(document),
        check_srp_evidence_boundary(document),
    ];
    let semantic_coverage_checks = vec![check_semantic_coverage(document)];
    let conflict_checks = vec![check_conflicts(document, sig0)];
    let formal_promotion_guardrail_checks = vec![
        check_formal_promotion_guardrail(document),
        check_projection_separation(document),
    ];
    let atomic_observation_checks = archmap_atomic_observation_checks(document);
    let atomic_observation_summary = archmap_atomic_observation_summary(document);

    let mut all_checks = Vec::new();
    all_checks.append(&mut source_inventory_checks.clone());
    all_checks.extend(source_ref_checks.clone());
    all_checks.extend(claim_boundary_checks.clone());
    all_checks.extend(semantic_coverage_checks.clone());
    all_checks.extend(conflict_checks.clone());
    all_checks.extend(formal_promotion_guardrail_checks.clone());
    all_checks.extend(atomic_observation_checks.clone());

    let failed_check_count = count_checks(&all_checks, "fail");
    let warning_check_count = count_checks(&all_checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    ArchMapValidationReportV0 {
        schema_version: ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        archmap_ref: input_path.to_string(),
        lean_preservation_vocabulary: archmap_lean_preservation_vocabulary(),
        lean_preservation_precondition_checklist: archmap_lean_preservation_checklist(document),
        source_inventory_checks,
        source_ref_checks,
        claim_boundary_checks,
        semantic_coverage_checks,
        conflict_checks,
        formal_promotion_guardrail_checks,
        atomic_observation_checks,
        atomic_observation_summary,
        summary: ArchMapValidationSummary {
            result: result.to_string(),
            map_item_count: document.map_items.len(),
            conflict_count: explicit_and_derived_conflicts(document, sig0).len(),
            failed_check_count,
            warning_check_count,
        },
        non_conclusions: archmap_non_conclusions(document),
    }
}

pub fn build_operation_support_estimate_from_archmap(
    document: &ArchMapDocumentV0,
    _input_path: &str,
) -> OperationSupportEstimateV0 {
    let source_ref_ids = archmap_sft_source_refs(document);
    let candidate_operation_families = archmap_sft_candidate_families(document, &source_ref_ids);
    let family_ids = candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();

    OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: format!("estimate:archmap:{}", stable_id(&document.map_id)),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            descriptor_id: format!("descriptor:archmap:{}", document.map_id),
            artifact_kind: "archmap".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids: archmap_sft_action_candidate_ids(document),
            non_conclusions: archmap_sft_non_conclusions(),
        },
        candidate_operation_families,
        policy_constraints: vec![OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:archmap:no-forecast-correctness".to_string(),
            constraint_kind: "claim-boundary".to_string(),
            applies_to_family_ids: family_ids.clone(),
            source_ref_ids: source_ref_ids.clone(),
            rule: "ArchMap-derived SFT input is bounded evidence and must not be treated as a forecast result".to_string(),
            safety_claim_boundary: "projection preserves source refs and missing evidence, not semantic truth or probability".to_string(),
            policy_refs: vec!["policy:archmap-sft-boundary".to_string()],
            support_disposition: "conditionallyAllowed".to_string(),
            governance_action_refs: vec!["governance:review-missing-evidence".to_string()],
            non_conclusions: archmap_sft_non_conclusions(),
        }],
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:archmap:llm-forecast-result".to_string(),
            operation_family: "llm-authored-forecast-result".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            constraint_refs: vec!["constraint:archmap:no-forecast-correctness".to_string()],
            reason: "LLM or ArchMap input may describe operation evidence, but does not write the forecast result".to_string(),
            boundary: "forecast correctness and causal prediction remain outside the ArchMap-to-SFT projection".to_string(),
            non_conclusions: archmap_sft_non_conclusions(),
        }],
        unknown_remainder: archmap_sft_unknown_remainders(document, &family_ids, &source_ref_ids),
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: format!("boundary:archmap:{}:sft-input", stable_id(&document.map_id)),
            source_ref_ids,
            measurement_boundary_refs: archmap_sft_measurement_boundary_refs(document),
            confidence_boundary:
                "ArchMap confidence is qualitative review priority, not probability".to_string(),
            evidence_kinds: unique_strings(
                document
                    .map_items
                    .iter()
                    .flat_map(|item| item.source_refs.iter().map(|source| source.kind.clone()))
                    .collect(),
            ),
            unsupported_constructs: document.coverage.unsupported_constructs.clone(),
            assumptions: vec![
                "SFT-facing projection uses selected ArchMap mapItems only".to_string(),
                "missing, private, and unavailable evidence remains boundary data".to_string(),
                "atom, circuit, and observation gap refs are consumed as observation refs, not universal atom truth".to_string(),
            ],
            non_conclusions: archmap_sft_non_conclusions(),
        },
        non_conclusions: archmap_sft_non_conclusions(),
    }
}

pub fn build_operation_support_estimate_from_archsig_measurement_packet(
    packet: &serde_json::Value,
    input_path: &str,
) -> Result<OperationSupportEstimateV0, Box<dyn std::error::Error>> {
    let schema_version = packet
        .get("schema")
        .or_else(|| packet.get("schema"))
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if schema_version != "archsig-measurement-packet/v0.5.3" {
        return Err(format!(
            "FieldSig ArchSig measurement handoff requires archsig-measurement-packet/v0.5.3, got {schema_version}"
        )
        .into());
    }
    validate_archsig_measurement_packet_handoff_shape(packet)?;

    let packet_id = packet
        .get("packetId")
        .and_then(|value| value.as_str())
        .unwrap_or("archsig-measurement-packet");
    let source_ref_ids = archsig_measurement_packet_sft_source_refs(packet, input_path);
    let action_class_candidate_ids = archsig_measurement_packet_action_candidate_ids(packet);
    let candidate_operation_families = archsig_measurement_packet_candidate_families(
        packet,
        &source_ref_ids,
        &action_class_candidate_ids,
    );
    let family_ids = candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    let non_conclusions = archsig_measurement_packet_sft_non_conclusions(packet);

    Ok(OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: format!("estimate:archsig-measurement:{}", stable_id(packet_id)),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            descriptor_id: format!("descriptor:archsig-measurement:{packet_id}"),
            artifact_kind: "archsig-measurement-packet".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids: action_class_candidate_ids.clone(),
            non_conclusions: non_conclusions.clone(),
        },
        candidate_operation_families,
        policy_constraints: vec![OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:archsig-measurement:no-forecast-truth-promotion"
                .to_string(),
            constraint_kind: "claim-boundary".to_string(),
            applies_to_family_ids: family_ids.clone(),
            source_ref_ids: source_ref_ids.clone(),
            rule: "ArchSig measurement packet is current AG measurement state for SFT evolution input, not forecast truth".to_string(),
            safety_claim_boundary:
                "SFT consumes selected structural verdict, computed invariant, analytic reading, and assumption refs as bounded coordinates only"
                    .to_string(),
            policy_refs: vec!["policy:archsig-measurement-sft-boundary".to_string()],
            support_disposition: "conditionallyAllowed".to_string(),
            governance_action_refs: vec![
                "governance:review-archsig-measurement-handoff".to_string(),
            ],
            non_conclusions: non_conclusions.clone(),
        }],
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:raw-archmap-forecast-truth".to_string(),
            operation_family: "raw-archmap-truth-promotion".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            constraint_refs: vec![
                "constraint:archsig-measurement:no-forecast-truth-promotion".to_string(),
            ],
            reason: "ArchSig measurement packets do not assert SFT forecast correctness or raw ArchMap truth".to_string(),
            boundary: "FieldSig must keep measurement packet refs as bounded current AG structural state, not ground truth, causal proof, or diff analysis".to_string(),
            non_conclusions: non_conclusions.clone(),
        }],
        unknown_remainder: archsig_measurement_packet_unknown_remainders(
            packet,
            &family_ids,
            &source_ref_ids,
        ),
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: format!("boundary:archsig-measurement:{}:sft-input", stable_id(packet_id)),
            source_ref_ids,
            measurement_boundary_refs: archsig_measurement_packet_measurement_boundary_refs(packet),
            confidence_boundary:
                "ArchSig measurement packet statuses are selected finite-measurement evidence, not probability"
                    .to_string(),
            evidence_kinds: vec![
                "archsig-measurement-packet/v0.5.3".to_string(),
                "measurement-profile/v0.5.3".to_string(),
                "structural-verdict".to_string(),
                "computed-invariant".to_string(),
                "analytic-reading".to_string(),
                "assumption-ledger".to_string(),
            ],
            unsupported_constructs: vec![
                "raw ArchMap observation completeness".to_string(),
                "SFT forecast correctness".to_string(),
                "causal repair safety".to_string(),
                "global architecture safety".to_string(),
            ],
            assumptions: vec![
                "FieldSig reads ArchSig measurement packet refs as current AG measurement state".to_string(),
                "PR, diff, change-vector, forecast, governance, and operational evolution remain FieldSig readings".to_string(),
                "analytic readings and theorem-candidate readings are retained as analytic state, not structural verdicts".to_string(),
                "not_computed verdicts and violated assumptions remain unknown remainder, not measured zero".to_string(),
            ],
            non_conclusions: archsig_measurement_packet_evidence_boundary_non_conclusions(packet),
        },
        non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
    })
}

fn json_path_string(packet: &serde_json::Value, path: &[&str], key: &str) -> Option<String> {
    let mut current = packet;
    for segment in path {
        current = current.get(*segment)?;
    }
    current.get(key)?.as_str().map(ToOwned::to_owned)
}

fn validate_archsig_measurement_packet_handoff_shape(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let schema = packet
        .get("schema")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if schema != "archsig-measurement-packet/v0.5.3" {
        return Err(
            "FieldSig ArchSig measurement handoff requires archsig-measurement-packet/v0.5.3"
                .into(),
        );
    }
    let packet_id = packet
        .get("packetId")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if packet_id.trim().is_empty() {
        return Err("FieldSig ArchSig measurement handoff requires non-empty packetId".into());
    }
    let fingerprints = packet
        .get("componentFingerprints")
        .and_then(|value| value.as_object())
        .ok_or("FieldSig ArchSig measurement handoff requires componentFingerprints object")?;
    let expected = BTreeSet::from(["lawPolicy", "lawSurface", "measurementProfile"]);
    let actual = fingerprints
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(
            "FieldSig ArchSig measurement handoff componentFingerprints must contain exactly lawPolicy, lawSurface, measurementProfile".into(),
        );
    }
    for component in expected {
        let fingerprint = fingerprints
            .get(component)
            .and_then(|value| value.as_str())
            .ok_or_else(|| format!("FieldSig ArchSig measurement handoff componentFingerprints.{component} must be a string"))?;
        if fingerprint.len() != 71
            || !fingerprint.starts_with("sha256:")
            || !fingerprint[7..]
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!(
                "FieldSig ArchSig measurement handoff componentFingerprints.{component} must be sha256:<64 hex chars>"
            ).into());
        }
    }
    let profile = packet
        .get("profile")
        .and_then(|value| value.as_object())
        .ok_or("FieldSig ArchSig measurement handoff requires profile object")?;
    if profile.get("schema").and_then(|value| value.as_str()) != Some("measurement-profile/v0.5.3")
    {
        return Err(
            "FieldSig ArchSig measurement handoff requires profile schema measurement-profile/v0.5.3"
                .into(),
        );
    }
    if profile.contains_key("witnessFamily") {
        return Err(
            "FieldSig ArchSig measurement handoff rejects profile witnessFamily; use the law-equation-surface input"
                .into(),
        );
    }
    let profile_id = profile
        .get("profileId")
        .and_then(|value| value.as_str())
        .unwrap_or_default();
    if profile_id.trim().is_empty() {
        return Err("FieldSig ArchSig measurement handoff requires profile.profileId".into());
    }
    for key in [
        "structuralVerdict",
        "computedInvariants",
        "analyticReadings",
        "assumptions",
        "suppliedData",
        "boundaryStatements",
        "nonConclusions",
    ] {
        if !packet.get(key).is_some_and(|value| value.is_array()) {
            return Err(
                format!("FieldSig ArchSig measurement handoff requires {key} array").into(),
            );
        }
    }
    validate_archsig_measurement_packet_structural_verdicts(packet)?;
    validate_archsig_measurement_packet_computed_invariants(packet)?;
    validate_archsig_measurement_packet_analytic_readings(packet)?;
    validate_archsig_measurement_packet_assumptions(packet)?;
    validate_archsig_measurement_packet_supplied_data(packet)?;
    Ok(())
}

fn validate_archsig_measurement_packet_structural_verdicts(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let invariant_ids = archsig_measurement_computed_invariant_ids(packet).collect::<BTreeSet<_>>();
    for (index, row) in packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let evaluator = required_string(row, "evaluator").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_string(row, "law").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let verdict = required_string(row, "verdict").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        if !matches!(
            verdict,
            "measured_zero" | "measured_nonzero" | "unmeasured" | "unknown" | "not_computed"
        ) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] has unsupported verdict {verdict}"
            )
            .into());
        }
        let data = row
            .get("verdictData")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires verdictData object"
                )
            })?;
        let zero = required_bool(data, "zero").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let non_zero = required_bool(data, "nonZero").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_bool(data, "inScope").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        required_object_string(data, "methodStatus").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] {message}")
        })?;
        let target = row
            .get("target")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires target object"
                )
            })?;
        for field in ["kind", "coverRef", "coefficient"] {
            required_object_string(target, field).map_err(|message| {
                format!("FieldSig ArchSig measurement handoff structuralVerdict[{index}] target {message}")
            })?;
        }
        target
            .get("scopeSize")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] target requires scopeSize object"
                )
            })?;
        let evidence = row
            .get("evidence")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] requires evidence object"
                )
            })?;
        evidence
            .get("computedInvariantRefs")
            .and_then(|value| value.as_array())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence requires computedInvariantRefs array"
                )
            })?;
        let computed_refs = evidence["computedInvariantRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|value| value.as_str())
            .collect::<Vec<_>>();
        for computed_ref in &computed_refs {
            if !invariant_ids.contains(computed_ref) {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence.computedInvariantRefs entry {computed_ref} does not resolve to computedInvariants[].invariantId"
                )
                .into());
            }
            if let Some(invariant_evaluator) =
                archsig_measurement_computed_invariant_evaluator(packet, computed_ref)
                && invariant_evaluator != evaluator
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence.computedInvariantRefs entry {computed_ref} has evaluator {invariant_evaluator}, expected {evaluator}"
                )
                .into());
            }
        }
        evidence
            .get("sourceRefs")
            .and_then(|value| value.as_array())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] evidence requires sourceRefs array"
                )
            })?;
        if zero && non_zero {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] for {evaluator} marks both zero and nonZero"
            )
            .into());
        }
        match verdict {
            "measured_zero" if !zero || non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_zero requires zero=true and nonZero=false"
                )
                .into());
            }
            "measured_nonzero" if zero || !non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_nonzero requires zero=false and nonZero=true"
                )
                .into());
            }
            "unknown" | "unmeasured" | "not_computed" if zero || non_zero => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} must not carry zero/nonZero measured flags"
                )
                .into());
            }
            _ => {}
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") && computed_refs.is_empty() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} requires non-empty evidence.computedInvariantRefs"
            )
            .into());
        }
        if verdict == "measured_nonzero" {
            let class_ref = target
                .get("classRef")
                .and_then(|value| value.as_str())
                .unwrap_or_default();
            let resolves = invariant_ids.contains(class_ref)
                || class_ref
                    .strip_prefix("computedInvariants/")
                    .is_some_and(|id| invariant_ids.contains(id));
            if !resolves {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] measured_nonzero target.classRef {class_ref} does not resolve to computed invariant evidence"
                )
                .into());
            }
            let class_ref_id = class_ref
                .strip_prefix("computedInvariants/")
                .unwrap_or(class_ref);
            if let Some(invariant_evaluator) =
                archsig_measurement_computed_invariant_evaluator(packet, class_ref_id)
                && invariant_evaluator != evaluator
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] target.classRef has evaluator {invariant_evaluator}, expected {evaluator}"
                )
                .into());
            }
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero") {
            if let Some(cert_ref) = data.get("certRef").and_then(|value| value.as_str()) {
                let cert_ref_id = cert_ref
                    .strip_prefix("computedInvariants/")
                    .unwrap_or(cert_ref);
                if let Some(invariant_evaluator) =
                    archsig_measurement_computed_invariant_evaluator(packet, cert_ref_id)
                    && invariant_evaluator != evaluator
                {
                    return Err(format!(
                        "FieldSig ArchSig measurement handoff structuralVerdict[{index}] certRef has evaluator {invariant_evaluator}, expected {evaluator}"
                    )
                    .into());
                }
            }
        }
        if matches!(verdict, "measured_zero" | "measured_nonzero")
            && !archsig_measurement_verdict_has_evidence(packet, row, evaluator)
        {
            return Err(format!(
                "FieldSig ArchSig measurement handoff structuralVerdict[{index}] {verdict} requires certRef or matching computed invariant evidence"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_computed_invariants(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    for (index, row) in packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        for field in ["invariantId", "kind"] {
            required_string(row, field).map_err(|message| {
                format!(
                    "FieldSig ArchSig measurement handoff computedInvariants[{index}] {message}"
                )
            })?;
        }
        let kind = row["kind"].as_str().unwrap_or_default();
        if !ARCHSIG_COMPUTED_INVARIANT_KINDS.contains(&kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] has unsupported kind {kind}"
            )
            .into());
        }
        if row.get("value").is_none() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] requires value"
            )
            .into());
        }
        if row.get("representation").is_none() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff computedInvariants[{index}] requires representation"
            )
            .into());
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_analytic_readings(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    for (index, row) in packet
        .get("analyticReadings")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        required_string(row, "readingId").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        required_string(row, "evaluator").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        let claim_status = required_string(row, "claimStatus").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        if !matches!(claim_status, "certified" | "candidate") {
            return Err(format!(
                "FieldSig ArchSig measurement handoff analyticReadings[{index}] has unsupported claimStatus {claim_status}"
            )
            .into());
        }
        let fidelity = required_string(row, "fidelity").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff analyticReadings[{index}] {message}")
        })?;
        if !matches!(fidelity, "faithful" | "proxy") {
            return Err(format!(
                "FieldSig ArchSig measurement handoff analyticReadings[{index}] has unsupported fidelity {fidelity}"
            )
            .into());
        }
    }
    Ok(())
}

fn archsig_measurement_verdict_has_evidence(
    packet: &serde_json::Value,
    row: &serde_json::Value,
    evaluator: &str,
) -> bool {
    let invariant_ids = archsig_measurement_computed_invariant_ids(packet).collect::<BTreeSet<_>>();
    if let Some(cert_ref) = row
        .get("verdictData")
        .and_then(|data| data.get("certRef"))
        .and_then(|value| value.as_str())
    {
        let cert_ref = cert_ref.trim();
        if cert_ref.is_empty() {
            return false;
        }
        return cert_ref
            .strip_prefix("computedInvariants/")
            .is_some_and(|invariant_id| invariant_ids.contains(invariant_id));
    }
    let computed_refs = row["evidence"]["computedInvariantRefs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str())
        .collect::<Vec<_>>();
    if !computed_refs.is_empty() {
        return computed_refs.iter().all(|id| invariant_ids.contains(id));
    }
    let certificate_prefixes = archsig_measurement_certificate_invariant_prefixes(evaluator);
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .any(|invariant| {
            invariant
                .get("evaluator")
                .and_then(|value| value.as_str())
                .is_some_and(|value| value == evaluator)
                && ["invariantId", "readingId", "id"].iter().any(|key| {
                    invariant
                        .get(*key)
                        .and_then(|value| value.as_str())
                        .is_some_and(|value| {
                            let value = value.trim();
                            if value.is_empty() {
                                return false;
                            }
                            certificate_prefixes
                                .map(|prefixes| {
                                    prefixes.iter().any(|prefix| value.starts_with(prefix))
                                })
                                .unwrap_or(true)
                        })
                })
        })
}

fn archsig_measurement_computed_invariant_ids(
    packet: &serde_json::Value,
) -> impl Iterator<Item = &str> {
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .flat_map(|invariant| {
            ["invariantId", "readingId", "id"]
                .into_iter()
                .filter_map(|key| {
                    invariant
                        .get(key)
                        .and_then(|value| value.as_str())
                        .map(str::trim)
                        .filter(|value| !value.is_empty())
                })
        })
}

fn archsig_measurement_computed_invariant_evaluator(
    packet: &serde_json::Value,
    reference: &str,
) -> Option<String> {
    packet
        .get("computedInvariants")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .find(|invariant| {
            ["invariantId", "readingId", "id"].iter().any(|key| {
                invariant
                    .get(*key)
                    .and_then(|value| value.as_str())
                    .is_some_and(|value| value == reference)
            })
        })
        .and_then(|invariant| invariant.get("evaluator"))
        .and_then(|value| value.as_str())
        .map(ToOwned::to_owned)
}

fn archsig_measurement_certificate_invariant_prefixes(
    evaluator: &str,
) -> Option<&'static [&'static str]> {
    match evaluator {
        "ag.cech-obstruction" => Some(&["cech-cohomology:"]),
        "ag.law-conflict-tor" => Some(&["law-conflict-tor:"]),
        "ag.square-free-repair" => Some(&["square-free-repair:"]),
        "ag.restriction-compatibility" => Some(&["restriction-compatibility:"]),
        "ag.section-factorization" => Some(&["section-factorization:"]),
        "ag.boundary-residue" => Some(&["boundary-residue:"]),
        "ag.coherence-obstruction" => Some(&["coherence-obstruction:"]),
        _ => None,
    }
}

fn validate_archsig_measurement_packet_assumptions(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut assumption_ids = BTreeSet::new();
    let mut violated_assumption_ids = BTreeSet::new();
    for (index, row) in packet
        .get("assumptions")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let assumption_id = required_string(row, "assumptionId").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        let _theorem_ref = required_string(row, "theoremRef").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        assumption_ids.insert(assumption_id.to_string());
        required_string(row, "assumption").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        let status = required_string(row, "status").map_err(|message| {
            format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
        })?;
        match status {
            "checked" => {
                required_string(row, "checkedBy").map_err(|message| {
                    format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
                })?;
            }
            "assumed" => {
                required_string(row, "assumedBy").map_err(|message| {
                    format!("FieldSig ArchSig measurement handoff assumptions[{index}] {message}")
                })?;
            }
            "violated" => {
                violated_assumption_ids.insert(assumption_id.to_string());
            }
            _ => {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff assumptions[{index}] has unsupported status {status}"
                )
                .into());
            }
        }
    }
    for (index, row) in packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
    {
        let verdict = row
            .get("verdict")
            .and_then(|value| value.as_str())
            .unwrap_or_default();
        for dependency in row
            .get("dependsOnAssumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|value| value.as_str())
        {
            if !assumption_ids.contains(dependency) {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] dependsOnAssumptions entry {dependency} does not resolve to an assumptionId"
                )
                .into());
            }
            if matches!(verdict, "measured_zero" | "measured_nonzero")
                && violated_assumption_ids.contains(dependency)
            {
                return Err(format!(
                    "FieldSig ArchSig measurement handoff structuralVerdict[{index}] keeps measured verdict while depending on violated assumption {dependency}"
                )
                .into());
            }
        }
    }
    Ok(())
}

fn validate_archsig_measurement_packet_supplied_data(
    packet: &serde_json::Value,
) -> Result<(), Box<dyn std::error::Error>> {
    let supplied = packet
        .get("suppliedData")
        .and_then(|value| value.as_array())
        .ok_or("FieldSig ArchSig measurement handoff requires suppliedData array")?;
    if supplied.is_empty() {
        return Err(
            "FieldSig ArchSig measurement handoff requires non-empty suppliedData ledger".into(),
        );
    }
    for (index, row) in supplied.iter().enumerate() {
        for field in ["suppliedId", "kind", "sourceArtifactRef"] {
            required_string(row, field).map_err(|message| {
                format!("FieldSig ArchSig measurement handoff suppliedData[{index}] {message}")
            })?;
        }
        let kind = row["kind"].as_str().unwrap_or_default();
        if !ARCHSIG_SUPPLIED_DATA_KINDS.contains(&kind) {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] has unsupported kind {kind}"
            )
            .into());
        }
        let conformance = row
            .get("conformance")
            .and_then(|value| value.as_object())
            .ok_or_else(|| {
                format!(
                    "FieldSig ArchSig measurement handoff suppliedData[{index}] requires conformance object"
                )
            })?;
        let status = conformance
            .get("status")
            .and_then(|value| value.as_str())
            .unwrap_or_default();
        if status.trim().is_empty() {
            return Err(format!(
                "FieldSig ArchSig measurement handoff suppliedData[{index}] requires conformance.status"
            )
            .into());
        }
    }
    Ok(())
}

fn required_string<'a>(
    object: &'a serde_json::Value,
    key: &str,
) -> Result<&'a str, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_str())
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| format!("requires non-empty {key}").into())
}

fn required_bool(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<bool, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_bool())
        .ok_or_else(|| format!("requires boolean verdictData.{key}").into())
}

fn required_object_string<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<&'a str, Box<dyn std::error::Error>> {
    object
        .get(key)
        .and_then(|value| value.as_str())
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| format!("requires non-empty verdictData.{key}").into())
}

fn archsig_measurement_packet_sft_source_refs(
    packet: &serde_json::Value,
    input_path: &str,
) -> Vec<String> {
    let mut refs = vec![format!("source:archsig-measurement-packet:{input_path}")];
    if let Some(packet_id) = packet.get("packetId").and_then(|value| value.as_str()) {
        refs.push(format!("archsigMeasurementPacket:{packet_id}"));
    }
    if let Some(profile_id) = json_path_string(packet, &["profile"], "profileId") {
        refs.push(format!("archsigMeasurementProfile:{profile_id}"));
    }
    if let Some(fingerprints) = packet
        .get("componentFingerprints")
        .and_then(|value| value.as_object())
    {
        for component in ["lawPolicy", "lawSurface", "measurementProfile"] {
            if let Some(fingerprint) = fingerprints.get(component).and_then(|value| value.as_str())
            {
                refs.push(format!(
                    "archsigMeasurementComponentFingerprint:{component}:{fingerprint}"
                ));
            }
        }
    }
    refs.extend(
        packet
            .get("suppliedData")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter(|entry| {
                entry.get("kind").and_then(|value| value.as_str()) == Some("law-equation-surface")
            })
            .filter_map(|entry| {
                entry
                    .get("sourceArtifactRef")
                    .and_then(|value| value.as_str())
                    .map(|source| format!("archsigMeasurementLawSurface:{source}"))
            }),
    );
    refs.extend(
        packet
            .get("structuralVerdict")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|verdict| {
                let mut refs = Vec::new();
                if let Some(verdict_ref) =
                    verdict.get("verdictRef").and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementStructuralVerdict:{verdict_ref}"));
                }
                if let Some(evaluator) = verdict.get("evaluator").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementStructuralEvaluator:{evaluator}"));
                }
                if let Some(law) = verdict.get("law").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementStructuralLaw:{law}"));
                }
                if let Some(cert_ref) = verdict
                    .get("verdictData")
                    .and_then(|data| data.get("certRef"))
                    .and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementCert:{cert_ref}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|invariant| {
                let mut refs = Vec::new();
                for key in ["invariantId", "readingId", "id"] {
                    if let Some(id) = invariant.get(key).and_then(|value| value.as_str()) {
                        refs.push(format!("archsigMeasurementComputedInvariant:{id}"));
                    }
                }
                if let Some(evaluator) = invariant.get("evaluator").and_then(|value| value.as_str())
                {
                    refs.push(format!("archsigMeasurementComputedEvaluator:{evaluator}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|reading| {
                let mut refs = Vec::new();
                if let Some(id) = reading.get("readingId").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementAnalyticReading:{id}"));
                }
                if let Some(evaluator) = reading.get("evaluator").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementAnalyticEvaluator:{evaluator}"));
                }
                refs
            }),
    );
    refs.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|assumption| {
                let assumption_id = assumption.get("assumptionId")?.as_str()?;
                let status = assumption
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!(
                    "archsigMeasurementAssumption:{assumption_id}:{status}"
                ))
            }),
    );
    refs.extend(
        packet
            .get("boundaryStatements")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|boundary| {
                let mut refs = Vec::new();
                if let Some(id) = boundary.get("id").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryStatement:{id}"));
                }
                if let Some(kind) = boundary.get("kind").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryKind:{kind}"));
                }
                refs
            }),
    );
    unique_strings(refs)
}

fn archsig_measurement_packet_action_candidate_ids(packet: &serde_json::Value) -> Vec<String> {
    let mut ids = json_object_string_array(packet, &["structuralVerdict"], "evaluator");
    ids.extend(json_object_string_array(
        packet,
        &["structuralVerdict"],
        "law",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["computedInvariants"],
        "evaluator",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["analyticReadings"],
        "evaluator",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["computedInvariants"],
        "invariantId",
    ));
    ids.extend(json_object_string_array(
        packet,
        &["analyticReadings"],
        "readingId",
    ));
    if ids.is_empty() {
        ids.push(
            packet
                .get("packetId")
                .and_then(|value| value.as_str())
                .unwrap_or("archsig-measurement-packet")
                .to_string(),
        );
    }
    unique_strings(ids)
}

fn archsig_measurement_packet_candidate_families(
    packet: &serde_json::Value,
    source_ref_ids: &[String],
    action_class_candidate_ids: &[String],
) -> Vec<CandidateOperationFamilyV0> {
    let non_conclusions = archsig_measurement_packet_sft_non_conclusions(packet);
    let mut families = packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, row)| {
            let evaluator = row
                .get("evaluator")
                .and_then(|value| value.as_str())
                .unwrap_or("ag-structural-evaluator");
            let law = row
                .get("law")
                .and_then(|value| value.as_str())
                .unwrap_or("selected-ag-law");
            let verdict = row
                .get("verdict")
                .and_then(|value| value.as_str())
                .unwrap_or("not_computed");
            let row_key = archsig_measurement_structural_row_key(index, row);
            CandidateOperationFamilyV0 {
                family_id: format!("family:archsig-measurement:{}", stable_id(&row_key)),
                operation_family: format!("review-ag-structural-{verdict}"),
                support_kind: "measurement-packet-structural-verdict".to_string(),
                action_class_candidate_ids: vec![evaluator.to_string(), law.to_string()],
                source_ref_ids: source_ref_ids.to_vec(),
                confidence: if matches!(verdict, "measured_zero" | "measured_nonzero") {
                    "medium"
                } else {
                    "low"
                }
                .to_string(),
                rationale:
                    "structural verdict is read from ArchSig measurement packet as current AG measurement state"
                        .to_string(),
                assumptions: Vec::new(),
                non_conclusions: non_conclusions.clone(),
            }
        })
        .collect::<Vec<_>>();
    families.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|reading| {
                let reading_id = reading.get("readingId")?.as_str()?;
                let evaluator = reading
                    .get("evaluator")
                    .and_then(|value| value.as_str())
                    .unwrap_or("ag-analytic-evaluator");
                let regime = reading
                    .get("regime")
                    .and_then(|value| value.as_str())
                    .unwrap_or("analytic");
                Some(CandidateOperationFamilyV0 {
                    family_id: format!(
                        "family:archsig-measurement-analytic:{}",
                        stable_id(reading_id)
                    ),
                    operation_family: format!("review-ag-analytic-{regime}"),
                    support_kind: "measurement-packet-analytic-reading".to_string(),
                    action_class_candidate_ids: vec![reading_id.to_string(), evaluator.to_string()],
                    source_ref_ids: source_ref_ids.to_vec(),
                    confidence: "low".to_string(),
                    rationale:
                        "analytic reading is retained as bounded measurement state, not converted into a structural verdict"
                            .to_string(),
                    assumptions: Vec::new(),
                    non_conclusions: non_conclusions.clone(),
                })
            }),
    );
    if families.is_empty() {
        families.push(CandidateOperationFamilyV0 {
            family_id: "family:archsig-measurement-review-only".to_string(),
            operation_family: "review-selected-archsig-measurement".to_string(),
            support_kind: "measurement-packet-review-boundary".to_string(),
            action_class_candidate_ids: action_class_candidate_ids.to_vec(),
            source_ref_ids: source_ref_ids.to_vec(),
            confidence: "low".to_string(),
            rationale:
                "no structural verdict or analytic reading is present; FieldSig keeps the packet as review input"
                    .to_string(),
            assumptions: vec!["selected MeasurementProfile may not cover all future SFT axes"
                .to_string()],
            non_conclusions,
        });
    }
    families
}

fn archsig_measurement_structural_row_key(index: usize, row: &serde_json::Value) -> String {
    let evaluator = row
        .get("evaluator")
        .and_then(|value| value.as_str())
        .unwrap_or("ag-structural-evaluator");
    let law = row
        .get("law")
        .and_then(|value| value.as_str())
        .unwrap_or("selected-ag-law");
    let verdict = row
        .get("verdict")
        .and_then(|value| value.as_str())
        .unwrap_or("not_computed");
    let cert_ref = row
        .get("verdictData")
        .and_then(|value| value.get("certRef"))
        .and_then(|value| value.as_str())
        .unwrap_or("no-cert");
    format!("{index}:{evaluator}:{law}:{verdict}:{cert_ref}")
}

fn archsig_measurement_packet_unknown_remainders(
    packet: &serde_json::Value,
    family_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<OperationSupportUnknownRemainderV0> {
    let mut remainders = Vec::new();
    remainders.extend(
        packet
        .get("structuralVerdict")
        .and_then(|value| value.as_array())
        .into_iter()
        .flatten()
        .enumerate()
        .filter_map(|(index, row)| {
            let verdict = row.get("verdict")?.as_str()?;
            if !matches!(verdict, "not_computed" | "unknown" | "unmeasured") {
                return None;
            }
                let evaluator = row
                    .get("evaluator")
                    .and_then(|value| value.as_str())
                    .unwrap_or("ag-structural-evaluator");
                let reason = row
                .get("reason")
                .and_then(|value| value.as_str())
                .unwrap_or("structural verdict is outside the selected finite measurement boundary");
            let row_key = archsig_measurement_structural_row_key(index, row);
            Some(OperationSupportUnknownRemainderV0 {
                remainder_id: format!(
                    "unknown:archsig-measurement:structural:{}",
                    stable_id(&row_key)
                ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec![verdict.to_string()],
                    reason: format!("ArchSig measurement evaluator {evaluator} returned {verdict}: {reason}"),
                    treatment: "carry as unknown remainder; do not round to absence, zero-valued support, forecast truth, or repair safety".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|invariant| {
                let status = invariant.get("status")?.as_str()?;
                if status != "not_computed" {
                    return None;
                }
                let id = invariant
                    .get("invariantId")
                    .or_else(|| invariant.get("id"))
                    .and_then(|value| value.as_str())
                    .unwrap_or("computed-invariant");
                Some(OperationSupportUnknownRemainderV0 {
                    remainder_id: format!(
                        "unknown:archsig-measurement:computed:{}",
                        stable_id(id)
                    ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec!["computedInvariant:not_computed".to_string()],
                    reason: format!("ArchSig measurement computed invariant {id} is not_computed"),
                    treatment: "carry as unknown remainder; do not synthesize zero analytic or structural support".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .enumerate()
            .filter_map(|(index, assumption)| {
                let status = assumption.get("status")?.as_str()?;
                if status == "checked" {
                    return None;
                }
                let assumption_id = assumption
                    .get("assumptionId")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let theorem_ref = assumption
                    .get("theoremRef")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let assumption_text = assumption
                    .get("assumption")
                    .and_then(|value| value.as_str())
                    .unwrap_or("assumption");
                let assumption_key = format!("{index}:{assumption_id}:{theorem_ref}:{assumption_text}:{status}");
                Some(OperationSupportUnknownRemainderV0 {
                    remainder_id: format!(
                        "unknown:archsig-measurement:assumption:{}",
                        stable_id(&assumption_key)
                    ),
                    affected_family_ids: family_ids.to_vec(),
                    source_ref_ids: source_ref_ids.to_vec(),
                    unknown_axes: vec![format!("assumption:{status}")],
                    reason: format!("ArchSig measurement assumption {assumption_id} ({theorem_ref}) is {status}: {assumption_text}"),
                    treatment: "retain assumption status as boundary data; do not promote it to proof, forecast truth, or repair safety".to_string(),
                    non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
                })
            }),
    );
    remainders.push(OperationSupportUnknownRemainderV0 {
        remainder_id: "unknown:archsig-measurement:fieldsig-evolution-boundary".to_string(),
        affected_family_ids: family_ids.to_vec(),
        source_ref_ids: source_ref_ids.to_vec(),
        unknown_axes: vec![
            "PR diff evidence".to_string(),
            "workflow history".to_string(),
            "operational outcome".to_string(),
            "unselected laws outside MeasurementProfile".to_string(),
        ],
        reason:
            "ArchSig measurement packet records current AG measurement state, not FieldSig evolution evidence"
                .to_string(),
        treatment:
            "retain as FieldSig-side unknown remainder; require separate workflow evidence before forecast or governance readings"
                .to_string(),
        non_conclusions: archsig_measurement_packet_sft_non_conclusions(packet),
    });
    remainders
}

fn archsig_measurement_packet_measurement_boundary_refs(packet: &serde_json::Value) -> Vec<String> {
    let mut refs = Vec::new();
    if let Some(profile_id) = json_path_string(packet, &["profile"], "profileId") {
        refs.push(format!("archsigMeasurementProfile:{profile_id}"));
    }
    refs.extend(
        packet
            .get("structuralVerdict")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|row| {
                let evaluator = row.get("evaluator")?.as_str()?;
                let verdict = row
                    .get("verdict")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!("archsigMeasurementVerdict:{evaluator}:{verdict}"))
            }),
    );
    refs.extend(
        packet
            .get("computedInvariants")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|invariant| {
                let id = invariant
                    .get("invariantId")
                    .or_else(|| invariant.get("id"))?
                    .as_str()?;
                let status = invariant
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("computed");
                Some(format!("archsigMeasurementInvariant:{id}:{status}"))
            }),
    );
    refs.extend(
        packet
            .get("analyticReadings")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|reading| {
                let id = reading.get("readingId")?.as_str()?;
                let regime = reading
                    .get("regime")
                    .and_then(|value| value.as_str())
                    .unwrap_or("analytic");
                Some(format!("archsigMeasurementAnalytic:{id}:{regime}"))
            }),
    );
    refs.extend(
        packet
            .get("assumptions")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .filter_map(|assumption| {
                let assumption_id = assumption.get("assumptionId")?.as_str()?;
                let status = assumption
                    .get("status")
                    .and_then(|value| value.as_str())
                    .unwrap_or("unknown");
                Some(format!(
                    "archsigMeasurementAssumptionBoundary:{assumption_id}:{status}"
                ))
            }),
    );
    refs.extend(
        packet
            .get("boundaryStatements")
            .and_then(|value| value.as_array())
            .into_iter()
            .flatten()
            .flat_map(|boundary| {
                let mut refs = Vec::new();
                if let Some(id) = boundary.get("id").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryStatement:{id}"));
                }
                if let Some(kind) = boundary.get("kind").and_then(|value| value.as_str()) {
                    refs.push(format!("archsigMeasurementBoundaryKind:{kind}"));
                }
                if let Some(scope_refs) =
                    boundary.get("scopeRefs").and_then(|value| value.as_array())
                {
                    refs.extend(scope_refs.iter().filter_map(|scope| {
                        scope
                            .as_str()
                            .map(|scope| format!("archsigMeasurementBoundaryScope:{scope}"))
                    }));
                }
                refs
            }),
    );
    unique_strings(refs)
}

fn archsig_measurement_packet_sft_non_conclusions(packet: &serde_json::Value) -> Vec<String> {
    let mut values = json_string_array(packet, &["nonConclusions"]);
    values.extend(
        OPERATION_SUPPORT_REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string()),
    );
    values.extend([
        "ArchSig measurement packet is FieldSig input state, not forecast correctness".to_string(),
        "raw ArchMap observations are not promoted to SFT ground truth".to_string(),
        "analytic readings are not converted into structural verdicts".to_string(),
        "not_computed measurements and violated assumptions are unknown remainder, not measured zero".to_string(),
        "FieldSig handoff does not prove causal correctness, repair safety, or global architecture safety".to_string(),
    ]);
    unique_strings(values)
}

fn archsig_measurement_packet_evidence_boundary_non_conclusions(
    packet: &serde_json::Value,
) -> Vec<String> {
    let mut values = json_string_array(packet, &["nonConclusions"]);
    values.extend(
        OPERATION_SUPPORT_EVIDENCE_BOUNDARY_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string()),
    );
    values.extend([
        "ArchSig measurement packet evidence boundary does not complete ArchMap observation coverage".to_string(),
        "FieldSig handoff evidence boundary does not prove forecast correctness".to_string(),
        "unsupported constructs remain outside the selected measurement profile".to_string(),
    ]);
    unique_strings(values)
}

pub fn build_air_from_archmap(
    document: &ArchMapDocumentV0,
    input_path: &str,
    sig0: Option<&Sig0Document>,
) -> AirDocumentV0 {
    let conflicts = explicit_and_derived_conflicts(document, sig0);
    let artifact_id = "artifact-archmap".to_string();
    let mut artifacts = vec![AirArtifact {
        artifact_id: artifact_id.clone(),
        kind: "archmap".to_string(),
        schema_version: Some(document.schema_version.clone()),
        path: Some(input_path.to_string()),
        content_hash: None,
        produced_by: document.generator.tool.clone(),
    }];
    if let Some(source_inventory_ref) = &document.source_inventory_ref {
        artifacts.push(AirArtifact {
            artifact_id: source_inventory_ref.artifact_id.clone(),
            kind: source_inventory_ref
                .kind
                .clone()
                .unwrap_or_else(|| "source_inventory".to_string()),
            schema_version: None,
            path: source_inventory_ref.path.clone(),
            content_hash: source_inventory_ref.content_hash.clone(),
            produced_by: document.generator.tool.clone(),
        });
    }

    let mut evidence = vec![AirEvidence {
        evidence_id: "evidence-archmap-artifact".to_string(),
        kind: "manual_annotation".to_string(),
        artifact_ref: Some(artifact_id.clone()),
        path: Some(input_path.to_string()),
        symbol: None,
        line: None,
        rule_id: Some(document.schema_version.clone()),
        confidence: Some("medium".to_string()),
    }];
    if let Some(source_inventory_ref) = &document.source_inventory_ref {
        evidence.push(AirEvidence {
            evidence_id: "evidence-archmap-source-inventory".to_string(),
            kind: "manual_annotation".to_string(),
            artifact_ref: Some(source_inventory_ref.artifact_id.clone()),
            path: source_inventory_ref.path.clone(),
            symbol: None,
            line: None,
            rule_id: Some(document.schema_version.clone()),
            confidence: Some("medium".to_string()),
        });
    }
    let mut source_evidence_ids = BTreeMap::new();
    for source_ref in all_source_refs(document) {
        let key = source_ref_key(source_ref);
        if source_evidence_ids.contains_key(&key) {
            continue;
        }
        let evidence_id = format!(
            "evidence-archmap-source-{:04}",
            source_evidence_ids.len() + 1
        );
        source_evidence_ids.insert(key, evidence_id.clone());
        evidence.push(AirEvidence {
            evidence_id,
            kind: "manual_annotation".to_string(),
            artifact_ref: Some(artifact_id.clone()),
            path: source_ref.path.clone(),
            symbol: source_ref.symbol.clone(),
            line: source_ref.line,
            rule_id: source_ref.section.clone(),
            confidence: Some("medium".to_string()),
        });
    }

    let mut components = Vec::new();
    let mut component_ids = BTreeSet::new();
    for item in &document.map_items {
        if item.mapping_kind == "object" {
            if let Some(id) = item.target_ref.id.clone() {
                if component_ids.insert(id.clone()) {
                    components.push(AirComponent {
                        id,
                        kind: "archmap-component".to_string(),
                        lifecycle: "after".to_string(),
                        owner: None,
                        evidence_refs: evidence_refs_for_item(item, &source_evidence_ids),
                    });
                }
            }
        }
    }
    for item in &document.map_items {
        for id in [&item.target_ref.from, &item.target_ref.to]
            .into_iter()
            .flatten()
        {
            if component_ids.insert(id.clone()) {
                components.push(AirComponent {
                    id: id.clone(),
                    kind: "archmap-component".to_string(),
                    lifecycle: "after".to_string(),
                    owner: None,
                    evidence_refs: evidence_refs_for_item(item, &source_evidence_ids),
                });
            }
        }
    }

    let mut relations = Vec::new();
    let mut claims = Vec::new();
    let mut architecture_paths = Vec::new();
    let mut semantic_diagrams = Vec::new();
    let mut nonfillability_witnesses = Vec::new();
    for (index, item) in document.map_items.iter().enumerate() {
        let claim_id = format!("claim-archmap-{}", item.map_item_id);
        let evidence_refs = evidence_refs_for_item(item, &source_evidence_ids);
        if (item.mapping_kind == "relation" || item.target_ref.kind == "air-relation")
            && item.target_ref.layer.as_deref() != Some("runtime")
        {
            if let (Some(from), Some(to)) = (&item.target_ref.from, &item.target_ref.to) {
                relations.push(AirRelation {
                    id: item
                        .target_ref
                        .id
                        .clone()
                        .unwrap_or_else(|| format!("relation-archmap-{:04}", index + 1)),
                    layer: item
                        .target_ref
                        .layer
                        .clone()
                        .unwrap_or_else(|| "semantic".to_string()),
                    from_component: Some(from.clone()),
                    to_component: Some(to.clone()),
                    kind: "archmap-relation".to_string(),
                    lifecycle: "after".to_string(),
                    protected_by: None,
                    extraction_rule: Some("archmap-schema050-projection".to_string()),
                    evidence_refs: evidence_refs.clone(),
                });
            }
        }
        if item.mapping_kind == "semanticDiagram"
            || item.mapping_kind == "semanticCommutationClaim"
            || item.target_ref.kind == "semantic-diagram"
        {
            let lhs = item
                .target_ref
                .lhs_path_ref
                .clone()
                .unwrap_or_else(|| format!("path-{}-lhs", item.map_item_id));
            let rhs = item
                .target_ref
                .rhs_path_ref
                .clone()
                .unwrap_or_else(|| format!("path-{}-rhs", item.map_item_id));
            architecture_paths.push(AirArchitecturePath {
                path_id: lhs.clone(),
                source_state: item
                    .target_ref
                    .from
                    .clone()
                    .unwrap_or_else(|| "selected-source".to_string()),
                target_state: item
                    .target_ref
                    .to
                    .clone()
                    .unwrap_or_else(|| "selected-target".to_string()),
                steps: item.preserves.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
            architecture_paths.push(AirArchitecturePath {
                path_id: rhs.clone(),
                source_state: item
                    .target_ref
                    .from
                    .clone()
                    .unwrap_or_else(|| "selected-source".to_string()),
                target_state: item
                    .target_ref
                    .to
                    .clone()
                    .unwrap_or_else(|| "selected-target".to_string()),
                steps: item.forgets.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
            semantic_diagrams.push(AirSemanticDiagram {
                id: item
                    .target_ref
                    .id
                    .clone()
                    .unwrap_or_else(|| format!("diagram-{}", item.map_item_id)),
                lhs_path_ref: lhs,
                rhs_path_ref: rhs,
                equivalence: item
                    .target_ref
                    .equivalence
                    .clone()
                    .unwrap_or_else(|| item.measurement_boundary.clone()),
                filler_claim_ref: Some(claim_id.clone()),
                nonfillability_witness_refs: Vec::new(),
                observation_refs: evidence_refs.clone(),
                lifecycle: "after".to_string(),
                evidence_refs: evidence_refs.clone(),
            });
        }
        if item.mapping_kind == "nonfillabilityWitness"
            || item.target_ref.kind == "nonfillability-witness"
        {
            nonfillability_witnesses.push(AirNonfillabilityWitness {
                witness_id: item
                    .target_ref
                    .id
                    .clone()
                    .unwrap_or_else(|| format!("witness-{}", item.map_item_id)),
                diagram_ref: item
                    .target_ref
                    .subject_ref
                    .clone()
                    .unwrap_or_else(|| "diagram-unresolved".to_string()),
                witness_kind: "archmap-nonfillability-witness".to_string(),
                claim_ref: claim_id.clone(),
                evidence_refs: evidence_refs.clone(),
            });
        }
        claims.push(air_claim_from_item(item, claim_id, evidence_refs));
    }
    for conflict in &conflicts {
        claims.push(air_claim_from_conflict(conflict));
    }

    AirDocumentV0 {
        schema_version: AIR_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        architecture_id: document.architecture_id.clone(),
        ids: AirIdPolicies {
            component_id_policy: "archmap targetRef id/from/to".to_string(),
            relation_id_policy: "archmap targetRef id or stable ordinal".to_string(),
            evidence_id_policy: "archmap source ref stable ordinal".to_string(),
            claim_id_policy: "archmap mapItemId and conflict id".to_string(),
        },
        revision: AirRevision {
            before: None,
            after: document.generated_at.clone(),
        },
        feature: AirFeature {
            feature_id: Some(document.map_id.clone()),
            title: Some("ArchMap supplied JSON projection".to_string()),
            description: Some("AIR generated from supplied archmap-schema050 artifact".to_string()),
            source: "manual".to_string(),
            ai_session: None,
        },
        artifacts,
        evidence,
        components,
        relations,
        policies: AirPolicies {
            laws: document
                .map_items
                .iter()
                .filter(|item| item.mapping_kind == "policyBoundary")
                .map(|item| item.map_item_id.clone())
                .collect(),
            boundaries: document.generation_boundary.scope.clone(),
            allowed_edges: Vec::new(),
            forbidden_edges: conflicts
                .iter()
                .filter(|conflict| conflict.category == "policy-disagreement")
                .map(|conflict| conflict.subject_ref.clone())
                .collect(),
            abstraction_rules: Vec::new(),
            protection_rules: Vec::new(),
        },
        semantic_diagrams,
        architecture_paths,
        homotopy_generators: Vec::new(),
        nonfillability_witnesses,
        signature: AirSignature {
            axes: archmap_signature_axes(document),
        },
        coverage: archmap_air_coverage(document, &conflicts),
        claims,
        operation_trace: AirOperationTrace {
            operations: Vec::new(),
        },
        extension: AirExtension {
            embedding_claim_ref: None,
            feature_view_claim_ref: None,
            interaction_claim_refs: Vec::new(),
            split_claim_ref: None,
            split_status: "unmeasured".to_string(),
        },
    }
}

fn json_string_array(packet: &serde_json::Value, path: &[&str]) -> Vec<String> {
    let mut current = packet;
    for key in path {
        let Some(next) = current.get(*key) else {
            return Vec::new();
        };
        current = next;
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str().map(ToOwned::to_owned))
        .collect()
}

fn json_object_string_array(packet: &serde_json::Value, path: &[&str], key: &str) -> Vec<String> {
    let mut current = packet;
    for segment in path {
        let Some(next) = current.get(*segment) else {
            return Vec::new();
        };
        current = next;
    }
    current
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|value| value.get(key)?.as_str().map(ToOwned::to_owned))
        .collect()
}

fn check_archmap_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "archmap-schema-version-supported",
        "ArchMap schema version is supported",
        if schema_version == ARCHMAP_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("unsupported schema: {schema_version}"));
    }
    check
}

fn check_source_inventory_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut missing = Vec::new();
    if document.source_universe.included_refs.is_empty() {
        missing.push(generic_validation_example(
            "sourceUniverse.includedRefs",
            "empty",
            "bounded source inventory must enumerate included refs",
        ));
    }
    if document
        .source_universe
        .selection_boundary
        .trim()
        .is_empty()
    {
        missing.push(generic_validation_example(
            "sourceUniverse.selectionBoundary",
            "empty",
            "source inventory selection boundary must be explicit",
        ));
    }
    if document.generation_boundary.non_conclusions.is_empty()
        && document.non_conclusions.is_empty()
    {
        missing.push(generic_validation_example(
            "generationBoundary.nonConclusions",
            "empty",
            "LLM generation boundary must preserve non-conclusions",
        ));
    }
    check_from_examples(
        "archmap-source-inventory-boundary",
        "Source inventory keeps included / excluded / unavailable / private boundary explicit",
        missing,
        "fail",
    )
}

fn check_source_inventory_artifact(
    document: &ArchMapDocumentV0,
    source_inventory: Option<&ArchMapSourceInventoryInput<'_>>,
) -> ValidationCheck {
    let Some(source_inventory_ref) = &document.source_inventory_ref else {
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            vec![generic_validation_example(
                "sourceInventoryRef",
                "missing",
                "source inventory artifact ref is absent; input boundary remains embedded only",
            )],
        );
    };

    let mut examples = Vec::new();
    let expected_path = source_inventory_ref.path.as_deref().unwrap_or_default();
    if expected_path.trim().is_empty() {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            "empty",
            "source inventory artifact path must be explicit",
        ));
    }

    let Some(source_inventory) = source_inventory else {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            expected_path,
            "source inventory artifact was not supplied to validation",
        ));
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            examples,
        );
    };

    if source_inventory.path != expected_path {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            source_inventory.path,
            "loaded source inventory path differs from ArchMap sourceInventoryRef.path",
        ));
    }
    if let Some(read_error) = &source_inventory.read_error {
        examples.push(generic_validation_example(
            "sourceInventoryRef.path",
            expected_path,
            read_error,
        ));
    }

    let Some(inventory) = source_inventory.document else {
        return warning_check_from_examples(
            "archmap-source-inventory-artifact",
            "Source inventory artifact ref is present and matches sourceUniverse",
            examples,
        );
    };

    if inventory.schema_version != ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION {
        examples.push(generic_validation_example(
            "sourceInventory.schema",
            &inventory.schema_version,
            "source inventory schema version is unsupported",
        ));
    }
    if inventory.root != document.source_universe.root {
        examples.push(generic_validation_example(
            "sourceInventory.root",
            &inventory.root,
            "source inventory root differs from ArchMap sourceUniverse.root",
        ));
    }
    if inventory.selection_boundary != document.source_universe.selection_boundary {
        examples.push(generic_validation_example(
            "sourceInventory.selectionBoundary",
            &inventory.selection_boundary,
            "source inventory selection boundary differs from ArchMap sourceUniverse",
        ));
    }

    compare_source_ref_sets(
        &mut examples,
        "includedRefs",
        &inventory.included_refs,
        &document.source_universe.included_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "excludedRefs",
        &inventory.excluded_refs,
        &document.source_universe.excluded_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "unavailableRefs",
        &inventory.unavailable_refs,
        &document.source_universe.unavailable_refs,
    );
    compare_source_ref_sets(
        &mut examples,
        "privateRefs",
        &inventory.private_refs,
        &document.source_universe.private_refs,
    );

    compare_artifact_ref_sets(
        &mut examples,
        "hashes",
        &inventory.hashes,
        &document.source_universe.hashes,
    );

    let mut check = warning_check_from_examples(
        "archmap-source-inventory-artifact",
        "Source inventory artifact ref is present and matches sourceUniverse",
        examples,
    );
    if check.result == "pass" {
        check.count = Some(
            inventory.included_refs.len()
                + inventory.excluded_refs.len()
                + inventory.unavailable_refs.len()
                + inventory.private_refs.len(),
        );
        check.reason = Some(
            "source inventory preserves included, excluded, unavailable, private, hash, and selection boundary categories"
                .to_string(),
        );
    }
    check
}

fn check_archmap_unique_map_item_ids(document: &ArchMapDocumentV0) -> ValidationCheck {
    let duplicate_ids = duplicates(
        document
            .map_items
            .iter()
            .map(|item| item.map_item_id.as_str()),
    );
    let examples = duplicate_ids
        .iter()
        .map(|id| generic_validation_example("mapItems[].mapItemId", id, "duplicate map item id"))
        .collect();
    check_from_examples(
        "archmap-map-item-ids-unique",
        "ArchMap map item ids are unique",
        examples,
        "fail",
    )
}

fn check_source_refs(document: &ArchMapDocumentV0) -> ValidationCheck {
    let included: BTreeSet<String> = document
        .source_universe
        .included_refs
        .iter()
        .map(source_ref_key)
        .collect();
    let examples: Vec<_> = document
        .map_items
        .iter()
        .flat_map(|item| {
            let included = &included;
            item.source_refs.iter().filter_map(move |source_ref| {
                let key = source_ref_key(source_ref);
                (!included.contains(&key)).then(|| {
                    generic_validation_example(
                        &format!("mapItems[{}].sourceRefs", item.map_item_id),
                        &key,
                        "source ref is outside includedRefs and is preserved as a dangling boundary",
                    )
                })
            })
        })
        .collect();
    check_from_examples(
        "archmap-source-refs-resolve",
        "Map item source refs resolve inside the selected source inventory",
        examples,
        "warn",
    )
}

fn check_measured_claim_evidence(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| item.claim_classification == "measured" && item.source_refs.is_empty())
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                &item.measurement_boundary,
                "measured ArchMap claim must cite source refs",
            )
        })
        .collect();
    check_from_examples(
        "archmap-measured-claims-have-evidence",
        "Measured ArchMap claims carry evidence refs",
        examples,
        "fail",
    )
}

fn check_missing_evidence_not_measured_zero(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| {
            item.measurement_boundary == "measuredZero" && !item.missing_evidence.is_empty()
        })
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                "measuredZero",
                "missing evidence cannot be rounded to measured zero",
            )
        })
        .collect();
    check_from_examples(
        "archmap-missing-evidence-not-measured-zero",
        "Missing evidence is not rounded to measured zero",
        examples,
        "fail",
    )
}

fn check_srp_evidence_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| is_srp_item(item))
        .filter(|item| {
            item.semantic_role.is_none()
                || item.responsibility_regions.is_empty()
                || item.reason_to_change.is_empty()
                || item.law_refs.is_empty()
        })
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                "SRP",
                "SRP review cue must keep semanticRole, responsibilityRegions, reasonToChange, and lawRefs typed",
            )
        })
        .collect();
    check_from_examples(
        "archmap-srp-evidence-boundary-typed",
        "SRP review cues keep typed semantic evidence",
        examples,
        "warn",
    )
}

fn is_srp_item(item: &ArchMapMapItem) -> bool {
    item.law_refs.iter().any(|law| law.contains("SRP"))
        || item
            .preserves
            .iter()
            .any(|preserve| preserve.to_ascii_lowercase().contains("srp"))
        || item.map_item_id.to_ascii_lowercase().contains("srp")
}

fn check_semantic_coverage(document: &ArchMapDocumentV0) -> ValidationCheck {
    let has_semantic_item = document.map_items.iter().any(|item| {
        item.mapping_kind.starts_with("semantic")
            || item.mapping_kind == "nonfillabilityWitness"
            || item.target_ref.layer.as_deref() == Some("semantic")
    });
    let semantic_recorded = document
        .coverage
        .measured_layers
        .iter()
        .chain(document.coverage.unmeasured_layers.iter())
        .chain(document.coverage.assumed_layers.iter())
        .any(|layer| layer == "semantic");
    let mut examples = Vec::new();
    if has_semantic_item && !semantic_recorded {
        examples.push(generic_validation_example(
            "coverage",
            "semantic",
            "semantic map items require measured, assumed, or unmeasured semantic coverage",
        ));
    }
    check_from_examples(
        "archmap-semantic-coverage-boundary",
        "Semantic coverage is explicit and is not inferred from absence",
        examples,
        "fail",
    )
}

fn check_conflicts(document: &ArchMapDocumentV0, sig0: Option<&Sig0Document>) -> ValidationCheck {
    let conflicts = explicit_and_derived_conflicts(document, sig0);
    let mut check = validation_check(
        "archmap-conflicts-preserved-as-review-cues",
        "ArchMap conflicts are preserved as review cues instead of resolved claims",
        if conflicts.is_empty() { "pass" } else { "warn" },
    );
    check.count = Some(conflicts.len());
    check.examples = conflicts
        .iter()
        .take(10)
        .map(|conflict| {
            generic_validation_example(
                &conflict.category,
                &conflict.subject_ref,
                &conflict.description,
            )
        })
        .collect();
    check
}

fn check_formal_promotion_guardrail(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples: Vec<_> = document
        .map_items
        .iter()
        .filter(|item| {
            matches!(item.claim_classification.as_str(), "proved" | "formal")
                && item.theorem_refs.is_empty()
        })
        .map(|item| {
            generic_validation_example(
                &item.map_item_id,
                &item.claim_classification,
                "formal/proved claim requires theorem refs and is not inferred from LLM output",
            )
        })
        .collect();
    check_from_examples(
        "archmap-formal-promotion-guardrail",
        "LLM-authored claims are not promoted to formal/proved theorem claims",
        examples,
        "fail",
    )
}

fn check_projection_separation(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    let has_aat = document.map_items.iter().any(is_aat_facing_item);
    let has_sft = document.map_items.iter().any(is_sft_facing_item);
    if !has_aat {
        examples.push(generic_validation_example(
            "mapItems[]",
            "aat-facing",
            "AAT-facing projection has no selected map item",
        ));
    }
    if !has_sft {
        examples.push(generic_validation_example(
            "mapItems[]",
            "sft-facing",
            "SFT-facing projection has no selected map item",
        ));
    }
    examples.extend(document.map_items.iter().filter_map(|item| {
        (is_sft_facing_item(item)
            && matches!(item.claim_classification.as_str(), "proved" | "formal"))
        .then(|| {
            generic_validation_example(
                &item.map_item_id,
                &item.claim_classification,
                "SFT-facing forecast input item must not be promoted to a Lean theorem claim",
            )
        })
    }));
    check_from_examples(
        "archmap-aat-sft-projection-separation",
        "AAT-facing and SFT-facing projections remain separate bounded readings",
        examples,
        "warn",
    )
}

fn archmap_atomic_observation_checks(document: &ArchMapDocumentV0) -> Vec<ValidationCheck> {
    vec![
        check_atomic_candidate_ids_unique(document),
        check_atom_candidates_have_source_evidence(document),
        check_obstruction_circuit_boundary(document),
        check_observation_gaps_are_not_measured_zero(document),
    ]
}

fn check_atomic_candidate_ids_unique(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    examples.extend(
        duplicates(
            document
                .atom_candidates
                .iter()
                .map(|candidate| candidate.atom_candidate_id.as_str()),
        )
        .iter()
        .map(|id| {
            generic_validation_example(
                "atomCandidates[].atomCandidateId",
                id,
                "duplicate atom candidate id",
            )
        }),
    );
    examples.extend(
        duplicates(
            document
                .molecule_candidates
                .iter()
                .map(|candidate| candidate.molecule_candidate_id.as_str()),
        )
        .iter()
        .map(|id| {
            generic_validation_example(
                "moleculeCandidates[].moleculeCandidateId",
                id,
                "duplicate molecule candidate id",
            )
        }),
    );
    examples.extend(
        duplicates(
            document
                .obstruction_circuit_candidates
                .iter()
                .map(|candidate| candidate.circuit_candidate_id.as_str()),
        )
        .iter()
        .map(|id| {
            generic_validation_example(
                "obstructionCircuitCandidates[].circuitCandidateId",
                id,
                "duplicate circuit candidate id",
            )
        }),
    );
    examples.extend(
        duplicates(
            document
                .observation_gaps
                .iter()
                .map(|gap| gap.gap_id.as_str()),
        )
        .iter()
        .map(|id| {
            generic_validation_example(
                "observationGaps[].gapId",
                id,
                "duplicate observation gap id",
            )
        }),
    );
    check_from_examples(
        "archmap-atomic-candidate-ids-unique",
        "Atomic observation candidate ids are unique inside each candidate family",
        examples,
        "fail",
    )
}

fn check_atom_candidates_have_source_evidence(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = document
        .atom_candidates
        .iter()
        .filter(|candidate| {
            candidate.measurement_boundary == "measuredNonzero" && candidate.source_refs.is_empty()
        })
        .map(|candidate| {
            generic_validation_example(
                &candidate.atom_candidate_id,
                &candidate.atom_family,
                "observed atom candidate must cite source refs; ArchMap does not certify unsupported atoms",
            )
        })
        .collect::<Vec<_>>();
    examples.extend(
        document
            .atom_candidates
            .iter()
            .filter(|candidate| {
                matches!(
                    candidate.observation_status.as_str(),
                    "certified" | "proved" | "groundTruth"
                )
            })
            .map(|candidate| {
                generic_validation_example(
                    &candidate.atom_candidate_id,
                    &candidate.observation_status,
                    "ArchMap may observe atom candidates, but must not certify universal atoms",
                )
            }),
    );
    check_from_examples(
        "archmap-atom-candidates-are-observed-not-certified",
        "Atom candidates preserve source evidence and are not certified as universal atoms by ArchMap",
        examples,
        "fail",
    )
}

fn check_obstruction_circuit_boundary(document: &ArchMapDocumentV0) -> ValidationCheck {
    let mut examples = document
        .atom_candidates
        .iter()
        .filter(|candidate| {
            candidate
                .atom_family
                .to_ascii_lowercase()
                .contains("obstruction")
        })
        .map(|candidate| {
            generic_validation_example(
                &candidate.atom_candidate_id,
                &candidate.atom_family,
                "obstruction belongs in obstructionCircuitCandidates, not atomCandidates",
            )
        })
        .collect::<Vec<_>>();
    examples.extend(
        document
            .obstruction_circuit_candidates
            .iter()
            .filter(|candidate| {
                candidate.atom_candidate_refs.is_empty()
                    && candidate.molecule_candidate_refs.is_empty()
            })
            .map(|candidate| {
                generic_validation_example(
                    &candidate.circuit_candidate_id,
                    &candidate.circuit_kind,
                    "obstruction circuit candidate should point to atom or molecule candidates when available",
                )
            }),
    );
    check_from_examples(
        "archmap-obstruction-circuits-are-not-atoms",
        "Obstruction circuits are composed review witnesses, not primitive architecture atoms",
        examples,
        "fail",
    )
}

fn check_observation_gaps_are_not_measured_zero(document: &ArchMapDocumentV0) -> ValidationCheck {
    let examples = document
        .observation_gaps
        .iter()
        .filter(|gap| {
            matches!(
                gap.evidence_status.as_str(),
                "measuredZero" | "observedAbsent" | "absent"
            )
        })
        .map(|gap| {
            generic_validation_example(
                &gap.gap_id,
                &gap.evidence_status,
                "observation gap must remain unknown/private/unavailable/out-of-scope, not measured zero",
            )
        })
        .collect::<Vec<_>>();
    check_from_examples(
        "archmap-observation-gaps-not-measured-zero",
        "Observation gaps are retained as gaps instead of absence claims",
        examples,
        "fail",
    )
}

fn archmap_atomic_observation_summary(
    document: &ArchMapDocumentV0,
) -> ArchMapAtomicObservationSummary {
    let atom_candidate_count = document.atom_candidates.len();
    let molecule_candidate_count = document.molecule_candidates.len();
    let obstruction_circuit_candidate_count = document.obstruction_circuit_candidates.len();
    let observation_gap_count = document.observation_gaps.len();
    ArchMapAtomicObservationSummary {
        atom_candidate_count,
        observed_atom_count: document
            .atom_candidates
            .iter()
            .filter(|candidate| {
                is_observed_atomic_boundary(
                    &candidate.observation_status,
                    &candidate.measurement_boundary,
                )
            })
            .count(),
        molecule_candidate_count,
        observed_molecule_count: document
            .molecule_candidates
            .iter()
            .filter(|candidate| candidate.observation_status == "observed")
            .count(),
        obstruction_circuit_candidate_count,
        observed_circuit_count: document
            .obstruction_circuit_candidates
            .iter()
            .filter(|candidate| {
                is_observed_atomic_boundary(
                    &candidate.observation_status,
                    &candidate.measurement_boundary,
                )
            })
            .count(),
        observation_gap_count,
        sft_handoff_ref_count: atom_candidate_count
            + obstruction_circuit_candidate_count
            + observation_gap_count,
        zero_curvature_reading:
            "zero curvature is read as absence of required obstruction circuits over observed atom arrangement, not as an ArchMap definition"
                .to_string(),
        boundary:
            "ArchMap records source-grounded atom, molecule, circuit, and gap candidates; AAT analysis decides theorem-facing meaning"
                .to_string(),
        non_conclusions: archmap_atomic_non_conclusions(),
    }
}

fn is_observed_atomic_boundary(observation_status: &str, measurement_boundary: &str) -> bool {
    matches!(observation_status, "observed" | "measured")
        || measurement_boundary == "measuredNonzero"
}

fn archmap_atomic_non_conclusions() -> Vec<String> {
    vec![
        "ArchMap atom candidate is not a certified ArchitectureAtom".to_string(),
        "responsibility is reported as a molecule over atom candidates, not as a primitive atom"
            .to_string(),
        "obstruction circuit candidate is not a primitive atom".to_string(),
        "observation gap is not measured zero".to_string(),
        "atomic observation summary does not prove zero curvature".to_string(),
        "atomic observation summary does not prove SFT forecast correctness".to_string(),
    ]
}

fn check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
    failure_result: &str,
) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if examples.is_empty() {
            "pass"
        } else {
            failure_result
        },
    );
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

fn warning_check_from_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    check_from_examples(id, title, examples, "warn")
}

fn compare_source_ref_sets(
    examples: &mut Vec<crate::ValidationExample>,
    field: &str,
    inventory_refs: &[ArchMapSourceRef],
    embedded_refs: &[ArchMapSourceRef],
) {
    let inventory_keys: BTreeSet<_> = inventory_refs.iter().map(source_ref_key).collect();
    let embedded_keys: BTreeSet<_> = embedded_refs.iter().map(source_ref_key).collect();
    for key in inventory_keys.difference(&embedded_keys) {
        examples.push(generic_validation_example(
            &format!("sourceInventory.{field}"),
            key,
            "source inventory ref is absent from embedded ArchMap sourceUniverse",
        ));
    }
    for key in embedded_keys.difference(&inventory_keys) {
        examples.push(generic_validation_example(
            &format!("sourceUniverse.{field}"),
            key,
            "embedded ArchMap sourceUniverse ref is absent from source inventory artifact",
        ));
    }
}

fn compare_artifact_ref_sets(
    examples: &mut Vec<crate::ValidationExample>,
    field: &str,
    inventory_refs: &[crate::ArchMapArtifactRef],
    embedded_refs: &[crate::ArchMapArtifactRef],
) {
    let inventory_keys: BTreeSet<_> = inventory_refs.iter().map(artifact_ref_key).collect();
    let embedded_keys: BTreeSet<_> = embedded_refs.iter().map(artifact_ref_key).collect();
    for key in inventory_keys.difference(&embedded_keys) {
        examples.push(generic_validation_example(
            &format!("sourceInventory.{field}"),
            key,
            "source inventory artifact hash is absent from embedded ArchMap sourceUniverse",
        ));
    }
    for key in embedded_keys.difference(&inventory_keys) {
        examples.push(generic_validation_example(
            &format!("sourceUniverse.{field}"),
            key,
            "embedded ArchMap sourceUniverse hash is absent from source inventory artifact",
        ));
    }
}

fn explicit_and_derived_conflicts(
    document: &ArchMapDocumentV0,
    sig0: Option<&Sig0Document>,
) -> Vec<ArchMapConflict> {
    let mut conflicts = document.conflicts.clone();
    conflicts.extend(document.map_items.iter().filter_map(|item| {
        item.conflict_category
            .as_ref()
            .map(|category| ArchMapConflict {
                conflict_id: format!("conflict-{}", item.map_item_id),
                category: category.clone(),
                subject_ref: item
                    .target_ref
                    .subject_ref
                    .clone()
                    .or_else(|| item.target_ref.id.clone())
                    .unwrap_or_else(|| item.map_item_id.clone()),
                description: format!("ArchMap item {} reports {}", item.map_item_id, category),
                source_refs: item.source_refs.clone(),
                non_conclusions: vec![
                    "conflict cue does not decide which source is correct".to_string(),
                ],
            })
    }));
    let included: BTreeSet<String> = document
        .source_universe
        .included_refs
        .iter()
        .map(source_ref_key)
        .collect();
    for item in &document.map_items {
        for source_ref in &item.source_refs {
            let key = source_ref_key(source_ref);
            if !included.contains(&key) {
                conflicts.push(ArchMapConflict {
                    conflict_id: format!("conflict-source-ref-dangling-{}", item.map_item_id),
                    category: "source-ref-dangling".to_string(),
                    subject_ref: key,
                    description: "map item cites a source ref outside sourceUniverse.includedRefs"
                        .to_string(),
                    source_refs: vec![source_ref.clone()],
                    non_conclusions: vec![
                        "dangling source ref is not measured zero".to_string(),
                        "validation does not infer source availability".to_string(),
                    ],
                });
            }
        }
    }
    if let Some(sig0) = sig0 {
        conflicts.extend(static_edge_conflicts(document, sig0));
    }
    unique_conflicts(conflicts)
}

fn static_edge_conflicts(
    document: &ArchMapDocumentV0,
    sig0: &Sig0Document,
) -> Vec<ArchMapConflict> {
    let static_edges: BTreeSet<(String, String)> = sig0
        .edges
        .iter()
        .map(|edge| (edge.source.clone(), edge.target.clone()))
        .collect();
    let archmap_edges: BTreeSet<(String, String)> = document
        .map_items
        .iter()
        .filter_map(|item| Some((item.target_ref.from.clone()?, item.target_ref.to.clone()?)))
        .collect();
    let mut conflicts = Vec::new();
    for (from, to) in archmap_edges.difference(&static_edges) {
        conflicts.push(ArchMapConflict {
            conflict_id: format!(
                "conflict-missing-static-edge-{}-{}",
                stable_id(from),
                stable_id(to)
            ),
            category: "missing-static-edge".to_string(),
            subject_ref: format!("{from}->{to}"),
            description: "ArchMap relation is not present in supplied Sig0 static edges"
                .to_string(),
            source_refs: Vec::new(),
            non_conclusions: vec![
                "semantic relation is not resolved by static extraction".to_string(),
            ],
        });
    }
    for (from, to) in static_edges.difference(&archmap_edges) {
        conflicts.push(ArchMapConflict {
            conflict_id: format!(
                "conflict-unexplained-static-edge-{}-{}",
                stable_id(from),
                stable_id(to)
            ),
            category: "unexplained-static-edge".to_string(),
            subject_ref: format!("{from}->{to}"),
            description: "Sig0 static edge has no ArchMap semantic explanation".to_string(),
            source_refs: Vec::new(),
            non_conclusions: vec![
                "unexplained static edge is a review cue, not a violation proof".to_string(),
            ],
        });
    }
    conflicts
}

fn unique_conflicts(conflicts: Vec<ArchMapConflict>) -> Vec<ArchMapConflict> {
    let mut seen = BTreeSet::new();
    conflicts
        .into_iter()
        .filter(|conflict| {
            seen.insert((
                conflict.category.clone(),
                conflict.subject_ref.clone(),
                conflict.description.clone(),
            ))
        })
        .collect()
}

fn archmap_air_coverage(
    document: &ArchMapDocumentV0,
    conflicts: &[ArchMapConflict],
) -> AirCoverage {
    let mut layers = Vec::new();
    for layer in ["static", "runtime", "semantic", "policy", "operation"] {
        let measured = document
            .coverage
            .measured_layers
            .iter()
            .any(|measured_layer| measured_layer == layer);
        let assumed = document
            .coverage
            .assumed_layers
            .iter()
            .any(|assumed_layer| assumed_layer == layer);
        let unmeasured = document
            .coverage
            .unmeasured_layers
            .iter()
            .any(|unmeasured_layer| unmeasured_layer == layer);
        let has_conflict = conflicts.iter().any(|conflict| {
            conflict.subject_ref.contains(layer) || conflict.category.contains(layer)
        });
        layers.push(AirCoverageLayer {
            layer: layer.to_string(),
            measurement_boundary: if measured {
                "measuredNonzero".to_string()
            } else {
                "unmeasured".to_string()
            },
            universe_refs: vec!["artifact-archmap".to_string()],
            measured_axes: measured
                .then(|| vec![format!("{layer}ArchMapCoverage")])
                .unwrap_or_default(),
            unmeasured_axes: if layer == "runtime" && !measured {
                vec!["runtimePropagation".to_string()]
            } else {
                (unmeasured || (!measured && !assumed) || assumed)
                    .then(|| vec![format!("{layer}ArchMapCoverage")])
                    .unwrap_or_default()
            },
            projection_rule: if layer == "runtime" && !measured {
                None
            } else {
                Some("archmap-schema050-to-air/v0.5.0".to_string())
            },
            extraction_scope: vec![document.source_universe.selection_boundary.clone()],
            exactness_assumptions: vec![
                "ArchMap projection preserves claim boundary but does not prove semantic preservation"
                    .to_string(),
            ],
            unsupported_constructs: unsupported_constructs_for_layer(document, layer, has_conflict),
        });
    }
    AirCoverage { layers }
}

fn unsupported_constructs_for_layer(
    document: &ArchMapDocumentV0,
    layer: &str,
    has_conflict: bool,
) -> Vec<String> {
    let mut constructs = document.coverage.unsupported_constructs.clone();
    if layer == "runtime" && !document.coverage.measured_layers.iter().any(|l| l == layer) {
        constructs.extend(document.source_universe.known_blind_spots.clone());
    }
    if has_conflict {
        constructs.push(format!("{layer} conflict requires human review"));
    }
    constructs.sort();
    constructs.dedup();
    constructs
}

fn archmap_signature_axes(document: &ArchMapDocumentV0) -> Vec<crate::AirSignatureAxis> {
    let mut axes: Vec<_> = ["static", "runtime", "semantic", "policy"]
        .into_iter()
        .map(|layer| {
            let measured = document
                .coverage
                .measured_layers
                .iter()
                .any(|measured_layer| measured_layer == layer);
            crate::AirSignatureAxis {
                axis: format!("{layer}ArchMapCoverage"),
                value: measured.then_some(1),
                measured,
                measurement_boundary: if measured {
                    "measuredNonzero".to_string()
                } else {
                    "unmeasured".to_string()
                },
                source: Some("archmap/v0.5.0".to_string()),
                reason: (!measured).then(|| format!("{layer} layer is not measured by ArchMap")),
            }
        })
        .collect();
    axes.push(crate::AirSignatureAxis {
        axis: "runtimePropagation".to_string(),
        value: None,
        measured: false,
        measurement_boundary: "unmeasured".to_string(),
        source: Some("archmap/v0.5.0".to_string()),
        reason: Some("runtime traces are not supplied by ArchMap MVP fixture".to_string()),
    });
    axes
}

fn air_claim_from_item(
    item: &ArchMapMapItem,
    claim_id: String,
    evidence_refs: Vec<String>,
) -> AirClaim {
    AirClaim {
        claim_id,
        subject_ref: item
            .target_ref
            .subject_ref
            .clone()
            .or_else(|| item.target_ref.id.clone())
            .unwrap_or_else(|| item.map_item_id.clone()),
        predicate: item
            .target_ref
            .predicate
            .clone()
            .unwrap_or_else(|| format!("ArchMap {} mapping", item.mapping_kind)),
        claim_level: "tooling".to_string(),
        claim_classification: item.claim_classification.clone(),
        measurement_boundary: item.measurement_boundary.clone(),
        theorem_refs: item.theorem_refs.clone(),
        evidence_refs,
        required_assumptions: archmap_item_required_assumptions(item),
        coverage_assumptions: item.preserves.clone(),
        exactness_assumptions: item.forgets.clone(),
        missing_preconditions: item.missing_evidence.clone(),
        non_conclusions: archmap_item_non_conclusions(item),
    }
}

pub fn archmap_lean_preservation_vocabulary() -> Vec<ArchMapLeanPreservationVocabularyEntry> {
    vec![
        lean_vocabulary_entry(
            "archmap-object-preservation",
            "mappingKind=object or targetRef.kind=air-component",
            "ObjectPreservation",
            "selected ArchMap object candidate preserves a bounded Lean object field",
        ),
        lean_vocabulary_entry(
            "archmap-relation-preservation",
            "mappingKind=relation or targetRef.kind=air-relation",
            "RelationPreservation",
            "selected ArchMap relation candidate preserves a bounded Lean relation field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-diagram-preservation",
            "mappingKind=semanticDiagram or targetRef.kind=semantic-diagram",
            "SemanticDiagramPreservation",
            "selected semantic diagram candidate preserves a bounded diagram field",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-commutation-preservation",
            "mappingKind=semanticCommutationClaim",
            "SemanticCommutationPreservation",
            "selected commutation claim candidate is tracked without proving commutation",
        ),
        lean_vocabulary_entry(
            "archmap-nonfillability-witness-preservation",
            "mappingKind=nonfillabilityWitness or targetRef.kind=nonfillability-witness",
            "NonfillabilityWitnessPreservation",
            "selected non-fillability witness candidate is preserved as review evidence",
        ),
        lean_vocabulary_entry(
            "archmap-law-policy-preservation",
            "mappingKind=policyBoundary, targetRef.layer=policy, or preserves[] contains Layered Architecture / SRP responsibility",
            "LawPolicyPreservation",
            "selected policy boundary candidate is tracked as supplied policy evidence",
        ),
        lean_vocabulary_entry(
            "archmap-contract-observation-preservation",
            "preserves[] contains contract preservation, contract-test observation, observation equivalence, or event sourcing projection",
            "SemanticDiagramPreservation",
            "selected contract or event-projection candidate is tracked as bounded semantic diagram evidence",
        ),
        lean_vocabulary_entry(
            "archmap-semantic-non-commutation-boundary",
            "preserves[] contains semantic non-commutation, saga compensation, or nonfillability witness",
            "NonfillabilityWitnessPreservation",
            "selected non-commutation or compensation candidate is preserved as bounded obstruction evidence",
        ),
        lean_vocabulary_entry(
            "archmap-flatness-precondition-preservation",
            "targetRef.subjectRef contains flatnessPrecondition or preserves contains flatness precondition boundary",
            "FlatnessPreconditionPreservation",
            "selected flatness precondition candidate is tracked without discharging flatness",
        ),
        lean_vocabulary_entry(
            "archmap-runtime-static-disagreement-boundary",
            "preserves[] contains runtime/static disagreement, framework convention boundary, or dynamic plugin blind spot",
            "CoverageExactnessBoundary",
            "review-only coverage boundary remains explicit and is not promoted to a preservation proof",
        ),
        lean_vocabulary_entry(
            "archmap-coverage-boundary",
            "coverage, missingEvidence, nonConclusions",
            "CoverageExactnessBoundary",
            "coverage gaps, exactness limits, missing evidence, and non-conclusions remain explicit",
        ),
    ]
}

pub fn archmap_lean_preservation_checklist(
    document: &ArchMapDocumentV0,
) -> Vec<ArchMapLeanPreservationChecklistEntry> {
    let mut entries: Vec<_> = document
        .map_items
        .iter()
        .map(|item| archmap_item_preservation_checklist_entry(document, item))
        .collect();
    entries.push(archmap_coverage_boundary_checklist_entry(document));
    entries.push(archmap_formal_promotion_guardrail_checklist_entry());
    entries
}

fn lean_vocabulary_entry(
    vocabulary_id: &str,
    archmap_selector: &str,
    lean_package_field: &str,
    preservation_role: &str,
) -> ArchMapLeanPreservationVocabularyEntry {
    ArchMapLeanPreservationVocabularyEntry {
        vocabulary_id: vocabulary_id.to_string(),
        archmap_selector: archmap_selector.to_string(),
        lean_package_field: lean_package_field.to_string(),
        preservation_role: preservation_role.to_string(),
        report_boundary:
            "tooling vocabulary records a preservation candidate; it is not a Lean proof witness"
                .to_string(),
    }
}

fn archmap_item_preservation_checklist_entry(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
) -> ArchMapLeanPreservationChecklistEntry {
    let lean_package_field = archmap_item_lean_package_field(item);
    let status = archmap_item_preservation_status(document, item, lean_package_field);
    let mut blocking_reasons = Vec::new();
    if !item.missing_evidence.is_empty() {
        blocking_reasons
            .push("missing evidence blocks preservation precondition discharge".to_string());
    }
    if status == "blockedByUnmeasuredCoverage" {
        blocking_reasons.push("unmeasured coverage remains a coverage gap".to_string());
    }
    if matches!(item.claim_classification.as_str(), "proved" | "formal")
        && item.theorem_refs.is_empty()
    {
        blocking_reasons.push(
            "formal promotion guardrail blocks theorem claim without theorem refs".to_string(),
        );
    }
    if lean_package_field == "OutOfScopeBoundary" {
        blocking_reasons
            .push("mapping kind is outside the ArchMapPreservationPackage vocabulary".to_string());
    }

    ArchMapLeanPreservationChecklistEntry {
        checklist_id: format!("archmap-preservation-{}", item.map_item_id),
        map_item_id: Some(item.map_item_id.clone()),
        lean_package_field: lean_package_field.to_string(),
        status: status.to_string(),
        candidate_sources: vec![
            format!("mappingKind={}", item.mapping_kind),
            format!("targetRef.kind={}", item.target_ref.kind),
        ],
        blocking_reasons,
        missing_evidence: item.missing_evidence.clone(),
        coverage_boundary: archmap_item_coverage_boundary(document, item),
        non_conclusions: archmap_item_non_conclusions(item),
    }
}

fn archmap_coverage_boundary_checklist_entry(
    document: &ArchMapDocumentV0,
) -> ArchMapLeanPreservationChecklistEntry {
    let mut blocking_reasons = Vec::new();
    if !document.coverage.unmeasured_layers.is_empty() {
        blocking_reasons.push(format!(
            "unmeasured layers remain: {}",
            document.coverage.unmeasured_layers.join(", ")
        ));
    }
    if !document.coverage.unsupported_constructs.is_empty() {
        blocking_reasons.push(format!(
            "unsupported constructs remain: {}",
            document.coverage.unsupported_constructs.join(", ")
        ));
    }
    ArchMapLeanPreservationChecklistEntry {
        checklist_id: "archmap-preservation-coverage-boundary".to_string(),
        map_item_id: None,
        lean_package_field: "CoverageExactnessBoundary".to_string(),
        status: if blocking_reasons.is_empty() {
            "candidate"
        } else {
            "blockedByUnmeasuredCoverage"
        }
        .to_string(),
        candidate_sources: vec!["coverage".to_string(), "nonConclusions".to_string()],
        blocking_reasons,
        missing_evidence: Vec::new(),
        coverage_boundary: format!(
            "measured=[{}]; unmeasured=[{}]; assumed=[{}]",
            document.coverage.measured_layers.join(", "),
            document.coverage.unmeasured_layers.join(", "),
            document.coverage.assumed_layers.join(", ")
        ),
        non_conclusions: archmap_non_conclusions(document),
    }
}

fn archmap_formal_promotion_guardrail_checklist_entry() -> ArchMapLeanPreservationChecklistEntry {
    ArchMapLeanPreservationChecklistEntry {
        checklist_id: "archmap-preservation-formal-promotion-guardrail".to_string(),
        map_item_id: None,
        lean_package_field: "FormalPromotionGuardrail".to_string(),
        status: "blockedByFormalPromotionGuardrail".to_string(),
        candidate_sources: vec![
            "archmap validation pass".to_string(),
            "AIR projection success".to_string(),
        ],
        blocking_reasons: vec![
            "validation and projection do not discharge ArchMapPreservationPackage fields"
                .to_string(),
        ],
        missing_evidence: vec![
            "Lean theorem witness not supplied by archmap-schema050".to_string(),
        ],
        coverage_boundary:
            "formal promotion requires explicit Lean theorem refs and discharged preconditions"
                .to_string(),
        non_conclusions: vec![
            "ArchMap validation pass is not a Lean theorem proof".to_string(),
            "AIR projection success is not a semantic preservation proof".to_string(),
        ],
    }
}

fn archmap_item_lean_package_field(item: &ArchMapMapItem) -> &'static str {
    let preserves_lower = item
        .preserves
        .iter()
        .map(|preserves| preserves.to_ascii_lowercase())
        .collect::<Vec<_>>();
    if item.mapping_kind == "object" || item.target_ref.kind == "air-component" {
        "ObjectPreservation"
    } else if item.mapping_kind == "relation" || item.target_ref.kind == "air-relation" {
        "RelationPreservation"
    } else if item.mapping_kind == "semanticCommutationClaim" {
        "SemanticCommutationPreservation"
    } else if item.mapping_kind == "semanticDiagram" || item.target_ref.kind == "semantic-diagram" {
        "SemanticDiagramPreservation"
    } else if item.mapping_kind == "nonfillabilityWitness"
        || item.target_ref.kind == "nonfillability-witness"
    {
        "NonfillabilityWitnessPreservation"
    } else if item.mapping_kind == "policyBoundary"
        || item.target_ref.layer.as_deref() == Some("policy")
        || preserves_lower.iter().any(|preserves| {
            preserves.contains("layered architecture")
                || preserves.contains("srp responsibility")
                || preserves.contains("reason-to-change")
        })
    {
        "LawPolicyPreservation"
    } else if preserves_lower.iter().any(|preserves| {
        preserves.contains("contract preservation")
            || preserves.contains("contract-test observation")
            || preserves.contains("observation equivalence")
            || preserves.contains("event sourcing projection")
    }) {
        "SemanticDiagramPreservation"
    } else if preserves_lower.iter().any(|preserves| {
        preserves.contains("semantic non-commutation")
            || preserves.contains("saga compensation")
            || preserves.contains("nonfillability witness")
            || preserves.contains("obstruction witness")
    }) {
        "NonfillabilityWitnessPreservation"
    } else if preserves_lower.iter().any(|preserves| {
        preserves.contains("runtime/static disagreement")
            || preserves.contains("framework convention boundary")
            || preserves.contains("dynamic plugin blind spot")
    }) {
        "CoverageExactnessBoundary"
    } else if item
        .target_ref
        .subject_ref
        .as_deref()
        .is_some_and(|subject_ref| subject_ref.contains("flatnessPrecondition"))
        || preserves_lower
            .iter()
            .any(|preserves| preserves.contains("flatness precondition"))
    {
        "FlatnessPreconditionPreservation"
    } else {
        "OutOfScopeBoundary"
    }
}

fn archmap_item_preservation_status(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
    lean_package_field: &str,
) -> &'static str {
    if lean_package_field == "OutOfScopeBoundary" {
        "notApplicableOutOfScope"
    } else if lean_package_field == "CoverageExactnessBoundary" {
        if item.missing_evidence.is_empty() && !archmap_item_has_unmeasured_coverage(document, item)
        {
            "candidate"
        } else {
            "blockedByUnmeasuredCoverage"
        }
    } else if matches!(item.claim_classification.as_str(), "proved" | "formal")
        && item.theorem_refs.is_empty()
    {
        "blockedByFormalPromotionGuardrail"
    } else if !item.missing_evidence.is_empty() {
        "blockedByMissingEvidence"
    } else if item.claim_classification == "assumed" || !item.required_assumptions.is_empty() {
        "satisfiedBySuppliedAssumption"
    } else if archmap_item_has_unmeasured_coverage(document, item) {
        "blockedByUnmeasuredCoverage"
    } else {
        "candidate"
    }
}

fn archmap_item_has_unmeasured_coverage(
    document: &ArchMapDocumentV0,
    item: &ArchMapMapItem,
) -> bool {
    item.measurement_boundary == "unmeasured"
        || item
            .target_ref
            .layer
            .as_ref()
            .is_some_and(|layer| document.coverage.unmeasured_layers.contains(layer))
}

fn archmap_item_coverage_boundary(document: &ArchMapDocumentV0, item: &ArchMapMapItem) -> String {
    let layer = item.target_ref.layer.as_deref().unwrap_or("unlayered");
    let layer_state = if document
        .coverage
        .measured_layers
        .iter()
        .any(|measured| measured == layer)
    {
        "measured"
    } else if document
        .coverage
        .assumed_layers
        .iter()
        .any(|assumed| assumed == layer)
    {
        "assumed"
    } else if document
        .coverage
        .unmeasured_layers
        .iter()
        .any(|unmeasured| unmeasured == layer)
    {
        "unmeasured"
    } else {
        "not listed"
    };
    format!(
        "layer={layer}; layerState={layer_state}; measurementBoundary={}",
        item.measurement_boundary
    )
}

fn archmap_item_required_assumptions(item: &ArchMapMapItem) -> Vec<String> {
    let mut required_assumptions = item.required_assumptions.clone();
    required_assumptions.push(format!(
        "ArchMapPreservationPackage.{} candidate",
        archmap_item_lean_package_field(item)
    ));
    if is_srp_item(item) {
        required_assumptions.push(
            "SRP probable violation requires LLM Review Skill judgment with evidence refs and policy refs"
                .to_string(),
        );
    }
    required_assumptions.sort();
    required_assumptions.dedup();
    required_assumptions
}

fn air_claim_from_conflict(conflict: &ArchMapConflict) -> AirClaim {
    AirClaim {
        claim_id: format!("claim-{}", conflict.conflict_id),
        subject_ref: conflict.subject_ref.clone(),
        predicate: format!("ArchMap conflict review cue: {}", conflict.category),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: vec!["evidence-archmap-artifact".to_string()],
        required_assumptions: Vec::new(),
        coverage_assumptions: vec![conflict.description.clone()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["human review of conflicting evidence".to_string()],
        non_conclusions: conflict.non_conclusions.clone(),
    }
}

fn archmap_item_non_conclusions(item: &ArchMapMapItem) -> Vec<String> {
    let mut non_conclusions = item.non_conclusions.clone();
    non_conclusions.push("ArchMap item is not architecture ground truth".to_string());
    non_conclusions.push("ArchMap item does not prove semantic preservation".to_string());
    non_conclusions.push(
        "ArchMap map item may support atom observation, but is not an atom certificate".to_string(),
    );
    if item.claim_classification != "proved" {
        non_conclusions.push("LLM-authored mapping is not a Lean theorem".to_string());
    }
    if is_srp_item(item) {
        non_conclusions.push("SRP cue is not a deterministic tool violation".to_string());
        non_conclusions.push(
            "SRP probableViolation requires review judgment with cited evidence and policy refs"
                .to_string(),
        );
    }
    non_conclusions.sort();
    non_conclusions.dedup();
    non_conclusions
}

fn archmap_non_conclusions(document: &ArchMapDocumentV0) -> Vec<String> {
    let mut non_conclusions = document.non_conclusions.clone();
    non_conclusions.extend(document.generation_boundary.non_conclusions.clone());
    non_conclusions.extend(archmap_atomic_non_conclusions());
    non_conclusions.push("ArchMap validation does not prove architecture lawfulness".to_string());
    non_conclusions.push("ArchMap validation does not prove semantic completeness".to_string());
    non_conclusions.sort();
    non_conclusions.dedup();
    non_conclusions
}

fn archmap_sft_candidate_families(
    document: &ArchMapDocumentV0,
    source_ref_ids: &[String],
) -> Vec<CandidateOperationFamilyV0> {
    let mut families = document
        .map_items
        .iter()
        .filter(|item| is_sft_facing_item(item))
        .map(|item| {
            let item_source_refs = retained_string_refs(
                &item
                    .source_refs
                    .iter()
                    .map(|source| format!("source:archmap:{}", source_ref_key(source)))
                    .collect::<Vec<_>>(),
                source_ref_ids,
            );
            CandidateOperationFamilyV0 {
                family_id: format!("family:archmap:{}", item.map_item_id),
                operation_family: archmap_sft_operation_family(item),
                support_kind: format!("archmap-{}-evidence", item.measurement_boundary),
                action_class_candidate_ids: vec![format!("candidate:archmap:{}", item.map_item_id)],
                source_ref_ids: item_source_refs,
                confidence: item.confidence.clone(),
                rationale: format!(
                    "Projected from ArchMap item {} without assigning forecast probability.",
                    item.map_item_id
                ),
                assumptions: item.required_assumptions.clone(),
                non_conclusions: archmap_sft_non_conclusions(),
            }
        })
        .collect::<Vec<_>>();
    if families.is_empty() {
        families.push(CandidateOperationFamilyV0 {
            family_id: "family:archmap:selected-boundary".to_string(),
            operation_family: "selected-archmap-boundary".to_string(),
            support_kind: "archmap-boundary-only".to_string(),
            action_class_candidate_ids: vec!["candidate:archmap:selected-boundary".to_string()],
            source_ref_ids: source_ref_ids.to_vec(),
            confidence: "low".to_string(),
            rationale: "ArchMap contains no SFT-facing item; retain the boundary as unknown input."
                .to_string(),
            assumptions: vec![
                "human review is required before SFT forecast construction".to_string(),
            ],
            non_conclusions: archmap_sft_non_conclusions(),
        });
    }
    families
}

fn archmap_sft_unknown_remainders(
    document: &ArchMapDocumentV0,
    family_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<OperationSupportUnknownRemainderV0> {
    let mut remainders = Vec::new();
    for item in &document.map_items {
        if !item.missing_evidence.is_empty() || item.measurement_boundary == "unmeasured" {
            remainders.push(OperationSupportUnknownRemainderV0 {
                remainder_id: format!("unknown:archmap:{}", item.map_item_id),
                affected_family_ids: family_ids.to_vec(),
                source_ref_ids: retained_string_refs(
                    &item
                        .source_refs
                        .iter()
                        .map(|source| format!("source:archmap:{}", source_ref_key(source)))
                        .collect::<Vec<_>>(),
                    source_ref_ids,
                ),
                unknown_axes: unique_strings(
                    item.missing_evidence
                        .iter()
                        .cloned()
                        .chain(std::iter::once(item.measurement_boundary.clone()))
                        .collect(),
                ),
                reason: format!(
                    "ArchMap item {} carries missing or unmeasured evidence",
                    item.map_item_id
                ),
                treatment: "retain as SFT input boundary; do not round to absence or measured zero"
                    .to_string(),
                non_conclusions: archmap_sft_non_conclusions(),
            });
        }
    }
    for gap in &document.observation_gaps {
        remainders.push(OperationSupportUnknownRemainderV0 {
            remainder_id: format!("unknown:archmap:gap:{}", gap.gap_id),
            affected_family_ids: family_ids.to_vec(),
            source_ref_ids: retained_string_refs(
                &gap.source_refs
                    .iter()
                    .map(|source| format!("source:archmap:{}", source_ref_key(source)))
                    .collect::<Vec<_>>(),
                source_ref_ids,
            ),
            unknown_axes: unique_strings(
                gap.expected_atom_families
                    .iter()
                    .cloned()
                    .chain(std::iter::once(gap.gap_kind.clone()))
                    .chain(std::iter::once(gap.evidence_status.clone()))
                    .collect(),
            ),
            reason: format!(
                "ArchMap observation gap {} is retained for SFT as unknown evidence",
                gap.gap_id
            ),
            treatment:
                "retain as atom observation gap; do not round to absence, safety, or measured zero"
                    .to_string(),
            non_conclusions: archmap_sft_non_conclusions(),
        });
    }
    if remainders.is_empty() {
        remainders.push(OperationSupportUnknownRemainderV0 {
            remainder_id: "unknown:archmap:private-unavailable-source-refs".to_string(),
            affected_family_ids: family_ids.to_vec(),
            source_ref_ids: source_ref_ids.to_vec(),
            unknown_axes: vec!["privateRefs".to_string(), "unavailableRefs".to_string()],
            reason: "ArchMap generation boundary may include private or unavailable refs"
                .to_string(),
            treatment: "retain boundary categories for later forecast and calibration artifacts"
                .to_string(),
            non_conclusions: archmap_sft_non_conclusions(),
        });
    }
    remainders
}

fn archmap_sft_action_candidate_ids(document: &ArchMapDocumentV0) -> Vec<String> {
    unique_strings(
        document
            .map_items
            .iter()
            .map(|item| format!("candidate:archmap:{}", item.map_item_id))
            .chain(
                document
                    .atom_candidates
                    .iter()
                    .map(|candidate| format!("atom:archmap:{}", candidate.atom_candidate_id)),
            )
            .chain(
                document
                    .obstruction_circuit_candidates
                    .iter()
                    .map(|candidate| format!("circuit:archmap:{}", candidate.circuit_candidate_id)),
            )
            .chain(
                document
                    .observation_gaps
                    .iter()
                    .map(|gap| format!("gap:archmap:{}", gap.gap_id)),
            )
            .collect(),
    )
}

fn archmap_sft_measurement_boundary_refs(document: &ArchMapDocumentV0) -> Vec<String> {
    unique_strings(
        vec![
            format!("archmap:{}", document.map_id),
            "docs/note/aat_sft_atomic_theory_v2.md#11-sft-integration".to_string(),
            "docs/note/aat_sft_atomic_theory_v2.md#12-atomic-reading-of-the-sft-grand-theorem"
                .to_string(),
        ]
        .into_iter()
        .chain(
            document
                .atom_candidates
                .iter()
                .map(|candidate| format!("archmapAtom:{}", candidate.atom_candidate_id)),
        )
        .chain(
            document
                .obstruction_circuit_candidates
                .iter()
                .map(|candidate| format!("archmapCircuit:{}", candidate.circuit_candidate_id)),
        )
        .chain(
            document
                .observation_gaps
                .iter()
                .map(|gap| format!("archmapObservationGap:{}", gap.gap_id)),
        )
        .collect(),
    )
}

fn archmap_sft_source_refs(document: &ArchMapDocumentV0) -> Vec<String> {
    let mut refs = Vec::new();
    refs.push(format!("source:archmap:{}", document.map_id));
    refs.extend(
        all_source_refs(document)
            .into_iter()
            .map(|source| format!("source:archmap:{}", source_ref_key(source))),
    );
    refs.extend(
        document
            .source_inventory_ref
            .iter()
            .map(|artifact| format!("source:archmap:{}", artifact.artifact_id)),
    );
    unique_strings(refs)
}

fn archmap_sft_operation_family(item: &ArchMapMapItem) -> String {
    let lower = item.mapping_kind.to_ascii_lowercase();
    if lower.contains("workflow") {
        "workflow".to_string()
    } else if lower.contains("event") {
        "event".to_string()
    } else if lower.contains("state") {
        "state-transition".to_string()
    } else if lower.contains("test") || item.source_refs.iter().any(|source| source.kind == "test")
    {
        "test-oracle".to_string()
    } else if item.target_ref.layer.as_deref() == Some("runtime") {
        "runtime-observation".to_string()
    } else if lower.contains("policy") {
        "proposal-force-candidate".to_string()
    } else if lower.contains("relation") || item.target_ref.kind == "air-relation" {
        "semantic-relation".to_string()
    } else {
        "operation-candidate".to_string()
    }
}

fn is_aat_facing_item(item: &ArchMapMapItem) -> bool {
    let target = item
        .target_ref
        .subject_ref
        .as_deref()
        .unwrap_or_default()
        .to_ascii_lowercase();
    item.preserves
        .iter()
        .any(|preserves| preserves.to_ascii_lowercase().contains("aat"))
        || target.contains("signature")
        || target.contains("flatness")
        || item
            .theorem_refs
            .iter()
            .any(|theorem| theorem.contains("ArchMap"))
}

fn is_sft_facing_item(item: &ArchMapMapItem) -> bool {
    matches!(
        item.mapping_kind.as_str(),
        "operation"
            | "workflow"
            | "event"
            | "state"
            | "transition"
            | "testOracle"
            | "runtimeObservation"
            | "proposalForceCandidate"
            | "relation"
            | "semanticRole"
            | "policyBoundary"
            | "nonfillabilityWitness"
    ) || item.target_ref.layer.as_deref() == Some("runtime")
        || item.preserves.iter().any(|preserves| {
            let lower = preserves.to_ascii_lowercase();
            lower.contains("operation")
                || lower.contains("workflow")
                || lower.contains("event")
                || lower.contains("runtime")
                || lower.contains("obstruction")
        })
}

fn archmap_sft_non_conclusions() -> Vec<String> {
    vec![
        "ArchMap-derived SFT input is not a forecast result".to_string(),
        "ArchMap confidence is review priority, not probability".to_string(),
        "ArchMap atom refs are observation refs, not certified universal atoms".to_string(),
        "ArchMap circuit refs are typed obstruction candidates, not primitive atoms".to_string(),
        "ArchMap observation gaps remain SFT unknown remainder".to_string(),
        "missing, private, unavailable, and unsupported evidence is not measured zero".to_string(),
        "SFT projection does not promote tooling evidence to a Lean theorem claim".to_string(),
    ]
}

fn retained_string_refs(candidate_refs: &[String], all_source_refs: &[String]) -> Vec<String> {
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

fn evidence_refs_for_item(
    item: &ArchMapMapItem,
    source_evidence_ids: &BTreeMap<String, String>,
) -> Vec<String> {
    let mut refs: Vec<String> = item
        .source_refs
        .iter()
        .filter_map(|source_ref| {
            source_evidence_ids
                .get(&source_ref_key(source_ref))
                .cloned()
        })
        .collect();
    refs.extend(item.evidence_refs.clone());
    if refs.is_empty() {
        refs.push("evidence-archmap-artifact".to_string());
    }
    refs.sort();
    refs.dedup();
    refs
}

fn all_source_refs(document: &ArchMapDocumentV0) -> Vec<&ArchMapSourceRef> {
    document
        .source_universe
        .included_refs
        .iter()
        .chain(document.source_universe.excluded_refs.iter())
        .chain(document.source_universe.unavailable_refs.iter())
        .chain(document.source_universe.private_refs.iter())
        .chain(document.generation_boundary.excluded_refs.iter())
        .chain(document.generation_boundary.unavailable_refs.iter())
        .chain(document.generation_boundary.private_refs.iter())
        .chain(
            document
                .map_items
                .iter()
                .flat_map(|item| item.source_refs.iter()),
        )
        .chain(
            document
                .atom_candidates
                .iter()
                .flat_map(|candidate| candidate.source_refs.iter()),
        )
        .chain(
            document
                .molecule_candidates
                .iter()
                .flat_map(|candidate| candidate.source_refs.iter()),
        )
        .chain(
            document
                .obstruction_circuit_candidates
                .iter()
                .flat_map(|candidate| candidate.source_refs.iter()),
        )
        .chain(
            document
                .observation_gaps
                .iter()
                .flat_map(|gap| gap.source_refs.iter()),
        )
        .collect()
}

fn source_ref_key(source_ref: &ArchMapSourceRef) -> String {
    if let Some(artifact_id) = &source_ref.artifact_id {
        return artifact_id.clone();
    }
    format!(
        "{}:{}:{}:{}:{}",
        source_ref.kind,
        source_ref.path.as_deref().unwrap_or(""),
        source_ref.symbol.as_deref().unwrap_or(""),
        source_ref
            .line
            .map(|line| line.to_string())
            .unwrap_or_default(),
        source_ref.section.as_deref().unwrap_or("")
    )
}

fn artifact_ref_key(artifact_ref: &crate::ArchMapArtifactRef) -> String {
    let mut parts = Vec::new();
    parts.push(format!("artifactId={}", artifact_ref.artifact_id));
    if let Some(kind) = &artifact_ref.kind {
        parts.push(format!("kind={kind}"));
    }
    if let Some(path) = &artifact_ref.path {
        parts.push(format!("path={path}"));
    }
    if let Some(content_hash) = &artifact_ref.content_hash {
        parts.push(format!("contentHash={content_hash}"));
    }
    parts.join("|")
}

fn stable_id(value: &str) -> String {
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

fn unique_strings(values: Vec<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    values
        .into_iter()
        .filter(|value| seen.insert(value.clone()))
        .collect()
}
