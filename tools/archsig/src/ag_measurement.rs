use std::collections::BTreeSet;

use serde_json::{Value, json};

use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, AgAnalyticReadingV1, AgAssumptionLedgerEntryV1,
    AgStructuralVerdictV1, AgVerdictDataV1, ArchSigMeasurementPacketV1, LawPolicyDocumentV1,
    MeasurementProfileV1, NormalizedArchMapV2, ValidationCheck, ValidationExample,
};

const VERDICTS: [&str; 5] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
];

pub fn selected_measurement_profile_v1(
    policy: &LawPolicyDocumentV1,
) -> Option<&MeasurementProfileV1> {
    let profile_ref = policy.measurement_profile_ref.as_deref()?;
    policy
        .measurement_profiles
        .iter()
        .find(|profile| profile.profile_id == profile_ref)
}

pub fn build_foundation_measurement_packet_v1(
    normalized: &NormalizedArchMapV2,
    policy: &LawPolicyDocumentV1,
    archmap_ref: &str,
    law_policy_ref: &str,
) -> Result<ArchSigMeasurementPacketV1, String> {
    let profile = selected_measurement_profile_v1(policy)
        .ok_or_else(|| "AG measurement packet requires measurementProfileRef".to_string())?
        .clone();
    validate_profile_refs(&profile, normalized)?;
    let structural_verdict = policy
        .policies
        .iter()
        .filter_map(|entry| {
            let evaluator = entry.evaluator.as_deref()?;
            evaluator.starts_with("ag.").then(|| AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry.law.clone().unwrap_or_else(|| evaluator.to_string()),
                verdict: "unmeasured".to_string(),
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: false,
                    non_zero: false,
                    method_status: "schema_foundation_only".to_string(),
                    cert_ref: None,
                },
                reason: Some(
                    "AG evaluator schema is registered; mathematical computation is implemented by follow-up evaluator issues".to_string(),
                ),
            })
        })
        .collect::<Vec<_>>();

    Ok(ArchSigMeasurementPacketV1 {
        schema: ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA.to_string(),
        packet_id: format!("measurement:{}", normalized.source_archmap_id),
        profile,
        structural_verdict,
        computed_invariants: vec![json!({
            "invariantId": "finite-poset-site-shape",
            "archmapRef": archmap_ref,
            "atomCount": normalized.summary.atom_count,
            "contextCount": normalized.summary.context_count,
            "coverCount": normalized.summary.cover_count,
            "doctrineFingerprint": normalized.summary.doctrine_fingerprint
        })],
        analytic_readings: vec![AgAnalyticReadingV1 {
            reading_id: "candidate-regime:stability-placeholder".to_string(),
            evaluator: "ag.foundation@1".to_string(),
            value: json!({
                "state": "not_evaluated",
                "reason": "theorem-candidate readings are analytic-only until a follow-up evaluator computes them"
            }),
            regime: Some("theorem-candidate".to_string()),
            structural_verdict_ref: None,
        }],
        assumptions: vec![
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/4.2".to_string(),
                assumption: "finite site".to_string(),
                status: "checked".to_string(),
                checked_by: Some("archmap-v2-validation.contexts-finite".to_string()),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/4.2".to_string(),
                assumption: "U-adequate cover".to_string(),
                status: "assumed".to_string(),
                checked_by: None,
                assumed_by: Some(format!(
                    "measurement-profile:{}",
                    policy
                        .measurement_profile_ref
                        .as_deref()
                        .unwrap_or_default()
                )),
            },
        ],
        non_conclusions: vec![
            format!(
                "ArchSig v0.4.0 foundation packet is computed from {archmap_ref} and {law_policy_ref}; it is not a Lean proof object."
            ),
            "Unmeasured AG evaluator rows are schema handoff rows, not measured zero.".to_string(),
            "Theorem-candidate readings are analytic-only and cannot generate structural verdicts."
                .to_string(),
        ],
    })
}

pub fn build_measurement_summary_v1(packet: &ArchSigMeasurementPacketV1) -> Value {
    let nonzero_count = packet
        .structural_verdict
        .iter()
        .filter(|verdict| verdict.verdict == "measured_nonzero")
        .count();
    let unmeasured_count = packet
        .structural_verdict
        .iter()
        .filter(|verdict| {
            matches!(
                verdict.verdict.as_str(),
                "unmeasured" | "unknown" | "not_computed"
            )
        })
        .count();
    let conclusion = if unmeasured_count > 0 {
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    } else if nonzero_count == 0 {
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    } else {
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    };
    json!({
        "schema": "archsig-analysis-summary/v2",
        "conclusion": conclusion,
        "measurementPacketSchema": packet.schema,
        "profileRef": packet.profile.profile_id,
        "structuralVerdictSummary": {
            "rowCount": packet.structural_verdict.len(),
            "measuredNonzeroCount": nonzero_count,
            "unmeasuredCount": packet.structural_verdict.iter().filter(|row| row.verdict == "unmeasured").count(),
            "nonTerminalCount": unmeasured_count
        },
        "assumptionSummary": {
            "checkedCount": packet.assumptions.iter().filter(|row| row.status == "checked").count(),
            "assumedCount": packet.assumptions.iter().filter(|row| row.status == "assumed").count(),
            "violatedCount": packet.assumptions.iter().filter(|row| row.status == "violated").count()
        },
        "nonConclusions": [
            "Summary conclusion is relative to MeasurementProfile and assumption ledger.",
            "Schema foundation rows do not claim completed AG invariant computation."
        ]
    })
}

pub fn build_measurement_viewer_data_v1(
    normalized: &NormalizedArchMapV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
) -> Value {
    json!({
        "schemaVersion": "archsig-atom-viewer-data-v2",
        "sourceArtifactRefs": {
            "normalizedArchMap": "normalized-archmap.json",
            "measurementPacket": "archsig-measurement-packet.json",
            "summary": "archsig-analysis-summary.json"
        },
        "reportPane": {
            "conclusion": summary["conclusion"],
            "profileRef": packet.profile.profile_id,
            "assumptionSummary": summary["assumptionSummary"],
            "structuralVerdictSummary": summary["structuralVerdictSummary"]
        },
        "finitePosetSite": {
            "atoms": normalized.atoms,
            "contexts": normalized.contexts,
            "covers": normalized.covers
        },
        "nonConclusions": [
            "Viewer data is a bounded projection of ArchMap v2 and measurement packet foundation rows.",
            "Layout and site visualization are not AG invariant values or Lean proof objects."
        ]
    })
}

fn validate_profile_refs(
    profile: &MeasurementProfileV1,
    normalized: &NormalizedArchMapV2,
) -> Result<(), String> {
    let site_resolves = profile.site_ref == "archmap:/contexts"
        || normalized.contexts.iter().any(|context| {
            context.normalized_context_id == profile.site_ref
                || context.source_context_id == profile.site_ref
        });
    if !site_resolves {
        return Err(format!(
            "measurementProfileRef {} has unresolved siteRef {}",
            profile.profile_id, profile.site_ref
        ));
    }

    let cover_resolves = normalized.covers.iter().any(|cover| {
        cover.normalized_cover_id == profile.cover_ref || cover.source_cover_id == profile.cover_ref
    });
    if !cover_resolves {
        return Err(format!(
            "measurementProfileRef {} has unresolved coverRef {}",
            profile.profile_id, profile.cover_ref
        ));
    }

    Ok(())
}

pub fn validate_measurement_packet_v1(packet: &ArchSigMeasurementPacketV1) -> Vec<ValidationCheck> {
    vec![
        check_packet_schema(packet),
        check_structural_verdict_values(packet),
        check_structural_verdict_data(packet),
        check_analytic_regime_boundary(packet),
        check_assumption_ledger(packet),
    ]
}

fn check_packet_schema(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut check = validation_check(
        "measurement-packet-v1-schema",
        "measurement packet uses archsig-measurement-packet/v1",
        if packet.schema == ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "expected {ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA}, found {}",
            packet.schema
        ));
    }
    check
}

fn check_structural_verdict_values(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let examples = packet
        .structural_verdict
        .iter()
        .filter(|row| !VERDICTS.contains(&row.verdict.as_str()))
        .map(|row| {
            generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "structural verdict must be one of the five AG verdict values",
            )
        })
        .collect::<Vec<_>>();
    check_examples(
        "measurement-packet-v1-five-verdict-values",
        "structural verdicts are limited to the five v0.4.0 values",
        examples,
    )
}

fn check_structural_verdict_data(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for row in &packet.structural_verdict {
        if row.verdict_data.zero && row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "zero+nonZero",
                "Zero_M and NonZero_M verdict data must not both be true",
            ));
        }
        if row.verdict == "measured_zero" && !row.verdict_data.zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_zero",
                "measured_zero requires zero=true in VerdictData",
            ));
        }
        if row.verdict == "measured_nonzero" && !row.verdict_data.non_zero {
            examples.push(generic_validation_example(
                &row.evaluator,
                "measured_nonzero",
                "measured_nonzero requires nonZero=true in VerdictData",
            ));
        }
        if matches!(
            row.verdict.as_str(),
            "unmeasured" | "unknown" | "not_computed"
        ) && (row.verdict_data.zero || row.verdict_data.non_zero)
        {
            examples.push(generic_validation_example(
                &row.evaluator,
                &row.verdict,
                "unmeasured, unknown, and not_computed are not zero or nonzero results",
            ));
        }
    }
    check_examples(
        "measurement-packet-v1-verdict-data-boundary",
        "VerdictData keeps zero, nonzero, unmeasured, unknown, and not_computed separate",
        examples,
    )
}

fn check_analytic_regime_boundary(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let structural_evaluators = packet
        .structural_verdict
        .iter()
        .map(|row| row.evaluator.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for reading in &packet.analytic_readings {
        if reading.regime.as_deref() == Some("theorem-candidate")
            && reading.structural_verdict_ref.is_some()
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                "structuralVerdictRef",
                "theorem-candidate readings must remain analytic-only",
            ));
        }
        if reading.regime.as_deref() == Some("theorem-candidate")
            && structural_evaluators.contains(reading.evaluator.as_str())
        {
            examples.push(generic_validation_example(
                &reading.reading_id,
                &reading.evaluator,
                "theorem-candidate reading must not reuse a structural verdict evaluator id",
            ));
        }
    }
    check_examples(
        "measurement-packet-v1-theorem-candidate-analytic-only",
        "theorem-candidate readings are flagged analytic readings and do not generate structural verdicts",
        examples,
    )
}

fn check_assumption_ledger(packet: &ArchSigMeasurementPacketV1) -> ValidationCheck {
    let violated = packet
        .assumptions
        .iter()
        .any(|entry| entry.status == "violated");
    let mut examples = Vec::new();
    for entry in &packet.assumptions {
        if !matches!(entry.status.as_str(), "checked" | "assumed" | "violated") {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.status,
                "assumption status must be checked, assumed, or violated",
            ));
        }
        if entry.status == "checked" && entry.checked_by.is_none() {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.assumption,
                "checked assumptions must record checkedBy",
            ));
        }
        if entry.status == "assumed" && entry.assumed_by.is_none() {
            examples.push(generic_validation_example(
                &entry.theorem_ref,
                &entry.assumption,
                "assumed assumptions must record assumedBy",
            ));
        }
    }
    if violated {
        for row in &packet.structural_verdict {
            if row.verdict != "not_computed" {
                examples.push(generic_validation_example(
                    &row.evaluator,
                    &row.verdict,
                    "violated assumptions require dependent structural verdicts to be not_computed",
                ));
            }
        }
    }
    check_examples(
        "measurement-packet-v1-assumption-ledger",
        "assumption ledger records checked / assumed / violated and fail-closed verdicts",
        examples,
    )
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet_fixture() -> ArchSigMeasurementPacketV1 {
        serde_json::from_value(json!({
            "schema": "archsig-measurement-packet/v1",
            "packetId": "measurement:test",
            "profile": {
                "schema": "measurement-profile/v1",
                "profileId": "profile:test",
                "siteRef": "archmap:/contexts",
                "coverRef": "cover:test",
                "coefficient": "F2",
                "effCoeff": "finite-linear-algebra@1",
                "witnessFamily": [],
                "resolutionSelector": "taylor@1",
                "domain": "finite-poset-site",
                "zeroPredicate": "rank-zero@1",
                "nonZeroPredicate": "rank-positive@1",
                "certSelector": "finite-certificate@1",
                "verdictDiscipline": "five-valued-structural-verdict@1"
            },
            "structuralVerdict": [{
                "evaluator": "ag.cech-obstruction@1",
                "law": "ag.cech-obstruction",
                "verdict": "unmeasured",
                "verdictData": {
                    "inScope": true,
                    "zero": false,
                    "nonZero": false,
                    "methodStatus": "schema_foundation_only"
                }
            }],
            "computedInvariants": [],
            "analyticReadings": [{
                "readingId": "candidate:test",
                "evaluator": "ag.foundation@1",
                "value": {"state": "not_evaluated"},
                "regime": "theorem-candidate",
                "structuralVerdictRef": null
            }],
            "assumptions": [{
                "theoremRef": "part8/4.2",
                "assumption": "finite site",
                "status": "checked",
                "checkedBy": "test"
            }],
            "nonConclusions": ["test fixture"]
        }))
        .expect("packet fixture parses")
    }

    #[test]
    fn invalid_structural_verdict_value_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict = "blocked".to_string();
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-v1-five-verdict-values" && check.result == "fail"
        }));
    }

    #[test]
    fn zero_and_nonzero_verdict_data_fails_validation() {
        let mut packet = packet_fixture();
        packet.structural_verdict[0].verdict_data.zero = true;
        packet.structural_verdict[0].verdict_data.non_zero = true;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-v1-verdict-data-boundary" && check.result == "fail"
        }));
    }

    #[test]
    fn violated_assumption_requires_not_computed_verdict() {
        let mut packet = packet_fixture();
        packet.assumptions[0].status = "violated".to_string();
        packet.assumptions[0].checked_by = None;
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-v1-assumption-ledger" && check.result == "fail"
        }));
    }

    #[test]
    fn theorem_candidate_reading_cannot_link_structural_verdict() {
        let mut packet = packet_fixture();
        packet.analytic_readings[0].structural_verdict_ref =
            Some("/structuralVerdict/0".to_string());
        let checks = validate_measurement_packet_v1(&packet);
        assert!(checks.iter().any(|check| {
            check.id == "measurement-packet-v1-theorem-candidate-analytic-only"
                && check.result == "fail"
        }));
    }
}
