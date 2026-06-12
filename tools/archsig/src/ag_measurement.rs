use std::collections::{BTreeMap, BTreeSet};

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
const MAX_SQUARE_FREE_WITNESS_VARIABLES: usize = 12;

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
    let mut structural_verdict = Vec::new();
    let mut computed_invariants = vec![json!({
        "invariantId": "finite-poset-site-shape",
        "archmapRef": archmap_ref,
        "atomCount": normalized.summary.atom_count,
        "contextCount": normalized.summary.context_count,
        "coverCount": normalized.summary.cover_count,
        "doctrineFingerprint": normalized.summary.doctrine_fingerprint
    })];
    let mut assumptions = vec![
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
    ];

    for entry in policy.policies.iter().filter(|entry| {
        entry
            .evaluator
            .as_deref()
            .is_some_and(|evaluator| evaluator.starts_with("ag."))
    }) {
        let evaluator = entry.evaluator.as_deref().unwrap_or_default();
        if evaluator == "ag.cech-obstruction@1" {
            validate_cech_profile_v1(&profile)?;
            let measurement = evaluate_cech_obstruction_v1(normalized, &profile);
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.cech-obstruction".to_string()),
                verdict: if measurement.h1_class_nonzero {
                    "measured_nonzero".to_string()
                } else {
                    "measured_zero".to_string()
                },
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: !measurement.h1_class_nonzero,
                    non_zero: measurement.h1_class_nonzero,
                    method_status: "finite_f2_cech_computed".to_string(),
                    cert_ref: Some(measurement.cert_ref),
                },
                reason: Some(if measurement.h1_class_nonzero {
                    "finite F2 Cech 1-cocycle is not a coboundary on the selected cover".to_string()
                } else {
                    "finite F2 Cech 1-cocycle is zero or a coboundary on the selected cover"
                        .to_string()
                }),
            });
        } else if evaluator == "ag.square-free-repair@1" {
            validate_square_free_profile_v1(&profile)?;
            let measurement = evaluate_square_free_repair_v1(normalized, &profile)?;
            computed_invariants.extend(measurement.computed_invariants);
            assumptions.extend(measurement.assumptions);
            structural_verdict.push(AgStructuralVerdictV1 {
                evaluator: evaluator.to_string(),
                law: entry
                    .law
                    .clone()
                    .unwrap_or_else(|| "ag.square-free-repair".to_string()),
                verdict: measurement.verdict,
                verdict_data: AgVerdictDataV1 {
                    in_scope: true,
                    zero: measurement.zero,
                    non_zero: measurement.non_zero,
                    method_status: measurement.method_status,
                    cert_ref: measurement.cert_ref,
                },
                reason: Some(measurement.reason),
            });
        } else {
            structural_verdict.push(AgStructuralVerdictV1 {
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
            });
        }
    }

    Ok(ArchSigMeasurementPacketV1 {
        schema: ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA.to_string(),
        packet_id: format!("measurement:{}", normalized.source_archmap_id),
        profile,
        structural_verdict,
        computed_invariants,
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
        assumptions,
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

#[derive(Debug, Clone)]
struct SquareFreeMeasurementV1 {
    verdict: String,
    zero: bool,
    non_zero: bool,
    method_status: String,
    cert_ref: Option<String>,
    reason: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct SquareFreeGeneratorV1 {
    generator_id: String,
    support: Vec<String>,
    support_atom_refs: Vec<String>,
}

#[derive(Debug, Clone)]
struct SquareFreeCertificateV1 {
    cert_ref: String,
    nsdepth: usize,
    support_atom_refs: Vec<String>,
}

fn evaluate_square_free_repair_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Result<SquareFreeMeasurementV1, String> {
    let selected_contexts = selected_cover_contexts(normalized, profile)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let witness_variables = square_free_witness_variables(profile);
    let generators = square_free_generators(normalized, &selected_contexts, &witness_variables)?;
    let minimal_forbidden_supports = minimal_supports(
        generators
            .iter()
            .map(|generator| generator.support.clone())
            .collect(),
    );
    let delta_faces = stanley_reisner_faces(&witness_variables, &minimal_forbidden_supports);
    let reduced_homology = reduced_simplicial_homology_f2(&delta_faces);
    let repair_hitting_sets = minimal_hitting_sets(&witness_variables, &minimal_forbidden_supports);
    let certificate = square_free_certificate(normalized, &selected_contexts)?;
    let has_obstruction = !minimal_forbidden_supports.is_empty();
    let (verdict, zero, non_zero, method_status, cert_ref, reason) = if !has_obstruction {
        (
            "measured_zero".to_string(),
            true,
            false,
            "square_free_ideal_computed".to_string(),
            certificate
                .as_ref()
                .map(|certificate| certificate.cert_ref.clone()),
            "square-free obstruction ideal has no selected generators".to_string(),
        )
    } else if let Some(certificate) = &certificate {
        (
            "unknown".to_string(),
            false,
            false,
            "nsdepth_certificate_author_supplied_unverified".to_string(),
            Some(certificate.cert_ref.clone()),
            "square-free obstruction generators were found and an NSdepth certificate reference was supplied, but no finite NSdepth verifier payload was checked; lawfulness is not concluded".to_string(),
        )
    } else {
        (
            "unknown".to_string(),
            false,
            false,
            "nsdepth_certificate_missing".to_string(),
            None,
            "square-free obstruction generators were found, but no NSdepth certificate was supplied; lawfulness is not concluded".to_string(),
        )
    };

    Ok(SquareFreeMeasurementV1 {
        verdict,
        zero,
        non_zero,
        method_status,
        cert_ref,
        reason,
        computed_invariants: vec![json!({
            "invariantId": format!("square-free-repair:{}", profile.profile_id),
            "evaluator": "ag.square-free-repair@1",
            "method": "finite-square-free-monomial-repair@1",
            "selectedCoverRef": profile.cover_ref,
            "witnessVariables": witness_variables,
            "obstructionIdeal": {
                "id": "I_Ob^U",
                "generators": generators.iter().map(|generator| {
                    json!({
                        "generatorId": generator.generator_id,
                        "support": generator.support,
                        "supportAtomRefs": generator.support_atom_refs
                    })
                }).collect::<Vec<_>>()
            },
            "minimalForbiddenSupports": minimal_forbidden_supports,
            "stanleyReisnerComplex": {
                "id": "Delta_U",
                "faces": delta_faces,
                "reducedHomology": {
                    "field": "F2",
                    "method": "finite-f2-simplicial-boundary@1",
                    "betti": reduced_homology
                }
            },
            "alexanderDualRepair": {
                "minimalHittingSets": repair_hitting_sets,
                "minimality": "checked_by_finite_support_enumeration"
            },
            "nsdepthCertificate": certificate.as_ref().map(|certificate| json!({
                "status": "author_supplied_unverified",
                "certificateRef": certificate.cert_ref,
                "nsdepth": certificate.nsdepth,
                "supportAtomRefs": certificate.support_atom_refs,
                "effect": "structural verdict remains unknown until a finite NSdepth verifier payload is checked"
            })).unwrap_or_else(|| json!({
                "status": "missing",
                "effect": "structural verdict remains unknown when obstruction generators are present"
            }))
        })],
        assumptions: vec![
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.1".to_string(),
                assumption: "square-free witness variables selected by MeasurementProfile"
                    .to_string(),
                status: "checked".to_string(),
                checked_by: Some(format!(
                    "measurement-profile:{}.witnessFamily",
                    profile.profile_id
                )),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/5.2".to_string(),
                assumption: "finite support family for Alexander dual enumeration".to_string(),
                status: "checked".to_string(),
                checked_by: Some("archmap-v2-validation.contexts-finite".to_string()),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part3/7.2B".to_string(),
                assumption: "NSdepth certificate value supplied by ArchMap author; finite verifier payload is not checked by this evaluator".to_string(),
                status: "assumed".to_string(),
                checked_by: None,
                assumed_by: Some(
                    certificate
                        .as_ref()
                        .map(|certificate| certificate.cert_ref.clone())
                        .unwrap_or_else(|| format!("measurement-profile:{}", profile.profile_id)),
                ),
            },
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
    let cech_nonzero = packet.structural_verdict.iter().any(|verdict| {
        verdict.evaluator == "ag.cech-obstruction@1" && verdict.verdict == "measured_nonzero"
    });
    let conclusion = if cech_nonzero {
        "MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    } else if nonzero_count > 0 {
        "MEASURED_AG_OBSTRUCTION_UNDER_PROFILE"
    } else if unmeasured_count > 0 {
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
    } else if nonzero_count == 0 {
        "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE"
    } else {
        "AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE"
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

#[derive(Debug, Clone)]
struct CechMeasurementV1 {
    h1_class_nonzero: bool,
    cert_ref: String,
    computed_invariants: Vec<Value>,
    assumptions: Vec<AgAssumptionLedgerEntryV1>,
}

#[derive(Debug, Clone)]
struct CechEdgeV1 {
    edge_id: String,
    source_context: String,
    target_context: String,
    value: u8,
    support_atom_refs: Vec<String>,
}

fn evaluate_cech_obstruction_v1(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> CechMeasurementV1 {
    let selected_contexts = selected_cover_contexts(normalized, profile);
    let edges = cech_edges(normalized, &selected_contexts);
    let component_count = graph_component_count(&selected_contexts, &edges);
    let h0_dimension = component_count;
    let h1_dimension = edges
        .len()
        .saturating_add(component_count)
        .saturating_sub(selected_contexts.len());
    let h1_class_nonzero = !edge_cochain_is_coboundary(&selected_contexts, &edges);
    let representative = edges
        .iter()
        .filter(|edge| edge.value == 1)
        .map(|edge| {
            json!({
                "edge": edge.edge_id,
                "sourceContext": edge.source_context,
                "targetContext": edge.target_context,
                "value": 1,
                "supportAtomRefs": edge.support_atom_refs
            })
        })
        .collect::<Vec<_>>();
    let mismatch_support_refs = edges
        .iter()
        .flat_map(|edge| edge.support_atom_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let witness_support_refs = witness_violation_support_refs(normalized);
    let witness_violation_count = witness_support_refs.len();

    CechMeasurementV1 {
        h1_class_nonzero,
        cert_ref: format!("computedInvariants/cech-cohomology:{}", profile.profile_id),
        computed_invariants: vec![
            json!({
                "invariantId": format!("cech-cohomology:{}", profile.profile_id),
                "evaluator": "ag.cech-obstruction@1",
                "method": "finite-f2-incidence-graph-cochain@1",
                "selectedCoverRef": profile.cover_ref,
                "coefficient": profile.coefficient,
                "contextCount": selected_contexts.len(),
                "restrictionEdgeCount": edges.len(),
                "rankD0": selected_contexts.len().saturating_sub(component_count),
                "dimensions": {
                    "H0": h0_dimension,
                    "H1": h1_dimension
                },
                "selectedH2": {
                    "dimension": 0,
                    "status": "computed_for_selected_1_skeleton",
                    "reason": "no selected 2-simplices are present in the finite incidence graph complex"
                },
                "observedCocycle": {
                    "classNonzero": h1_class_nonzero,
                    "representative": representative,
                    "mismatchSupportRefs": mismatch_support_refs
                }
            }),
            json!({
                "invariantId": format!("witness-counting:{}", profile.profile_id),
                "evaluator": "witness-counting@1",
                "verdict": if witness_violation_count == 0 {
                    "measured_zero"
                } else {
                    "measured_nonzero"
                },
                "violationCount": witness_violation_count,
                "supportAtomRefs": witness_support_refs,
                "nonConclusion": "Witness counting is reported as a fixture discriminator and does not determine Cech H1."
            }),
        ],
        assumptions: vec![
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/B.8.2".to_string(),
                assumption: "F2 finite coefficient field".to_string(),
                status: "checked".to_string(),
                checked_by: Some(format!(
                    "measurement-profile:{}.coefficient={}",
                    profile.profile_id, profile.coefficient
                )),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/B.8.2".to_string(),
                assumption: "cover-relative Cech reading".to_string(),
                status: "checked".to_string(),
                checked_by: Some(format!(
                    "measurement-profile:{}.coverRef",
                    profile.profile_id
                )),
                assumed_by: None,
            },
            AgAssumptionLedgerEntryV1 {
                theorem_ref: "part8/B.8.2".to_string(),
                assumption: "Leray / acyclicity comparison to sheaf cohomology".to_string(),
                status: "assumed".to_string(),
                checked_by: None,
                assumed_by: Some(format!("measurement-profile:{}", profile.profile_id)),
            },
        ],
    }
}

fn selected_cover_contexts(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> Vec<String> {
    normalized
        .covers
        .iter()
        .find(|cover| {
            cover.normalized_cover_id == profile.cover_ref
                || cover.source_cover_id == profile.cover_ref
        })
        .map(|cover| cover.context_ids.clone())
        .unwrap_or_default()
}

fn validate_cech_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.cech-obstruction@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if !profile
        .witness_family
        .iter()
        .any(|witness| witness.law == "ag.cech-obstruction")
    {
        return Err(format!(
            "ag.cech-obstruction@1 requires MeasurementProfile {} witnessFamily law ag.cech-obstruction",
            profile.profile_id
        ));
    }
    Ok(())
}

fn validate_square_free_profile_v1(profile: &MeasurementProfileV1) -> Result<(), String> {
    let expected = [
        ("coefficient", profile.coefficient.as_str(), "F2"),
        (
            "effCoeff",
            profile.eff_coeff.as_str(),
            "finite-linear-algebra@1",
        ),
        (
            "resolutionSelector",
            profile.resolution_selector.as_str(),
            "taylor@1",
        ),
        (
            "zeroPredicate",
            profile.zero_predicate.as_str(),
            "rank-zero@1",
        ),
        (
            "nonZeroPredicate",
            profile.non_zero_predicate.as_str(),
            "rank-positive@1",
        ),
        (
            "certSelector",
            profile.cert_selector.as_str(),
            "finite-certificate@1",
        ),
    ];
    for (field, actual, expected) in expected {
        if actual != expected {
            return Err(format!(
                "ag.square-free-repair@1 requires MeasurementProfile {field}={expected}, found {actual}"
            ));
        }
    }
    if square_free_witness_variables(profile).is_empty() {
        return Err(format!(
            "ag.square-free-repair@1 requires MeasurementProfile {} witnessFamily law ag.square-free-repair",
            profile.profile_id
        ));
    }
    if square_free_witness_variables(profile).len() > MAX_SQUARE_FREE_WITNESS_VARIABLES {
        return Err(format!(
            "ag.square-free-repair@1 supports at most {MAX_SQUARE_FREE_WITNESS_VARIABLES} witness variables for finite support enumeration"
        ));
    }
    Ok(())
}

fn square_free_witness_variables(profile: &MeasurementProfileV1) -> Vec<String> {
    profile
        .witness_family
        .iter()
        .filter(|witness| witness.law == "ag.square-free-repair")
        .map(|witness| witness.variable.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn square_free_generators(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
    witness_variables: &[String],
) -> Result<Vec<SquareFreeGeneratorV1>, String> {
    let witness_set = witness_variables.iter().cloned().collect::<BTreeSet<_>>();
    let mut generators = Vec::new();
    for atom in normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "square-free" && atom.predicate == "obstructionGenerator")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
    {
        let raw_variables = square_free_atom_variables(atom);
        let unknown = raw_variables
            .iter()
            .filter(|variable| !witness_set.contains(*variable))
            .cloned()
            .collect::<Vec<_>>();
        if !unknown.is_empty() {
            return Err(format!(
                "ag.square-free-repair@1 generator {} contains variables outside witnessFamily: {}",
                atom.normalized_atom_id,
                unknown.join(",")
            ));
        }
        if raw_variables.is_empty() {
            return Err(format!(
                "ag.square-free-repair@1 generator {} has no square-free witness variables",
                atom.normalized_atom_id
            ));
        }
        generators.push(SquareFreeGeneratorV1 {
            generator_id: atom.normalized_atom_id.clone(),
            support: raw_variables,
            support_atom_refs: vec![atom.normalized_atom_id.clone()],
        });
    }
    generators.sort_by(|left, right| left.generator_id.cmp(&right.generator_id));
    Ok(generators)
}

fn square_free_atom_variables(atom: &crate::NormalizedAtomV2) -> Vec<String> {
    let mut support = Vec::new();
    for value in std::iter::once(atom.subject.as_str()).chain(atom.object.as_deref()) {
        for variable in value
            .split(',')
            .map(str::trim)
            .filter(|value| !value.is_empty())
        {
            support.push(variable.to_string());
        }
    }
    support.sort();
    support.dedup();
    support
}

fn square_free_certificate(
    normalized: &NormalizedArchMapV2,
    selected_contexts: &BTreeSet<String>,
) -> Result<Option<SquareFreeCertificateV1>, String> {
    let certificates = normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "square-free" && atom.predicate == "nsdepthCertificate")
        .filter(|atom| atom_belongs_to_selected_context(atom, selected_contexts))
        .map(|atom| {
            let raw = atom.object.as_deref().ok_or_else(|| {
                format!(
                    "ag.square-free-repair@1 NSdepth certificate {} requires numeric object",
                    atom.normalized_atom_id
                )
            })?;
            let nsdepth = raw.parse::<usize>().map_err(|_| {
                format!(
                    "ag.square-free-repair@1 NSdepth certificate {} has non-numeric object {raw}",
                    atom.normalized_atom_id
                )
            })?;
            if nsdepth == 0 {
                return Err(format!(
                    "ag.square-free-repair@1 NSdepth certificate {} must have positive object",
                    atom.normalized_atom_id
                ));
            }
            Ok(SquareFreeCertificateV1 {
                cert_ref: atom.normalized_atom_id.clone(),
                nsdepth,
                support_atom_refs: vec![atom.normalized_atom_id.clone()],
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    if certificates.len() > 1 {
        return Err(format!(
            "ag.square-free-repair@1 expected at most one selected NSdepth certificate, found {}",
            certificates.len()
        ));
    }

    Ok(certificates.into_iter().next())
}

fn atom_belongs_to_selected_context(
    atom: &crate::NormalizedAtomV2,
    selected_contexts: &BTreeSet<String>,
) -> bool {
    atom.context_memberships
        .iter()
        .any(|membership| selected_contexts.contains(membership))
}

fn minimal_supports(mut supports: Vec<Vec<String>>) -> Vec<Vec<String>> {
    for support in &mut supports {
        support.sort();
        support.dedup();
    }
    supports.sort();
    supports.dedup();
    supports
        .iter()
        .filter(|support| {
            !supports.iter().any(|candidate| {
                candidate.len() < support.len()
                    && is_subset(candidate.as_slice(), support.as_slice())
            })
        })
        .cloned()
        .collect()
}

fn stanley_reisner_faces(
    witness_variables: &[String],
    minimal_forbidden_supports: &[Vec<String>],
) -> Vec<Vec<String>> {
    all_subsets(witness_variables)
        .into_iter()
        .filter(|face| {
            !minimal_forbidden_supports
                .iter()
                .any(|forbidden| is_subset(forbidden.as_slice(), face.as_slice()))
        })
        .collect()
}

fn reduced_simplicial_homology_f2(faces: &[Vec<String>]) -> Vec<Value> {
    let mut simplices_by_degree = BTreeMap::<usize, Vec<Vec<String>>>::new();
    for face in faces.iter().filter(|face| !face.is_empty()) {
        simplices_by_degree
            .entry(face.len() - 1)
            .or_default()
            .push(face.clone());
    }
    for simplices in simplices_by_degree.values_mut() {
        simplices.sort();
        simplices.dedup();
    }

    let max_degree = simplices_by_degree.keys().next_back().copied().unwrap_or(0);
    let mut betti = Vec::new();
    for degree in 0..=max_degree {
        let dim_chain = simplices_by_degree
            .get(&degree)
            .map_or(0, std::vec::Vec::len);
        let boundary_rank = if degree == 0 {
            usize::from(dim_chain > 0)
        } else {
            boundary_rank_f2(&simplices_by_degree, degree)
        };
        let next_boundary_rank = boundary_rank_f2(&simplices_by_degree, degree + 1);
        let dimension = dim_chain.saturating_sub(boundary_rank + next_boundary_rank);
        betti.push(json!({
            "degree": degree,
            "dimension": dimension
        }));
    }
    betti
}

fn boundary_rank_f2(
    simplices_by_degree: &BTreeMap<usize, Vec<Vec<String>>>,
    degree: usize,
) -> usize {
    if degree == 0 {
        return 0;
    }
    let Some(domain) = simplices_by_degree.get(&degree) else {
        return 0;
    };
    let Some(codomain) = simplices_by_degree.get(&(degree - 1)) else {
        return 0;
    };
    let row_index = codomain
        .iter()
        .enumerate()
        .map(|(index, simplex)| (simplex.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut rows = vec![vec![0u8; domain.len()]; codomain.len()];
    for (column, simplex) in domain.iter().enumerate() {
        for omitted in 0..simplex.len() {
            let mut facet = simplex.clone();
            facet.remove(omitted);
            if let Some(row) = row_index.get(&facet) {
                rows[*row][column] ^= 1;
            }
        }
    }
    matrix_rank_f2(rows)
}

fn matrix_rank_f2(mut rows: Vec<Vec<u8>>) -> usize {
    if rows.is_empty() {
        return 0;
    }
    let column_count = rows[0].len();
    let mut rank = 0;
    for column in 0..column_count {
        let Some(pivot) = (rank..rows.len()).find(|row| rows[*row][column] == 1) else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && rows[row][column] == 1 {
                for next_column in column..column_count {
                    rows[row][next_column] ^= rows[rank][next_column];
                }
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rank
}

fn minimal_hitting_sets(
    witness_variables: &[String],
    minimal_forbidden_supports: &[Vec<String>],
) -> Vec<Vec<String>> {
    if minimal_forbidden_supports.is_empty() {
        return Vec::new();
    }
    let hitting_sets = all_subsets(witness_variables)
        .into_iter()
        .filter(|candidate| !candidate.is_empty())
        .filter(|candidate| {
            minimal_forbidden_supports
                .iter()
                .all(|support| candidate.iter().any(|variable| support.contains(variable)))
        })
        .collect::<Vec<_>>();
    let mut minimal = minimal_supports(hitting_sets);
    minimal.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    minimal
}

fn all_subsets(items: &[String]) -> Vec<Vec<String>> {
    let mut subsets = Vec::new();
    let limit = 1usize << items.len();
    for mask in 0..limit {
        let mut subset = Vec::new();
        for (index, item) in items.iter().enumerate() {
            if mask & (1usize << index) != 0 {
                subset.push(item.clone());
            }
        }
        subsets.push(subset);
    }
    subsets.sort();
    subsets
}

fn is_subset(left: &[String], right: &[String]) -> bool {
    left.iter().all(|item| right.contains(item))
}

fn cech_edges(normalized: &NormalizedArchMapV2, selected_contexts: &[String]) -> Vec<CechEdgeV1> {
    let selected = selected_contexts.iter().cloned().collect::<BTreeSet<_>>();
    let marker_atoms = normalized
        .atoms
        .iter()
        .filter(|atom| {
            atom.axis == "cech"
                && matches!(
                    atom.predicate.as_str(),
                    "mismatch" | "cechMismatch" | "residue"
                )
        })
        .collect::<Vec<_>>();
    let mut seen_edges = BTreeSet::new();
    let mut edges = Vec::new();
    for context in &normalized.contexts {
        if !selected.contains(&context.normalized_context_id) {
            continue;
        }
        for target in context
            .restricts_to
            .iter()
            .filter(|target| selected.contains(*target))
        {
            let edge_key = if context.normalized_context_id < *target {
                (
                    context.normalized_context_id.clone(),
                    target.clone(),
                    context.normalized_context_id.clone(),
                    target.clone(),
                )
            } else {
                (
                    target.clone(),
                    context.normalized_context_id.clone(),
                    context.normalized_context_id.clone(),
                    target.clone(),
                )
            };
            if !seen_edges.insert((edge_key.0.clone(), edge_key.1.clone())) {
                continue;
            }
            let support_atom_refs = marker_atoms
                .iter()
                .filter(|atom| marker_atom_marks_edge(atom, &edge_key.2, &edge_key.3))
                .map(|atom| atom.normalized_atom_id.clone())
                .collect::<Vec<_>>();
            edges.push(CechEdgeV1 {
                edge_id: format!("{}->{}", edge_key.2, edge_key.3),
                source_context: edge_key.2,
                target_context: edge_key.3,
                value: (support_atom_refs.len() % 2) as u8,
                support_atom_refs,
            });
        }
    }
    edges.sort_by(|left, right| left.edge_id.cmp(&right.edge_id));
    edges
}

fn marker_atom_marks_edge(
    atom: &crate::NormalizedAtomV2,
    source_context: &str,
    target_context: &str,
) -> bool {
    let source_matches =
        atom.subject == source_context || atom.subject == unprefixed(source_context);
    let object_matches = atom
        .object
        .as_deref()
        .is_some_and(|object| object == target_context || object == unprefixed(target_context));
    let target_matches = atom
        .source_refs
        .iter()
        .any(|value| value == target_context || value == unprefixed(target_context));
    let source_ref_matches = atom
        .source_refs
        .iter()
        .any(|value| value == source_context || value == unprefixed(source_context));
    let context_membership_matches = atom.context_memberships.iter().any(|membership| {
        membership == source_context
            || membership == target_context
            || membership == unprefixed(source_context)
            || membership == unprefixed(target_context)
    });
    source_matches
        && object_matches
        && source_ref_matches
        && target_matches
        && context_membership_matches
}

fn unprefixed(value: &str) -> &str {
    value
        .split_once(':')
        .map(|(_, suffix)| suffix)
        .unwrap_or(value)
}

fn graph_component_count(selected_contexts: &[String], edges: &[CechEdgeV1]) -> usize {
    let adjacency = adjacency_map(selected_contexts, edges);
    let mut visited = BTreeSet::new();
    let mut components = 0usize;
    for context in selected_contexts {
        if visited.contains(context) {
            continue;
        }
        components += 1;
        let mut stack = vec![context.clone()];
        while let Some(current) = stack.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for next in adjacency.get(&current).into_iter().flatten() {
                if !visited.contains(next) {
                    stack.push(next.clone());
                }
            }
        }
    }
    components
}

fn edge_cochain_is_coboundary(selected_contexts: &[String], edges: &[CechEdgeV1]) -> bool {
    let adjacency = valued_adjacency_map(selected_contexts, edges);
    let mut potentials: BTreeMap<String, u8> = BTreeMap::new();
    for context in selected_contexts {
        if potentials.contains_key(context) {
            continue;
        }
        potentials.insert(context.clone(), 0);
        let mut stack = vec![context.clone()];
        while let Some(current) = stack.pop() {
            let current_value = *potentials.get(&current).unwrap_or(&0);
            for (next, edge_value) in adjacency.get(&current).into_iter().flatten() {
                let expected = current_value ^ *edge_value;
                match potentials.get(next) {
                    Some(existing) if *existing != expected => return false,
                    Some(_) => {}
                    None => {
                        potentials.insert(next.clone(), expected);
                        stack.push(next.clone());
                    }
                }
            }
        }
    }
    true
}

fn adjacency_map(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
) -> BTreeMap<String, Vec<String>> {
    let mut adjacency = selected_contexts
        .iter()
        .map(|context| (context.clone(), Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in edges {
        adjacency
            .entry(edge.source_context.clone())
            .or_default()
            .push(edge.target_context.clone());
        adjacency
            .entry(edge.target_context.clone())
            .or_default()
            .push(edge.source_context.clone());
    }
    adjacency
}

fn valued_adjacency_map(
    selected_contexts: &[String],
    edges: &[CechEdgeV1],
) -> BTreeMap<String, Vec<(String, u8)>> {
    let mut adjacency = selected_contexts
        .iter()
        .map(|context| (context.clone(), Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in edges {
        adjacency
            .entry(edge.source_context.clone())
            .or_default()
            .push((edge.target_context.clone(), edge.value));
        adjacency
            .entry(edge.target_context.clone())
            .or_default()
            .push((edge.source_context.clone(), edge.value));
    }
    adjacency
}

fn witness_violation_support_refs(normalized: &NormalizedArchMapV2) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .filter(|atom| atom.axis == "witness" && atom.predicate == "violation")
        .map(|atom| atom.normalized_atom_id.clone())
        .collect()
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
